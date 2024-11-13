//! A simple state management library inspired by Redux, supporting multiple state types.
use std::{
    fmt::Debug,
    any::{Any, TypeId},
    collections::{HashMap, VecDeque},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering}, Mutex,
    }
};

pub type SubscriberId = usize;
type Shared<T> = Arc<Mutex<T>>;

/// Trait that all state types must implement. States must be clonable, debuggable and thread-safe.
pub trait State: Debug + Sized + Clone + Send + Sync + 'static {}

/// Trait that all action types must implement. Actions should define how they transform the state.
pub trait Action<S: State>: Send + 'static {
    fn reduce(&self, state: S) -> S;
}

/// Enum representing different error types that can occur within the store.
#[derive(Debug, PartialEq)]
pub enum StoreError {
    StateNotFound,
    WrongStateType,
    StateAlreadyExists,
    LockError,
}

/// Struct representing a container that holds a state and its subscribers.
struct Container<S: State> {
    state: Shared<S>,
    subscribers: Shared<Vec<(SubscriberId, Box<dyn Fn(&S) + Send + Sync>)>>,
    next_subscriber_id: Arc<AtomicUsize>,
}

impl<S: State> Container<S> {
    /// Creates a new `Container` with the given initial state.
    fn new(initial_state: S) -> Self {
        Container {
            state: Arc::new(Mutex::new(initial_state)),
            subscribers: Arc::new(Mutex::new(Vec::new())),
            next_subscriber_id: Arc::new(AtomicUsize::new(0)),
        }
    }

    /// Retrieves the current state.
    fn get_state(&self) -> Result<S, StoreError> {
        self.state
            .lock()
            .map(|state| state.clone())
            .map_err(|_| StoreError::LockError)
    }

    /// Applies an action to the current state.
    fn apply_action<A: Action<S>>(&self, action: A) -> Result<(), StoreError> {
        let mut state = self.state.lock().map_err(|_| StoreError::LockError)?;
        let new_state = action.reduce(state.clone());
        *state = new_state.clone();
        drop(state);

        let subscribers = self.subscribers.lock().map_err(|_| StoreError::LockError)?;
        for (_, subscriber) in subscribers.iter() {
            subscriber(&new_state);
        }
        Ok(())
    }

    /// Subscribes to state changes with a given callback.
    fn subscribe<F: Fn(&S) + Send + Sync + 'static>(&self, callback: F) -> Result<SubscriberId, StoreError> {
        let id = self.next_subscriber_id.fetch_add(1, Ordering::SeqCst);
        let mut subscribers = self.subscribers.lock().map_err(|_| StoreError::LockError)?;
        subscribers.push((id, Box::new(callback)));
        Ok(id)
    }

    /// Unsubscribes from state changes using the given subscriber ID.
    fn unsubscribe(&self, id: SubscriberId) -> Result<(), StoreError> {
        let mut subscribers = self.subscribers.lock().map_err(|_| StoreError::LockError)?;
        subscribers.retain(|(sub_id, _)| *sub_id != id);
        Ok(())
    }
}

/// The Store struct holding multiple containers for different state types.
#[derive(Clone)]
pub struct Store {
    containers: Shared<HashMap<TypeId, Box<dyn Any + Send + Sync>>>,
    action_queue: Shared<VecDeque<Box<dyn FnOnce(&HashMap<TypeId, Box<dyn Any + Send + Sync>>) + Send + 'static>>>,
}

impl Store {
    /// Creates a new, empty store.
    ///
    /// # Returns
    /// A new instance of `Store`.
    ///
    /// # Examples
    /// ```
    /// use sovran_state::Store;
    ///
    /// let store = Store::new();
    /// ```
    pub fn new() -> Self {
        Store {
            containers: Arc::new(Mutex::new(HashMap::new())),
            action_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    /// Provides an initial state of a certain type to the store.
    ///
    /// # Arguments
    /// * `initial_state` - The initial state to be held in the store.
    ///
    /// # Returns
    /// A `Result` indicating success or failure.
    ///
    /// # Examples
    /// ```
    /// use sovran_state::{Store, State, StoreError};
    ///
    /// #[derive(Clone, Debug)]
    /// struct MyState {
    ///     value: i32,
    /// }
    ///
    /// impl State for MyState {}
    ///
    /// let store = Store::new();
    /// match store.provide(MyState { value: 20 }) {
    ///     Ok(_) => println!("State provided successfully"),
    ///     Err(err) => println!("Failed to provide state: {:?}", err),
    /// }
    /// ```
    pub fn provide<S: State>(&self, initial_state: S) -> Result<(), StoreError> {
        let mut containers = self.containers.lock().map_err(|_| StoreError::LockError)?;
        if containers.contains_key(&TypeId::of::<S>()) {
            return Err(StoreError::StateAlreadyExists);
        }
        containers.insert(TypeId::of::<S>(), Box::new(Container::<S>::new(initial_state)));
        Ok(())
    }

    /// Retrieves the current state of a given type.
    ///
    /// # Returns
    /// A `Result` containing the state on success, or a `StoreError` on failure.
    ///
    /// # Examples
    /// ```
    /// use sovran_state::{Store, State, StoreError};
    ///
    /// #[derive(Clone, Debug)]
    /// struct MyState {
    ///     value: i32,
    /// }
    ///
    /// impl State for MyState {}
    ///
    /// let store = Store::new();
    /// store.provide(MyState { value: 20 }).unwrap();
    /// match store.get_state::<MyState>() {
    ///     Ok(state) => println!("State value: {}", state.value),
    ///     Err(err) => println!("Failed to get state: {:?}", err),
    /// }
    /// ```
    pub fn get_state<S: State>(&self) -> Result<S, StoreError> {
        let containers = self.containers.lock().map_err(|_| StoreError::LockError)?;
        let container = containers
            .get(&TypeId::of::<S>())
            .ok_or(StoreError::StateNotFound)?;
        let state = container
            .downcast_ref::<Container<S>>()
            .ok_or(StoreError::WrongStateType)?
            .get_state()?;
        Ok(state)
    }

    /// Dispatches an action to the store, affecting the state of a specific type.
    ///
    /// # Arguments
    /// * `action` - An action that transforms the state.
    ///
    /// # Returns
    /// A `Result` indicating success or failure.
    ///
    /// # Examples
    /// ```
    /// use sovran_state::{Store, State, Action, StoreError};
    ///
    /// #[derive(Clone, Debug)]
    /// struct MyState {
    ///     value: i32,
    /// }
    ///
    /// impl State for MyState {}
    ///
    /// struct IncrementAction;
    ///
    /// impl Action<MyState> for IncrementAction {
    ///     fn reduce(&self, state: MyState) -> MyState {
    ///         MyState { value: state.value + 1 }
    ///     }
    /// }
    ///
    /// let store = Store::new();
    /// store.provide(MyState { value: 0 }).unwrap();
    /// match store.dispatch(IncrementAction) {
    ///     Ok(_) => println!("Action dispatched successfully"),
    ///     Err(err) => println!("Failed to dispatch action: {:?}", err),
    /// }
    /// ```
    pub fn dispatch<S: State, A: Action<S> + Send + 'static>(&self, action: A) -> Result<(), StoreError> {
        let mut queue = self.action_queue.lock().map_err(|_| StoreError::LockError)?;

        if self.containers.lock().map_err(|_| StoreError::LockError)?.get(&TypeId::of::<S>()).is_some() {
            queue.push_back(Box::new(move |containers: &HashMap<TypeId, Box<dyn Any + Send + Sync>>| {
                if let Some(container) = containers.get(&TypeId::of::<S>()) {
                    container
                        .downcast_ref::<Container<S>>()
                        .unwrap()
                        .apply_action(action)
                        .expect("action application should not fail");
                }
            }));

            drop(queue);
            self.process_actions();
            Ok(())
        } else {
            Err(StoreError::StateNotFound)
        }
    }

    /// Processes all actions in the action queue, applying them to the relevant states.
    fn process_actions(&self) {
        let mut queue = self.action_queue.lock().unwrap();
        let containers = self.containers.lock().unwrap();

        while let Some(apply_action) = queue.pop_front() {
            apply_action(&*containers);
        }
    }

    /// Subscribes to state changes of a specific type with a given callback. The callback will
    /// receive the current state of the type immediately.
    ///
    /// # Arguments
    /// * `callback` - A callback function that will be invoked when the state changes.
    ///
    /// # Returns
    /// A `Result` containing the subscriber ID on success, or a `StoreError` on failure.
    ///
    /// # Examples
    /// ```
    /// use sovran_state::{Store, State, StoreError};
    ///
    /// #[derive(Clone, Debug)]
    /// struct MyState {
    ///     value: i32,
    /// }
    ///
    /// impl State for MyState {}
    ///
    /// let store = Store::new();
    /// store.provide(MyState { value: 10 }).unwrap();
    /// match store.subscribe(|state: &MyState| {
    ///     println!("State changed: {:?}", state);
    /// }) {
    ///     Ok(subscriber_id) => println!("Subscribed with ID: {}", subscriber_id),
    ///     Err(err) => println!("Failed to subscribe: {:?}", err),
    /// }
    /// ```
    pub fn subscribe<S: State, F: Fn(&S) + Send + Sync + 'static>(&self, callback: F) -> Result<SubscriberId, StoreError> {
        let containers = self.containers.lock().map_err(|_| StoreError::LockError)?;
        let container = containers.get(&TypeId::of::<S>()).ok_or(StoreError::StateNotFound)?;
        let container = container
            .downcast_ref::<Container<S>>()
            .ok_or(StoreError::WrongStateType)?;

        // Get current state and call the callback immediately
        let current_state = container.get_state()?;
        callback(&current_state);

        // Subscribe to future updates
        let id = container.subscribe(callback)?;
        Ok(id)
    }

    /// Unsubscribes from state changes of a specific type using the given subscriber ID.
    ///
    /// # Arguments
    /// * `id` - The ID of the subscriber to be removed.
    ///
    /// # Returns
    /// A `Result` indicating success or failure.
    ///
    /// # Examples
    /// ```
    /// use sovran_state::{Store, State, StoreError};
    ///
    /// #[derive(Clone, Debug)]
    /// struct MyState {
    ///     value: i32,
    /// }
    ///
    /// impl State for MyState {}
    ///
    /// let store = Store::new();
    /// store.provide(MyState { value: 10 }).unwrap();
    /// let id = store.subscribe(|state: &MyState| {
    ///     println!("State changed: {:?}", state);
    /// }).unwrap();
    /// match store.unsubscribe::<MyState>(id) {
    ///     Ok(_) => println!("Unsubscribed successfully"),
    ///     Err(err) => println!("Failed to unsubscribe: {:?}", err),
    /// }
    /// ```
    pub fn unsubscribe<S: State>(&self, id: SubscriberId) -> Result<(), StoreError> {
        let containers = self.containers.lock().map_err(|_| StoreError::LockError)?;
        let container = containers.get(&TypeId::of::<S>()).ok_or(StoreError::StateNotFound)?;
        container
            .downcast_ref::<Container<S>>()
            .ok_or(StoreError::WrongStateType)?
            .unsubscribe(id)?;
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    //use std::cell::{Ref, RefCell};
    use std::time::Duration;
    use std::thread;
    use super::*;

    #[derive(Clone, Debug)]
    struct MyState {
        value: i32,
    }

    impl State for MyState {}

    struct TestIncrementAction;

    impl Action<MyState> for TestIncrementAction {
        fn reduce(&self, state: MyState) -> MyState {
            MyState { value: state.value + 1 }
        }
    }

    #[derive(Clone, Debug)]
    struct AnotherState {
        count: i32,
    }

    impl State for AnotherState {}

    struct AnotherIncrementAction;

    impl Action<AnotherState> for AnotherIncrementAction {
        fn reduce(&self, state: AnotherState) -> AnotherState {
            AnotherState { count: state.count + 1 }
        }
    }

    #[derive(Clone)]
    struct SetValueAction(i32);

    impl Action<MyState> for SetValueAction {
        fn reduce(&self, _state: MyState) -> MyState {
            MyState { value: self.0 }
        }
    }

    #[test]
    fn test_store_creation() {
        let store = Store::new();
        store.provide(MyState { value: 10 }).unwrap();

        assert_eq!(store.get_state::<MyState>().unwrap().value, 10);
    }

    #[test]
    fn test_provide_state_already_exists() {
        let store = Store::new();
        assert!(store.provide(MyState { value: 10 }).is_ok());
        let result = store.provide(MyState { value: 20 });
        assert_eq!(result, Err(StoreError::StateAlreadyExists));
    }

    #[test]
    fn test_dispatch_action() {
        let store = Store::new();
        store.provide(MyState { value: 0 }).unwrap();

        assert!(store.dispatch(TestIncrementAction).is_ok());
        thread::sleep(Duration::from_millis(100));
        assert_eq!(store.get_state::<MyState>().unwrap().value, 1);
    }

    #[test]
    fn test_dispatch_multiple_actions() {
        let store = Store::new();
        store.provide(MyState { value: 0 }).unwrap();

        assert!(store.dispatch(TestIncrementAction).is_ok());
        assert!(store.dispatch(TestIncrementAction).is_ok());
        assert!(store.dispatch(TestIncrementAction).is_ok());
        thread::sleep(Duration::from_millis(100));
        assert_eq!(store.get_state::<MyState>().unwrap().value, 3);
    }

    #[test]
    fn test_dispatch_fifo_order() {
        let store = Store::new();
        store.provide(MyState { value: 0 }).unwrap();

        assert!(store.dispatch(SetValueAction(5)).is_ok());
        assert!(store.dispatch(SetValueAction(10)).is_ok());
        assert!(store.dispatch(SetValueAction(15)).is_ok());
        thread::sleep(Duration::from_millis(100));
        assert_eq!(store.get_state::<MyState>().unwrap().value, 15);
    }

    #[test]
    fn test_get_state() {
        let store = Store::new();
        let initial_state = MyState { value: 42 };
        store.provide(initial_state.clone()).unwrap();

        let state = store.get_state::<MyState>().unwrap();
        assert_eq!(state.value, initial_state.value);
    }

    #[test]
    fn test_dispatch_non_existent_state() {
        let store = Store::new();

        let result = store.dispatch(TestIncrementAction);
        assert_eq!(result, Err(StoreError::StateNotFound));
    }

    #[test]
    fn test_get_non_existent_state() {
        let store = Store::new();

        let result = store.get_state::<MyState>();
        match result {
            Err(StoreError::StateNotFound) => (),
            _ => panic!("Expected StateNotFound error"),
        }
    }

    #[test]
    fn test_subscription() {
        let store = Store::new();
        store.provide(MyState { value: 0 }).unwrap();

        let subscriber_called = Arc::new(Mutex::new(false));
        let subscriber_called_clone = subscriber_called.clone();

        let subscriber_id = store.subscribe(move |state: &MyState| {
            println!("Subscriber called with state: {:?}", state);
            let mut called = subscriber_called_clone.lock().unwrap();
            *called = true;
        }).unwrap();

        assert!(store.dispatch(TestIncrementAction).is_ok());
        thread::sleep(Duration::from_millis(100));

        assert_eq!(*subscriber_called.lock().unwrap(), true);

        // state made it to 1.
        let s = store.get_state::<MyState>().unwrap();
        assert_eq!(s.value, 1);

        // Test unsubscribe
        store.unsubscribe::<MyState>(subscriber_id).unwrap();

        *subscriber_called.lock().unwrap() = false;
        assert!(store.dispatch(TestIncrementAction).is_ok());
        thread::sleep(Duration::from_millis(100));

        // Subscriber should no longer be called
        assert_eq!(*subscriber_called.lock().unwrap(), false);
    }

    #[test]
    fn test_subscription_initial_update() {
        let store = Store::new();
        store.provide(MyState { value: 0 }).unwrap();

        let initial_callback_called = Arc::new(Mutex::new(false));
        let initial_callback_called_clone = initial_callback_called.clone();

        // Create a subscriber that tracks if it was called
        let subscriber_id = store.subscribe(move |_state: &MyState| {
            let mut called = initial_callback_called_clone.lock().unwrap();
            *called = true;
        }).unwrap();

        // Verify the initial state was supplied, scope the lock
        {
            assert_eq!(*initial_callback_called.lock().unwrap(), true);
        }

        // Reset the flag, scope the lock
        {
            *initial_callback_called.lock().unwrap() = false;
        }

        // Verify the a second update still works
        store.dispatch(TestIncrementAction).unwrap();
        thread::sleep(Duration::from_millis(100));
        assert_eq!(*initial_callback_called.lock().unwrap(), true);

        // Cleanup
        store.unsubscribe::<MyState>(subscriber_id).unwrap();
    }

    #[test]
    fn test_multithreading_stress_test() {
        let store = Store::new();
        thread::sleep(Duration::from_millis(100));

        let num_threads = 10;
        let num_actions_per_thread = 10000; // Reduced for quicker tests

        // Provide multiple states
        store.provide(MyState { value: 0 }).unwrap();
        store.provide(AnotherState { count: 0 }).unwrap();

        let sub1_inc = Arc::new(Mutex::new(0));  // Wrap sub1_inc in Arc<Mutex<i32>>
        let sub1_inc_clone = Arc::clone(&sub1_inc);  // Clone it for the closure
        // Subscribe and increment sub1_inc within the closure
        _ = store.subscribe(move |_state: &MyState| {
            let mut count = sub1_inc_clone.lock().unwrap();  // Lock the mutex to get mutable access
            *count += 1;
        });

        let sub2_inc = Arc::new(Mutex::new(0));  // Wrap sub1_inc in Arc<Mutex<i32>>
        let sub2_inc_clone = Arc::clone(&sub2_inc);  // Clone it for the closure

        // Subscribe and increment sub1_inc within the closure
        _ = store.subscribe(move |_state: &AnotherState| {
            let mut count = sub2_inc_clone.lock().unwrap();  // Lock the mutex to get mutable access
            *count += 1;
        });

        let mut handles = vec![];

        use std::time::Instant;
        let start_time = Instant::now();

        for _ in 0..num_threads {
            let store_clone = store.clone();
            let handle = thread::spawn(move || {
                for _ in 0..num_actions_per_thread {
                    store_clone.dispatch(TestIncrementAction).unwrap();
                    store_clone.dispatch(AnotherIncrementAction).unwrap();
                }
            });
            handles.push(handle);
        }

        // Collecting all thread handles to ensure they finish execution
        for handle in handles {
            handle.join().unwrap();
        }

        let duration = start_time.elapsed();
        println!("Time taken for 200_000 actions (2 per thread): {:?}", duration);

        // Calculate the expected value
        let expected_my_state_value = num_threads * num_actions_per_thread;
        let expected_another_state_count = num_threads * num_actions_per_thread;

        // Check states with debugging output
        let my_state = store.get_state::<MyState>().unwrap();
        let another_state = store.get_state::<AnotherState>().unwrap();

        println!("MyState value: {}", my_state.value);
        println!("AnotherState count: {}", another_state.count);

        assert_eq!(my_state.value, expected_my_state_value);
        assert_eq!(another_state.count, expected_another_state_count);

        let sub1_called = sub1_inc.lock().unwrap().clone();
        let sub2_called = sub2_inc.lock().unwrap().clone();

        println!("Subscriber 1 called {} times", sub1_called);
        println!("Subscriber 2 called {} times", sub2_called);

        // +1 because the initial state was dispatched
        assert_eq!(sub1_called, expected_my_state_value + 1);
        assert_eq!(sub2_called, expected_another_state_count + 1);
    }
}
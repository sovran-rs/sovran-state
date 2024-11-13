# sovran-state

A lightweight, Redux-inspired state management library for Rust that encourages composable, granular state management. Unlike traditional Redux which uses a single state tree, sovran-state allows you to maintain multiple independent state containers, making it ideal for modular applications.

## Features

- 🚀 Multiple state containers in a single store
- 🔒 Thread-safe state management
- 🎯 Type-safe actions and state updates
- 📦 Zero dependencies
- 🔄 Predictable state updates through actions
- 📢 Subscribe to specific state changes
- ⚡ Efficient action dispatching with FIFO ordering

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
sovran-state = "0.1.0"
```

## Quick Start

```rust
use sovran_state::{Store, State, Action};

// Define your state
#[derive(Clone, Debug)]
struct CounterState {
    value: i32,
}

impl State for CounterState {}

// Define an action
struct IncrementAction;

impl Action<CounterState> for IncrementAction {
    fn reduce(&self, state: CounterState) -> CounterState {
        CounterState { value: state.value + 1 }
    }
}

// Use the store
fn main() {
    // Create a new store
    let store = Store::new();
    
    // Provide initial state
    store.provide(CounterState { value: 0 }).unwrap();
    
    // Subscribe to state changes
    store.subscribe(|state: &CounterState| {
        println!("Counter value: {}", state.value);
    }).unwrap();
    
    // Dispatch an action
    store.dispatch(IncrementAction).unwrap();
}
```

## Why sovran-state?

While Redux is great for JavaScript applications, its pattern of using a single state tree doesn't always translate well to Rust applications. sovran-state takes the best parts of Redux (predictable state updates, action-based mutations) and adapts them to be more idiomatic in Rust:

- **Multiple State Types**: Instead of maintaining a giant state object, you can have multiple smaller, focused state containers.
- **Type Safety**: Leverage Rust's type system to ensure type-safe state updates and action handling.
- **Thread Safety**: Built with concurrency in mind, making it suitable for multi-threaded applications.
- **Modular Design**: Each state type is independent, making it easier to maintain and test different parts of your application.

## Usage Examples

### Managing Multiple States

```rust
use sovran_state::{Store, State, Action};

// First state type
#[derive(Clone, Debug)]
struct UserState {
    name: String,
    logged_in: bool,
}

impl State for UserState {}

// Second state type
#[derive(Clone, Debug)]
struct ThemeState {
    dark_mode: bool,
}

impl State for ThemeState {}

// Actions
struct LoginAction(String);
struct ToggleThemeAction;

impl Action<UserState> for LoginAction {
    fn reduce(&self, state: UserState) -> UserState {
        UserState {
            name: self.0.clone(),
            logged_in: true,
        }
    }
}

impl Action<ThemeState> for ToggleThemeAction {
    fn reduce(&self, state: ThemeState) -> ThemeState {
        ThemeState { dark_mode: !state.dark_mode }
    }
}

// Usage
let store = Store::new();

// Provide initial states
store.provide(UserState { name: String::new(), logged_in: false }).unwrap();
store.provide(ThemeState { dark_mode: false }).unwrap();

// Subscribe to specific state changes
store.subscribe(|user: &UserState| {
    println!("User state changed: {:?}", user);
}).unwrap();

store.subscribe(|theme: &ThemeState| {
    println!("Theme changed: {:?}", theme);
}).unwrap();

// Dispatch actions
store.dispatch(LoginAction("Alice".to_string())).unwrap();
store.dispatch(ToggleThemeAction).unwrap();
```

### Thread-Safe State Management

```rust
use std::thread;
use sovran_state::{Store, State, Action};

#[derive(Clone, Debug)]
struct CounterState {
    value: i32,
}

impl State for CounterState {}

struct IncrementAction;

impl Action<CounterState> for IncrementAction {
    fn reduce(&self, state: CounterState) -> CounterState {
        CounterState { value: state.value + 1 }
    }
}

let store = Store::new();
store.provide(CounterState { value: 0 }).unwrap();

let store_clone = store.clone();
let handle = thread::spawn(move || {
    store_clone.dispatch(IncrementAction).unwrap();
});

handle.join().unwrap();
```

## Error Handling

The library uses a `StoreError` enum to handle various error cases:

```rust
pub enum StoreError {
    StateNotFound,
    WrongStateType,
    StateAlreadyExists,
    LockError,
}
```

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

MIT License

Copyright (c) 2024 Sovran.la, Inc.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.


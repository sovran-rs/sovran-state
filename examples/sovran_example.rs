use sovran_state::{Store, State, Action};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

// Define our state
#[derive(Clone, Debug)]
struct BankState {
    balance: f64,
    transaction_count: u32,
}

impl State for BankState {}

// Define our actions
struct DepositAction(f64);
struct WithdrawAction(f64);

impl Action<BankState> for DepositAction {
    fn reduce(&self, state: BankState) -> BankState {
        BankState {
            balance: state.balance + self.0,
            transaction_count: state.transaction_count + 1,
        }
    }
}

impl Action<BankState> for WithdrawAction {
    fn reduce(&self, state: BankState) -> BankState {
        BankState {
            balance: state.balance - self.0,
            transaction_count: state.transaction_count + 1,
        }
    }
}

// Define some example components that use the state
struct AccountMonitor {
    store: Arc<Store>,
}

struct TransactionLogger {
    store: Arc<Store>,
}

impl AccountMonitor {
    fn new(store: Arc<Store>) -> Self {
        let monitor = AccountMonitor { store: store.clone() };

        // Subscribe to state changes
        monitor.store.subscribe(move |state: &BankState| {
            println!("🏦 Account Monitor: Balance changed to ${:.2}", state.balance);
        }).expect("Failed to subscribe to state changes");

        monitor
    }

    fn check_balance(&self) -> f64 {
        self.store.get_state::<BankState>()
            .map(|state| state.balance)
            .unwrap_or(0.0)
    }
}

impl TransactionLogger {
    fn new(store: Arc<Store>) -> Self {
        let logger = TransactionLogger { store: store.clone() };

        // Subscribe to state changes
        logger.store.subscribe(move |state: &BankState| {
            println!("📝 Transaction Logger: Transaction #{} processed",
                     state.transaction_count);
        }).expect("Failed to subscribe to state changes");

        logger
    }
}

fn main() {
    // Create store and provide initial state
    let store = Arc::new(Store::new());
    store.provide(BankState {
        balance: 1000.0,
        transaction_count: 0,
    }).expect("Failed to provide initial state");

    // Create our components
    let monitor = AccountMonitor::new(store.clone());
    let _logger = TransactionLogger::new(store.clone());

    println!("Initial balance: ${:.2}", monitor.check_balance());

    // Simulate some transactions
    println!("\nProcessing transactions...\n");

    // Deposit
    store.dispatch(DepositAction(500.0))
        .expect("Failed to process deposit");
    thread::sleep(Duration::from_millis(500));

    // Withdraw
    store.dispatch(WithdrawAction(200.0))
        .expect("Failed to process withdrawal");
    thread::sleep(Duration::from_millis(500));

    // Deposit again
    store.dispatch(DepositAction(750.0))
        .expect("Failed to process deposit");
    thread::sleep(Duration::from_millis(500));

    println!("\nFinal balance: ${:.2}", monitor.check_balance());
}
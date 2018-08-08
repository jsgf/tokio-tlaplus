# TLA+ specs for Tokio/Futures

Some [TLA+](https://lamport.azurewebsites.net/tla/tla.html) specs various things in Tokio/Futures.

You'll probably want to install the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) to work with these.

Feedback appreciated! I'm a dabbler in this kind of thing.

The specs are:

## Park/Unpark
- parkunpark - the default_park implementation for tokio_threadpool 0.1.5
- parkunpark014 - ditto for 0.1.4
- parkunparkdedup - @stjepang's https://github.com/tokio-rs/tokio/pull/528

For all these I check for deadlocks and a temporal assertion that any unpark results in a parked process making progress
(with 3 unparking processes).

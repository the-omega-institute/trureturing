# Event Orbit Data

## Abstract

An event sequence uniquely determines its state orbit, while the history component records the same sequence one event at a time.

Given a transition function, an initial state, and a fixed event sequence, any two state sequences that begin at the initial state and obey the transition recurrence are equal. This is the orbit-uniqueness clause of Theorem 18.5.

If the history of the initial state is empty and every transition appends its event to history, then at every step the state's history equals the corresponding finite event prefix. This is the history-recording clause of Theorem 18.5.

`D5/S0/History/EventOrbitData` exposes `event_sequence_determines_orbit_and_history`, whose two conjuncts package exactly these orbit and history conclusions.

## References

- Dependency: [D5/S0/History/HistoryCarrier](HistoryCarrier.md)

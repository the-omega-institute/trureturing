# Marker History Search

## Abstract

Marker histories admit exhaustive finite length layers and verified bounded counterexample search.

The two-constructor marker alphabet gives a finite list of every history at each exact length. The theorem `mem_historiesOfLength_length` proves that each history occurs in its own layer; concatenating layers through a natural-number bound therefore covers every history whose length is at most that bound.

A finite reading is an executable function from marker histories to `Bool`, with `false` designated as rejection. The bounded search inspects the finite layers in increasing length order. `findCounterexample_sound` proves that every returned history is rejected, while `findCounterexample_complete` proves that any rejected history within the supplied bound forces some returned counterexample.

`D5/S0/History/MarkerHistorySearch` includes an executable non-vacuity witness: for the reading that accepts empty histories and histories beginning with `E0`, bound one returns the one-marker history `[E1]`. The bound is explicit, so this construction makes no false claim that an unbounded search terminates when no counterexample exists.

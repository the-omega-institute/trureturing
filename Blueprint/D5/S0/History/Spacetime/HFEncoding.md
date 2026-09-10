# Hereditary Finite Event Codes

## Abstract

A fixed small copy of the hereditarily finite set universe supports literal event codes.

**Definition 1.1 (The exact set universe).**

Lean statement: `D5/S0/History/Spacetime/HFEncoding.hf_equiv`

*Formalization.* `D5/S0/History/Spacetime/HFEncoding.hf_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Event names inhabit a fixed small copy of the elements of Mathlib's von Neumann omega stage. The explicit equivalence retains the set representation. Natural codes are finite ordinals and ordered pairs are literal Kuratowski pairs; pair injectivity applies Mathlib's theorem.

**Definition 1.2 (Finite event sets and HF sets).**

Lean statement: `D5/S0/History/Spacetime/HFEncoding.finite_set_equiv`

*Formalization.* `D5/S0/History/Spacetime/HFEncoding.finite_set_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every HF set has finitely many members. Encoding a finite set and enumerating those members are mutual inverses, with no common bound on archive size. This is a Lean representation theorem over Mathlib's set universe; it makes no first-order ZFC conservativity claim.

## References

- Truth anchor: `D5/S0/History/Spacetime/HFEncoding.finite_set_equiv`
- Truth anchor: `D5/S0/History/Spacetime/HFEncoding.hf_equiv`

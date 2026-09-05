# Certified CNF Semantics for DFA Identification

## Abstract

Certified CNF encodings separate untrusted formula generation from sound and complete identification semantics.

**Theorem 1.1 (Formula satisfiability is equivalent to a valid identification).**

$$\operatorname{Satisfiable}(\operatorname{formula}(E)) \iff \operatorname{Nonempty}(\operatorname{Identification}(S, B, C))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/DFAIdentificationCNF.identification_formula_satisfiable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The CNF bytes and solver are allowed to be untrusted. Admission requires separate proofs that every satisfying valuation decodes to a valid identification and that every valid identification induces a satisfying valuation.

This file freezes the proof-carrying interface. An optimized concrete APTA encoder remains an instance obligation and cannot inherit correctness merely from its implementation.

## References

- Truth anchor: `D5/S0/Certificates/DFAIdentificationCNF.identification_formula_satisfiable_iff`
- Dependency: [D5/S0/Automata/IdentificationColoring](../Automata/IdentificationColoring.md)

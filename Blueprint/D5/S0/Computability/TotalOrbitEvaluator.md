# No Total Evaluator for Program Orbits

## Abstract

No computable total function evaluates every partial-recursive code at every input.

**Theorem 1.1 (A computable total orbit evaluator cannot exist).**

$$\neg\exists V: \operatorname{Code}\to \mathbb{N}\to \mathbb{N}, \operatorname{Computable}_2(V) \land \forall c, n, \operatorname{eval}(c, n) = \operatorname{some}(V(c, n)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/TotalOrbitEvaluator.no_computable_total_orbit_evaluator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The claim quantifies over total functions from a program code and a natural input to a natural output. It excludes precisely those functions that are computable and agree, through Part.some, with the partial evaluation of every code at every input. Both the code type and the total function type are inhabited; the theorem has no external hypotheses, so hypothesis satisfiability is vacuous rather than hidden in an empty domain.

This is an honest partial closure of clause (iii) of the source theorem. The output swap is instantiated by successor, a computable map with no fixed natural number. Clauses (i) and (ii), concerning predicate enumeration and binary streams, remain unresolved by this deposit and the source atom must therefore remain partial and open.

Pinned Mathlib was searched before proving. Function.cantor_surjective is an exact hit for clause (i). Nat.Partrec.Code.fixed_point and the existing code_fixed_point wrapper were found but are unary. Nat.Partrec.Code.fixed_point2 was queried under its rendered library name and found as the exact binary fixed-point engine; Nat.Partrec.Code.eval_part and Computable.succ were also found. The related closure_reading_unreachable declaration was inspected, but no exact universal-total-evaluator theorem was found.

The proof forms successor of the proposed evaluator as a binary partial recursive function. The library fixed-point theorem supplies a code whose behavior equals that diagonal function. Specializing the equality at zero and rewriting with the evaluator premise forces a natural number to equal its successor.

## References

- Truth anchor: `D5/S0/Computability/TotalOrbitEvaluator.no_computable_total_orbit_evaluator`

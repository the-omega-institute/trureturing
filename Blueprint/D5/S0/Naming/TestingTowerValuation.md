# Testing Tower Valuation

## Abstract

Finite tables and program codes receive the testing tower's concrete partial valuation.

**Lemma 1.1 (Program-name definedness is halting).**

$$\begin{gathered}\forall O: \operatorname{Type}, \forall o0: O,\\{}\forall decode: \mathbb{N} \to \left(\mathbb{N} \to O\right),\\{}\forall input: \mathbb{N},\\{}\forall p: \mathbb{N},\\{}\operatorname{isSome}\left(\operatorname{testingAssignment}\left(o0, decode, input, \operatorname{inr}\left(p\right)\right)\right) \iff \operatorname{Dom}\left(\operatorname{eval}\left(\operatorname{ofNatCode}\left(p\right), input\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/TestingTowerValuation.program_assignment_defined_iff_halts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A natural-number program name is decoded by Mathlib's denumerable code bijection and evaluated by Nat.Partrec.Code.eval on the supplied input. Its assignment is present exactly on the evaluator's domain.

**Theorem 1.2 (Program-name definedness is not computable).**

$$\begin{gathered}\forall O: \operatorname{Type}, \forall o0: O,\\{}\forall decode: \mathbb{N} \to \left(\mathbb{N} \to O\right),\\{}\forall input: \mathbb{N},\\{}\neg \operatorname{ComputablePred}\left((c: PartrecCode \mapsto \operatorname{isSome}\left(\operatorname{testingAssignment}\left(o0, decode, input, \operatorname{inr}\left(\operatorname{encodeCode}\left(c\right)\right)\right)\right))\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/TestingTowerValuation.program_name_domain_not_computable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting natural-number names along the canonical encoding of partial-recursive codes recovers Mathlib's halting predicate. A computable definedness test would contradict the pinned halting theorem.

## References

- Truth anchor: `D5/S0/Naming/TestingTowerValuation.program_assignment_defined_iff_halts`
- Truth anchor: `D5/S0/Naming/TestingTowerValuation.program_name_domain_not_computable`
- Dependency: [D5/S0/Naming/Conservation/TestingTowerMembership](Conservation/TestingTowerMembership.md)

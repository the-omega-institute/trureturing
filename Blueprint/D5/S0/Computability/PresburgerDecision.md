# Integer decisions by recursive elimination

## Abstract

Recursive Cooper elimination computes the truth of every integer formula.

Formula.quantifierEliminate leaves QF formulas alone, maps Boolean constructors recursively and applies Cooper.eliminate to the recursively converted body of an existential. Derived universal quantifiers are not-exists-not, so arbitrary alternation and nested negation are included.

decideHolds evaluates the resulting QF under the supplied integer list. holdsDecidable branches on this Bool and transfers its equality-to-true proof to Formula.holds. decideSentence evaluates at the empty valuation; presburgerArithmetic_decidable uses the same executable decision. These definitions and proofs are upstream ProveIt results, separate from the native Nat compiler. No recursion-theoretic Computable theorem or complexity bound is asserted.

**Theorem 1.1 (Full formula semantics).**

$$\forall p \in Formula,\; \forall xs \in \operatorname{List}\left(Int\right),\; (\operatorname{holds}\left(p, xs\right)) \iff (\operatorname{eval}\left(\operatorname{quantifierEliminate}\left(p\right), xs\right) = true)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerDecision.holds_iff_quantifierEliminate` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Formula induction proves the Boolean cases directly. The existential case combines the induction hypothesis at x::xs with Cooper.eliminate_correct.

**Theorem 1.2 (Executable Bool contract).**

$$\forall p \in Formula,\; \forall xs \in \operatorname{List}\left(Int\right),\; (\operatorname{decideHolds}\left(p, xs\right) = true) \iff (\operatorname{holds}\left(p, xs\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerDecision.decideHolds_eq_true_iff` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

The decision is definitionally the eliminated formula evaluation; the previous equivalence is reversed. This contract is the integer decision interface used by NatPresburger.test.

**Theorem 1.3 (Empty valuation convention).**

$$\forall p \in Sentence,\; (\operatorname{decideSentence}\left(p\right) = true) \iff (\operatorname{holds}\left(p, nil\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerDecision.decideSentence_eq_true_iff` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

This is the same decision contract specialized to the empty integer valuation. It does not require a new elimination proof.

## References

- Truth anchor: `D5/S0/Computability/PresburgerDecision.decideHolds_eq_true_iff`
- Truth anchor: `D5/S0/Computability/PresburgerDecision.decideSentence_eq_true_iff`
- Truth anchor: `D5/S0/Computability/PresburgerDecision.holds_iff_quantifierEliminate`
- Dependency: [D5/S0/Computability/PresburgerElimination](PresburgerElimination.md)

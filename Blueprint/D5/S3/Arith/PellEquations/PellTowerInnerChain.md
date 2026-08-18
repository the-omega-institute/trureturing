# Pell Tower Inner-Chain Preservation

## Abstract

The inner-chain map preserves the Pell-type tower equation.

**Theorem 1.1 (The inner-chain map preserves the tower equation).**

$$\forall D, d, k \in \mathbb{Z},\ (d+1)\cdot (d-3)=D\cdot k^{2} \Rightarrow ((d\cdot (d-2)+1)\cdot (d\cdot (d-2)-3))=D\cdot ((d-1)\cdot k)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PellEquations/PellTowerInnerChain.pell_tower_inner_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For integers D, d, and k, suppose (d + 1)(d - 3) = Dk^2. Set d' = d(d - 2). Then (d' + 1)(d' - 3) = D((d - 1)k)^2, so the transformed dimension remains on the same Pell-type tower and its new Pell coordinate is explicit.

The proof factors the transformed left-hand side as (d - 1)^2(d + 1)(d - 3), substitutes the assumed tower equation, and normalizes the remaining polynomial identity with Mathlib's ring tactic. Pinned Mathlib Pell declarations and source search had no exact theorem for this transformation. Online Loogle returned zero matches for the formula-shaped query.

This node closes only the inner-chain sentence in remark 27.594, namely that d maps to d(d - 2) within a fixed Pell-type tower. It does not formalize the atom's unit-norm dichotomy, Lucas identities, SIC classification data, torsion spectrum, or numerical searches.

## References

- Truth anchor: `D5/S3/Arith/PellEquations/PellTowerInnerChain.pell_tower_inner_chain`

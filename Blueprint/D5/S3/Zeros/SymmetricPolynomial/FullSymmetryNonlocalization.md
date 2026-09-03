# Full Symmetry Does Not Force Localization

## Abstract

An explicit entire quartic has every zeta symmetry while all four zeros remain off line.

**Theorem 1.1 (A fully symmetric entire function with four off-line zeros).**

$$\begin{aligned}\forall delta, gamma\in \mathbb{R}, delta \neq 0 \land gamma \neq 0 \Rightarrow\\{\exists F: \mathbb{C} \to \mathbb{C},\\{}F = \operatorname{offCriticalQuartic}\left(delta, gamma\right) \land\\{}\operatorname{Differentiable}\left(\mathbb{C}, F\right) \land\\{}{\forall s: \mathbb{C}, F(1 - s) = F(s)} \land {\forall s: \mathbb{C}, F(\operatorname{conj}\left(s\right)) = \operatorname{conj}\left(F(s)\right)} \land\\{}{\forall s: \mathbb{C}, F(s) = 0 \Leftrightarrow s \in \operatorname{sourceZeros}\left(delta, gamma\right)} \land\\{}\operatorname{card}\left(\operatorname{sourceZeros}\left(delta, gamma\right)\right) = 4 \land\\{}{\forall s: \mathbb{C}, F(s) = 0 \Rightarrow \operatorname{re}\left(s\right) \neq criticalAbscissa}} \land \neg{\forall F: \mathbb{C} \to \mathbb{C},\\{}\operatorname{Differentiable}\left(\mathbb{C}, F\right) \Rightarrow {\forall s: \mathbb{C}, F(1 - s) = F(s)} \land {\forall s: \mathbb{C}, F(\operatorname{conj}\left(s\right)) = \operatorname{conj}\left(F(s)\right)} \Rightarrow {\forall s: \mathbb{C}, F(s) = 0 \Rightarrow \operatorname{re}\left(s\right) = criticalAbscissa}}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/SymmetricPolynomial/FullSymmetryNonlocalization.full_symmetry_not_fixed_line_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero real delta and gamma, the witness is exactly the source quartic P_delta,gamma(s), formed from z = s - 1/2. It is complex differentiable everywhere and satisfies both generators of the source Klein-four symmetry: reflection s maps to 1-s, and complex conjugation commutes with evaluation.

The zero condition is an equivalence, not a one-way inclusion: a point is a zero exactly when it belongs to sourceZeros(delta,gamma). That named finite set consists of 1/2 plus or minus delta plus or minus i gamma, has cardinality four, and every zero has real part different from the repository critical abscissa.

The second top-level conjunct is the boxed consequence. It negates the universal implication from entire full-zeta symmetry to fixed-line localization, using the same explicit quartic as counterexample. No Riemann-hypothesis assumption or unformalized zero data enters the declaration.

## References

- Truth anchor: `D5/S3/Zeros/SymmetricPolynomial/FullSymmetryNonlocalization.full_symmetry_not_fixed_line_localization`
- Dependency: [D5/S3/Weil/ReflectionLedger](../../Weil/ReflectionLedger.md)

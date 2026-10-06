# Positive Rulings and Actual Second Queries

## Abstract

Positive eigenvector rulings obstruct three-read recovery except at nontrivial shear second endpoints.

R is a real 2 by 2 matrix with all four entries strictly positive and R11 R22=R12 R21. At cumulative A the exact read is trace(AR).

A query is a pair (previous literal word,new finite segment). Histories record that query and its real response. A policy is an arbitrary function from histories to either a next query or an output relation with an unread finite tail. It first queries the empty word. OriginalValid requires every source to terminate under native execution with at most three reads, chronological prefix extension, and output equal to the initial R. Action cost is the sum of segment lengths plus the terminal tail length.

**Theorem 1.1 (A collision for every third linear read).**

$$\forall A,B,c,l,lambda \operatorname{PositiveEigenvectors}\left(A, c, l, lambda\right) \implies \operatorname{RulingCollision}\left(A, B, c, l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/SelfCalibratingRulings.positive_ruling_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive column c and row l satisfy Ac=lambda c and lA=lambda l. For every real B there are two distinct positive rank-one sources with the same initial trace lc, the same A read lambda lc, and the same B read. Perturbing the row and column along their annihilating directions preserves the first two reads. Small parameters retain positivity; matching the third slopes gives a collision, including when either slope is zero.

**Theorem 1.2 (Global correctness forces the actual second shear).**

$$\forall P,x \operatorname{OriginalValid}\left(P\right) \land x >0 \implies \exists w,k, \operatorname{ActualSecondShear}\left(P, x, w, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/SelfCalibratingRulings.second_query_shear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x>0, P selects a second query with empty previous word and a finite literal word w. For some natural k>0, E(w) has rows (1,k),(0,1) or (1,0),(k,1). Stopping after the first read fails on distinct sources of that trace. Two positive offdiagonals supply positive left and right eigenvectors, whose rulings defeat every history-selected third query. Integral nonnegative entries and determinant of absolute value one leave the shear forms. Identity has the same ruling obstruction and is excluded. No continuity of P, finite candidate set, or uniform action budget is required. Every source also has the explicit positive factorization c=(R11,R21), l=(1,R12/R11). For every word its relation read is l(E(w)c). The same l is retained throughout that source's run; different compatible sources may have different positive rows.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/SelfCalibratingRulings.positive_ruling_collision`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/SelfCalibratingRulings.second_query_shear`
- Dependency: [D5/S3/Arith/FibonacciAtomic/SelfCalibratingRawWords](../../Arith/FibonacciAtomic/SelfCalibratingRawWords.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization](PassivePolicyNormalization.md)

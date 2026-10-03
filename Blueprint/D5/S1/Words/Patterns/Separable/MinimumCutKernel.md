# Actual Minimum-Cut Kernel

## Abstract

Actual minimum-cut events have Cartesian conditional shape laws and literal block labels.

**Theorem 1.1 (Minimum-cut shape probabilities on actual avoiders).**

$$\forall s,m,k, m>0 \land k>0 \Rightarrow \exists e: \operatorname{J}\left(s, m\right) \times \operatorname{U}\left(k\right) equiv \operatorname{MinimumFiber}\left(s, m, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/MinimumCutKernel.minimum_cut_cartesian_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each Boolean sign s and positive natural lengths m and k, U is the actual 2413/3142-avoiding permutation subtype, and J consists of its members without a proper cut of sign s. False is direct and true is skew. MinimumFiber is the actual length m+k class with a cut at m and no positive smaller cut. The existential equivalence reconstructs each member by the actual blockSum.

For all predicates A on J and B on U(k), the full actual event consisting of block sums of A and B has cardinality card(A) times card(B). Under the uniform PMF on all actual U(m+k), its real probability is this cardinality divided by card(U(m+k)). Dividing by the probability of the minimum-cut fiber gives (card(A)/card(J)) times (card(B)/card(U(k))). Field division is totalized at zero; probability conditioning requires a nonempty fiber.

At a left position i the reconstructed zero-based value is (if s then k else 0)+alpha(i); at right position m+j it is (if s then 0 else m)+beta(j). These are literal labels, not standardized flags. The proof establishes the restriction and extension of every smaller same-sign cut, then uses the frozen fixed-cut actual factorization and the pinned Mathlib uniform finite PMF cardinal formula.

The minimum cut is not the greatest-cut convention used in the compiled but unfrozen enumeration supplier. Count asymptotics, finite-history truncation, limiting cylinders, occupation, hitting, and the full derangement-ratio limit are not conclusions of this kernel.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/MinimumCutKernel.minimum_cut_cartesian_kernel`
- Dependency: [D5/S1/Words/Patterns/Separable/CutFactorization](CutFactorization.md)

# The finite-sum obstruction solver

## Abstract

Weighted semilinear averaging for principal-unit section conjugacy.

A finite quotient section-comparison cocycle can be solved without dividing by the order of the acting group when the coefficient action admits a weighted trace-one element. The coefficient space is only required to be an additive K-module; this keeps the lemma applicable to the unrestricted End_F(K) top layer of the odd-prime jet radical.

**Theorem 1.1 (Weighted semilinear cocycles are coboundaries).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetSectionConjugacy.weighted_semilinear_cocycle_coboundary`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetSectionConjugacy.weighted_semilinear_cocycle_coboundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Γ be a finite group, σ assign field endomorphisms to its elements, and ρ act additively on a K-module W. Assume σ respects multiplication, ρ is σ-semilinear, and f satisfies the crossed-homomorphism identity f(gh)=f(g)+ρ_g(f(h)). If θ has weighted trace ∑_h σ_h(θ)=1, then the explicit finite sum b=∑_h σ_h(θ)·f(h) satisfies f(g)=b−ρ_g(b) for every g. The proof reindexes by left multiplication and uses no inverse of |Γ|, so it remains valid when the quotient order is divisible by the characteristic.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetSectionConjugacy.weighted_semilinear_cocycle_coboundary`

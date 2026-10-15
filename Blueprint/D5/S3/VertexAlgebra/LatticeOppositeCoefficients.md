# Finite Opposite Coefficients on the Actual Matter Carrier

## Abstract

Finite actual opposite coefficients retain every Sugawara descendant and the indispensable current zero correction.

Write L1=sugawaraMode(D,H,1), Y=LatticeAllStateField.Y and A_i(q)=neutralMode(D,i,q). For an integer h the opposite coefficient is paritySign(h) times the sum over j=0,...,N(a) of (j!)^-1 Y(L1^j a)[2h-n-j-2]. This is a family of endomorphism coefficients, not a claim that the opposite family is a native lower-truncated VertexOperator. The algebraic definition accepts every integer h; its conformal interpretation uses a in the actual grade h.

Local nilpotence and cutoff independence require no inverse-Gram equations. The actual normalized current commutator and all conformal weight statements retain both H*gramComplex(D)=1 and gramComplex(D)*H=1. Weights may be negative and the state may have any finite charge and monomial support. No form, adjoint, unitarity or positivity premise occurs.

The upstream factorial identities give choose(k+ell,ell)*(r)_ell/(k+ell)!=choose(r,ell)/k!; the ell=r term is the original current-zero action. For an actual state a of grade h, each actual L1^j a has grade h-j. Applying actual_mode_grade to Y(L1^j a)[2h-n-j-2]b puts every summand in grade k-h+n+1 when b has grade k; finite addition therefore gives the same grade for O_a(n)b. This is an application of the original grade and factorial suppliers, not a new positivity statement.

**Definition 1.1 (A factorial-weighted actual descendant mode).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeTerm`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The j-th term uses the original L1 iterate, the original reconstructed Y and the exact reflected integer index.

**Definition 1.2 (Finite opposite coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeCoeff`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum truncates only at the true native oscillator bound N(a).

**Theorem 1.3 (Independence of every larger cutoff).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every cutoff strictly larger than N(a) gives exactly the same endomorphism coefficient; each extra actual descendant is zero.

**Theorem 1.4 (Finite descendant support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_terms_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_terms_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual descendant-term family has finite support in j, uniformly for its endomorphism value at a fixed n.

**Theorem 1.5 (Actual pointwise cutoff expression).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_cutoff_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_cutoff_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every cutoff larger than N(a) gives the same original coefficient action on each tested vector; the finite sum uses exact factorials and reflected indices.

**Theorem 1.6 (Finite-support sum expression).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_finsum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_finsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chosen finite cutoff agrees with the supported natural-index finsum.

**Theorem 1.7 (The exact current zero correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.zero_current_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.zero_current_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Y(b)[q] A_i(0)+Y(A_i(0)b)[q]=A_i(0)Y(b)[q]. The original actual mode_commutator at p=0 proves the identity; A_i(0) is not silently discarded on charged states.

**Theorem 1.8 (Actual negative-current reconstruction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.current_negative_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.current_negative_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r=degree+1, Y(A_i(-r)b)[n]v equals sum_t choose(t+r-1,r-1) A_i(-t-r)Y(b)[n+t]v plus (-1)^(r-1) sum_s choose(s+r-1,r-1)Y(b)[n-s-r]A_i(s)v. Both sums have actual pointwise finite support. This is the original residue reconstruction, not a globally finite End-valued infinite sum.

**Theorem 1.9 (Every actual insertion power).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_current_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_current_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antidiagonal expansion sums over ell+k=j with coefficient choose(j,ell)*(r)_ell and state A_i(ell-r)L1^k b. Both inverse-Gram equations are explicit; the ell=r zero-current term survives.

**Theorem 1.10 (The exact finite insertion range).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_current_insertion_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_current_insertion_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural insertion sum runs through ell<=min(j,r), with the original neutral current and actual L1^(j-ell)b.

**Theorem 1.11 (Signed conformal weight of descendants).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a has actual integer grade h then L1^j a has grade h-j, including negative weights. Both inverse equations are required.

**Definition 1.12 (First reversed pointwise term).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversedFirstTerm`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversedFirstTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The term is choose(t+r-1,r-1) O_b(n+t) A_i(t+r)v.

**Definition 1.13 (Second reversed pointwise term).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversedSecondTerm`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversedSecondTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The term is choose(s+r-1,r-1) A_i(-s) O_b(n-s-r)v, including s=0.

**Theorem 1.14 (Finite first reversed support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversed_first_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversed_first_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual current truncation on the tested vector bounds the first reversed support before opposite-mode evaluation.

**Definition 1.15 (A common finite descendant truncation bound).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeInputBound`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeInputBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite maximum over the actual Y(L1^j b) thresholds gives one bound on the tested vector for the second reversed order.

**Theorem 1.16 (Uniform high reflected-input annihilation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_reversed_input_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_reversed_input_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above the common descendant bound, every actual Y coefficient in O_b(n-s-r)v vanishes in its original order.

**Theorem 1.17 (Finite second reversed support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversed_second_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversed_second_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite maximum over actual descendant truncation thresholds bounds the complete second reversed family; no state-independent occupation cutoff is imposed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.current_negative_insertion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_current_insertion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_current_insertion_bounded`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.one_pow_grade`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeCoeff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeInputBound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.oppositeTerm`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_cutoff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_cutoff_apply`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_finsum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_reversed_input_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.opposite_terms_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversedFirstTerm`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversedSecondTerm`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversed_first_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.reversed_second_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCoefficients.zero_current_correction`
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence](LatticeSugawaraLocalNilpotence.md)

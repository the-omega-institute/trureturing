# Original lattice field energy bounds

## Abstract

Uniform energy bounds on the original finite lattice carrier with its integer-frequency Hermitian form.

D is the original LatticeData, with its symmetric integral Gram matrix G and even diagonal. Carrier(D) is the original finite charge sum of oscillator polynomials. The real Gram matrix is assumed positive definite. H is a complex matrix with both H*gramComplex(D)=1 and gramComplex(D)*H=1. There is no integral determinant-unit hypothesis, diagonal-Gram restriction, support-size bound, oscillator-degree cutoff, alternative carrier or half-frequency metric.

The original normD is supplied by Energy/OriginalCurrentEnergy and remains in the OriginalChargedEnergy namespace through this module import. Energy/OriginalWordEnergy supplies the single seed-parametrized arbitrary-charge word induction. Energy/OriginalNeutralEnergy specializes it to the identity seed and supplies finite energy recombination. The consumed shared charged_pre_relaxation_grade_le retains the input-grade factor for nonnegative raw modes and the actual output-grade factor for negative raw modes before introducing a mode scale. The original public types and exponents in this module are preserved.

**Theorem 1.1 (Uniform homogeneous neutral bound).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy.neutral_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy.neutral_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D with positive definite real Gram matrix, every complex H satisfying both inverse equations, every p:Oscillator(D), every w:N, and the hypothesis that p is weighted homogeneous of weight w for weight(i,r)=r+1, there exists K:R with K>0 such that for every v:Carrier(D), normD(((Y(D,single(0,p)))[[w-1]])v) <= K*normD(((1+sugawaraMode(D,H,0))^(2*w))v). K is chosen before v and is independent of its charge, energy, oscillator degree and size of mixed support. Zero p, weight zero and rank zero are included.

Under inverse full-frame substitution the exact original form has weights product e(i,r)!*(r+1)^e(i,r). Summing all frequency-r derivatives gives the occupation-number identity; finite vector-valued Cauchy-Schwarz bounds arbitrary colour directions, including their interference. The adjoint and commutator give the corresponding creation estimate, and Gram Cauchy-Schwarz bounds zero currents. Literal word induction uses the two original normal-product branches at a general vertex mode. Derivative modes in the strip between the derivative branch and the current branch vanish by their binomial coefficient. Negative currents remain on the left and nonnegative currents on the right; no factors are commuted and no contractions are discarded.

For a word between grades E,F<=M, positive energy gives finite left and right ranges F+1 and E+r+1 at derivative order r. Every surviving intermediate grade is between 0 and M. With A(r)=(r+1)^r/r!, an admissible recursive constant is K(empty)=1 and K((i,r)::tail)=(r+2)*A(r)*sqrt(3*G(i,i))*K(tail). The word exponent is its weight plus length, at most twice its weight. The polynomial constant is 1+sum_e |coeff(p,e)|*K(occurrences(e)), hence strictly positive even for p=0. Exact charge and energy orthogonality give the full finite-state result without an input-support multiplier.

**Theorem 1.2 (All-integer charged energy bound).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy.charged_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy.charged_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D with positive definite real Gram matrix, every complex H with both inverse equations, and every nonzero a:Charge(D), let d=(chargeEnergy(D,a)).toNat. There exists C:R with C>0 such that for every m:Z and every v:Carrier(D), normD((actualField(D,a)[[m+d-1]])v) <= C*(1+abs(m:R))^(2*d)*normD(((1+sugawaraMode(D,H,0))^(2*d))v). Original lattice positivity proves d>0 and (d:Z)=B(a,a)/2. C depends on D and a and is fixed before m and v, with no dependence on the input charge or its mixed support.

The neutral creation coefficient of weight 2*d supplies energy order 4*d. The original cocycle phase, charged Hermitian adjoint and positive normal-product quadratic identity yield the charged order 2*d after Cauchy-Schwarz and square roots whenever m>=1-d. For m<=-d, the opposite-charge controlled estimate applies to the actual output grade E-m through the adjoint. Zero output norm is treated before cancellation. The inequality E-m+1 <= (1+abs(m))*(E+1) gives the claimed mode factor. Distinct input grades have distinct output grades E-m, so orthogonal finite recombination proves the arbitrary-state bound. One choice of C is the sum of the square roots of the two neutral polynomial constants for a and -a.

The proof reuses the original lattice fields, factorial pairing, full-frame matrix suppliers, source transpose, energy grading and Sugawara identities. Their Bakalov-Kac, Matsuo-Nagatomo, Carnahan and Mathlib attributions remain with those suppliers. The new content is the uniform analytic inequality on the literal original carrier; no claim of literature novelty is made. The homogeneous and finite-energy all-state consumers are authored separately in Energy/OriginalAllStateEnergy. Closable smeared fields on the Hilbert completion, strong locality, full string theory and AdS/CFT remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy.charged_energy_bound`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy.neutral_energy_bound`
- Dependency: [D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy](../Energy/OriginalNeutralEnergy.md)

# Charged Seed Physical Coefficient

## Abstract

Actual charged-seed physical coefficients

Let D:LatticeData be any integral symmetric even-diagonal Gram datum, hu:IsUnit D.G.det, a:Charge D, e:Int and v:ActualTensor D hu. The carrier is the original Oscillator D tensor_C ActualGround D hu. There is no positivity, positive-rank, nonzero-charge, input homogeneity or finite-occupation assumption. All signed current modes and all integer exponents remain in scope, including rank-zero and zero-charge fibres.

Write E[a,e]=chargedCoefficient D hu a e and q=chargeNorm D a. The singleton is exactly wordField D hu (chargedField D hu a) [(colour,0)]. Its coefficients come from wordField_coefficient and its actual flatTerm_finite bound, separately after application to each input tensor. The proof constructs neither a replacement normal field nor an endomorphism-valued infinite sum. The private weightedWord is only a finite linear combination of those existing coefficients; modeSummand is only their original flat terms.

On 1 tensor g, nonnegative modes vanish. Reindexing the remaining integer modes by m=-r-1 gives the finite creation sum. Taking coefficients in exponential_derivative and using series_derivative_coeff proves (d/2) C[a,d] = sum_r (sum_colour a_colour X[colour,r]) C[a,d-1-2r]. Signed-to-natural transport retains the d<0 vanishing case and the d=0 scalar-zero case. charged_vacuum_coefficient transports this identity through the actual chargeScalar and groundAction without absorbing either normalization.

Let K_e be the charge-weighted singleton coefficient and let C_i be the actual creation current of i=(colour,k), with w_i=2k+1 and b_i=B(unitCharge(colour),a). The live creation step derives K_e(C_i v)=C_i(K_e v)-b_i K_(e+w_i)(v)+(k+1/2)b_i E[a,e+2k+3]v. charged_tensor_current_ward gives the exact charged creation relation, and current_heisenberg_apply gives the mixed current correction. Pointwise finite supports justify mapping and subtracting the sums. These are actual operators on ActualTensor D hu, with no assumed seed or translation law.

MvPolynomial.induction_on propagates the ground law through constants, addition and creation. Both shifted induction hypotheses at e and e+w_i are consumed on the creation branch. The frequency correction cancels their coefficient difference, yielding K_e(p tensor g)=((e+q+2)/2) E[a,e+2](p tensor g) for every oscillator polynomial p. TensorProduct.inductionOn then extends the identity to arbitrary actual tensors. Subtracting (q/2) E[a,e+2] gives the displayed physical coefficient law. Scalar normalization, coefficient packaging, support adapters and signed casts are consumed helpers, not separate mathematical achievements.

The substantive new repository inference is the unrestricted ground-to-polynomial creation induction just described, after inlining the private helpers. Focused search reuses the canonical charged exponential derivative, series derivative coefficients, charged vacuum coefficients, all-mode Ward identity, current Heisenberg relation, arbitrary-word support and word coefficient APIs. Pinned Mathlib supplies PowerSeries.coeff_derivative, coefficient convolution and antidiagonal reindexing, finsum mapping and finite-support transport, MvPolynomial.induction_on and TensorProduct.inductionOn. Existing grading and annihilation results do not state this singleton coefficient invariant. No literature novelty is asserted.

Source attribution: the classical twisted lattice construction follows Frenkel, Lepowsky and Meurman, Vertex Operator Algebras and the Monster (1988), Dong and Nagatomo math/9808088v1 section 3.2, and Bakalov and Kac math/0402315v1 section 4.4. The proof cone is adapted from the preserved OriginalTranslation source (SHA256 0442324ef84346403888d5faa093adffdd3ec23b77918c37b81252c5404b008a) and its archived FirstDescendant, FirstDescendantCuts, ChargedTranslation and ChargedTranslationExtension suppliers. Their declared source digests are respectively f3ff080fabf42c4bc25887d09979c97a469aa94e1567e6fbf14a0182bfef3a7e, 2745cf7ccc35156d59954b28b3fa222ebe8002a260a0d8f94a5a6f8fc34521fd, 2502396fca51c38bf06a9d5e195eba5489cae31171a921a87cbd4ec81bb70832, and 8ed941f58212dd6c7559e051e4c70975df2cb93666286fe8eafed7c3c92114c0. Inherited half-Fock construction copyright (c) 2025 Kalle Kytola; additional actual half-integer matrix implementation copyright (c) 2026; Apache 2.0. The finite-support and induction architecture follows VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 and PolynomialFock sources bfd9ff0f15397a4fb933f36d701a60d325d84b08.

This coefficient law is the charged-seed prerequisite of the original arbitrary-source physical translation endpoint for correctedField, whose shift is e to e+2 and scalar is (e+2)/2. Word permutation and polynomial insertion, singleton Leibniz and shift calculus, normalEvaluation_physical, Corr_sectorTranslation and the final arbitrary-source evaluator induction remain further obligations. The present theorem does not establish that endpoint, a full VOA or CFT, anomaly or fusion structures, string dynamics, spacetime reconstruction or AdS/CFT. The Monster moonshine to string and AdS/CFT programme remains active.

**Theorem 1.1 (Charged special-conformal coefficient base).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical.charged_l1_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical.charged_l1_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original D, determinant-unit proof hu, signed charge a and integer e, the commutator of tensorL at mode 1 with chargedCoefficient at e equals ((e-2)/2+B(a,a)) times chargedCoefficient at e-2, as an endomorphism of the original actual tensor module. The proof expands the pointwise finite quadratic sum, retains the j=0 boundary, contracts both inverse Gram identities and consumes the original physical seed identity. The full-source proof uses this charged base. No positivity, rank restriction or homogeneous target is assumed.

**Theorem 1.2 (The existing charged singleton support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical.singleton_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical.singleton_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Visibility-only exposure of the original pointwise charged singleton finite-support result. The exact proof is preserved and the charged L1 quadratic-to-singleton summation consumes it for the two inverse Gram contractions.

**Theorem 1.3 (The actual all-tensor charged-seed coefficient law).**

$$\operatorname{K}\left(a, e, v\right)-\operatorname{smul}\left(\frac{\operatorname{q}\left(a\right)}{2}, \operatorname{E}\left(a, e+2, v\right)\right)=\operatorname{smul}\left(\frac{e+2}{2}, \operatorname{E}\left(a, e+2, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical.charged_seed_physical_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, a:Charge D, e:Int and v:ActualTensor D hu, K(a,e,v) is sum_colour (a colour:Complex) smul (wordField D hu (chargedField D hu a) [(colour,0)]).coeff e v, q(a)=chargeNorm D a, and E(a,e,v)=chargedCoefficient D hu a e v. The equality is in ActualTensor D hu. The proof is the actual ground exponential recurrence followed by unrestricted creation and tensor induction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical.charged_l1_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical.charged_seed_physical_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical.singleton_finite`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero](LatticeHalfFockChargedLZero.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField](LatticeHalfFockFockNormalField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](LatticeSugawaraConformal.md)

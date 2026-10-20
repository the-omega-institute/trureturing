# Actual Half-Fock Normal Fields

## Abstract

Actual arbitrary-word half-Fock normal fields and their finite-charge source extension.

Let D be any LatticeData and hu:IsUnit D.G.det. The determinant hypothesis is used by the existing actual twisted ground representation. The target is exactly ActualTensor(D,hu)=Oscillator(D) tensor ActualGround(D,hu), with the supplier's groundRank, groundRepresentation and groundAction. Rank zero and indefinite Gram matrices are included. There is no positivity assumption, oscillator occupation bound, homogeneous-source restriction, replacement ground representation, or restriction to a generating set of charges. The seed A is any NativeField(D,hu), and every finite list of indices (colour,order) is permitted, including the empty list and repeated occurrences.

For original mode j, jetScalar(k,j) is the product of -j-3/2-r for 0<=r<k divided by k!, and jetCurrent is this scalar times the actual tensorCurrent. Every recursive coefficient step retains the original j<0 split: a negative mode multiplies on the left, while a nonnegative mode multiplies on the right. Its seed coefficient index changes by e+2*j+2*order+3. No split at a derivative-shifted mode and no ordinary normalMinusOne is substituted. J(word)=sum(2*order+3); n=length(word); S(modes)=sum of original modes. Consequently the exact factorization is leftAction times A.coeff(e+2*S+J) times rightAction.

The current Heisenberg relation makes all nonnegative original modes commute on the actual tensor module. tensor_current_truncation supplies, for each actual vector v, one natural c valid for every colour. Nonzero terms force each original mode to be less than c. Negative modes have no right action, so rightCode replaces each negative mode by -1 and preserves the exact rightAction. These codes lie in the finite box [-1,c]^word. Let L be the minimum of zero and the orders of A applied to all right actions of that finite box. Nonzero factorized terms require L<=e+2*S+J. This bounds the joint mode support for each fixed e,v; it is never support in Module.End and never a globally finite family of operators.

**Theorem 1.1 (The exact arbitrary-word original-mode factorization).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For all D,hu, seeds A, finite words w, mode tuples m and integer exponents e, flatCoefficient(D,hu,A,w,m,e)=leftAction(D,hu,w,m)*A.coeff(e+2*modeSum(D,w,m)+jetShift(D,w))*rightAction(D,hu,w,m). Induction preserves the actual ordered operators, negative-left/nonnegative-right convention and original jet shifts. The seed-index lower estimate consumes this identity before any sum is formed.

**Theorem 1.2 (A pointwise finite box for every joint mode tuple).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For any actual v, integer e and natural c that kills all original tensorCurrent modes j>=c on v, support(flatTerm(D,hu,A,w,e,v)) is contained in modeBox(w,min(L-e-J,0)-n*c,c), with L=flatLower(D,hu,A,w,v,c). The premise belongs to this internal estimate. The public finiteness and lower-truncation results obtain c from the existing actual tensor current theorem and impose no cutoff on their callers. The joint lower bound uses the finite right-action minimum and a lower bound on modeSum, not iterated unproved operator-valued sums.

**Theorem 1.3 (Finite support after applying to every actual tensor state).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D,hu,A,w,e and actual vector v, the function of all mode tuples flatTerm(D,hu,A,w,e,v) has finite support. tensor_current_truncation supplies its cutoff internally. wordCoefficient(e)v is the finsum of this vector-valued function. Additivity uses the two separately proved finite supports at v and u; scalar compatibility uses the finite support at v. Only these proofs make wordCoefficient an actual complex-linear endomorphism.

**Theorem 1.4 (Derived lower truncation of the actual word coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.wordCoefficient_lower_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.wordCoefficient_lower_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D,hu,A,w and actual vector v, there exists an integer lower such that wordCoefficient(D,hu,A,w,e)v=0 for every integer e<lower. To derive it, obtain c by tensor_current_truncation, and put lower=L-2*n*c-J. A nonzero summand has S<=n*c and L<=e+2*S+J, hence lower<=e. Below this bound every summand is zero. The proof therefore establishes BddBelow support and its IsWF/IsPWO consequence, which wordField passes to HVertexOperator.of_coeff. Neither lower truncation nor finite endomorphism support is assumed.

**Theorem 1.5 (The constructed Hahn field has the actual pointwise mode sum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.wordField_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.wordField_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For all D,hu,A,w,e,v, (wordField(D,hu,A,w)).coeff(e)v equals finsum_m flatTerm(D,hu,A,w,e,v,m). This coefficient identity is the of_coeff interface consumed by sourceField_coefficient; its proof is a binding step, not a separate mathematical novelty. The actual construction is the pointwise linear map and derived bound preceding it. In particular the empty word sums over Unit and recovers A.

chargedWordField uses exactly chargedField(D,hu,a) as its seed, for every integral charge a. That existing seed retains chargeNorm=B(a,a), chargeScalar=2^(-B(a,a)), the native half-creation/translation coefficients and the actual groundAction(a). occurrences(d)=d.toMultiset.toList enumerates each natural exponent with its multiplicity. polynomialField extends the corresponding charged word fields by basisMonomials.constr over every oscillator polynomial. sourceField is Finsupp.lsum of these linear maps over the existing ordinary source Carrier(D)=Charge(D) ->finitely-supported Oscillator(D). Thus it is a linear map from every finite-charge source to genuine Hahn fields acting on all actual twisted states. The occurrence lists retain multiplicity. Permutation invariance identifies different enumerations, and multiplication by one oscillator becomes singleton word insertion.

**Theorem 1.6 (Finite charge and monomial extension of the actual coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.sourceField_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.sourceField_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For all D,hu, source u:Carrier(D), integer e and actual target v, (sourceField(D,hu)u).coeff(e)v is the finite sum over a in u.support and d in the monomial-basis representation support of u(a), of repr(u(a))(d) times finsum_m flatTerm(D,hu,chargedField(D,hu,a),occurrences(d),e,v,m). The outer sums are finite native source supports; the innermost sum is pointwise in ActualTensor. This binding identity is consumed in the full-source truncation proof.

**Theorem 1.7 (A derived bound for every finite-charge inhomogeneous source).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.sourceField_lower_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.sourceField_lower_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For all D,hu,u:Carrier(D) and actual v, there exists an integer lower such that (sourceField(D,hu)u).coeff(e)v=0 whenever e<lower. One cutoff c for v suffices. For each supported monomial at each charge, use L-2*n*c-J for its actual charged seed. polynomialLower takes the finite minimum with zero over monomials, and sourceLower the finite minimum with zero over charges. The coefficient formula and wordCoefficient_vanish kill every term below sourceLower. Empty supports, rank zero, arbitrary word length and negative integer exponents are covered by the same proof.

Source provenance: the preserved arbitrary-word support candidate is the 347-line LatticeHalfFockFockNormalField.SOURCE.lean supplied with the converged design. The candidate identifies its prior supplier extraction by SHA256 da8469c7f1a7b7c8b9f6be6c48a7e83f9f5154d57c5309958d9806342273ecea; this is inherited attribution, not a hash of the present file or a native acceptance claim. Its ActualGround/ActualTensor, original jet scalar, mode tuple, actions, factorization, rightCode, finite minimum and support estimate are preserved, with the seed-index argument shared privately by support and truncation. The duplicate tensor-induction finiteness supplier is replaced by the existing tensor_current_truncation. New work is the consumed exponent estimate, pointwise linear coefficients, actual Hahn-field packaging, actual charged seed and native basis/finite-charge extension with its explicit finite-minimum bound.

The native current/tensor architecture retains Kalle Kytola's 2025 copyright, Apache-2.0 notice and the additional 2026 half-integer implementation notice. Finite-support, contraction and induction architecture comes through VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 and completed trureturing PolynomialFock sources at bfd9ff0f15397a4fb933f36d701a60d325d84b08. These are architectural sources, not an imported arbitrary-word half-Fock theorem. Mathematical context: Dong-Nagatomo, math/9808088v1, section 3.2, PDF pp.12-14, especially oscillator tensor ground and Delta on p.13; rank/16 is on p.19, proof of Theorem 3.13(3), attributed there to FLM. Bakalov-Kac, math/0402315v1, (4.4) and pp.10-13, (4.23)-(4.38), supplies twisted-current/field context. FLM and FHL full texts were not retrieved by this source phase. No mathematical or literature novelty is claimed.

The proof scope includes arbitrary-word pointwise finite support, derived lower truncation and finite-charge source extension on the actual dependent tensor module. The determinant witness hu remains part of the actual carrier.

The normal field is distinct from the Corr-corrected field. The shift dictionary is S_s(A)[e]=A[e+2*s], t^(-2*s)=z^(-s), with z=t^2. LatticeHalfFockOriginalTranslation proves physical translation of every corrected source. LatticeHalfFockCorrectedMonodromy proves arbitrary-polynomial parity and all-source coordinate theta monodromy. Twisted locality, Jacobi and Borcherds, full conformal identification, twisted intertwiners, holomorphic extension, Leech/Monster, anomalies and fusion, full CFT, string theory and the AdS/CFT bridge remain further obligations.

**Theorem 1.8 (Oscillator multiplication is singleton word insertion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.polynomialField_X_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.polynomialField_X_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, q:Charge D, i:Index D and p:Oscillator D, polynomialField D hu q (X i * p) equals wordField D hu (polynomialField D hu q p) [i]. singletonLinear is precisely this existing singleton wordField, organized as a linear map on its seed. The cons identity applies finsum_curry to the joint mode support of the whole word at fixed exponent and input. Adjacent exchanges reindex both modes by an involution. Same-sign jet currents commute by the actual half-integer Heisenberg law l+r+1=0; mixed signs require only association. List permutation then transports the monomial occurrence enumeration. Basis linear extension proves the statement on every algebraic oscillator polynomial, including repeated variables and inhomogeneous inputs. The normal evaluator uses this identity in its polynomial induction.

**Theorem 1.9 (The monomial basis value).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.polynomialField_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.polynomialField_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, q:Charge D and a:Index D -> finitely-supported Nat, polynomialField D hu q (monomial a 1) = wordField D hu (chargedField D hu q) (occurrences D a). This is the original basisMonomials.constr basis value, used in polynomial insertion and in the cancellation of oscillator sigma with word-length parity. Multiplicities are retained.

`D5/L/VertexAlgebra/bakalovkac2004lattice`

`D5/L/VertexAlgebra/kytola2025virasoro`

`D5/L/VertexAlgebra/flm1988monster`

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.polynomialField_X_mul`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.polynomialField_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.sourceField_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.sourceField_lower_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.wordCoefficient_lower_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.wordField_coefficient`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)

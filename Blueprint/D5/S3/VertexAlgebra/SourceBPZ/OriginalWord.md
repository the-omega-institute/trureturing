# Conditional original-carrier word and all-source BPZ

## Abstract

OriginalWord

The carrier, signed integer modes, wordField, Y, charge energy and Sugawara operators are the original lattice constructions. B is an arbitrary complex bilinear form, retaining its input order. The smaller suppliers are current transpose for every signed integer mode, including zero, and charged-primary transpose for actualField. No symmetry, nondegeneracy, positivity, rank restriction, identification with the restricted dual, or all-source BPZ premise is used. The pairing and the charged-primary supplier are not constructed by this conditional unit.

A word occurrence x=(i,p) has weight p+1. WordChoice assigns each labelled occurrence a number r in 0,...,p+1. At r=0 it deletes that occurrence with coefficient bilinear(unitCharge i,alpha); at r>0 it keeps (i,r-1) with coefficient choose(p+1,r). Repeated letters remain distinct choices. choiceRetained is the sum of these r values, choiceCoefficient is their product, and choiceLower is their ordered surviving word. The empty choice has weight zero and coefficient one.

**Theorem 1.1 (Actual charge-sector support).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.word_choice_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.word_choice_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice D, charges alpha and beta, actual oscillator word w, integer mode n and oscillator polynomial v, there exists an oscillator polynomial p such that wordField(alpha,w)[n] applied to single(beta,v) is single(alpha+beta,p). The proof propagates this property through both actual statewise finite normal-product sums. The neutral zero mode on single(beta,v) is bilinear(unitCharge i,beta) times that vector; charge additivity therefore derives the actual word zero-mode commutator, rather than requiring it as a supplier.

**Theorem 1.2 (Labelled transpose of every actual word).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_word_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_word_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix D, a complex bilinear B and charge alpha. Assume B(h_i(k)x,y)=-B(x,h_i(-k)y) for every i, signed integer k and x,y. Assume the charged-primary transpose B(actualField(alpha)[t]x,y)=paritySign(q(alpha)) B(x,actualField(alpha)[2*q(alpha)-t-2]y) for every integer t and inputs. Then for every actual word w, integer m and original u,v, its left matrix coefficient equals paritySign(q(alpha)) times (-1) raised to R times the finite sum over all WordChoice(w) of C(rho) B(u,wordField(alpha,w_rho)[2*q(alpha)+R+R_rho-m-2]v). Here R is wordWeight(w), R_rho is choiceRetained and C(rho) is choiceCoefficient.

The cons proof consumes consumed_normal_product_form. Its tail constants are K=2*q(alpha)+R_tail+R_tailchoice-2. The nondeleted branch has mode K+p+s+2-m for s=0,...,p; the deleted branch has mode K+p+1-m. choice_cons_sum separates the zero choice and the positive choices, retaining every repeated occurrence. The charged zero-mode covariance used by the insertion theorem is derived from the preceding charge-sector theorem.

The occurrence bridge uses genuine finite scalar rectangles. Choose positive current cutoffs A and C for the two inputs. The actual constructor's vector sums are finite before scalar evaluation; the divided derivative has coefficient choose(-k-1,p), with its omitted band -p<=k<0 equal to zero. Current transpose moves every negative current onto the second input, leaving a finite interval 1-C<=k<=A-1. The Heisenberg commutator proves that nonnegative currents commute and preserve both cutoffs. Expanding each recursive step in this common interval gives a finite Cartesian box. Adjacent swaps exchange two finite coordinates; currents on the same input commute, while currents on different inputs act independently. Thus scalarWord is permutation invariant. The multiset of occurrences identifies the word polynomial with the actual monomial and stateField_monomial identifies its field with Y. Applying the same argument to the flipped bilinear form proves the right-slot bridge without assuming that B is symmetric.

For each actual variable X(i,p), the existing flowPolynomial_coeff, variable_power and variable_power_charge give the finite polynomial with nondeleted terms choose(p+1,r+1) z^(p-r) X(i,r) and the charged term z^(p+1) C(kappa). Multiplicativity expands the product over WordChoice into monomial z^(R-R_rho) with coefficient C(rho) times the surviving word polynomial. Coefficient extraction and sugawara_pow_single identify the coefficient at l with (l!)^(-1) times the actual Sugawara L1 power on the original single-charge state. This is the original finite charge-sector substitution used by sourceFlow, including its charged constant term. It assumes neither BPZ nor a new source transformation law. The determinant-unit premise supplies both inverse-Gram matrix identities. The scalar choice sum is regrouped by l=R-R_rho; the resulting mode is 2*(q(alpha)+R)-l-m-2.

**Theorem 1.3 (BPZ for every actual homogeneous source).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_homogeneous_source_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_homogeneous_source_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary D with IsUnit(D.G.det), B satisfying the original current and all charged-primary transpose suppliers above, arbitrary actual source a in the existing integer grade d, integer m and original u,v, B(Y(a)[m]u,v) equals paritySign(d) times the sum over 0<=l<N(a) of (l!)^(-1) B(u,Y(L1^l a)[2*d-l-m-2]v). L1 is sugawaraMode D (gramComplex D)^(-1) 1. N(a)=sourceBound D a is exactly one plus the supremum, over the actual finite charge support of a, of the oscillator weighted total degree.

The grade premise is the existing grade D d, whose mem_grade_iff identifies every nonzero actual charge-monomial coefficient with q(alpha)+oscillatorEnergy=d. The proof expands the original finite charge and monomial supports, applies the word result, pads each finite l sum by the existing actual_sugawara_one_monomial_bound, and combines the actual linear readouts. Signed charge energies are retained. No fixed oscillator degree or finite-dimensionality assumption replaces the actual homogeneous source.

**Theorem 1.4 (Finite extension to every original source).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_source_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_source_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same determinant-unit, current and charged-primary premises, every original source a and every integer mode m satisfy the finite sum over d in stateEnergies D a of paritySign(d) times the sum over 0<=l<N(a) of (l!)^(-1) B(u,Y(L1^l(gradeProjection D d a))[2*d-l-m-2]v). This equals B(Y(a)[m]u,v). The existing sum_gradeProjections decomposes every actual finite source. Projection coefficient support proves sourceBound(projection)<=sourceBound(a), and actual_sugawara_one_bound permits the common original cutoff N(a).

The zero source, empty word, neutral charge and rank zero are retained. For a single order-one oscillator over charge alpha the correction is kappa times the primary field at the mode one lower than the reflected descendant; at order two the three coefficients are 1, 2 and kappa. These are the zero-boundary and factorial conventions in the general derivation. The transpose uses the actual L1; it does not substitute the translation operator T or identify the carrier with its restricted dual.

This is a conditional finite source calculation. Instantiation of the original pairing and charged-primary law, mixed Jacobi, full VOA/CFT/fusion, string theory and AdS/CFT remain separate mathematical obligations. The finite normal-order construction retains the source attribution of FieldNormalProduct, LatticeAllStateField and the original scalar insertion theorem; no literature novelty is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_homogeneous_source_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_source_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_word_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.word_choice_charge`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](../LatticeAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeEnergyGrading](../LatticeEnergyGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticePositiveEnergy](../LatticePositiveEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner](../Sectors/LatticeSectorIntertwiner.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose](NormalScalarTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/Coordinates](../SourceMobius/Coordinates.md)
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/OriginalCarrier](../SourceMobius/OriginalCarrier.md)

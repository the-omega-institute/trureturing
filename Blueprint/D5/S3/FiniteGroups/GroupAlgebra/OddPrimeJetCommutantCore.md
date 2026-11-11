# Actual actions and unrestricted top endomorphisms

## Abstract

Generated operators, normal form and units of the original odd-prime jet commutant

Let p be any odd prime, including three, F=ZMod p, and K any field with an F-algebra structure. The universe of K is independent. No finiteness, finite-dimensionality, perfection or nonzero-q assumption is imposed. The carrier remains V=Polynomial.degreeLT K p and the action remains the originalRepresentation q supplied by OddPrimeJetDeformation, with normalized arbitrary F-linear q satisfying q(1)=0. Every candidate X is only F-linear.

**Theorem 1.1 (The generated-action degree normal form).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutantCore.actual_commutant_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutantCore.actual_commutant_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual commutant has a unique degree-indexed form toeplitzDegree c T with c(0)=0 and arbitrary F-linear T. The operator is sum_(j<p) m(c_j) N^(p-1-j) plus the top map obtained by applying N^(p-1), reading its constant coefficient, applying T, and embedding the result as a constant polynomial. toeplitzDegree_injective proves uniqueness and coordinatesEquiv gives the two-sided coordinate equivalence. No K-linearity, injectivity or surjectivity is imposed on T.

The supplier polynomial_log_action recovers L_q(a)=aN+q(a)N^(p-1) from the original action using coefficients in F. Conversely commuting with all L_q(a) gives commuting with their finite exponentials. Since L_q(1)=N, commutation gives commutation with N. Composing L_q(a) with N^(p-2) kills the deformation term, because 2p-3>=p, and yields m(a)N^(p-1). Subtracting this highest term from L_q(a) then recovers every m(a)N. All inequalities retain p=3. The original labeled representation is preserved; only its commutant is described by these generated operators.

For e_j(z)=z*t^j/j!, e_j(z)=N^(p-1-j)e_(p-1)(z). Thus a commuting X is determined by X(e_(p-1)(z)). Reconstruction in divided monomials and commutation with m(a)N show that all its positive-degree coefficient maps are K-linear: A_j(a*z)=a*A_j(z) for j>0, hence A_j(z)=A_j(1)*z. The degree-zero coefficient map remains arbitrary F-linear. Evaluation on top vectors proves uniqueness and the converse uses the vanishing products of the top term with m(a)N.

The definition coordinatesEquiv is an explicit two-sided equivalence from the actual commutant subtype to the scalar coordinates and End_F(K), with inverse the displayed actual polynomial operator. Internally the scalar family is indexed by output degree j: c_0=0 and a_r=c_(p-1-r). This convention makes the top coefficient map visible without duplicating it as a scalar coordinate. The shift-indexed entry module verifies the change to ordinary shift indexing.

The characterization has no q on its coordinate side. Consequently the commutants of all normalized q are equal, including zero and singular q. This consequence concerns the commutant; the original labeled actions and their intertwining conditions are not identified.

**Theorem 1.2 (Units over arbitrary K).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutantCore.toeplitzDegree_isUnit_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutantCore.toeplitzDegree_isUnit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual F-linear operator is a unit if and only if a_0 is nonzero, equivalently c_(p-1) is nonzero. Any operator commuting with N and killing constants has p-th power zero: induct on the derivative-kernel filtration and use N^p=0. A zero leading scalar therefore makes X nilpotent. When a_0 is nonzero, Z=m(a_0^(-1))X-I commutes with N and kills constants, so Z^p=0. The finite nilpotent geometric inverse makes I+Z a unit, and X=m(a_0)(I+Z). The proof uses actual endomorphisms and requires no finite dimension over F.

For a fixed parameter automorphism and two existing intertwiners P,Q, their ratio Q P^(-1) is an invertible element of the source or target commutant according to composition order. Extra nonscalar F-linear top maps therefore enlarge the possible lifts of an already admissible parameter change. They do not create new admissible parameter changes: that existence criterion is the separate original-pair classification supplier. Finite-field coefficient orbit classes and the full intertwiner-group splitting require their own results and do not follow from the commutant theorem alone.

The polynomial action, finite exponential/logarithm, divided monomials and derivative-kernel suppliers retain their attribution in OddPrimeJetDeformation and the original-pair sources. The block-Toeplitz centralizer argument is classical; a broader reference is Drensky, Szigeti and van Wyk, Centralizers in endomorphism rings, arXiv:0910.2357. Nilpotent-unit calculus is reused from pinned Mathlib.RingTheory.Nilpotent.Basic. This development makes no literature-priority claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutantCore.actual_commutant_normal_form`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutantCore.toeplitzDegree_isUnit_iff`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation](OddPrimeJetDeformation.md)

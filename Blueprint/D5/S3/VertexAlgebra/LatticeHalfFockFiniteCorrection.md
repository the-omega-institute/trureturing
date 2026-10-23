# Finite Twisted Correction

## Abstract

Finite singleton and pair correction on the full ordinary lattice oscillator algebra.

LatticeData consists of an arbitrary finite rank and a symmetric integral Gram matrix with even diagonal. Rank zero, degeneracy and indefinite forms are allowed. The source weight of (i,k) is k+1; the native half-Fock weight is 2k+1. The extra polynomial variable records physical negative shifts. Singleton weights are binomial(-1/2,m) times the charge pairing; pair weights are mn binomial(-1/2,m) binomial(-1/2,n)/(m+n) times the Gram pairing. No inverse Gram matrix, positivity, rank condition or occupation cutoff occurs.

**Theorem 1.1 (Positive source weight half convolution).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.halfBinomial_positive_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.halfBinomial_positive_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all natural m,n with m>0, sum over 0<=s<=n of halfBinomial(m+s) choose(1/2,n-s) equals m halfBinomial(m) halfBinomial(n)/(m+n), over Complex. The certificate uses the arbitrary-complex binomial recurrence, telescopes only the interior 0<=s<n, and treats s=n separately. Division uses m+n nonzero from m>0, and includes n=0. The divided extension at m=n=0 is false: its left side is 1 and its right side is 0. The actual finite-current insertion triangle consumes this theorem at m=sourceWeight(D,index)=index.2+1; no standalone general cross-form API is asserted.

**Theorem 1.2 (The original pair derivation on an ordinary variable).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_variable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_variable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The original generator lemma is public for direct reuse by correctionConnection_pair_commutator in CorrectionTranslation. Its statement and proof are retained; this is consumed support, not additional mathematical content.

**Theorem 1.3 (The original half-binomial successor coefficient).**

$$\forall d\in \mathbb{N}, \operatorname{halfBinomial}\left(d+1\right)=\frac{(\frac{-1}{2}-d)\operatorname{halfBinomial}\left(d\right)}{d+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.half_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every natural d, halfBinomial(d+1) = ((-1/2-d) halfBinomial(d))/(d+1), over Complex. This factorial-product recurrence supplies the weighted binomial transform and the two-coordinate pair recurrence.

**Theorem 1.4 (Independent all-order reflection of the original pair coefficient).**

$$\forall m,n\in \mathbb{N}, \operatorname{pairScalar}\left(m+1, n+1\right)=\sum_{r=0}^{m} \sum_{s=0}^{n} ((-1)^{m+1}\operatorname{choose}\left(m+1, r+1\right))((-1)^{n+1}\operatorname{choose}\left(n+1, s+1\right))\operatorname{pairScalar}\left(r+1, s+1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairScalar_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every pair of natural orders m,n, pairScalar(m+1,n+1) is the sum over 0 <= r <= m and 0 <= s <= n of ((-1)^(m+1) choose(m+1,r+1)) ((-1)^(n+1) choose(n+1,s+1)) pairScalar(r+1,s+1). Both orders are independent and unbounded. The coefficients are exactly the original jetReflectionScalar coefficients. The definitions halfBinomial(d) = product over 0 <= j < d of (-1/2-j), divided by d!, and pairScalar(k,l) = k l halfBinomial(k) halfBinomial(l)/(k+l) are unchanged.

The finite binomial transform obeys an all-order inductive identity: its signed transform equals the original pairScalar, with zero auxiliary axis values. The proof derives a finite two-coordinate recurrence and identifies its unique solution by induction, using the positive cast of the sum of the two source weights. It assumes no covariance premise, rank, signature, occupation cutoff, determinant or lattice data.

In the actual pairPolynomial, the Gram entry stays unchanged. A reduced pair of orders r,s needs the extra shift power (m-r)+(n-s) to recover the original total source weight m+n+2. This scalar theorem alone does not prove correctionWord covariance or native all-state BPZ; labelled remainders, singleton contributions, and the operator transpose law remain required.

**Theorem 1.5 (Pair derivations annihilate every shift power).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every LatticeData, oscillator index and natural degree, pairDerivation sends X(none) raised to that degree to zero. The shift coordinate has derivative zero. This identity supplies the shift-generator case of commutation on arbitrary correction polynomials.

**Theorem 1.6 (Pair derivations annihilate every pair coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_pair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every LatticeData and every three oscillator indices, pairDerivation annihilates pairPolynomial. Its scalar coefficient is constant and its polynomial factor is a shift power. This identity supplies generator commutation and permits pair coefficients to pass through insertions.

**Theorem 1.7 (Symmetric differential insertions commute).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Each insertion is the sum of multiplication by the retained variable plus its singleton correction and the pair derivation. Pair derivations kill the shift variable and every singleton and pair coefficient. Their commutator vanishes on every polynomial generator; the mixed multiplication commutators cancel by Gram and pair-coefficient symmetry.

**Theorem 1.8 (Occurrence order does not change the correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The insertion algorithm terminates by word length. Adjacent swaps use the actual commuting insertions, and transitivity gives every occurrence permutation. Repeated variables remain separate list occurrences; differentiation supplies their multiplicities. The existing monomial basis extends the construction linearly to every finite oscillator polynomial.

**Theorem 1.9 (Every monomial enumeration gives the same finite correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every word whose occurrences permute the canonical list, the monomial-basis correction equals its word correction. The proof uses insertion commutation to compare these enumerations. Corr records this finite coefficient family as a linear map on the original oscillator algebra. The insertion of two occurrences expands into the full retained-plus-singleton product plus its pair derivative, including singleton-singleton contributions and repeated variables.

**Theorem 1.10 (Differentiation contracts one labelled occurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

labelledRemainders traverses positions recursively. Each entry retains every occurrence except the selected one, including other occurrences of the same variable. The derivation of an arbitrary correction word is the finite sum of its pair coefficient times the correction of each such remainder. The proof commutes the pair derivation through an insertion and inducts on the actual source word.

**Theorem 1.11 (Every word obeys the singleton and labelled-pair recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The active occurrence is either retained, removed as a singleton, or paired with exactly one labelled remaining occurrence. Recursive remainders shorten the word. Two occurrences therefore include retained factors, each singleton, the singleton-singleton term and the pair term, without erasing all equal variables.

**Theorem 1.12 (Word corrections never exceed the ordinary source weight).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Strong induction on occurrence count bounds the degree of the actual shift polynomial. A singleton spends the active source weight. A pair spends both removed weights, while the remainder has exactly the complementary weight. The bound applies without positivity, a charge norm bound or a rank hypothesis.

**Theorem 1.13 (Every supported shift of an arbitrary polynomial is bounded).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The unrestricted polynomial expands over its actual finite monomial support. Scalar multiplication cannot increase shift degree; every supported monomial weight is bounded by the ordinary weighted total degree. The bound holds for the actual support of Corr, with no cutoff on the polynomial or the shift index.

For the state-field application, write V_D=Carrier D=(Charge D -> finitely supported Oscillator D). A source u is thus a finite sum of single-charge states [a,p], with p an arbitrary polynomial in Fin(D.rank) times N. When hu:IsUnit D.G.det, let T_D=Oscillator D tensor ActualGround D hu, using exactly the actual ground representation and chargedField of `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients`. This determinant premise is needed for that ground realization; Corr itself still allows degenerate forms. The ordinary source field is Y_D from `D5/S3/VertexAlgebra/LatticeAllStateField`. Its source variables have weight k+1, whereas the target half-Fock variables have cover weight 2k+1.

Define N_a(p) by extending linearly from monomials the normally ordered insertion of their labelled divided-current derivatives into chargedField(a). Negative current modes act to the left and nonnegative modes to the right; the insertion order is independent of the chosen occurrence enumeration. For a native Laurent field A(t)=sum_e A[e] t^e, define S_s(A)[e]=A[e+2s], so S_s is multiplication by t^(-2s), or z^(-s) for physical z=t^2. Write Corr(a,p)[s] for its finite oscillator coefficient. The corrected field is Ytw([a,p])=sum_s S_s(N_a(Corr(a,p)[s])); extend by the actual finite charge sum to Ytw:V_D -> HVertexOperator(C,T_D). The singleton, pair and singleton-singleton terms of Corr are all retained. In particular Ytw([a,1])=chargedField(a), and the neutral first source Ytw([0,X(i,0)]) is the actual tensor current. No abstract replacement representation enters this definition.

Corr_shift_bound controls the inner shift support by the ordinary source weight, not by a chosen occupation bound. Each normal coefficient also uses finite sums on each target vector. These are different finiteness statements from a finite Laurent field: the complete field may have infinitely many external cover coefficients. Its lower bound depends on the input vector. Neither the source polynomial, its charge nor the external mode is truncated.

For A=Ytw(u), B=Ytw(w), first choose an actual operator-uniform locality order N: (t^2-s^2)^N A(t)B(s)=(t^2-s^2)^N B(s)A(t), coefficientwise as endomorphisms of the same T_D. Such an N exists for every u,w in V_D. Write C_0[e,f]=A[e] B[f] and C_(n+1)[e,f]=C_n[e-2,f]-C_n[e,f-2] for the cleared ordered coefficients. For r<N, set d=N-r-1 and define Pair_N(A,B;r)[e]x=sum_{j in Z} choose(j/2,d) C_N[j,e+2d-j]x. If L_A(x),L_B(x) are native lower bounds, locality restricts this sum to L_A(x)<=j<=e+2d-L_B(x), so it is finite on each x. For r>=N set Pair_N(A,B;r)=0. The product is independent of the chosen valid order. The all-source identity is Pair_N(Ytw(u),Ytw(w);r)=Ytw((Y_D(u)[[r]])w), for every integer r. No theta-sector hypothesis is imposed on this native identity. A product totalized as zero when no locality witness exists can be used only after this existence result, so totalization cannot supply the identity by itself.

The derivation compares the actual cleared charged products in both cover charts, including the ground cocycle and the scalar 2^(-B(a,a)). Current insertion then propagates locality and the residue equations through the same normally ordered construction. For the defect D_r(u,w)=Ytw((Y_D(u)[[r]])w)-Pair_N(Ytw(u),Ytw(w);r), the two insertion recurrences reduce negative-current insertions on the left and on the right to lower source-generation cases. First induct on the left source against theta-projected charged ground states, then on the right source against arbitrary left states. The projections span each charged ground state, so the native conclusion is unrestricted. Finite source frequency bounds and common locality orders justify each sum and cancellation. The scalar correction identities alone do not supply these operator comparisons or either source induction.

To pass to ordinary modes, define I_alpha(A).coeff(k)=A[2k-alpha], equivalently I_alpha(A)[[m]]=A[-2m-alpha-2]. For integers P,Q,r,k and x in T_D, assume the actual left sector condition: Ytw(u)[e]=0 whenever e+P is odd. A sufficient source condition is theta(u)=(-1)^P u, with theta the lattice involution of `D5/S3/VertexAlgebra/LatticeInvolution`. Then the ordinary r-th residue product of I_P(Ytw(u)) and I_Q(Ytw(w)), at mode k on x, equals sum_{i>=0} choose(P/2,i) Ytw((Y_D(u)[[r+i]])w)[-P-Q-2k+2i-2]x. The sum is finite because high ordinary source modes vanish. The right source w and its label Q are arbitrary; no right theta-eigenstate premise is added. Omitting the left sector condition would erase the distinction between the two cover parities.

This is an application of the classical twisted-lattice construction of Frenkel, Lepowsky and Meurman, with the twisted-module context also described by Bakalov and Kac, Twisted Modules over Lattice Vertex Algebras, math/0402315; no literature novelty is claimed. The finite correction, local residue comparison and state-field faithfulness concern formal Laurent operators. Translation and arbitrary-word BPZ transpose require their own identities; a full VOA or twisted-module structure, analytic CFT, anomalies, fusion, string dynamics and AdS/CFT do not follow from this application alone.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.halfBinomial_positive_convolution`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.half_successor`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_pair`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_shift`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_variable`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairScalar_reflection`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
- Narrative reference: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
- Narrative reference: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
- Narrative reference: [D5/S3/VertexAlgebra/LatticeInvolution](LatticeInvolution.md)

# Actual Mobius L1 covariance

## Abstract

Original actual-field special-conformal Ward law

**Theorem 1.1 (All-source original physical special-conformal Ward coefficient law).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance.corrected_field_l1_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance.corrected_field_l1_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The statement has every original lattice D, determinant-unit witness hu, finite-charge source a and signed exponent e. With physical z=t squared, its two independent source terms are the original inverse-Gram Sugawara modes S1 and S0: [T1,Ae(a)] = Ae(S1 a) + (e/2-1) A(e-2)(a) + 2 A(e-2)(S0 a), as an equality on the whole original actual tensor module. No source homogeneity, positivity, fixed rank, covariance premise or Jacobi premise is introduced.

The proof consumes the charged quadratic Ward calculation, the pointwise original singleton normal-order identity with its mode minus one to zero crossover, the universal half-binomial insertion cancellation after the original evaluator, and strong induction on ordinary oscillator degree. Positive source currents differentiate and lower that degree; the zero current retains the original charge scalar. Polynomial and finite-charge linearity give the full original source telescope.

For every D:LatticeData, hu:IsUnit D.G.det, a:Carrier D and e:Int, put A_e(a)=(correctedField D hu a).coeff e, T1=tensorL D (ActualGround D hu) (actualInverse D) 1 and Sj=sugawaraMode D (gramComplex D)^(-1) j. The physical z=t^2 coefficient law is T1*A_e(a)-A_e(a)*T1=A_e(S1 a)+(e/2-1) A_(e-2)(a)+2 A_(e-2)(S0 a). It acts on the entire original actual tensor module, retaining every target input, signed charge and exponent, rank zero and indefinite symmetric even unimodular Gram forms.

The charged proof route expands tensor_rawL_finsum at mode 1, where the pair indices are j and -j. The charged current Ward identity produces the original singleton at exponent e-4 and its reindexing under j to -j. At j=0 the reversed normal ordering leaves the product of the two original charge pairings times C_(e-2). The inverse Gram contractions must retain the resulting Q/2 term. The existing charged_seed_physical_coefficient then supplies the required coefficient (e-2)/2+Q. All infinite-looking sums are pointwise finite after application at x or C_e x; no finite support in Module.End is assumed.

The local singleton commutator is proved pointwise on every original actual target input. Write N_(i,r)(F)=singletonLinear (i,r) F. Given the shorter-source induction data [T1,F_d]=G_d+(d/2-1)F_(d-2)+2H_(d-2), its conclusion is [T1,N_(i,r)(F)_e]=N_(i,r)(G)_e+(e/2-1+2(r+1))N_(i,r)(F)_(e-2)+2N_(i,r)(H)_(e-2), plus zero for r=0 or (r+1)N_(i,r-1)(F)_e otherwise, plus (1/2)halfBinomial(r)[tensorCurrent_i(0),F_(e+2r+1)]. The single-term proof isolates j=-1 to 0. The summed proof uses finite support only after application at x or T1(x), reindexes j to j+1, and applies the original jet Pascal/product-rule scalar. This local induction lemma does not assume or establish the final all-source law as an external premise.

The source induction uses correctedField_negative_current_insertion. For the original insertion scalar k(m,n)=m hb(m) hb(n)/(m+n), the cancellation is (1/2)hb(m-1)choose(1/2,n)=(m+n)k(m,n)+prev(m,n)+(if m>1 then m k(m-1,n) else delta(n,0)), with prev=0 at n=0 and (n-1)k(m,n-1) otherwise. After evaluation, this cancels the current-zero crossover and the adjacent positive-current terms, including both boundary axes. Ordinary Corr commutation with source L1 while fixing the shift symbol is not used. The independent source L0 and L1 terms both remain in the conclusion.

The classical background is Frenkel, Lepowsky and Meurman, Vertex Operator Algebras and the Monster; Dong and Nagatomo, math/9808088v1; and Bakalov and Kac, math/0402315v1. Imported current and tensor implementations retain their Kalle Kytola and other original attributions. No literature novelty, independent review or Pro participation is claimed by this source. Translation, energy covariance, finite conjugation, inversion and analytic/global geometry have their own proof obligations. The full Monster, VOA, CFT, anomalies, fusion, string theory and AdS/CFT objective remains incomplete.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance.corrected_field_l1_coefficient`
- Dependency: [D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity](../../Quantum/Algebra/ConditionalPolynomialRigidity.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero](../LatticeHalfFockChargedLZero.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentWard](../LatticeHalfFockCurrentWard.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](../LatticeHalfFockOriginalTranslation.md)
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/PositiveMode](../SourceMobius/PositiveMode.md)

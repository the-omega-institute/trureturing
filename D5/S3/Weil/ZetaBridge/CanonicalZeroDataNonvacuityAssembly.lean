/- GID: D5/S3/Weil/ZetaBridge/CanonicalZeroDataNonvacuityAssembly
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/CanonicalZeroDataNonvacuityAssembly
   mirror-E: none(waiver:canonical-zero-data-semantic-assembly)
   anchors: []
   digest: Assemble count growth, zero-set infinitude, exhaustive enumeration, analytic multiplicity, symmetry, local finiteness, and realized universal claims. -/

import D5.S3.Weil.ZetaBridge.CanonicalZeroDataProvider
import D5.S3.Weil.ZetaBridge.ZeroDataSemanticNonvacuity

/-!
# Closed semantic-nonvacuity chain for canonical `ZeroData`

This module is the final logical assembly downstream of a canonical
Riemann--von Mangoldt source.  It exposes one audit certificate containing
all semantic properties that downstream RH-lane consumers need:

* an actual `ZeroData` value;
* only genuine nontrivial zeta zeros are represented;
* every such zero has exactly one index;
* exact analytic multiplicities are positive;
* reflection and conjugation preserve points and multiplicities;
* every symmetric spectral cutoff is finite.

It also proves that any theorem universally quantified over `ZeroData` is
realized on this actual canonical provider.  Hence the outer quantifier can
no longer be satisfied solely because `ZeroData` might be empty.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.CanonicalZeroDataNonvacuityAssembly

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataProvider
open D5.S3.Weil.ZetaBridge.ZeroDataSemanticNonvacuity

/-- Explicit audit certificate for a genuine exhaustive zeta-zero
enumeration.  Its fields intentionally restate the semantic obligations in
consumer-facing form rather than hiding them behind a bare structure value. -/
structure CanonicalZeroDataCertificate where
  data : ZeroData
  represents : ∀ n : ℕ, IsNontrivialZero (data.zero n)
  exhaustiveUnique : ∀ {rho : ℂ}, IsNontrivialZero rho →
    ∃! n : ℕ, data.zero n = rho
  multiplicityPositive : ∀ n : ℕ, 0 < data.multiplicity n
  reflectionFaithful : ∀ n : ℕ,
    data.zero (data.reflection n) = 1 - data.zero n
  reflectionMultiplicity : ∀ n : ℕ,
    data.multiplicity (data.reflection n) = data.multiplicity n
  conjugationFaithful : ∀ n : ℕ,
    data.zero (data.conjugation n) = conj (data.zero n)
  conjugationMultiplicity : ∀ n : ℕ,
    data.multiplicity (data.conjugation n) = data.multiplicity n
  locallyFinite : ∀ T : ℝ,
    {n : ℕ | spectralRadius (data.zero n) ≤ T}.Finite

/-- Build the complete semantic certificate from the canonical provider. -/
noncomputable def certificate (S : CanonicalZeroDataSource) :
    CanonicalZeroDataCertificate where
  data := canonicalZeroData S
  represents := canonicalZeroData_isNontrivial S
  exhaustiveUnique := canonicalZeroData_exhaustiveUnique S
  multiplicityPositive := canonicalZeroData_multiplicity_pos S
  reflectionFaithful := canonicalZeroData_reflection S
  reflectionMultiplicity := canonicalZeroData_multiplicity_reflection S
  conjugationFaithful := canonicalZeroData_conjugation S
  conjugationMultiplicity := canonicalZeroData_multiplicity_conjugation S
  locallyFinite := canonicalZeroData_locallyFinite S

/-- The certificate characterizes the represented complex numbers exactly as
the nontrivial zeta zeros. -/
theorem certificate_representation_iff
    (C : CanonicalZeroDataCertificate) (rho : ℂ) :
    IsNontrivialZero rho ↔ ∃! n : ℕ, C.data.zero n = rho := by
  constructor
  · exact C.exhaustiveUnique
  · rintro ⟨n, hn, _hunique⟩
    simpa [hn] using C.represents n

/-- Every certificate has an actual represented nontrivial zero. -/
theorem certificate_exists_nontrivial_zero
    (C : CanonicalZeroDataCertificate) :
    ∃ rho : ℂ, IsNontrivialZero rho :=
  ⟨C.data.zero 0, C.represents 0⟩

/-- Full closed chain from canonical Riemann--von Mangoldt growth to a
semantically faithful `ZeroData` certificate. -/
theorem canonical_zeroData_closed_chain
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    {rho : ℂ | IsNontrivialZero rho}.Infinite ∧
      Nonempty ZeroData ∧
      ∃ C : CanonicalZeroDataCertificate,
        C.data = canonicalZeroData ⟨hRvM⟩ := by
  refine ⟨nontrivial_zeta_zero_set_infinite_of_riemannVonMangoldt hRvM,
    nonempty_zeroData_of_riemannVonMangoldt hRvM, ?_⟩
  exact ⟨certificate ⟨hRvM⟩, rfl⟩

/-- Expanded consumer-facing version of the closed chain.  It returns one
actual enumeration together with exact representation, multiplicity,
symmetry, and cutoff guarantees. -/
theorem exists_faithful_zeroData_of_riemannVonMangoldt
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    ∃ Z : ZeroData,
      (∀ rho : ℂ, IsNontrivialZero rho ↔ ∃! n : ℕ, Z.zero n = rho) ∧
      (∀ n : ℕ, 0 < Z.multiplicity n) ∧
      (∀ n : ℕ, Z.zero (Z.reflection n) = 1 - Z.zero n) ∧
      (∀ n : ℕ,
        Z.multiplicity (Z.reflection n) = Z.multiplicity n) ∧
      (∀ n : ℕ, Z.zero (Z.conjugation n) = conj (Z.zero n)) ∧
      (∀ n : ℕ,
        Z.multiplicity (Z.conjugation n) = Z.multiplicity n) ∧
      (∀ T : ℝ, {n : ℕ | spectralRadius (Z.zero n) ≤ T}.Finite) := by
  let C : CanonicalZeroDataCertificate := certificate ⟨hRvM⟩
  refine ⟨C.data, ?_, C.multiplicityPositive, C.reflectionFaithful,
    C.reflectionMultiplicity, C.conjugationFaithful,
    C.conjugationMultiplicity, C.locallyFinite⟩
  intro rho
  exact certificate_representation_iff C rho

/-- Every universal `ZeroData` theorem is realized on the certified canonical
enumeration, together with a concrete represented nontrivial zero. -/
theorem universal_claim_realized_on_canonical_zeroData
    {P : ZeroData → Prop}
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig)
    (h : ∀ Z : ZeroData, P Z) :
    ∃ C : CanonicalZeroDataCertificate,
      P C.data ∧ ∃ rho : ℂ, IsNontrivialZero rho := by
  let C : CanonicalZeroDataCertificate := certificate ⟨hRvM⟩
  exact ⟨C, h C.data, certificate_exists_nontrivial_zero C⟩

/-- The outer universal quantifier is therefore semantically realized in the
precise predicate introduced by `ZeroDataSemanticNonvacuity`. -/
theorem universal_claim_is_realized
    {P : ZeroData → Prop}
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig)
    (h : ∀ Z : ZeroData, P Z) :
    RealizedZeroDataClaim P :=
  ⟨(certificate ⟨hRvM⟩).data, h (certificate ⟨hRvM⟩).data⟩

#print axioms certificate_representation_iff
#print axioms certificate_exists_nontrivial_zero
#print axioms canonical_zeroData_closed_chain
#print axioms exists_faithful_zeroData_of_riemannVonMangoldt
#print axioms universal_claim_realized_on_canonical_zeroData
#print axioms universal_claim_is_realized

end D5.S3.Weil.ZetaBridge.CanonicalZeroDataNonvacuityAssembly

/- GID: D5/S3/Weil/ZetaBridge/ZeroDataSemanticNonvacuity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ZeroDataSemanticNonvacuity
   mirror-E: none(waiver:semantic-nonvacuity-interface-only)
   anchors: []
   digest: Distinguish vacuous universal ZeroData claims from claims realized by an actual canonical zero enumeration. -/

import D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt

/-!
# Semantic nonvacuity for `ZeroData`

The index of every supplied `ZeroData` is already `ℕ`, so an actual value
`Z : ZeroData` always contains a zeroth enumerated zero.  The possible
vacuity is one level higher: the type `ZeroData` itself may be empty, in
which case a theorem of shape `∀ Z : ZeroData, P Z` is true without being
instantiated on any zeta-zero enumeration.

This module makes that distinction explicit.  It gives the general
eliminator from `Nonempty ZeroData` and specializes it to the canonical
Riemann--von Mangoldt source constructed by the preceding bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.ZeroDataSemanticNonvacuity

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt

/-- A predicate on zero enumerations is semantically realized when it holds
for at least one actual `ZeroData` value. -/
def RealizedZeroDataClaim (P : ZeroData → Prop) : Prop :=
  ∃ Z : ZeroData, P Z

/-- Every supplied `ZeroData` value already exhibits an actual nontrivial
zeta zero, namely its zeroth entry. -/
theorem ZeroData.exists_nontrivial_zero (Z : ZeroData) :
    ∃ rho : ℂ, IsNontrivialZero rho :=
  ⟨Z.zero 0, Z.zero_isNontrivial 0⟩

/-- Exact outer-vacuity audit: if `ZeroData` has no inhabitant, every
universally quantified predicate on `ZeroData` is propositionally true. -/
theorem forall_zeroData_of_not_nonempty
    {P : ZeroData → Prop} (hEmpty : ¬ Nonempty ZeroData) :
    ∀ Z : ZeroData, P Z := by
  intro Z
  exact (hEmpty ⟨Z⟩).elim

/-- An inhabited zero-data domain converts a universal conditional theorem
into a theorem realized by an actual enumeration. -/
theorem realized_of_forall_of_nonempty
    {P : ZeroData → Prop} (hZ : Nonempty ZeroData)
    (h : ∀ Z : ZeroData, P Z) :
    RealizedZeroDataClaim P := by
  rcases hZ with ⟨Z⟩
  exact ⟨Z, h Z⟩

/-- Canonical Riemann--von Mangoldt growth eliminates outer vacuity for every
universal `ZeroData` theorem. -/
theorem realized_of_forall_of_riemannVonMangoldt
    {P : ZeroData → Prop}
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig)
    (h : ∀ Z : ZeroData, P Z) :
    RealizedZeroDataClaim P :=
  realized_of_forall_of_nonempty
    (nonempty_zeroData_of_riemannVonMangoldt hRvM) h

/-- The canonical Riemann--von Mangoldt source implies the existence of a
nontrivial zeta zero as a direct semantic consequence of the constructed
`ZeroData` inhabitant. -/
theorem exists_nontrivial_zero_of_riemannVonMangoldt
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    ∃ rho : ℂ, IsNontrivialZero rho :=
  (zeroDataOfRiemannVonMangoldt hRvM).exists_nontrivial_zero

/-- A universal theorem and canonical Riemann--von Mangoldt data jointly
produce both a realizing enumeration and a represented nontrivial zero. -/
theorem realized_claim_with_nontrivial_zero
    {P : ZeroData → Prop}
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig)
    (h : ∀ Z : ZeroData, P Z) :
    ∃ Z : ZeroData, P Z ∧ ∃ rho : ℂ, IsNontrivialZero rho := by
  let Z : ZeroData := zeroDataOfRiemannVonMangoldt hRvM
  exact ⟨Z, h Z, Z.exists_nontrivial_zero⟩

#print axioms ZeroData.exists_nontrivial_zero
#print axioms forall_zeroData_of_not_nonempty
#print axioms realized_of_forall_of_nonempty
#print axioms realized_of_forall_of_riemannVonMangoldt
#print axioms exists_nontrivial_zero_of_riemannVonMangoldt
#print axioms realized_claim_with_nontrivial_zero

end D5.S3.Weil.ZetaBridge.ZeroDataSemanticNonvacuity

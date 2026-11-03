import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth
import Reg.Support.DependentFamily

/-! The complete odd-parameter telescope with its actual quotient-image observation. -/
namespace Reg.D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth

open _root_.D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth
open _root_.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity

/-- All integer parameter fibers, with their actual quotient-image observations. -/
abbrev asymmetricSignature : Signature where
  Params := Σ _ : ℤ, Σ _ : ℤ, Σ _ : ℤ, ℤ
  State t :=
    let p := t.1
    let m := t.2.1
    let a := t.2.2.1
    let b := t.2.2.2
    let v1 : Plane := ![p*(m-a)/2, p*(m+a)/2]
    let v2 : Plane := ![p*(m-b)/2, -(p*(m+b)/2)]
    Finset (Plane ⧸ Submodule.span ℤ (Set.range ![v1, v2]))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def asymmetricActual : Realization asymmetricSignature :=
  realize asymmetricSignature (fun _ _ s => s.card) (fun e => nomatch e)

noncomputable def asymmetricRejected : Realization asymmetricSignature :=
  realize asymmetricSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev asymmetricArena : Arena where
  signature := asymmetricSignature
  Law R := ∀ (p m a b : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (hmo : Odd m) (hao : Odd a) (hbo : Odd b)
    (ha : 0 < a) (ham : a < m) (hb : 0 < b) (hbm : b < m),
    let v1 : Plane := ![p*(m-a)/2, p*(m+a)/2]
    let v2 : Plane := ![p*(m-b)/2, -(p*(m+b)/2)]
    let K : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1, v2])
    let G := Plane ⧸ K
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let F : Plane →+ G := K.mkQ.toAddMonoidHom
    let f : (ℤ × ℤ) →+ G := F.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    Finite G ∧ ¬ IsAddCyclic G ∧
      (Nat.card G : ℤ) = p^2*(m^2-a*b)/2 ∧
      (∀ r : ℕ, r ≤ s →
        let wa : ℤ := 2*(r : ℤ)-p*(m-a)+1
        let wb : ℤ := 2*(r : ℤ)-p*(m-b)+1
        R.readout () ⟨p,m,a,b⟩ ((leeDiamond r).image f) + (wa.toNat*wb.toNat+1)/2 =
          2*r^2+2*r+1) ∧
      LeeCovers F (s : ℤ) ∧
      ¬ LeeCovers F ((s-1 : ℕ) : ℤ) ∧
      ∀ R : ℕ, LeeCovers F (R : ℤ) ↔ s ≤ R

private theorem asymmetricRejected_law : ¬ asymmetricArena.Law asymmetricRejected := by
  intro h
  have hh := h 3 3 1 1 (by norm_num) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hz := hh.2.2.2.1 0 (by norm_num)
  norm_num [asymmetricRejected, realize] at hz

noncomputable def asymmetricSource : Registration asymmetricArena
    (type_of% (@asymmetric_quotient_growth)) where
  actual := asymmetricActual
  bridge := Iff.rfl
  variation := ⟨asymmetric_quotient_growth, asymmetricRejected, asymmetricRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨asymmetricRejected, ?_, rfl, asymmetricRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨3,3,1,1⟩, ∅, {0}, ?_⟩
    change (0 : ℕ) ≠ 1
    decide

noncomputable def asymmetricRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@asymmetric_quotient_growth)
      (Realization asymmetricSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth.asymmetric_quotient_growth.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth.asymmetricSource
  realizationSource := none
  generated := false
  arena := .source ⟨asymmetricArena⟩
  objectArena := .source ⟨asymmetricArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source asymmetricArena ⟨asymmetricSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize asymmetricSignature
    (fun _ _ s => s.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","arg","arg","fn","arg","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth

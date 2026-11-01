import LeanInformationAuditInterface.Contract.Registration
import D5.S3.SpectralTopology.RectangularDilation
import Reg.Support.DependentFamily

/-! Source-bound family audit of the full real-to-complex ordered spectrum identity. -/

namespace Reg.D5.S3.SpectralTopology.RectangularDilation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
noncomputable section
universe u
structure Index where
  carrier : Type u
  finite : Fintype carrier
  equality : DecidableEq carrier
attribute [instance] Index.finite Index.equality
abbrev signature : Signature where
  Params := Index.{u}
  State p := (Fin (Fintype.card p.carrier) → ℝ) × (Fin (Fintype.card p.carrier) → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Index, ∀ (A : Matrix p.carrier p.carrier ℝ) (hA : A.IsHermitian)
    (hC : (A.map Complex.ofReal).IsHermitian), R.readout () p (hC.eigenvalues₀, hA.eigenvalues₀)
private def bad : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private theorem bridge : (type_of% (@_root_.D5.S3.SpectralTopology.RectangularDilation.eigenvalues_ofReal.{u})) ↔
    (arena.{u}).Law (actual.{u}) := by
  constructor
  · intro h p
    exact @h p.carrier p.finite p.equality
  · intro h ι finite equality
    exact h ⟨ι, finite, equality⟩
private theorem bad_reject : ¬ arena.Law (bad : Realization signature.{u}) := by
  intro h
  let p : Index.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  exact h p 0 isHermitian_zero (by simpa using (isHermitian_zero :
    (0 : Matrix p.carrier p.carrier ℂ).IsHermitian))
def eigenvalues_ofReal_family : Registration (arena.{u})
    (type_of% (@_root_.D5.S3.SpectralTopology.RectangularDilation.eigenvalues_ofReal.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @_root_.D5.S3.SpectralTopology.RectangularDilation.eigenvalues_ofReal.{u},
    bad, bad_reject⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, bad_reject⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let p : Index.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
    refine ⟨p, (fun _ => 0, fun _ => 0), (fun _ => 0, fun _ => 1), ?_⟩
    intro h
    have hh : (fun _ : Fin (Fintype.card p.carrier) => (0:ℝ)) = fun _ => 1 := Eq.mp h rfl
    have hv : (0:ℝ) = 1 := congrFun hh ⟨0, by simp [p]⟩
    exact zero_ne_one hv
def registration_eigenvalues_ofReal : Contract.Registration
    (@_root_.D5.S3.SpectralTopology.RectangularDilation.eigenvalues_ofReal.{u})
    (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.SpectralTopology.RectangularDilation.eigenvalues_ofReal_unit
  realizationName := `Reg.D5.S3.SpectralTopology.RectangularDilation.eigenvalues_ofReal_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨eigenvalues_ofReal_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.1 = x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.SpectralTopology.RectangularDilation

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio
open _root_.D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder
noncomputable section

abbrev ratioSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def ratioActual : Realization ratioSignature :=
  realize ratioSignature (fun _ _ r t => (phi r t : ℂ)) (fun e => nomatch e)

def ratioRejected : Realization ratioSignature :=
  realize ratioSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev ratioArena : Arena where
  signature := ratioSignature
  Law Q := ∀ r : ℝ, r < 1 →
    ¬ _root_.D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
      (Q.readout () () r)

private theorem ratioArenaRejected : ¬ ratioArena.Law ratioRejected := by
  intro h
  exact h 0 (by norm_num) (fun m x => _root_.Matrix.PosSemidef.zero)

private theorem ratioArenaDependence : ObservationalDependence ratioSignature ratioActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrArg (fun g : ℝ → ℂ => (g 1).re) he
  have hs : Real.sinh 1 ≠ 0 := Real.sinh_ne_zero.mpr (by norm_num)
  change phi 0 1 = phi 1 1 at h
  have hh : Real.cosh 1 / Real.sinh 1 = 1 / Real.sinh 1 := by
    simpa [phi] using h
  have heq := (div_left_inj' hs).mp hh
  have hgt : 1 < Real.cosh 1 := Real.one_lt_cosh.mpr (by norm_num)
  linarith

def ratioArenaSource : Registration ratioArena (type_of% @result) where
  actual := ratioActual
  bridge := Iff.rfl
  variation := ⟨result, ratioRejected, ratioArenaRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨ratioRejected, ?_, rfl, ratioArenaRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := ratioArenaDependence

def ratioAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization ratioSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio.ratioAuditUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio.ratioArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨ratioArena⟩
  objectArena := .source ⟨ratioArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ratioArena ⟨ratioArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ratioSignature (fun _ _ r t => (phi r t : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio
    definition := some {
      owner := `D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio
      name := `D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms ratioAudit

end
end Reg.D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio

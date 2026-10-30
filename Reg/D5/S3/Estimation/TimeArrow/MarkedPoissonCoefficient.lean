import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient

open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open _root_.D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
open _root_.D5.S3.Estimation.TimeArrow.ForwardMarkedPathTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ × ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M q T k : ℕ} {r : ℝ},
    1 ≤ q → q < M → 0 < r → r < 1 → compensation M q r < 1 →
    ∀ (S : Support M q) (m : Fin k → Fin M), Function.Injective m →
    ∀ zp zm : Fin k → ℂ,
      actualPGF r S m zp zm T =
        R.readout () () (forwardState (driftA r S m zp zm) (driftB r S m zp zm) T) ∧
      actualPGF r S m zp zm T =
        (forwardMatrix (driftA r S m zp zm) (driftB r S m zp zm) ^ T) 0 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : Support 2 1 := ⟨{0}, by simp⟩
  let m : Fin 0 → Fin 2 := Fin.elim0
  let z : Fin 0 → ℂ := Fin.elim0
  have hm : Function.Injective m := by intro i; exact Fin.elim0 i
  have hc : compensation 2 1 (1 / 4) < 1 := by norm_num [compensation]
  have hp := (actual_marked_path_transfer (T := 0) (by norm_num : 1 ≤ 1)
    (by norm_num : 1 < 2) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hc S m hm z z).1
  have hp' : actualPGF (1 / 4) S m z z 0 = 1 := by
    exact hp.trans (by rfl)
  have hb := (law (M := 2) (q := 1) (T := 0) (k := 0) (r := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc S m hm z z).1
  change actualPGF (1 / 4) S m z z 0 = 0 at hb
  rw [hp'] at hb
  norm_num at hb

def family : Registration arena (type_of% @actual_marked_path_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_marked_path_transfer, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), ((0 : ℂ), (0 : ℂ)), ((1 : ℂ), (0 : ℂ)), ?_⟩
    change (0 : ℂ) ≠ 1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_marked_path_transfer) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient.unit
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient

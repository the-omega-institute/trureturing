import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.FiveModeDensityFiber
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Quantum.Fibers.FiveModeDensityFiber
noncomputable section
open scoped ComplexOrder MatrixOrder
namespace Reg.D5.S3.Quantum.Fibers.FiveModeDensityFiber

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (Fin 3 → ℝ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (ρ : Matrix (Fin 5) (Fin 5) ℂ) (hρ : ρ.PosDef) (ht : Matrix.trace ρ = 1),
    Module.finrank ℝ (LinearMap.ker modeReadout) = 21 ∧
    (∀ σ : Matrix (Fin 5) (Fin 5) ℂ, σ.IsHermitian →
      ((Matrix.trace σ = 1 ∧ r.readout () () (means σ) (means ρ)) ↔
        ∃! h : LinearMap.ker modeReadout, σ = fibrePoint ρ h)) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : LinearMap.ker modeReadout,
      ‖CStarMatrix.ofMatrix h.1.1.1‖ < ε →
      (fibrePoint ρ h).PosDef ∧ Matrix.trace (fibrePoint ρ h) = 1 ∧
        r.readout () () (means (fibrePoint ρ h)) (means ρ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : fiveModeCenter.PosDef := Matrix.PosDef.one.smul (by norm_num)
  have ht : Matrix.trace fiveModeCenter = 1 := by simp [fiveModeCenter,Matrix.trace]
  obtain ⟨_,_,ε,hε,hball⟩ := h fiveModeCenter hp ht
  have hz : ‖CStarMatrix.ofMatrix (0 : LinearMap.ker modeReadout).1.1.1‖ < ε := by
    simpa using hε
  exact (hball 0 hz).2.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have he := congrFun h 0
  have hc : (1 : Fin 3 → ℝ) = 0 := he.mp rfl
  have hh := congrFun hc 0
  norm_num at hh

def family : Registration arena (type_of% (@full_rank_local_fibre)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@full_rank_local_fibre,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_rank_local_fibre)
    (type_of% (realize signature (fun _ _ x y => x = y) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Fibers.FiveModeDensityFiber.full_rank_local_fibre.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.FiveModeDensityFiber.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.FiveModeDensityFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]}

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Fibers.FiveModeDensityFiber

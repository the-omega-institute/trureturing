import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Resource.CompositeCones
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays
open scoped BigOperators ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

abbrev signature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Fin p.1 × Fin p.2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ ψ => 1 + (2 : ℂ) • vecMulVec ψ (star ψ)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} (ψ : Fin m × Fin n → ℂ),
    (∑ ij, ‖ψ ij‖ ^ 2) = 1 → separableCone (R.readout () ⟨m, n⟩ ψ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) (fun _ => 1) (by simp)
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤ -1 at hd
  norm_num [Complex.le_def] at hd

def family : Registration arena (type_of% @separableCone_one_add_two_rankOne) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨separableCone_one_add_two_rankOne, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrFun (congrFun h (0, 0)) (0, 0)
    change
      (1 + (2 : ℂ) • vecMulVec (fun _ : Fin 1 × Fin 1 => (0 : ℂ))
        (star (fun _ : Fin 1 × Fin 1 => (0 : ℂ)))) (0, 0) (0, 0) =
      (1 + (2 : ℂ) • vecMulVec (fun _ : Fin 1 × Fin 1 => (1 : ℂ))
        (star (fun _ : Fin 1 × Fin 1 => (1 : ℂ)))) (0, 0) (0, 0) at he
    norm_num [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.vecMulVec_apply, Pi.star_apply] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@separableCone_one_add_two_rankOne) (Realization signature)
    Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount
import Reg.Support.DependentFamily

/-! Source-bound audit of the exact quantum-graph component count. -/

namespace Reg.D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount

open _root_.D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount
open _root_.D5.S3.Quantum.Matrix.CfmRadialDerivative (Mat)
open _root_.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment (offDiag)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the component count as the common diagonal varies. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ _ : Mat n, Mat n
  State p := Fin p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d =>
    graphComponentCount p.2.1 p.2.2 + loopFreeStrangeComponentCount p.2.1 p.2.2 d)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain all projector hypotheses and the complete greatest-count assertion. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (A C : Mat n) (d : Fin n → ℂ),
    (∀ i, A i i = d i) → (∀ i, C i i = d i) →
    (realignedProjector A C d).IsHermitian →
    realignedProjector A C d * realignedProjector A C d = realignedProjector A C d →
    (offDiag A).IsHermitian →
    IsGreatest {k | HasComponents (adjacency A C d) k} (r.readout () ⟨n, A, C⟩ d)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hR : realignedProjector (0 : Mat 1) 0 0 = 0 := by
    ext p q
    simp [realignedProjector]
  have hbad := h 1 0 0 0 (by simp) (by simp)
    (by rw [hR]; exact Matrix.isHermitian_zero)
    (by rw [hR]; simp) (by simp)
  have hone : HasComponents (adjacency (0 : Mat 1) 0 0) 1 := by
    refine ⟨fun _ => 1, fun _ => ⟨IsStarProjection.one _, one_ne_zero⟩, ?_, ?_⟩
    · simp
    · intro s t hst
      exact (hst (Subsingleton.elim s t)).elim
  have hle := hbad.2 hone
  change 1 ≤ (0 : ℕ) at hle
  omega

private def halfMatrix : Mat 2 := fun _ _ => 1 / 2

private theorem strange_zero_pos :
    0 < loopFreeStrangeComponentCount halfMatrix 0 0 := by
  classical
  have htop : underlyingGraph halfMatrix 0 = (⊤ : SimpleGraph (Fin 2)) := by
    ext i j
    simp [underlyingGraph, halfMatrix]
  let Q := (underlyingGraph halfMatrix 0).connectedComponentMk 0
  have hs : Q.supp = Set.univ := by
    have hall : ∀ c : (underlyingGraph halfMatrix 0).ConnectedComponent,
        c.supp = Set.univ := by
      rw [htop]
      exact SimpleGraph.ConnectedComponent.top_supp_eq_univ
    exact hall Q
  have hpair : Q.supp = {0, 1} := by
    rw [hs]
    ext i
    fin_cases i <;> simp
  change 0 < Fintype.card {Q : (underlyingGraph halfMatrix 0).ConnectedComponent //
    IsLoopFreeStrangeComponent halfMatrix 0 0 Q}
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨Q, 0, 1, by decide, hpair,
    by simp [underlyingGraph, halfMatrix], rfl, rfl, rfl⟩⟩

private theorem strange_one_zero :
    loopFreeStrangeComponentCount halfMatrix 0 (fun _ => 1) = 0 := by
  classical
  let : IsEmpty {Q : (underlyingGraph halfMatrix 0).ConnectedComponent //
      IsLoopFreeStrangeComponent halfMatrix 0 (fun _ => 1) Q} := ⟨by
    rintro ⟨Q, i, j, hij, hpair, hadj, hhalf, hdi, hdj⟩
    exact one_ne_zero hdi⟩
  exact Fintype.card_eq_zero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, halfMatrix, 0⟩, 0, (fun _ => 1), ?_⟩
  change graphComponentCount halfMatrix 0 + loopFreeStrangeComponentCount halfMatrix 0 0 ≠
    graphComponentCount halfMatrix 0 +
      loopFreeStrangeComponentCount halfMatrix 0 (fun _ => 1)
  rw [strange_one_zero]
  have hpos := strange_zero_pos
  omega

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d =>
    graphComponentCount p.2.1 p.2.2 + loopFreeStrangeComponentCount p.2.1 p.2.2 d)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount
    definition := some {
      owner := `D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount
      name := `D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount.claim
      path := #[] }
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount

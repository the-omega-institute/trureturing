import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness
import Reg.Support.UniverseSingleReadout

/-! Source-bound audit of the conference-graph return probability. -/

namespace Reg.D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness
open _root_.D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness
open _root_.D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (hamiltonianPropagator)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Retain the graph's original finite and decidable structures as parameters. -/
abbrev Parameters : Type 1 :=
  Σ _m : ℕ, Σ V : Type, Σ _ : Fintype V, Σ _ : DecidableEq V,
    Σ G : SimpleGraph V, Σ _ : DecidableRel G.Adj, V

/-- Time is the original unrestricted real state. -/
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Parameters (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p t =>
    letI : Fintype (Sigma.fst (Sigma.snd p)) :=
      Sigma.fst (Sigma.snd (Sigma.snd p))
    letI : DecidableEq (Sigma.fst (Sigma.snd p)) :=
      Sigma.fst (Sigma.snd (Sigma.snd (Sigma.snd p)))
    let G := Sigma.fst (Sigma.snd (Sigma.snd (Sigma.snd (Sigma.snd p))))
    letI : DecidableRel G.Adj :=
      Sigma.fst (Sigma.snd (Sigma.snd (Sigma.snd (Sigma.snd (Sigma.snd p)))))
    let u := Sigma.snd (Sigma.snd (Sigma.snd (Sigma.snd (Sigma.snd (Sigma.snd p)))))
    ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Replace only the return probability in the nonsquare approximation clause. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (m : ℕ), 1 ≤ m → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m → ∀ u : V,
      (IsSquare (4 * m + 1) →
        (∀ t : ℝ, 1 / (4 * (m : ℝ) + 1) ^ 2 ≤
          ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2) ∧
        (∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 =
          1 / (4 * (m : ℝ) + 1) ^ 2)) ∧
      (¬ IsSquare (4 * m + 1) →
        (∀ t : ℝ, 0 ≤ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2) ∧
        ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧
          R.readout () ⟨m, V, inferInstance, inferInstance, G, inferInstance, u⟩ t < ε)) ∧
    ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ (m : ℕ), 1 ≤ m → N ≤ 4 * m + 1 →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m → ∀ u : V,
      ∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 < c

/-- The five-cycle supplies a concrete nonsquare conference graph. -/
def pentagon : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun i j => i - j = 1 ∨ j - i = 1)

instance : DecidableRel pentagon.Adj := by
  unfold pentagon
  infer_instance

private theorem pentagon_srg : pentagon.IsSRGWith 5 2 0 1 where
  card := Fintype.card_fin 5
  regular := by unfold SimpleGraph.IsRegularOfDegree; decide
  of_adj := by decide
  of_not_adj := by unfold Pairwise; decide

private theorem five_nonsquare : ¬ IsSquare (5 : ℕ) := by
  rintro ⟨k, hk⟩
  have hlow : k ≤ 2 ∨ 3 ≤ k := by omega
  rcases hlow with h | h <;> nlinarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, _, ht⟩ := (h.1 1 (by norm_num) (Fin 5) pentagon
    pentagon_srg 0).2 five_nonsquare |>.2 1 (by norm_num)
  exact (lt_irrefl (1 : ℝ)) ht

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨t, _, ht⟩ := (result.1 1 (by norm_num) (Fin 5) pentagon
    pentagon_srg 0).2 five_nonsquare |>.2 1 (by norm_num)
  refine ⟨⟨1, Fin 5, inferInstance, inferInstance, pentagon,
    inferInstance, 0⟩, 0, t, ?_⟩
  change ‖hamiltonianPropagator (pentagon.adjMatrix ℂ) (-0) 0 0‖ ^ 2 ≠
    ‖hamiltonianPropagator (pentagon.adjMatrix ℂ) (-t) 0 0‖ ^ 2
  have hz : ‖hamiltonianPropagator (pentagon.adjMatrix ℂ) (-0) 0 0‖ ^ 2 =
      1 := by simp [hamiltonianPropagator]
  rw [hz]
  exact ne_of_gt ht

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness.result)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness.unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness
    definition := some {
      owner := `D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness
      name := `D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness.claim
      path := #[] }
    coordinates := #[0, 2, 3, 4, 5, 6, 8]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body", "body", "arg", "body", "arg",
        "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness

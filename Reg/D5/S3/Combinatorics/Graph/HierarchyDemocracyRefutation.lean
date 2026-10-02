import D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
open _root_.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n) (Fin n) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete negated claim; only the matrix in `WeaklyConnected A` is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ¬ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, 0 ≤ A i j) → (∀ i, A i i = 0) →
    WeaklyConnected (O.readout () n A) → ∀ g, IsForwardLevels A g → forwardDemocracy A g ≤ 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro n A _ hdiag hconn g _
  change WeaklyConnected (0 : Matrix (Fin n) (Fin n) ℝ) at hconn
  rcases n with _ | _ | n
  · exact hconn.nonempty.elim fun v => Fin.elim0 v
  · have hA : A = 0 := by
      ext i j
      fin_cases i; fin_cases j
      exact hdiag 0
    subst hA
    simp [forwardDemocracy]
  · exfalso
    obtain ⟨w⟩ := hconn.preconnected 0 1
    cases w with
    | cons hadj _ =>
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with hlt | hlt <;> simp at hlt

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  change (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 at this
  simp at this

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.result in arena
  readout via (realize signature (fun _ _ A => A) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
    «definition» := some {
      owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
      name := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.claim
      path := #["arg"] }
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation

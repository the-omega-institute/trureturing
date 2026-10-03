import D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
import Reg.Support.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
open _root_.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Equiv.Perm (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin n → Fin n
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => ⇑s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => id) (fun e => nomatch e)

/-- The complete claim; only the permutation in the fixed-point condition is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ n : ℕ, 2 < n →
    ((∃ s : Equiv.Perm (Fin n), (∀ i, O.readout () n s i ≠ i) ∧
      ∀ X : Type, IsSolution n (simpleMap (X := X) s)) ↔ Even n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, hs, -⟩ := (h 4 (by norm_num)).mpr (by decide)
  exact hs 0 rfl

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, Equiv.refl (Fin 2), (Equiv.swap (0 : Fin 2) 1 : Equiv.Perm (Fin 2)),
    fun h => ?_⟩
  have h0 : Equiv.refl (Fin 2) 0 = Equiv.swap (0 : Fin 2) 1 0 := congrFun h (0 : Fin 2)
  simp at h0

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.result in arena
  readout via (realize signature (fun _ _ s => ⇑s) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
    «definition» := some {
      owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
      name := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.claim }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "fn", "arg", "body", "fn", "arg",
        "fn"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations

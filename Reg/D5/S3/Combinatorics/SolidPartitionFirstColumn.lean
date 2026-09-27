import D5.S3.Combinatorics.SolidPartitionFirstColumn
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn
open _root_.D5.S3.Combinatorics.SolidPartitionFirstColumn

/-- Dimension is unrestricted (including zero); the positive-dimension and size
guards belong to the complete Law, not to a restricted signature. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ d n => tau d n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → firstColumn d n = r.readout () d n ∧
    shrinkColumn d n = tau d (n + 1)

theorem tau_one (d : ℕ) : tau d 1 = 1 := by
  have singleton : {v : Fin d → ℕ | ∏ i, v i = 1} = {fun _ => 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.prod_eq_one_iff,
      Finset.mem_univ, forall_const, funext_iff]
  rw [tau, singleton, Set.ncard_singleton]

theorem tau_two_two_ne_one : tau 2 2 ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h
  let a : Fin 2 → ℕ := fun i => if i = 0 then 2 else 1
  let b : Fin 2 → ℕ := fun i => if i = 1 then 2 else 1
  have ha : a ∈ {v : Fin 2 → ℕ | ∏ i, v i = 2} := by decide
  have hb : b ∈ {v : Fin 2 → ℕ | ∏ i, v i = 2} := by decide
  rw [hv, Set.mem_singleton_iff] at ha hb
  have e := congrFun (ha.trans hb.symm) 0
  change 2 = 1 at e
  contradiction

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have original :=
    (_root_.D5.S3.Combinatorics.SolidPartitionFirstColumn.result 2 1 (by decide) (by decide)).1
  rw [tau_one] at original
  have zero := (h 2 1 (by decide) (by decide)).1
  change firstColumn 2 1 = 0 at zero
  omega

/-- One permitted fiber witnesses dependence; the Law still quantifies over every dimension. -/
theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨2, 1, 2, ?_⟩
  change tau 2 1 ≠ tau 2 2
  rw [tau_one]
  exact Ne.symm tau_two_two_ne_one

noncomputable def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.SolidPartitionFirstColumn.result, rejected, rejected_law⟩
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
  _root_.D5.S3.Combinatorics.SolidPartitionFirstColumn.result in arena
  readout via (realize signature (fun _ d n => tau d n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn
    «definition» := some {
      owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn
      name := `D5.S3.Combinatorics.SolidPartitionFirstColumn.claim }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn

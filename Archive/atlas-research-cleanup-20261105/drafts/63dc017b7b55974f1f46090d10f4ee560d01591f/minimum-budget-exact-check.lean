import D5.S3.Combinatorics.CircularWords.ThreeSpecifiedDeletions
import D5.S3.Observer.Budget.MinimumCompleteSetCover
set_option autoImplicit false
namespace MinimumDeletionBudgetExactCheck
open D5.S3.Combinatorics.CircularWords
open CircularDeletionTransport DeletionReadoutReconstruction ThreeSpecifiedDeletions
open D5.S3.Observer.Budget.MinimumCompleteSetCover
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
universe u
variable {α : Type u} [DecidableEq α]

theorem complete_iff {A : Finset α} (hA : 4 ≤ A.card) (J : Finset A) :
    Function.Injective (jointReadout
      (fun i : {candidate // candidate ∈ J} => deletionReadout A i.1)) ↔
    3 ≤ J.card := by
  classical
  constructor
  · intro hinj
    by_contra hn
    have small : J.card ≤ 2 := by omega
    have enough : 2 ≤ (Finset.univ : Finset A).card := by
      simpa using (show 2 ≤ A.card by omega)
    obtain ⟨K, hJK, _, hK⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ J) small enough
    obtain ⟨a,b,hab,hKab⟩ := Finset.card_eq_two.mp hK
    have hv : a.1 ≠ b.1 := fun eq => hab (Subtype.ext eq)
    obtain ⟨C,D,hC,hD,sC,sD,hCD,da,db⟩ :=
      two_deletions_insufficient hA a.2 b.2 hv
    apply counterexample_certifies_incomplete_budget J (deletionReadout A) ?_ hinj
    refine ⟨⟨C,hC,sC⟩,⟨D,hD,sD⟩,?_,?_⟩
    · intro eq
      exact hCD (congrArg Subtype.val eq)
    · funext i
      have hi : i.1 ∈ K := hJK i.2
      rw [hKab] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · simpa [jointReadout, deletionReadout, hi] using da
      · simpa [jointReadout, deletionReadout, hi] using db
  · intro hJ C D eq
    obtain ⟨T,hTJ,hT⟩ := Finset.exists_subset_card_eq hJ
    obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := Finset.card_eq_three.mp hT
    apply Subtype.ext
    apply reconstruct_three hA a.2 b.2 c.2
      (fun eq => hab (Subtype.ext eq))
      (fun eq => hac (Subtype.ext eq))
      (fun eq => hbc (Subtype.ext eq)) C.2.1 D.2.1 C.2.2 D.2.2
    · exact congrFun eq ⟨a,hTJ (by simp [hTabc])⟩
    · exact congrFun eq ⟨b,hTJ (by simp [hTabc])⟩
    · exact congrFun eq ⟨c,hTJ (by simp [hTabc])⟩

theorem minimum_iff {A : Finset α} (hA : 4 ≤ A.card) (J : Finset A) :
    IsMinimumCompleteBudget J (deletionReadout A) (fun _ => 1) ↔
      J.card = 3 := by
  classical
  have unitCost (B : Finset A) : budgetCost B (fun _ : A => 1) = B.card := by
    simp [budgetCost, observerCost]
  constructor
  · intro h
    have lower := (complete_iff hA J).mp h.1
    have enough : 3 ≤ (Finset.univ : Finset A).card := by
      simpa using (show 3 ≤ A.card by omega)
    obtain ⟨K,_,hK⟩ := Finset.exists_subset_card_eq enough
    have compK := (complete_iff hA K).mpr (by omega)
    have cost := h.2 K compK
    rw [unitCost,unitCost,hK] at cost
    omega
  · intro hJ
    apply (minimum_complete_budget_iff_minimum_cover J (deletionReadout A)
      (fun _ => 1)).mpr
    refine ⟨(finite_budget_injective_iff_cover J (deletionReadout A)).mp
      ((complete_iff hA J).mpr (by omega)), ?_⟩
    intro K cover
    have lower := (complete_iff hA K).mp
      ((finite_budget_injective_iff_cover K (deletionReadout A)).mpr cover)
    rw [unitCost,unitCost,hJ]
    exact lower

#check @complete_iff
#check @minimum_iff
#print axioms complete_iff
#print axioms minimum_iff
#check @rooted
#print axioms rooted
#check @CyclicInsertionGap.anchored_coe_injective
#print axioms CyclicInsertionGap.anchored_coe_injective
#print axioms reconstruct
#print axioms finite_budget_injective_iff_cover
#print axioms minimum_complete_budget_iff_minimum_cover
end MinimumDeletionBudgetExactCheck

/- GID: D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily
   generality: G
   mirror-B: D5/B/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-limit attachments produce an actual branch-labeled convergent MAD family. -/

import D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily

open Set Filter Topology
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open scoped Cardinal

namespace D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily

private theorem branchSet_injective : Function.Injective branchSet := by
  intro x y h
  by_contra hxy
  have hf := (branch_system 0).2.2.1 x y hxy
  rw [h, inter_self] at hf
  exact (branch_system 0).2.1 y hf

private theorem attach_same_limit (M : Set (Set Word))
    (hc : ∀ A ∈ M, ∃ r, ConvergesOn wordValue A r) :
    ∃ j : {A : Set Word // A ∈ M ∧ A ∉ range branchSet} → Branch,
      Function.Injective j ∧ ∀ A, ConvergesOn wordValue A.val (limitValue (j A)) := by
  classical
  let Extra := {A : Set Word // A ∈ M ∧ A ∉ range branchSet}
  let r : Extra → unitInterval := fun A => (hc A.val A.property.1).choose
  have hr : ∀ A : Extra, ConvergesOn wordValue A.val (r A) := fun A =>
    (hc A.val A.property.1).choose_spec
  have hcard : Cardinal.mk (Set Word) = Cardinal.continuum := by
    rw [Cardinal.mk_set, Cardinal.mk_eq_aleph0 Word, Cardinal.two_power_aleph0]
  have hle (t : unitInterval) :
      Cardinal.mk {A : Extra // r A = t} ≤ Cardinal.mk {x : Branch // limitValue x = t} := by
    rw [(branch_system 0).2.2.2.2.2.2 t]
    exact ((Cardinal.mk_subtype_le _).trans (Cardinal.mk_subtype_le _)).trans_eq hcard
  let e (t : unitInterval) : {A : Extra // r A = t} ↪ {x : Branch // limitValue x = t} :=
    Classical.choice ((Cardinal.le_def _ _).mp (hle t))
  have ec : ∀ (t t' : unitInterval) (A : Extra) (ht : r A = t) (ht' : r A = t'),
      t = t' → (e t ⟨A, ht⟩).val = (e t' ⟨A, ht'⟩).val := by
    intro t t' A ht ht' h
    cases h
    rfl
  let j : Extra → Branch := fun A => (e (r A) ⟨A, rfl⟩).val
  have hj : ∀ A : Extra, limitValue (j A) = r A := fun A =>
    (e (r A) ⟨A, rfl⟩).property
  refine ⟨j, ?_, ?_⟩
  · intro A B h
    have hAB : r A = r B := (hj A).symm.trans ((congrArg limitValue h).trans (hj B))
    have hh : e (r B) ⟨A, hAB⟩ = e (r B) ⟨B, rfl⟩ := by
      apply Subtype.ext
      change (e (r A) ⟨A, rfl⟩).val = (e (r B) ⟨B, rfl⟩).val at h
      exact (ec (r A) (r B) A rfl hAB hAB).symm.trans h
    exact congrArg Subtype.val ((e (r B)).injective hh)
  · intro A
    rw [hj A]
    exact hr A

/-- Finite unions preserve convergence to a common value. This supplier is consumed by the
branch attachment and by actual threshold-partitioner elimination. -/
theorem finite_sUnion_converges {α : Type*} (u : α → unitInterval)
    (F : Set (Set α)) (hF : F.Finite) (r : unitInterval)
    (hc : ∀ A ∈ F, ConvergesOn u A r) : ConvergesOn u (⋃₀ F) r := by
  intro V hV
  apply (hF.biUnion (fun A hA => hc A hA V hV)).subset
  rintro a ⟨ha, hv⟩
  obtain ⟨A, hA, haA⟩ := mem_sUnion.mp ha
  exact mem_iUnion.mpr ⟨A, mem_iUnion.mpr ⟨hA, haA, hv⟩⟩

/-- Every old member lies in one final member; each final member has its own original
branch, the same binary limit, and unrestricted maximal almost-disjointness. -/
private theorem word_branch_labeled_mad :
    ∃ M : Branch → Set Word,
      (∀ x, branchSet x ⊆ M x) ∧
      (∀ x y, x ≠ y → (M x ∩ M y).Finite) ∧ MADFamily (range M) ∧
      (∀ x, ConvergesOn wordValue (M x) (limitValue x)) := by
  classical
  obtain ⟨M₀, hbranch, hmad, hc⟩ := exists_convergent_mad
  obtain ⟨j, hj, hjc⟩ := attach_same_limit M₀ hc
  let Extra := {A : Set Word // A ∈ M₀ ∧ A ∉ range branchSet}
  let F : Branch → Set (Set Word) := fun x =>
    {branchSet x} ∪ {A | ∃ E : Extra, j E = x ∧ E.val = A}
  have hFM : ∀ x, F x ⊆ M₀ := by
    intro x A hA
    rcases hA with hA | ⟨E, _, rfl⟩
    · exact hbranch (hA ▸ mem_range_self x)
    · exact E.property.1
  have hFbranch : ∀ x, branchSet x ∈ F x := fun x => Or.inl rfl
  have hFfin : ∀ x, (F x).Finite := by
    intro x
    apply (finite_singleton _).union
    by_cases hex : ∃ E : Extra, j E = x
    · obtain ⟨E, hE⟩ := hex
      apply (finite_singleton E.val).subset
      rintro A ⟨E', hE', rfl⟩
      exact congrArg Subtype.val (hj (hE'.trans hE.symm))
    · have he : {A | ∃ E : Extra, j E = x ∧ E.val = A} = ∅ := by
        ext A
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨E, hE, _⟩
        exact hex ⟨E, hE⟩
      rw [he]
      exact finite_empty
  have hdisj : ∀ x y, x ≠ y → ∀ A ∈ F x, ∀ B ∈ F y, A ≠ B := by
    intro x y hxy A hA B hB hab
    rcases hA with hA | ⟨E, hE, hEA⟩ <;>
      rcases hB with hB | ⟨E', hE', hEB⟩
    · exact hxy (branchSet_injective (hA.symm.trans (hab.trans hB)))
    · exact E'.property.2 ⟨x, hA.symm.trans (hab.trans hEB.symm)⟩
    · exact E.property.2 ⟨y, hB.symm.trans (hab.symm.trans hEA.symm)⟩
    · have hee : E = E' := Subtype.ext (hEA.trans (hab.trans hEB.symm))
      exact hxy (hE.symm.trans ((congrArg j hee).trans hE'))
  let M : Branch → Set Word := fun x => ⋃₀ F x
  have hsub : ∀ x, branchSet x ⊆ M x := fun x => subset_sUnion_of_mem (hFbranch x)
  have hinf : ∀ x, (M x).Infinite := fun x => ((branch_system 0).2.1 x).mono (hsub x)
  have had : ∀ x y, x ≠ y → (M x ∩ M y).Finite := by
    intro x y hxy
    apply ((hFfin x).biUnion (fun A hA => (hFfin y).biUnion (fun B hB =>
      hmad.1.2 (hFM x hA) (hFM y hB) (hdisj x y hxy A hA B hB)))).subset
    rintro a ⟨ha, hb⟩
    obtain ⟨A, hA, haA⟩ := mem_sUnion.mp ha
    obtain ⟨B, hB, haB⟩ := mem_sUnion.mp hb
    exact mem_iUnion.mpr ⟨A, mem_iUnion.mpr ⟨hA,
      mem_iUnion.mpr ⟨B, mem_iUnion.mpr ⟨hB, haA, haB⟩⟩⟩⟩
  have hold : ∀ A ∈ M₀, ∃ x, A ⊆ M x := by
    intro A hA
    by_cases hb : A ∈ range branchSet
    · obtain ⟨x, rfl⟩ := hb
      exact ⟨x, hsub x⟩
    · let E : Extra := ⟨A, hA, hb⟩
      exact ⟨j E, subset_sUnion_of_mem (Or.inr ⟨E, rfl, rfl⟩)⟩
  refine ⟨M, hsub, had, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro A ⟨x, rfl⟩
    exact hinf x
  · rintro A ⟨x, rfl⟩ B ⟨y, rfl⟩ hxy
    exact had x y (fun h => hxy (congrArg M h))
  · intro E hE
    obtain ⟨A, hA, hi⟩ := hmad.2 E hE
    obtain ⟨x, hx⟩ := hold A hA
    exact ⟨M x, mem_range_self x, hi.mono (inter_subset_inter_right _ hx)⟩
  · intro x
    apply finite_sUnion_converges wordValue (F x) (hFfin x)
    intro A hA
    rcases hA with hA | ⟨E, hE, rfl⟩
    · rw [hA]
      exact (branch_system 0).2.2.2.1 x
    · simpa only [hE] using hjc E

noncomputable def natValue (n : ℕ) : unitInterval := wordValue (wordEquivNat.symm n)
noncomputable def natBranch (x : Branch) : Set ℕ := wordEquivNat '' branchSet x

/-- An unconditional branch-labeled convergent MAD family on actual natural numbers.
The original branch remains inside each labeled member. -/
theorem exists_branch_labeled_mad :
    ∃ M : Branch → Set ℕ,
      (∀ x, natBranch x ⊆ M x) ∧
      (∀ x y, x ≠ y → (M x ∩ M y).Finite) ∧ MADFamily (range M) ∧
      (∀ x, ConvergesOn natValue (M x) (limitValue x)) := by
  classical
  obtain ⟨F, hFbranch, hFlabeled, hFmad, hFc⟩ := word_branch_labeled_mad
  let M : Branch → Set ℕ := fun x => wordEquivNat '' F x
  have hsub : ∀ x, natBranch x ⊆ M x := fun x => image_mono (hFbranch x)
  have hinf : ∀ x, (M x).Infinite := fun x =>
    (hFmad.1.1 (F x) (mem_range_self x)).image wordEquivNat.injective.injOn
  have had : ∀ x y, x ≠ y → (M x ∩ M y).Finite := by
    intro x y hxy
    have hi := hFlabeled x y hxy
    apply (hi.image wordEquivNat).subset
    rintro n ⟨⟨a, ha, han⟩, b, hb, hbn⟩
    have hab := wordEquivNat.injective (han.trans hbn.symm)
    exact ⟨a, ⟨ha, hab ▸ hb⟩, han⟩
  refine ⟨M, hsub, had, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro A ⟨x, rfl⟩
    exact hinf x
  · rintro A ⟨x, rfl⟩ B ⟨y, rfl⟩ hxy
    exact had x y (fun h => hxy (congrArg M h))
  · intro E hE
    have hEw : (wordEquivNat.symm '' E).Infinite :=
      hE.image wordEquivNat.symm.injective.injOn
    obtain ⟨A, hA, hi⟩ := hFmad.2 _ hEw
    obtain ⟨x, rfl⟩ := hA
    refine ⟨M x, mem_range_self x, ?_⟩
    apply (hi.image wordEquivNat.injective.injOn).mono
    rintro n ⟨a, ⟨⟨k, hk, hka⟩, ha⟩, han⟩
    refine ⟨?_, ⟨a, ha, han⟩⟩
    have hkn : k = n := by rw [← hka, wordEquivNat.apply_symm_apply] at han; exact han
    exact hkn ▸ hk
  · intro x V hV
    apply ((hFc x V hV).image wordEquivNat).subset
    rintro n ⟨⟨a, ha, han⟩, hn⟩
    refine ⟨a, ⟨ha, ?_⟩, han⟩
    intro hav
    exact hn (by simpa [natValue, ← han] using hav)

end D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily

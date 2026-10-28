/- GID: D5/S3/Combinatorics/Transportation/DyadicAllocation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/DyadicAllocation
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Exact allocation of distinct dyadic coins is characterized by capacity residues. -/
module
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-! Exact labelled allocation by maximal-coin deletion and capacity residues. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Transportation.DyadicAllocation
open scoped BigOperators

/-- A partition of the actual labels, with prescribed masses. No injectivity of
its denomination function is required. -/
def Allocation {α β : Type*} [DecidableEq α] [Fintype β]
    (S : Finset α) (e : α → ℕ) (b : β → ℕ) : Prop :=
  ∃ K : β → Finset α,
    (∀ i, K i ⊆ S) ∧ (∀ i j, i ≠ j → Disjoint (K i) (K j)) ∧
    (∀ a ∈ S, ∃ i, a ∈ K i) ∧ (∀ i, ∑ a ∈ K i, 2 ^ e a = b i)

private theorem residue_bound {α : Type*} [DecidableEq α]
    (S : Finset α) (e : α → ℕ) (q : ℕ) :
    (∑ a ∈ S, 2 ^ e a) % 2 ^ q ≤ ∑ a ∈ S.filter (fun a => e a < q), 2 ^ e a := by
  have he : (∑ a ∈ S, 2 ^ e a % 2 ^ q) =
      ∑ a ∈ S.filter (fun a => e a < q), 2 ^ e a % 2 ^ q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : e a < q
    · simp [h]
    · have hd : 2 ^ q ∣ (2 : ℕ) ^ e a := pow_dvd_pow 2 (by omega)
      simp [h, Nat.mod_eq_zero_of_dvd hd]
  have hm : (∑ a ∈ S, 2 ^ e a) % 2 ^ q =
      (∑ a ∈ S.filter (fun a => e a < q), 2 ^ e a) % 2 ^ q := by
    rw [Finset.sum_nat_mod S, he, ← Finset.sum_nat_mod]
  rw [hm]
  exact Nat.mod_le _ _

/-- Deleting a maximal physical coin supplies a terminating construction,
including when some denominations or all bins are absent. -/
theorem allocation_of_residues {α β : Type*} [DecidableEq α] [Fintype β]
    (S : Finset α) (e : α → ℕ) (b : β → ℕ)
    (total : (∑ a ∈ S, 2 ^ e a) = ∑ i, b i)
    (residue : ∀ q : ℕ, (∑ i, b i % 2 ^ q) ≤
      ∑ a ∈ S.filter (fun a => e a < q), 2 ^ e a) : Allocation S e b := by
  classical
  induction S using Finset.strongInduction generalizing b with
  | H S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨a, ha, hmax⟩ := S.exists_max_image e hS
      let F := 2 ^ e a
      have hF : 0 < F := by dsimp [F]; positivity
      have herase : (∑ x ∈ S.erase a, 2 ^ e x) + F = ∑ x ∈ S, 2 ^ e x := by
        simpa [F] using Finset.sum_erase_add S (fun x => 2 ^ e x) ha
      obtain ⟨i, hi⟩ : ∃ i, F ≤ b i := by
        by_contra! h
        have heq : (∑ i, b i % F) = ∑ i, b i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Nat.mod_eq_of_lt (h i)
        have hlow : S.filter (fun x => e x < e a) ⊆ S.erase a := by
          intro x hx
          obtain ⟨hx, he⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_erase.mpr ⟨by intro h; subst x; omega, hx⟩
        have hle := Finset.sum_le_sum_of_subset (f := fun x => 2 ^ e x) hlow
        have hr := residue (e a)
        change (∑ i, b i % F) ≤ _ at hr
        rw [heq, ← total] at hr
        omega
      let b' : β → ℕ := fun j => if j = i then b j - F else b j
      have hb' : (∑ j, b' j) + F = ∑ j, b j := by
        have ht : ∀ j, b' j + (if j = i then F else 0) = b j := by
          intro j
          dsimp [b']
          split_ifs with h
          · subst j; omega
          · omega
        simpa [Finset.sum_add_distrib] using
          (Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => ht j))
      have ht' : (∑ x ∈ S.erase a, 2 ^ e x) = ∑ j, b' j := by omega
      have hr' : ∀ q : ℕ, (∑ j, b' j % 2 ^ q) ≤
          ∑ x ∈ (S.erase a).filter (fun x => e x < q), 2 ^ e x := by
        intro q
        by_cases hq : q ≤ e a
        · have hmod : ∀ j, b' j % 2 ^ q = b j % 2 ^ q := by
            intro j
            by_cases hj : j = i
            · subst j
              have hd : 2 ^ q ∣ F := pow_dvd_pow 2 hq
              have hde : b i - F + F = b i := Nat.sub_add_cancel hi
              have he := congrArg (fun n => n % 2 ^ q) hde
              rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, add_zero,
                Nat.mod_mod] at he
              simpa [b'] using he
            · simp [b', hj]
          have hfilter : (S.erase a).filter (fun x => e x < q) =
              S.filter (fun x => e x < q) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · tauto
            · rintro ⟨hx, he⟩
              exact ⟨⟨by intro h; subst x; omega, hx⟩, he⟩
          simpa only [hmod, hfilter] using residue q
        · have hf : (S.erase a).filter (fun x => e x < q) = S.erase a := by
            apply Finset.filter_true_of_mem
            intro x hx
            have := hmax x (Finset.mem_of_mem_erase hx)
            omega
          rw [hf, ht']
          apply Finset.sum_le_sum
          intro j _
          exact Nat.mod_le _ _
      obtain ⟨K, hKS, hKD, hKC, hKb⟩ :=
        ih (S.erase a) (Finset.erase_ssubset ha) b' ht' hr'
      let K' : β → Finset α := fun j => if j = i then insert a (K j) else K j
      have haK : ∀ j, a ∉ K j := fun j hj =>
        (Finset.mem_erase.mp (hKS j hj)).1 rfl
      refine ⟨K', ?_, ?_, ?_, ?_⟩
      · intro j x hx
        by_cases hj : j = i
        · simp only [K', ite_eq_left hj, Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact ha
          · exact Finset.mem_of_mem_erase (hKS j hx)
        · exact Finset.mem_of_mem_erase (hKS j (by simpa [K', hj] using hx))
      · intro j l hjl
        apply Finset.disjoint_left.mpr
        intro x hxj hxl
        by_cases hj : j = i <;> by_cases hl : l = i
        · exact hjl (hj.trans hl.symm)
        · simp only [K', ite_eq_left hj, Finset.mem_insert] at hxj
          simp only [K', ite_eq_right hl] at hxl
          rcases hxj with rfl | hxj
          · exact haK l hxl
          · exact Finset.disjoint_left.mp (hKD j l hjl) hxj hxl
        · simp only [K', ite_eq_right hj] at hxj
          simp only [K', ite_eq_left hl, Finset.mem_insert] at hxl
          rcases hxl with rfl | hxl
          · exact haK j hxj
          · exact Finset.disjoint_left.mp (hKD j l hjl) hxj hxl
        · exact Finset.disjoint_left.mp (hKD j l hjl)
            (by simpa [K', hj] using hxj) (by simpa [K', hl] using hxl)
      · intro x hx
        by_cases hxa : x = a
        · exact ⟨i, by simp [K', hxa]⟩
        · obtain ⟨j, hj⟩ := hKC x (Finset.mem_erase.mpr ⟨hxa, hx⟩)
          refine ⟨j, ?_⟩
          by_cases h : j = i
          · simp only [K', h, ite_true, Finset.mem_insert]
            exact Or.inr (by simpa [h] using hj)
          · simpa [K', h] using hj
      · intro j
        by_cases hj : j = i
        · subst j
          simp only [K', ite_eq_left rfl, Finset.sum_insert (haK i)]
          rw [hKb]
          dsimp [b']
          simp only [ite_eq_left rfl]
          change F + (b i - F) = b i
          omega
        · simpa [K', b', hj] using hKb j
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      have hz : ∀ i, b i = 0 := by
        intro i
        have := Finset.single_le_sum (fun j _ => Nat.zero_le (b j))
          (Finset.mem_univ i)
        simp only [Finset.sum_empty] at total
        omega
      exact ⟨fun _ => ∅, by simp, by simp, by simp, by simp [hz]⟩

/-- The residue obstruction is both necessary and sufficient for exact physical
allocation. Repeated values do not identify labels. -/
theorem allocation_iff_residues {α β : Type*} [DecidableEq α] [Fintype β]
    (S : Finset α) (e : α → ℕ) (b : β → ℕ)
    (total : (∑ a ∈ S, 2 ^ e a) = ∑ i, b i) :
    Allocation S e b ↔ ∀ q : ℕ, (∑ i, b i % 2 ^ q) ≤
      ∑ a ∈ S.filter (fun a => e a < q), 2 ^ e a := by
  classical
  constructor
  · rintro ⟨K, hS, hD, hC, hb⟩ q
    let L : β → Finset α := fun i => (K i).filter (fun a => e a < q)
    have hLD : Set.PairwiseDisjoint (↑(Finset.univ : Finset β)) L := by
      intro i _ j _ hij
      exact (hD i j hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hL : Finset.univ.biUnion L = S.filter (fun a => e a < q) := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_filter, L]
      constructor
      · rintro ⟨i, ha, he⟩
        exact ⟨hS i ha, he⟩
      · rintro ⟨ha, he⟩
        obtain ⟨i, hi⟩ := hC a ha
        exact ⟨i, hi, he⟩
    calc
      (∑ i, b i % 2 ^ q) ≤ ∑ i, ∑ a ∈ L i, 2 ^ e a := by
        apply Finset.sum_le_sum
        intro i _
        rw [← hb i]
        exact residue_bound (K i) e q
      _ = ∑ a ∈ S.filter (fun a => e a < q), 2 ^ e a := by
        exact (Finset.sum_biUnion hLD).symm.trans (congrArg (fun T : Finset α => ∑ a ∈ T, 2 ^ e a) hL)
  · exact allocation_of_residues S e b total

end D5.S3.Combinatorics.Transportation.DyadicAllocation

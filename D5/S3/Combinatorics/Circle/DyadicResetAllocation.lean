/- GID: D5/S3/Combinatorics/Circle/DyadicResetAllocation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/DyadicResetAllocation
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Dyadic residue allocation selects actual coins and fills coupled reset bins. -/
module
public import D5.S3.Combinatorics.Transportation.DyadicAllocation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Exact coin selection and coupled reset-bin allocation use the same criterion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.DyadicResetAllocation
open scoped BigOperators
open D5.S3.Combinatorics.Transportation.DyadicAllocation

/-- Selection of an exact power of two is a two-bin application of labelled
allocation, rather than a second selection construction. -/
theorem select_power {α : Type*} [DecidableEq α] (S : Finset α)
    (e : α → ℕ) (b : ℕ) (he : ∀ a ∈ S, e a ≤ b)
    (hmass : 2 ^ b ≤ ∑ a ∈ S, 2 ^ e a) :
    ∃ R : Finset α, R ⊆ S ∧ (∑ a ∈ R, 2 ^ e a) = 2 ^ b := by
  classical
  let T := ∑ a ∈ S, 2 ^ e a
  let cap : Fin 2 → ℕ := fun i => if i = 0 then 2 ^ b else T - 2 ^ b
  have htotal : (∑ a ∈ S, 2 ^ e a) = ∑ i, cap i := by
    simp only [Fin.sum_univ_two, cap, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      ite_false]
    dsimp [T] at *
    omega
  have hsingle : Allocation S e (fun _ : Unit => T) := by
    refine ⟨fun _ => S, by simp, ?_, ?_, by simp [T]⟩
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))
    · intro a ha; exact ⟨(), ha⟩
  have hlow := (allocation_iff_residues S e (fun _ : Unit => T)
    (by simp [T])).mp hsingle
  have hr : ∀ q : ℕ, (∑ i, cap i % 2 ^ q) ≤
      ∑ a ∈ S.filter (fun a => e a < q), 2 ^ e a := by
    intro q
    simp only [Fin.sum_univ_two, cap, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      ite_false]
    by_cases hq : q ≤ b
    · have hd : 2 ^ q ∣ (2 : ℕ) ^ b := pow_dvd_pow 2 hq
      have hsub : (T - 2 ^ b) % 2 ^ q = T % 2 ^ q := by
        have hz : T - 2 ^ b + 2 ^ b = T := Nat.sub_add_cancel hmass
        have h := congrArg (fun n => n % 2 ^ q) hz
        simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd] using h
      rw [Nat.mod_eq_zero_of_dvd hd, zero_add, hsub]
      simpa using hlow q
    · have hf : S.filter (fun a => e a < q) = S := by
        apply Finset.filter_true_of_mem
        intro a ha
        have := he a ha
        omega
      rw [hf]
      have h1 := Nat.mod_le (2 ^ b) (2 ^ q)
      have h2 := Nat.mod_le (T - 2 ^ b) (2 ^ q)
      dsimp [T] at *
      omega
  obtain ⟨K, hK, _, _, hb⟩ := allocation_of_residues S e cap htotal hr
  exact ⟨K 0, hK 0, by simpa [cap] using hb 0⟩

private theorem dyadic_pred_mod (b q : ℕ) (hq : q ≤ b) :
    (2 ^ b - 1) % 2 ^ q = 2 ^ q - 1 := by
  have hB : 0 < (2 : ℕ) ^ b := by positivity
  have hF : 0 < (2 : ℕ) ^ q := by positivity
  apply (Nat.mod_eq_sub_iff (by omega : 0 < 1) (by omega : 1 ≤ 2 ^ q)).mpr
  simpa [Nat.sub_add_cancel hB] using (pow_dvd_pow 2 hq : 2 ^ q ∣ (2 : ℕ) ^ b)

/-- A least fresh denomination supplies the extra low-scale budget. The old
reset bins supply the remaining residue bounds. Both are about the same labels. -/
theorem coupled_allocation {α : Type*} [DecidableEq α]
    (S : Finset α) (e : α → ℕ) (a : α) (b j p r g : ℕ)
    (ha : a ∉ S) (haj : e a = j) (hj : j < b) (hp : 1 ≤ p)
    (hr : p + 1 ≤ r) (hg : 0 < g) (hgs : g < 2 ^ j)
    (he : ∀ x ∈ S, e x < b)
    (hmass : (∑ x ∈ S, 2 ^ e x) + g = p * (2 ^ b - 1))
    (owned : ∀ q ≤ j, (∑ x ∈ S.filter (fun x => e x < q), 2 ^ e x) =
      r * (2 ^ q - 1))
    (oldBins : ∀ q, j < q → q ≤ b →
      p * (2 ^ q - 1) - g ≤ ∑ x ∈ S.filter (fun x => e x < q), 2 ^ e x) :
    Allocation (insert a S) e (fun i : Fin p ⊕ Unit =>
      Sum.elim (fun _ => 2 ^ b - 1) (fun _ => 2 ^ j - g) i) := by
  classical
  let cap : Fin p ⊕ Unit → ℕ := Sum.elim (fun _ => 2 ^ b - 1) (fun _ => 2 ^ j - g)
  have hB : 0 < (2 : ℕ) ^ b := by positivity
  have hs : 0 < (2 : ℕ) ^ j := by positivity
  have hcap : (∑ i, cap i) = p * (2 ^ b - 1) + (2 ^ j - g) := by
    simp [cap, Fintype.sum_sum_type]
  have htotal : (∑ x ∈ insert a S, 2 ^ e x) = ∑ i, cap i := by
    rw [Finset.sum_insert ha, haj, hcap]
    omega
  apply allocation_of_residues (insert a S) e cap htotal
  intro q
  have hF : 0 < (2 : ℕ) ^ q := by positivity
  have hres : (∑ i, cap i % 2 ^ q) =
      p * ((2 ^ b - 1) % 2 ^ q) + (2 ^ j - g) % 2 ^ q := by
    simp [cap, Fintype.sum_sum_type]
  rw [hres]
  by_cases hq : q ≤ b
  · rw [dyadic_pred_mod b q hq]
    by_cases hqj : q ≤ j
    · have hlow : (insert a S).filter (fun x => e x < q) =
          S.filter (fun x => e x < q) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hlt⟩
          · omega
          · exact ⟨hx, hlt⟩
        · tauto
      rw [hlow, owned q hqj]
      have hmod : (2 ^ j - g) % 2 ^ q ≤ 2 ^ q - 1 := by
        have := Nat.mod_lt (2 ^ j - g) hF
        omega
      have hbudget := Nat.mul_le_mul_right (2 ^ q - 1) hr
      nlinarith
    · have hlt : 2 ^ j < (2 : ℕ) ^ q :=
        pow_lt_pow_right₀ (by decide) (by omega)
      have hlow : (insert a S).filter (fun x => e x < q) =
          insert a (S.filter (fun x => e x < q)) := by
        simp [Finset.filter_insert, haj, show j < q by omega]
      rw [hlow, Finset.sum_insert (fun h => ha (Finset.mem_filter.mp h).1), haj,
        Nat.mod_eq_of_lt (by omega : 2 ^ j - g < 2 ^ q)]
      have hold := oldBins q (by omega) hq
      have hpg : g ≤ p * (2 ^ q - 1) := by
        have hx : 2 ^ q - 1 ≤ p * (2 ^ q - 1) := by nlinarith
        omega
      omega
  · have hlow : (insert a S).filter (fun x => e x < q) = insert a S := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · have := he x hx; omega
    rw [hlow]
    have h1 := Nat.mod_le (2 ^ b - 1) (2 ^ q)
    have h2 := Nat.mod_le (2 ^ j - g) (2 ^ q)
    have hmul := Nat.mul_le_mul_left p h1
    rw [htotal, hcap]
    omega


/-- Exact mass is conserved by a physical allocation. -/
theorem allocation_total {α β : Type*} [DecidableEq α] [Fintype β]
    (S : Finset α) (e : α → ℕ) (cap : β → ℕ) (hal : Allocation S e cap) :
    (∑ a ∈ S, 2 ^ e a) = ∑ i, cap i := by
  classical
  obtain ⟨K, hKS, hKD, hKC, hKb⟩ := hal
  have hD : Set.PairwiseDisjoint (↑(Finset.univ : Finset β)) K := by
    intro i _ j _ hij; exact hKD i j hij
  have hU : Finset.univ.biUnion K = S := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hKS i hi, hKC a⟩
  rw [← hU, Finset.sum_biUnion hD]
  simp_rw [hKb]

/-- Original positive bins provide every residue budget above the least fresh
SMALL denomination. This is derived from their actual physical allocation. -/
theorem old_bins_residues {α : Type*} [DecidableEq α]
    (S : Finset α) (e : α → ℕ) (b j n h g : ℕ)
    (hgap : h + g = 2 ^ (b + 1) - 1) (hgs : g < 2 ^ j)
    (hal : Allocation S e (fun i : Fin n ⊕ Unit =>
      Sum.elim (fun _ => 2 ^ (b + 1) - 1) (fun _ => h) i)) :
    ∀ q, j < q → q ≤ b →
      (n + 1) * (2 ^ q - 1) - g ≤
        ∑ x ∈ (S.filter (fun x => e x < b)).filter (fun x => e x < q), 2 ^ e x := by
  classical
  intro q hjq hqb
  have htotal := allocation_total S e _ hal
  have hr := (allocation_iff_residues S e _ htotal).mp hal q
  simp [Fintype.sum_sum_type] at hr
  rw [dyadic_pred_mod (b + 1) q (by omega)] at hr
  have hF : 0 < (2 : ℕ) ^ q := by positivity
  have hlt : g < 2 ^ q := lt_of_lt_of_le hgs
    (pow_le_pow_right₀ (by decide) (by omega))
  have hm : h % 2 ^ q = 2 ^ q - (g + 1) := by
    apply (Nat.mod_eq_sub_iff (by omega : 0 < g + 1) (by omega : g + 1 ≤ 2 ^ q)).mpr
    have hp : 0 < (2 : ℕ) ^ (b + 1) := by positivity
    have heq : h + (g + 1) = 2 ^ (b + 1) := by omega
    rw [heq]
    exact pow_dvd_pow 2 (by omega)
  rw [hm] at hr
  have hf : (S.filter (fun x => e x < b)).filter (fun x => e x < q) =
      S.filter (fun x => e x < q) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, _⟩, hq⟩; exact ⟨hx, hq⟩
    · rintro ⟨hx, hq⟩; exact ⟨⟨hx, lt_of_lt_of_le hq hqb⟩, hq⟩
  rw [hf]
  have heq : (n + 1) * (2 ^ q - 1) - g =
      n * (2 ^ q - 1) + (2 ^ q - (g + 1)) := by
    rw [Nat.add_mul, one_mul]
    omega
  rw [heq]
  exact hr

end D5.S3.Combinatorics.Circle.DyadicResetAllocation

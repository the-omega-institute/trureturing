/- GID: D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RestrictedEulerCancellation
   mirror-E: none(waiver:restricted-euler-factor-cancellation)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Glaisher]
   utility: none
   digest: Exact cancellation of distinct allowed Euler factors from restricted partition products. -/

import D5.S3.Combinatorics.Partitions.OrdinaryEulerProduct
import Mathlib.Tactic

/-! Restricted partition products are kept as actual counting series.  Cancelling
distinct allowed Euler factors leaves precisely the complementary restricted
partition product, so its coefficients remain nonnegative. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Partitions.RestrictedEulerCancellation

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def restrictedSeries (p : ℕ → Prop) : PowerSeries ℚ := by
  classical
  exact PowerSeries.mk fun n => ((Nat.Partition.restricted n p).card : ℚ)

theorem coeff_restricted_nonnegative (p : ℕ → Prop) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (restrictedSeries p) := by
  classical
  simp only [restrictedSeries, PowerSeries.coeff_mk]
  positivity

theorem restricted_constant_one (p : ℕ → Prop) :
    PowerSeries.constantCoeff (restrictedSeries p) = 1 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, restrictedSeries,
    PowerSeries.coeff_mk]
  simp [Nat.Partition.restricted]

/-- An explicit allowed multiset gives an all-index coefficient lower bound. -/
theorem coeff_restricted_ge_one_of_parts (p : ℕ → Prop) (n : ℕ)
    (l : Multiset ℕ) (hpos : ∀ m ∈ l, 0 < m) (hsum : l.sum = n)
    (hp : ∀ m ∈ l, p m) : 1 ≤ PowerSeries.coeff n (restrictedSeries p) := by
  classical
  let a : Nat.Partition n := ⟨l, fun hm => hpos _ hm, hsum⟩
  have ha : a ∈ Nat.Partition.restricted n p := by
    simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp
  have hc := Finset.card_pos.mpr ⟨a, ha⟩
  simp only [restrictedSeries, PowerSeries.coeff_mk]
  exact_mod_cast (show 1 ≤ (Nat.Partition.restricted n p).card by omega)

/-- Unrestricted parts two and three cover every degree other than one. -/
theorem coeff_restricted_ge_one_of_two_three (p : ℕ → Prop)
    (hp2 : p 2) (hp3 : p 3) (n : ℕ) (hn : n = 0 ∨ 2 ≤ n) :
    1 ≤ PowerSeries.coeff n (restrictedSeries p) := by
  rcases hn with rfl | hn
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, restricted_constant_one, le_rfl]
  by_cases he : n % 2 = 0
  · apply coeff_restricted_ge_one_of_parts p n (Multiset.replicate (n / 2) 2)
    · intro m hm
      have hm2 := (Multiset.mem_replicate.mp hm).2
      omega
    · simp only [Multiset.sum_replicate, smul_eq_mul]
      omega
    · intro m hm
      simpa only [(Multiset.mem_replicate.mp hm).2] using hp2
  · apply coeff_restricted_ge_one_of_parts p n
      (Multiset.replicate ((n - 3) / 2) 2 + {3})
    · intro m hm
      rcases Multiset.mem_add.mp hm with hm | hm
      · have hm2 := (Multiset.mem_replicate.mp hm).2
        omega
      · have hm3 := Multiset.mem_singleton.mp hm
        omega
    · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul,
        Multiset.sum_singleton]
      omega
    · intro m hm
      rcases Multiset.mem_add.mp hm with hm | hm
      · simpa only [(Multiset.mem_replicate.mp hm).2] using hp2
      · simpa only [Multiset.mem_singleton.mp hm] using hp3

/-- Only allowed parts at most the degree affect a restricted coefficient. -/
theorem coeff_restricted_congr (p q : ℕ → Prop) (n : ℕ)
    (h : ∀ m, 0 < m → m ≤ n → (p m ↔ q m)) :
    PowerSeries.coeff n (restrictedSeries p) =
      PowerSeries.coeff n (restrictedSeries q) := by
  classical
  simp only [restrictedSeries, PowerSeries.coeff_mk]
  apply congrArg (fun x : ℕ => (x : ℚ))
  apply congrArg Finset.card
  ext a
  simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro m
  apply forall_congr'
  intro hm
  exact h m (a.parts_pos hm) (Nat.Partition.le_of_mem_parts hm)

/-- Removing an allowed positive part cancels its actual geometric factor. -/
theorem restricted_mul_one_sub (p : ℕ → Prop) (m : ℕ) (hm : 0 < m) (hp : p m) :
    restrictedSeries p * (1 - PowerSeries.X ^ m) =
      restrictedSeries (fun k => p k ∧ k ≠ m) := by
  classical
  letI : TopologicalSpace ℚ := ⊥
  letI : DiscreteTopology ℚ := ⟨rfl⟩
  let f : ℕ → PowerSeries ℚ := fun i =>
    if p (i + 1) then ∑' j : ℕ, PowerSeries.X ^ ((i + 1) * j) else 1
  have hf : HasProd f (restrictedSeries p) :=
    Nat.Partition.hasProd_powerSeriesMk_card_restricted ℚ p
  have hg : HasProd (fun i => f i *
      if i = m - 1 then (1 - PowerSeries.X ^ m) else 1)
      (restrictedSeries p * (1 - PowerSeries.X ^ m)) :=
    hf.mul (hasProd_ite_eq (m - 1) (1 - PowerSeries.X ^ m))
  have hpoint (i : ℕ) :
      f i * (if i = m - 1 then (1 - PowerSeries.X ^ m) else 1) =
      if p (i + 1) ∧ i + 1 ≠ m then
        ∑' j : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ ((i + 1) * j) else 1 := by
    by_cases hi : i + 1 = m
    · have he : i = m - 1 := by omega
      rw [if_pos he]
      dsimp only [f]
      rw [hi, if_pos hp]
      simp only [ne_eq, not_true_eq_false, and_false, if_false]
      simp_rw [pow_mul]
      exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
        (by simp only [map_pow, PowerSeries.constantCoeff_X, zero_pow hm.ne'])
    · have he : i ≠ m - 1 := by omega
      simp [f, hi, he]
  simp_rw [hpoint] at hg
  apply hg.unique
  simpa only [restrictedSeries, Nat.Partition.restricted, Finset.filter_congr_decidable] using
    Nat.Partition.hasProd_powerSeriesMk_card_restricted ℚ (fun k => p k ∧ k ≠ m)

/-- All finite cancellations are simultaneous and multiplicity-free. -/
theorem restricted_mul_euler_finset (p : ℕ → Prop) (s : Finset ℕ)
    (hs : ∀ m ∈ s, 0 < m ∧ p m) :
    restrictedSeries p * (∏ m ∈ s, (1 - PowerSeries.X ^ m)) =
      restrictedSeries (fun k => p k ∧ k ∉ s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert m s hms ih =>
    have hsm : 0 < m ∧ p m := hs m (by simp)
    have hss : ∀ k ∈ s, 0 < k ∧ p k := fun k hk => hs k (by simp [hk])
    rw [Finset.prod_insert hms]
    rw [show restrictedSeries p * ((1 - PowerSeries.X ^ m) *
        ∏ x ∈ s, (1 - PowerSeries.X ^ x)) =
        (restrictedSeries p * ∏ x ∈ s, (1 - PowerSeries.X ^ x)) *
          (1 - PowerSeries.X ^ m) by ring]
    rw [ih hss, restricted_mul_one_sub (fun k => p k ∧ k ∉ s) m hsm.1 ⟨hsm.2, hms⟩]
    congr 1
    funext k
    simp only [Finset.mem_insert, not_or]
    apply propext
    tauto

/-- Euler factors can be cancelled without ever dividing a coefficient inequality. -/
theorem coeff_cancelled_product_nonnegative (p : ℕ → Prop) (s : Finset ℕ)
    (hs : ∀ m ∈ s, 0 < m ∧ p m) (n : ℕ) :
    0 ≤ PowerSeries.coeff n
      (restrictedSeries p * (∏ m ∈ s, (1 - PowerSeries.X ^ m))) := by
  rw [restricted_mul_euler_finset p s hs]
  exact coeff_restricted_nonnegative _ n

/-- A finite family of distinct allowed weights can be indexed in any type. -/
theorem restricted_mul_indexed_euler {ι : Type*}
    (p : ℕ → Prop) (s : Finset ι) (w : ι → ℕ)
    (hinj : Set.InjOn w s) (hw : ∀ i ∈ s, 0 < w i ∧ p (w i)) :
    restrictedSeries p * (∏ i ∈ s, (1 - PowerSeries.X ^ w i)) =
      restrictedSeries (fun k => p k ∧ k ∉ s.image w) := by
  classical
  have h := restricted_mul_euler_finset p (s.image w) (by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    exact hw i hi)
  rw [Finset.prod_image hinj] at h
  exact h

theorem coeff_cancelled_indexed_product_nonnegative {ι : Type*}
    (p : ℕ → Prop) (s : Finset ι) (w : ι → ℕ)
    (hinj : Set.InjOn w s) (hw : ∀ i ∈ s, 0 < w i ∧ p (w i)) (n : ℕ) :
    0 ≤ PowerSeries.coeff n
      (restrictedSeries p * (∏ i ∈ s, (1 - PowerSeries.X ^ w i))) := by
  classical
  have h := coeff_cancelled_product_nonnegative p (s.image w) (by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    exact hw i hi) n
  rw [Finset.prod_image hinj] at h
  exact h

end D5.S3.Combinatorics.Partitions.RestrictedEulerCancellation

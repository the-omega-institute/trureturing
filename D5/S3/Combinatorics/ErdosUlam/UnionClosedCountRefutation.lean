/- GID: D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation
   mirror-E: none(waiver:general-counting-refutation)
   anchors: []
   utility: none
   digest: Labelled union-closed families violate the proposed quasipolynomial counting threshold. -/

import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Finset Filter
open scoped BigOperators Topology

namespace D5.S3.Combinatorics.ErdosUlam.UnionClosedCountRefutation

noncomputable def U (n N : ℕ) : ℕ := by
  classical
  exact ((univ : Finset (Finset (Fin n))).powerset.filter fun F =>
    F.card = N ∧ ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F).card

def claim : Prop := ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ,
  (n : ℝ) ^ (C * Real.logb 2 (Real.logb 2 n)) ≤ N → U n N < 2 ^ (N - 1)

/-- The lower binomial tail is less than a quarter of the next level. -/
theorem binomial_tail_bound (r : ℕ) (hr : 1 ≤ r) :
    4 * (∑ i ∈ range r, (6 * r).choose i) < (6 * r).choose r := by
  let H := ∑ i ∈ range r, (6 * r).choose i
  let B := (6 * r).choose r
  have step : ∀ i ∈ range r,
      (5 * r + 1) * (6 * r).choose i ≤ r * (6 * r).choose (i + 1) := by
    intro i hi
    have hi' := mem_range.mp hi
    have hrec := Nat.choose_succ_right_eq (6 * r) i
    have a : 5 * r + 1 ≤ 6 * r - i := by omega
    have b : i + 1 ≤ r := by omega
    calc
      _ ≤ (6 * r - i) * (6 * r).choose i := Nat.mul_le_mul_right _ a
      _ = (i + 1) * (6 * r).choose (i + 1) := by nlinarith [hrec]
      _ ≤ r * (6 * r).choose (i + 1) := Nat.mul_le_mul_right _ b
  have hs := sum_le_sum step
  rw [← mul_sum, ← mul_sum] at hs
  have shift : (∑ i ∈ range r, (6 * r).choose (i + 1)) + 1 = H + B := by
    have h := sum_range_succ' (fun i => (6 * r).choose i) r
    rw [sum_range_succ, Nat.choose_zero_right] at h
    simpa [H, B] using h.symm
  change (5 * r + 1) * H ≤ r * (∑ i ∈ range r, (6 * r).choose (i + 1)) at hs
  have : (4 * r + 1) * H < r * B := by
    nlinarith [congrArg (fun t : ℕ => r * t) shift]
  dsimp [H, B] at *
  nlinarith

/-- Selecting one point from each block of six gives exponential level growth. -/
theorem binomial_level_growth (r : ℕ) : 6 ^ r ≤ (6 * r).choose r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hv := Nat.add_choose_eq (6 * r) 6 (r + 1)
    have ht : (6 * r).choose r * 6 ≤
        ∑ ij ∈ antidiagonal (r + 1), (6 * r).choose ij.1 * (6 : ℕ).choose ij.2 := by
      simpa using (single_le_sum (f := fun ij : ℕ × ℕ =>
        (6 * r).choose ij.1 * (6 : ℕ).choose ij.2) (fun _ _ => Nat.zero_le _)
        (show (r, 1) ∈ antidiagonal (r + 1) by simp))
    rw [← hv] at ht
    simpa [Nat.mul_add, pow_succ] using (Nat.mul_le_mul_right 6 ih).trans ht

/-- Independent four-way choices on one level produce distinct union-closed families. -/
theorem level_selection_injection (n k q : ℕ) (h : 4 * q ≤ n.choose k) :
    ∃ f : (Fin q → Fin 4) → Finset (Finset (Fin n)), Function.Injective f ∧
      ∀ x, (f x).card = (univ.filter fun A : Finset (Fin n) => k < A.card).card + q ∧
        ∀ A ∈ f x, ∀ B ∈ f x, A ∪ B ∈ f x := by
  classical
  let L := (univ : Finset (Fin n)).powersetCard k
  have hL : L.card = n.choose k := by simp [L, card_powersetCard]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin q × Fin 4) (β := {A // A ∈ L}) (by
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hL]
      omega)
  let E : Fin q → Fin 4 → Finset (Fin n) := fun t a => (e (t, a)).val
  have ec : ∀ t a, (E t a).card = k := by
    intro t a
    exact (mem_powersetCard.mp (e (t, a)).property).2
  have ei : ∀ t a u b, E t a = E u b → t = u ∧ a = b := by
    intro t a u b hab
    have he := e.injective (Subtype.ext hab)
    exact Prod.mk.inj he
  let H := univ.filter fun A : Finset (Fin n) => k < A.card
  let f := fun x : Fin q → Fin 4 => H ∪ univ.image (fun t => E t (x t))
  have memf : ∀ x A, A ∈ f x ↔ k < A.card ∨ ∃ t, E t (x t) = A := by
    intro x A
    simp [f, H]
  have hinj : Function.Injective f := by
    intro x y hxy
    funext t
    have hm : E t (x t) ∈ f y := by
      rw [← hxy, memf]
      exact Or.inr ⟨t, rfl⟩
    rcases (memf y _).mp hm with hbad | ⟨u, hu⟩
    · rw [ec] at hbad
      omega
    · obtain ⟨htu, ha⟩ := ei u (y u) t (x t) hu
      subst u
      exact ha.symm
  refine ⟨f, hinj, ?_⟩
  intro x
  constructor
  · have hd : Disjoint H (univ.image fun t => E t (x t)) := by
      apply disjoint_left.mpr
      intro A hA hB
      obtain ⟨t, _, rfl⟩ := mem_image.mp hB
      have hh := (mem_filter.mp hA).2
      rw [ec] at hh
      omega
    have hc : (univ.image fun t => E t (x t)).card = q := by
      rw [card_image_of_injective]
      · simp
      · intro t u htu
        exact (ei t (x t) u (x u) htu).1
    simpa [f, H, hc] using card_union_of_disjoint hd
  · intro A hA B hB
    have hsub : A ⊆ A ∪ B := subset_union_left
    have hcard := card_le_card hsub
    rcases (memf x A).mp hA with ha | ⟨t, rfl⟩
    · exact (memf x _).mpr (Or.inl (lt_of_lt_of_le ha hcard))
    · by_cases hh : k < (E t (x t) ∪ B).card
      · exact (memf x _).mpr (Or.inl hh)
      · have heq : E t (x t) = E t (x t) ∪ B :=
          eq_of_subset_of_card_le hsub (by rw [ec]; omega)
        rw [← heq]
        exact (memf x _).mpr (Or.inr ⟨t, rfl⟩)

/-- The injection gives the labelled counting lower bound. -/
theorem level_selection_count (n k q : ℕ) (h : 4 * q ≤ n.choose k) :
    4 ^ q ≤ U n ((univ.filter fun A : Finset (Fin n) => k < A.card).card + q) := by
  classical
  obtain ⟨f, hi, hf⟩ := level_selection_injection n k q h
  let S := ((univ : Finset (Finset (Fin n))).powerset.filter fun F =>
    F.card = (univ.filter fun A : Finset (Fin n) => k < A.card).card + q ∧
      ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
  have hm : ∀ x, f x ∈ S := by intro x; simpa [S] using hf x
  have hc := Fintype.card_le_of_injective (fun x => (⟨f x, hm x⟩ : {F // F ∈ S}))
    (fun x y hh => hi (congrArg Subtype.val hh))
  rw [Fintype.card_coe] at hc
  simpa [Fintype.card_fun, S, U] using hc

/-- Complementation identifies the upper strict tail with the lower binomial tail. -/
theorem upper_tail_card (r : ℕ) :
    (univ.filter fun A : Finset (Fin (6 * r)) => 5 * r < A.card).card =
      ∑ i ∈ range r, (6 * r).choose i := by
  classical
  let low := univ.filter fun A : Finset (Fin (6 * r)) => A.card < r
  have hc : low.card = ∑ i ∈ range r, (6 * r).choose i := by
    have hs := sum_card_fiberwise_eq_card_filter
      (univ : Finset (Finset (Fin (6 * r)))) (range r) Finset.card
    have hl : ∀ i, (univ.filter fun A : Finset (Fin (6 * r)) => A.card = i) =
        (univ : Finset (Fin (6 * r))).powersetCard i := by
      intro i; ext A; simp
    simpa [hl, low, card_powersetCard] using hs.symm
  rw [← hc]
  have he : (univ.filter fun A : Finset (Fin (6 * r)) => 5 * r < A.card) =
      low.image (fun A => Aᶜ) := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro ha
      refine ⟨Aᶜ, ?_, by simp⟩
      simp only [low, mem_filter, mem_univ, true_and, card_compl, Fintype.card_fin]
      have hn := A.card_le_univ
      simp only [Fintype.card_fin] at hn
      omega
    · rintro ⟨B, hB, rfl⟩
      have hb := (mem_filter.mp hB).2
      rw [card_compl, Fintype.card_fin]
      omega
  rw [he, card_image_of_injective]
  exact fun A B hAB => compl_injective hAB

/-- Counterexamples have an exponentially large size, with at least two choices per member. -/
theorem counting_counterexample (r : ℕ) (hr : 4 ≤ r) :
    let H := ∑ i ∈ range r, (6 * r).choose i
    let q := (6 * r).choose r / 4
    2 ^ r ≤ H + q ∧ 2 ^ (H + q) ≤ U (6 * r) (H + q) := by
  classical
  dsimp only
  let H := ∑ i ∈ range r, (6 * r).choose i
  let B := (6 * r).choose r
  let q := B / 4
  have htail : 4 * H < B := binomial_tail_bound r (by omega)
  have hq : H ≤ q := by dsimp [q]; omega
  have h4q : 4 * q ≤ B := by dsimp [q]; omega
  have hsym : (6 * r).choose (5 * r) = B := by
    simpa [B, show 6 * r - r = 5 * r by omega] using
      Nat.choose_symm (show r ≤ 6 * r by omega)
  have hcount := level_selection_count (6 * r) (5 * r) q (by omega)
  rw [upper_tail_card] at hcount
  change 4 ^ q ≤ U (6 * r) (H + q) at hcount
  have hgrowth : 6 ^ r ≤ B := binomial_level_growth r
  have hthree : 4 ≤ 3 ^ r := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) (show 2 ≤ r by omega)
    norm_num at this
    omega
  have hsmall : 4 * 2 ^ r ≤ B := calc
    _ ≤ 3 ^ r * 2 ^ r := Nat.mul_le_mul_right _ hthree
    _ = 6 ^ r := by rw [← mul_pow]; norm_num
    _ ≤ B := hgrowth
  have hpow : 2 ^ r ≤ q := by dsimp [q]; omega
  constructor
  · change 2 ^ r ≤ H + q
    omega
  · change 2 ^ (H + q) ≤ U (6 * r) (H + q)
    calc
      _ ≤ 2 ^ (2 * q) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 ^ q := by rw [pow_mul]; norm_num
      _ ≤ _ := hcount

/-- Every fixed quasipolynomial threshold is eventually below the exponential size. -/
theorem eventual_threshold (C : ℝ) :
    ∀ᶠ r : ℕ in atTop,
      ((6 * r : ℕ) : ℝ) ^ (C * Real.logb 2 (Real.logb 2 (6 * r : ℕ))) ≤
        (2 : ℝ) ^ r := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K := |C| / Real.log 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht : Tendsto (fun r : ℕ => Real.logb 2 (6 * (r : ℝ)) ^ 2 / (r : ℝ))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2)
      (1 / 6) 0 2 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 6))
    convert h using 1
    funext r
    simp only [Function.comp_apply, add_zero]
    congr 1
    ring
  have he : ∀ᶠ r : ℕ in atTop,
      K * (Real.logb 2 (6 * (r : ℝ)) ^ 2 / (r : ℝ)) < 1 :=
    (ht.const_mul K).eventually (gt_mem_nhds (by simp))
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with r he hr
  have rp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  let L := Real.logb 2 (6 * (r : ℝ))
  have rone : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have nx : (1 : ℝ) ≤ 6 * (r : ℝ) := by linarith
  have hL : 1 ≤ L := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ 6 * (r : ℝ) by linarith)
    simpa [L] using this
  have hLL : 0 ≤ Real.logb 2 L := by
    simpa using (Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1) hL)
  have hbound : Real.logb 2 L ≤ L / Real.log 2 := by
    exact (div_le_div_iff_of_pos_right hlog).mpr (Real.log_le_self (by linarith))
  have hexp : L * (C * Real.logb 2 L) ≤ (r : ℝ) := by
    have ha := le_abs_self C
    have hb := mul_le_mul_of_nonneg_left hbound (show 0 ≤ |C| * L by positivity)
    have hc := mul_le_mul_of_nonneg_right ha (show 0 ≤ L * Real.logb 2 L by positivity)
    have hd : K * L ^ 2 < (r : ℝ) := by
      have he' : K * L ^ 2 / (r : ℝ) < 1 := by simpa [L, mul_div_assoc] using he
      exact (div_lt_iff₀ rp).mp he' |>.trans_eq (one_mul _)
    calc
      L * (C * Real.logb 2 L) = C * (L * Real.logb 2 L) := by ring
      _ ≤ |C| * (L * Real.logb 2 L) := hc
      _ = |C| * L * Real.logb 2 L := by ring
      _ ≤ |C| * L * (L / Real.log 2) := hb
      _ = K * L ^ 2 := by dsimp [K]; ring
      _ ≤ r := hd.le
  have nxp : 0 < 6 * (r : ℝ) := by positivity
  have heq : (2 : ℝ) ^ L = 6 * (r : ℝ) :=
    Real.rpow_logb (by norm_num) (by norm_num) nxp
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  change (6 * (r : ℝ)) ^ (C * Real.logb 2 L) ≤ (2 : ℝ) ^ r
  calc
    _ = ((2 : ℝ) ^ L) ^ (C * Real.logb 2 L) := by rw [heq]
    _ = (2 : ℝ) ^ (L * (C * Real.logb 2 L)) := (Real.rpow_mul (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (r : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2 : ℝ) ^ r := Real.rpow_natCast _ _

theorem result : ¬ claim := by
  rintro ⟨C, n₀, hc⟩
  obtain ⟨r, hthreshold, hr⟩ := ((eventual_threshold C).and
    (eventually_ge_atTop (max 4 n₀))).exists
  have hr4 : 4 ≤ r := (le_max_left _ _).trans hr
  have hrn : n₀ ≤ 6 * r := by have := (le_max_right 4 n₀).trans hr; omega
  let N := (∑ i ∈ range r, (6 * r).choose i) + (6 * r).choose r / 4
  have hcounts := counting_counterexample r hr4
  change 2 ^ r ≤ N ∧ 2 ^ N ≤ U (6 * r) N at hcounts
  have hsize : ((6 * r : ℕ) : ℝ) ^
      (C * Real.logb 2 (Real.logb 2 (6 * r : ℕ))) ≤ (N : ℝ) :=
    hthreshold.trans (by exact_mod_cast hcounts.1)
  have bad := hc (6 * r) hrn N hsize
  have hN : 1 ≤ N := by have := Nat.one_le_pow r 2 (by norm_num); omega
  have hp : 2 ^ (N - 1) < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end D5.S3.Combinatorics.ErdosUlam.UnionClosedCountRefutation

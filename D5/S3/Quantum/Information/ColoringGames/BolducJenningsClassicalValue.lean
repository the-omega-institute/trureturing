/- GID: D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Sharp classical complete-graph coloring value at low diagonal weight. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Classical value of the complete-graph coloring game

The deterministic score reduces to diagonal agreements and ordered color collisions.
Disjoint residual color supports give two upper bounds whose greater value is attained
by a balanced synchronous table or by a balanced common block with two reserved colors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue

open Finset
open scoped BigOperators

private theorem half_product (R : ℕ) :
    4 * ((R / 2) * (R - R / 2)) + R % 2 = R ^ 2 := by
  set q := R / 2
  have hdiv : R % 2 + 2 * q = R := Nat.mod_add_div R 2
  rcases Nat.mod_two_eq_zero_or_one R with h | h
  · have hR : R = 2 * q := by omega
    have hh : R - R / 2 = q := by omega
    rw [hh, h, hR]
    ring
  · have hR : R = 2 * q + 1 := by omega
    have hh : R - R / 2 = q + 1 := by omega
    rw [hh, h, hR]
    ring

private theorem natural_endpoint (a b R : ℕ) (h : a + b < R) :
    4 * R * a * b ≤ 4 * (a + b) * ((R / 2) * (R - R / 2)) := by
  set C := a + b
  have hsq : 4 * a * b ≤ C ^ 2 := by
    have hh : (4 : ℤ) * (a : ℤ) * b ≤ ((a : ℤ) + b) ^ 2 := by
      nlinarith [sq_nonneg ((a : ℤ) - b)]
    exact_mod_cast hh
  have hC : C + 1 ≤ R := h
  have hprod := Nat.mul_le_mul_left R hC
  have hh := half_product R
  have hmod : R % 2 ≤ 1 := by omega
  have hmid : R * C ≤ 4 * ((R / 2) * (R - R / 2)) := by
    have he : R * (C + 1) = R * C + R := by ring
    rw [he] at hprod
    have hR : 1 ≤ R := by omega
    have hpow : R ^ 2 = R * R := by ring
    rw [hpow] at hh
    omega
  calc
    4 * R * a * b = R * (4 * a * b) := by ring
    _ ≤ R * C ^ 2 := Nat.mul_le_mul_left _ hsq
    _ = C * (R * C) := by ring
    _ ≤ C * (4 * ((R / 2) * (R - R / 2))) := Nat.mul_le_mul_left _ hmid
    _ = _ := by ring


/-- The balanced sum of squares for a feasible total of `s` distributed over `d` colors. -/
def B (d s : ℕ) : ℕ :=
  d * (s / d) ^ 2 + (2 * (s / d) + 1) * (s % d)

private theorem B_two (R : ℕ) :
    B 2 R = (R / 2) ^ 2 + (R - R / 2) ^ 2 := by
  have hdiv := Nat.mod_add_div R 2
  have hsum : R - R / 2 = R / 2 + R % 2 := by omega
  unfold B
  rw [hsum]
  rcases Nat.mod_two_eq_zero_or_one R with h | h <;> rw [h] <;> ring

private theorem real_endpoint (a b R : ℕ) (h : a + b < R) (lam : ℝ) :
    (lam - (R : ℝ)) * ((a : ℝ) + b) + 2 * (a : ℝ) * b ≤
      max 0 (lam * (R : ℝ) - B 2 R) := by
  have hR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hC : (a : ℝ) + b ≤ R := by exact_mod_cast h.le
  set C : ℝ := (a : ℝ) + b
  set H : ℝ := ((R / 2 : ℕ) : ℝ) * ((R - R / 2 : ℕ) : ℝ)
  have hab : 4 * (R : ℝ) * a * b ≤ 4 * C * H := by
    dsimp [C, H]
    exact_mod_cast natural_endpoint a b R h
  have hB : (B 2 R : ℝ) = (R : ℝ) ^ 2 - 2 * H := by
    have hsplit : (R / 2 : ℕ) + (R - R / 2) = R := by omega
    have hs : ((R / 2 : ℕ) : ℝ) + ((R - R / 2 : ℕ) : ℝ) = R := by
      exact_mod_cast hsplit
    rw [B_two]
    push_cast
    dsimp [H]
    nlinarith [congrArg (fun x : ℝ => x ^ 2) hs]
  have hlo : 0 ≤ C / (R : ℝ) := div_nonneg (by dsimp [C]; positivity) hR.le
  have hhi : C / (R : ℝ) ≤ 1 := (div_le_iff₀ hR).2 (by simpa using hC)
  have haux : 2 * (a : ℝ) * b ≤ C / (R : ℝ) * (2 * H) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hR]
    nlinarith only [hab]
  calc
    _ ≤ (lam - (R : ℝ)) * C + C / (R : ℝ) * (2 * H) := add_le_add_right haux _
    _ = C / (R : ℝ) * (lam * (R : ℝ) - (B 2 R : ℝ)) := by
      rw [hB]
      field_simp
      <;> ring
    _ ≤ C / (R : ℝ) * max 0 (lam * (R : ℝ) - B 2 R) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hlo
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right hhi
        (le_max_left 0 (lam * (R : ℝ) - B 2 R))

private theorem square_lower (v q : ℕ) : (2 * q + 1) * v ≤ v ^ 2 + q * (q + 1) := by
  have hh : (2 * (q : ℤ) + 1) * (v : ℤ) ≤ (v : ℤ) ^ 2 + (q : ℤ) * ((q : ℤ) + 1) := by
    have h : 0 ≤ ((v : ℤ) - q) * ((v : ℤ) - q - 1) := by
      by_cases hq : (v : ℤ) ≤ q
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact mul_nonneg (by omega) (by omega)
    nlinarith only [h]
  exact_mod_cast hh

private theorem B_le_sum_sq {α : Type*} (u : Finset α) (v : α → ℕ) :
    B u.card (∑ i ∈ u, v i) ≤ ∑ i ∈ u, v i ^ 2 := by
  set d := u.card
  set s := ∑ i ∈ u, v i
  set q := s / d
  set r := s % d
  have hsum : (2 * q + 1) * s ≤ (∑ i ∈ u, v i ^ 2) + d * (q * (q + 1)) := by
    calc
      _ = ∑ i ∈ u, (2 * q + 1) * v i := mul_sum ..
      _ ≤ ∑ i ∈ u, (v i ^ 2 + q * (q + 1)) :=
        sum_le_sum fun i _ => square_lower (v i) q
      _ = _ := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        rfl
  have hdiv : s = d * q + r := by
    exact (Nat.mod_add_div s d).symm.trans (Nat.add_comm _ _)
  have hcalc : (2 * q + 1) * s = B d s + d * (q * (q + 1)) := by
    change (2 * q + 1) * s = d * q ^ 2 + (2 * q + 1) * r + d * (q * (q + 1))
    calc
      _ = (2 * q + 1) * (d * q + r) := congrArg _ hdiv
      _ = _ := by ring
  omega

private def balanced (d s : ℕ) (i : Fin d) : ℕ :=
  s / d + if (i : ℕ) < s % d then 1 else 0

private theorem balanced_totals (d s : ℕ) (h : 0 < d ∨ s = 0) :
    (∑ i, balanced d s i) = s ∧ (∑ i, balanced d s i ^ 2) = B d s := by
  rcases eq_or_ne d 0 with rfl | hd
  · have hs : s = 0 := h.resolve_left (by omega)
    subst s
    simp [B]
  have hr : s % d < d := Nat.mod_lt _ (Nat.pos_of_ne_zero hd)
  have hc : (∑ i : Fin d, if (i : ℕ) < s % d then (1 : ℕ) else 0) = s % d := by
    rw [← sum_filter]
    simp [Fin.card_filter_val_lt, Nat.min_eq_right hr.le]
  constructor
  · simp only [balanced, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      hc]
    exact (Nat.add_comm _ _).trans (Nat.mod_add_div _ _)
  · have hterm (i : Fin d) :
        balanced d s i ^ 2 =
          (s / d) ^ 2 + (2 * (s / d) + 1) * (if (i : ℕ) < s % d then 1 else 0) := by
      simp only [balanced]
      split <;> ring
    simp only [hterm, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_sum, hc, B, Nat.cast_id]

private theorem B_succ (d s : ℕ) (hd : 0 < d) :
    B d (s + 1) = B d s + (2 * (s / d) + 1) := by
  have hr := Nat.mod_lt s hd
  by_cases h : s % d + 1 < d
  · have hmod : (s + 1) % d = s % d + 1 := by
      rw [← Nat.mod_add_mod s d 1, Nat.mod_eq_of_lt h]
    have hq : (s + 1) / d = s / d :=
      Nat.succ_div_of_mod_ne_zero (by rw [hmod]; omega)
    simp only [B, hq, hmod]
    ring
  · have hh : s % d + 1 = d := by omega
    have hmod : (s + 1) % d = 0 := by
      rw [← Nat.mod_add_mod s d 1, hh, Nat.mod_self]
    have hq : (s + 1) / d = s / d + 1 := Nat.succ_div_of_mod_eq_zero hmod
    simp only [B, hq, hmod, mul_zero, add_zero]
    calc
      _ = d * (s / d) ^ 2 + (2 * (s / d) + 1) * d := by ring
      _ = d * (s / d) ^ 2 + (2 * (s / d) + 1) * (s % d + 1) :=
        congrArg (fun z => d * (s / d) ^ 2 + (2 * (s / d) + 1) * z) hh.symm
      _ = _ := by ring

/-- Size of the balanced common block for the strategy with two reserved colors. -/
noncomputable def commonSize (n d : ℕ) (t : ℝ) : ℕ :=
  min n (d * ⌈t / 2⌉₊)

private noncomputable def balanceScore (d s : ℕ) (lam : ℝ) : ℝ :=
  lam * (s : ℝ) - B d s

private theorem score_succ (d s : ℕ) (hd : 0 < d) (t : ℝ) :
    balanceScore d (s + 1) (1 + t) - balanceScore d s (1 + t) =
      t - 2 * ((s / d : ℕ) : ℝ) := by
  unfold balanceScore
  rw [B_succ d s hd]
  push_cast
  ring

private theorem balanceScore_max (n d s : ℕ) (h : s ≤ n)
    (hfeas : 0 < d ∨ s = 0) (t : ℝ) :
    balanceScore d s (1 + t) ≤ balanceScore d (commonSize n d t) (1 + t) := by
  rcases eq_or_ne d 0 with rfl | hd
  · obtain rfl := hfeas.resolve_left (by omega)
    simp [commonSize]
  have hd' := Nat.pos_of_ne_zero hd
  set L := d * ⌈t / 2⌉₊
  set target := commonSize n d t
  have htarget : target = min n L := rfl
  have hup : ∀ j < target, balanceScore d j (1 + t) ≤ balanceScore d (j + 1) (1 + t) := by
    intro j hj
    have hjL : j < L := hj.trans_le (htarget ▸ min_le_right _ _)
    have hdiv : j / d < ⌈t / 2⌉₊ := by
      apply Nat.lt_of_not_ge
      intro hh
      have hmul := (Nat.le_div_iff_mul_le hd').mp hh
      rw [Nat.mul_comm] at hmul
      exact (not_le_of_gt hjL) hmul
    have hreal := Nat.lt_ceil.mp hdiv
    linarith [score_succ d j hd' t]
  have hdown : ∀ j, target ≤ j → j < n →
      balanceScore d (j + 1) (1 + t) ≤ balanceScore d j (1 + t) := by
    intro j hj hjn
    have hLj : L ≤ j := (min_le_iff.mp (htarget ▸ hj)).resolve_left hjn.not_ge
    have hdiv : ⌈t / 2⌉₊ ≤ j / d :=
      (Nat.le_div_iff_mul_le hd').mpr (by simpa [L, Nat.mul_comm] using hLj)
    have hreal := Nat.ceil_le.mp hdiv
    linarith [score_succ d j hd' t]
  rcases le_total s target with hs | hs
  · have hchain : ∀ j, s ≤ j → j ≤ target →
        balanceScore d s (1 + t) ≤ balanceScore d j (1 + t) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ j _ ih =>
        intro hjt
        exact (ih (by omega)).trans (hup j (by omega))
    exact hchain target hs le_rfl
  · have hchain : ∀ j, target ≤ j → j ≤ n →
        balanceScore d j (1 + t) ≤ balanceScore d target (1 + t) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ j hj ih =>
        intro hjn
        exact (hdown j hj (by omega)).trans (ih (by omega))
    exact hchain s hs h

private theorem sum_without_two {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (f : Fin m → ℕ) :
    (∑ x ∈ ((univ : Finset (Fin m)).erase i).erase j, f x) + f j + f i = ∑ x, f x := by
  have hj : j ∈ (univ : Finset (Fin m)).erase i := by simp [Ne.symm hij]
  rw [sum_erase_add _ _ hj, sum_erase_add _ _ (mem_univ i)]

private theorem min_support {m : ℕ} (c r : Fin m → ℕ) (hr : 0 < ∑ x, r x) :
    ∃ i, 0 < r i ∧ c i * (∑ x, r x) ≤ ∑ x, c x * r x := by
  classical
  let u := (univ : Finset (Fin m)).filter (fun x => 0 < r x)
  have hu : u.Nonempty := by
    by_contra hn
    have hz : ∀ x, r x = 0 := by
      intro x
      by_contra hx
      exact hn ⟨x, mem_filter.mpr ⟨mem_univ _, Nat.pos_of_ne_zero hx⟩⟩
    simp [hz] at hr
  obtain ⟨i, hi, hmin⟩ := exists_min_image u c hu
  refine ⟨i, (mem_filter.mp hi).2, ?_⟩
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  by_cases hx : 0 < r x
  · exact Nat.mul_le_mul_right _ (hmin x (mem_filter.mpr ⟨mem_univ _, hx⟩))
  · simp [show r x = 0 by omega]

private theorem residual_upper {n m ξ : ℕ} (hm : 2 ≤ m)
    (A B' : Fin m → ℕ) (ha : ∑ i, A i = n) (hb : ∑ i, B' i = n)
    (hξ : ξ ≤ ∑ i, min (A i) (B' i))
    (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) * (ξ : ℝ) - (↑(∑ i, A i * B' i) : ℝ) ≤
      max (balanceScore m n (1 + t))
        (balanceScore (m - 2) (commonSize n (m - 2) t) (1 + t)) := by
  let c : Fin m → ℕ := fun i => min (A i) (B' i)
  let r : Fin m → ℕ := fun i => A i - c i
  let u : Fin m → ℕ := fun i => B' i - c i
  set k := n - ∑ i, c i
  have hA (i : Fin m) : c i + r i = A i :=
    Nat.add_sub_of_le (min_le_left _ _)
  have hB (i : Fin m) : c i + u i = B' i :=
    Nat.add_sub_of_le (min_le_right _ _)
  have ha' : (∑ i, c i) + (∑ i, r i) = n := by
    simpa only [← sum_add_distrib, hA] using ha
  have hb' : (∑ i, c i) + (∑ i, u i) = n := by
    simpa only [← sum_add_distrib, hB] using hb
  have hkr : ∑ i, r i = k := by omega
  have hku : ∑ i, u i = k := by omega
  have hdisj (i : Fin m) : r i = 0 ∨ u i = 0 := by
    rcases le_total (A i) (B' i) with h | h
    · exact Or.inl (by simp [r, c, min_eq_left h])
    · exact Or.inr (by simp [u, c, min_eq_right h])
  have hdot :
      (∑ i, A i * B' i) =
        (∑ i, c i ^ 2) + (∑ i, c i * r i) + (∑ i, c i * u i) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by
      rw [← hA i, ← hB i]
      rcases hdisj i with h | h <;> rw [h] <;> ring
  set lam := 1 + t
  have hlam : 0 ≤ lam := by dsimp [lam]; linarith
  have hxreal : (ξ : ℝ) ≤ (↑(∑ i, c i) : ℝ) := by exact_mod_cast hξ
  have hagree := mul_le_mul_of_nonneg_left hxreal hlam
  by_cases hk : k = 0
  · have hcn : ∑ i, c i = n := by omega
    have hbal : B m n ≤ ∑ i, c i ^ 2 := by
      simpa only [card_univ, Fintype.card_fin, hcn] using B_le_sum_sq univ c
    have hμ : B m n ≤ ∑ i, A i * B' i := by rw [hdot]; omega
    have hμreal : (B m n : ℝ) ≤ (↑(∑ i, A i * B' i) : ℝ) := by exact_mod_cast hμ
    rw [hcn] at hagree
    exact (sub_le_sub hagree hμreal).trans (le_max_left _ _)
  have hpos : 0 < k := Nat.pos_of_ne_zero hk
  obtain ⟨i, hi, hir⟩ := min_support c r (hkr ▸ hpos)
  obtain ⟨j, hj, hju⟩ := min_support c u (hku ▸ hpos)
  rw [hkr] at hir
  rw [hku] at hju
  have hij : i ≠ j := by
    rintro rfl
    rcases hdisj i with h | h <;> omega
  set other := ((univ : Finset (Fin m)).erase i).erase j
  set S := ∑ x ∈ other, c x
  set E := ∑ x ∈ other, c x ^ 2
  set a := c i
  set b := c j
  set R := n - S
  have hS : S + b + a = ∑ x, c x := sum_without_two hij c
  have hE : E + b ^ 2 + a ^ 2 = ∑ x, c x ^ 2 :=
    sum_without_two hij (fun x => c x ^ 2)
  have hcard : other.card = m - 2 := by
    simp [other, card_erase_of_mem, Ne.symm hij]
    <;> omega
  have hR : R = a + b + k := by omega
  have hRS : S + R = n := by omega
  have habR : a + b < R := by omega
  have hSn : S ≤ n := by omega
  have hfeas : 0 < m - 2 ∨ S = 0 := by
    by_cases hn : 0 < m - 2
    · exact Or.inl hn
    · have hzero : other = ∅ := card_eq_zero.mp (by omega)
      exact Or.inr (by simp [S, hzero])
  have hsmall : B (m - 2) S ≤ E := by
    rw [← hcard]
    exact B_le_sum_sq other c
  have hlarge : B m n ≤ E + B 2 R := by
    let v (x : Fin m) : ℕ :=
      if x = i then R / 2 else if x = j then R - R / 2 else c x
    have hvi : v i = R / 2 := by simp [v]
    have hvj : v j = R - R / 2 := by simp [v, Ne.symm hij]
    have hv (x : Fin m) (hx : x ∈ other) : v x = c x := by
      have hn := mem_erase.mp hx
      simp [v, hn.1, (mem_erase.mp hn.2).1]
    have hs' : (∑ x ∈ other, v x) = S := sum_congr rfl hv
    have he' : (∑ x ∈ other, v x ^ 2) = E := sum_congr rfl fun x hx => by rw [hv x hx]
    have hvs := sum_without_two hij v
    change (∑ x ∈ other, v x) + v j + v i = ∑ x, v x at hvs
    rw [hs', hvi, hvj] at hvs
    have hve := sum_without_two hij (fun x => v x ^ 2)
    change (∑ x ∈ other, v x ^ 2) + v j ^ 2 + v i ^ 2 = ∑ x, v x ^ 2 at hve
    rw [he', hvi, hvj] at hve
    have hvn : (∑ x, v x) = n := by omega
    have h := B_le_sum_sq univ v
    simp only [card_univ, Fintype.card_fin, hvn, ← hve, B_two]
      at h ⊢
    omega
  have hμ : E + b ^ 2 + a ^ 2 + a * k + b * k ≤ ∑ i, A i * B' i := by
    rw [hdot, ← hE]
    exact Nat.add_le_add (Nat.add_le_add_left hir _) hju
  have hμreal : (E : ℝ) + (b : ℝ) ^ 2 + (a : ℝ) ^ 2 + (a : ℝ) * k + (b : ℝ) * k ≤
      (↑(∑ i, A i * B' i) : ℝ) := by exact_mod_cast hμ
  have hSreal : (S : ℝ) + b + a = (↑(∑ x, c x) : ℝ) := by exact_mod_cast hS
  have hRreal : (R : ℝ) = (a : ℝ) + b + k := by exact_mod_cast hR
  have hRSreal : (S : ℝ) + R = n := by exact_mod_cast hRS
  have hsmallReal : (B (m - 2) S : ℝ) ≤ E := by exact_mod_cast hsmall
  have hlargeReal : (B m n : ℝ) ≤ (E : ℝ) + (B 2 R : ℝ) := by exact_mod_cast hlarge
  have hend := real_endpoint a b R habR lam
  have hzero : lam * S - E ≤ balanceScore (m - 2) (commonSize n (m - 2) t) lam :=
    (sub_le_sub_left hsmallReal _).trans (balanceScore_max n (m - 2) S hSn hfeas t)
  have hfull : lam * S - E + (lam * R - (B 2 R : ℝ)) ≤ balanceScore m n lam := by
    unfold balanceScore
    rw [← hRSreal]
    linarith only [hlargeReal]
  calc
    _ ≤ lam * (S : ℝ) - E + ((lam - R) * ((a : ℝ) + b) + 2 * (a : ℝ) * b) := by
      rw [← hSreal] at hagree
      rw [hRreal]
      nlinarith only [hagree, hμreal]
    _ ≤ lam * (S : ℝ) - E + max 0 (lam * R - B 2 R) := add_le_add_right hend _
    _ ≤ _ := by
      rw [add_max, add_zero]
      exact max_le (hzero.trans (le_max_right _ _)) (hfull.trans (le_max_left _ _))

/-- A deterministic strategy specifies one local response table for each player. -/
abbrev Strategy (n m : ℕ) := (Fin n → Fin m) × (Fin n → Fin m)

/-- Each ordered input pair receives its diagonal or off-diagonal probability. -/
noncomputable def inputWeight {n : ℕ} (p : ℝ) (xy : Fin n × Fin n) : ℝ :=
  if xy.1 = xy.2 then p / (n : ℝ) else (1 - p) / ((n : ℝ) * ((n : ℝ) - 1))

/-- The winning probability summed over ordered input pairs. -/
noncomputable def detWin {n m : ℕ} (p : ℝ) (σ : Strategy n m) : ℝ :=
  ∑ xy : Fin n × Fin n,
    if (xy.1 = xy.2 ↔ σ.1 xy.1 = σ.2 xy.2) then inputWeight p xy else 0

/-- A distribution over pairs of response tables, drawn independently of the referee's input. -/
noncomputable def mixedWin {n m : ℕ} (p : ℝ)
    (w : Convexity.StdSimplex ℝ (Strategy n m)) : ℝ :=
  ∑ σ, w.weights σ * detWin p σ

private def count {n m : ℕ} (f : Fin n → Fin m) (i : Fin m) : ℕ :=
  (univ.filter fun x => f x = i).card

private def agreements {n m : ℕ} (σ : Strategy n m) : ℕ :=
  (univ.filter fun x => σ.1 x = σ.2 x).card

private def collisions {n m : ℕ} (σ : Strategy n m) : ℕ :=
  (univ.filter fun xy : Fin n × Fin n => σ.1 xy.1 = σ.2 xy.2).card

private theorem count_total {n m : ℕ} (f : Fin n → Fin m) : ∑ i, count f i = n := by
  simpa [count] using
    (card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := f) (fun _ _ => mem_univ _)).symm

private theorem agreements_le_overlap {n m : ℕ} (σ : Strategy n m) :
    agreements σ ≤ ∑ i, min (count σ.1 i) (count σ.2 i) := by
  let s := univ.filter fun x => σ.1 x = σ.2 x
  have h := card_eq_sum_card_fiberwise (s := s) (t := univ) (f := σ.1)
    (fun _ _ => mem_univ _)
  change s.card ≤ _
  rw [h]
  apply sum_le_sum
  intro i _
  apply le_min
  · exact card_le_card (fun x hx => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩)
  · apply card_le_card
    intro x hx
    have hh := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hh.1).2).symm.trans hh.2⟩

private theorem collisions_eq {n m : ℕ} (σ : Strategy n m) :
    collisions σ = ∑ i, count σ.1 i * count σ.2 i := by
  let s := univ.filter fun xy : Fin n × Fin n => σ.1 xy.1 = σ.2 xy.2
  have h := card_eq_sum_card_fiberwise (s := s) (t := univ) (f := fun xy => σ.1 xy.1)
    (fun _ _ => mem_univ _)
  change s.card = _
  rw [h]
  refine sum_congr rfl fun i _ => ?_
  rw [count, count, ← card_product]
  congr 1
  ext xy
  simp only [s, mem_filter, mem_univ, true_and, mem_product]
  exact ⟨fun h => ⟨h.2, h.1.symm.trans h.2⟩, fun h => ⟨h.1.trans h.2.symm, h.1⟩⟩

private theorem diagonal_count {n : ℕ} (F : Fin n → Prop) [DecidablePred F] :
    (univ.filter fun xy : Fin n × Fin n => xy.1 = xy.2 ∧ F xy.1).card =
      (univ.filter F).card := by
  rw [← filter_filter, ← univ_product_univ, ← diag_eq_filter, diag, filter_map, card_map]
  rfl

private theorem diagonal_agreements {n m : ℕ} (σ : Strategy n m) :
    (univ.filter fun xy : Fin n × Fin n => xy.1 = xy.2 ∧ σ.1 xy.1 = σ.2 xy.2).card =
      agreements σ := by
  have h : (univ.filter fun xy : Fin n × Fin n => xy.1 = xy.2 ∧ σ.1 xy.1 = σ.2 xy.2) =
      univ.filter (fun xy => xy.1 = xy.2 ∧ σ.1 xy.1 = σ.2 xy.1) := by
    ext xy
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hD, hK⟩
      exact ⟨hD, hD.symm ▸ hK⟩
    · rintro ⟨hD, hK⟩
      exact ⟨hD, hD ▸ hK⟩
  rw [h]
  exact diagonal_count (fun x => σ.1 x = σ.2 x)

private def offWins {n m : ℕ} (σ : Strategy n m) : ℕ :=
  (univ.filter fun xy : Fin n × Fin n => xy.1 ≠ xy.2 ∧ σ.1 xy.1 ≠ σ.2 xy.2).card

private theorem off_count (n : ℕ) :
    (univ.filter fun xy : Fin n × Fin n => xy.1 ≠ xy.2).card = n * (n - 1) := by
  rw [filter_not, ← univ_product_univ, ← diag_eq_filter, product_sdiff_diag,
    offDiag_card, card_univ, Fintype.card_fin, Nat.mul_sub, Nat.mul_one]

private theorem offWins_add_collisions {n m : ℕ} (σ : Strategy n m) :
    offWins σ + collisions σ = n * (n - 1) + agreements σ := by
  let D (xy : Fin n × Fin n) := xy.1 = xy.2
  let K (xy : Fin n × Fin n) := σ.1 xy.1 = σ.2 xy.2
  let off := univ.filter fun xy => ¬ D xy
  let col := univ.filter K
  have hcol := card_filter_add_card_filter_not (s := col) D
  have hoff := card_filter_add_card_filter_not (s := off) K
  have hdc : (col.filter D).card = agreements σ := by
    simpa only [col, filter_filter, D, K, and_comm] using diagonal_agreements σ
  have hsame : off.filter K = col.filter (fun xy => ¬ D xy) := by
    ext xy
    simp [off, col, and_comm]
  change offWins σ + col.card = n * (n - 1) + agreements σ
  have hwin : (off.filter fun xy => ¬ K xy).card = offWins σ := by
    simp only [off, filter_filter, offWins, D, K]
  rw [hsame, hwin, off_count n] at hoff
  rw [hdc] at hcol
  omega

/-- The parameter in the affine rescaling of the winning probability. -/
noncomputable def tParam (n : ℕ) (p : ℝ) : ℝ := p * ((n : ℝ) - 1) / (1 - p)

private noncomputable def offWeight (n : ℕ) (p : ℝ) : ℝ :=
  (1 - p) / ((n : ℝ) * ((n : ℝ) - 1))

/-- Affine transformation from the rescaled score to winning probability. -/
noncomputable def probability (n : ℕ) (p score : ℝ) : ℝ := 1 - p + offWeight n p * score

/-- The affine-rescaled score of a deterministic response-table pair. -/
noncomputable def detScore {n m : ℕ} (t : ℝ) (σ : Strategy n m) : ℝ :=
  (1 + t) * (agreements σ : ℝ) - collisions σ

private theorem inputWeight_total {n : ℕ} (hn : 1 < n) (p : ℝ) :
    ∑ xy : Fin n × Fin n, inputWeight p xy = 1 := by
  have hnℝ : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdiag : (univ.filter fun xy : Fin n × Fin n => xy.1 = xy.2).card = n := by
    rw [← univ_product_univ, ← diag_eq_filter, diag_card, card_univ, Fintype.card_fin]
  unfold inputWeight
  rw [sum_ite, sum_const, sum_const, hdiag, off_count n]
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  field_simp
  ring

private theorem detWin_eq {n m : ℕ} (hn : 1 < n) (p : ℝ) (hp : p < 1)
    (σ : Strategy n m) :
    detWin p σ = probability n p (detScore (tParam n p) σ) := by
  have hnℝ : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum :
      detWin p σ =
        (agreements σ : ℝ) * (p / (n : ℝ)) + (offWins σ : ℝ) * offWeight n p := by
    unfold detWin
    calc
      _ = ∑ xy : Fin n × Fin n,
        ((if xy.1 = xy.2 ∧ σ.1 xy.1 = σ.2 xy.2 then p / (n : ℝ) else 0) +
         (if xy.1 ≠ xy.2 ∧ σ.1 xy.1 ≠ σ.2 xy.2 then offWeight n p else 0)) := by
        refine sum_congr rfl fun xy _ => ?_
        by_cases hd : xy.1 = xy.2 <;> by_cases hc : σ.1 xy.1 = σ.2 xy.2 <;>
          simp [inputWeight, offWeight, hd, hc]
      _ = _ := by
        simp only [sum_add_distrib, sum_ite, sum_const, nsmul_eq_mul, mul_zero, add_zero,
          diagonal_agreements, offWins]
  have hcount : (offWins σ : ℝ) + (collisions σ : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) + (agreements σ : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) (offWins_add_collisions σ)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
      using h
  have hweight : offWeight n p * ((n : ℝ) * ((n : ℝ) - 1)) = 1 - p := by
    unfold offWeight
    field_simp
  have hdiag : offWeight n p * tParam n p = p / (n : ℝ) := by
    unfold offWeight tParam
    field_simp
  rw [hsum, probability, detScore, ← hdiag, ← hweight]
  have heq : (offWins σ : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) + (agreements σ : ℝ) - (collisions σ : ℝ) :=
    eq_sub_of_add_eq hcount
  rw [heq]
  ring

private theorem exists_balanced_table (d s : ℕ) (h : 0 < d ∨ s = 0) :
    ∃ f : Fin s → Fin d, (∑ i, count f i ^ 2) = B d s := by
  classical
  have ht := balanced_totals d s h
  have hcard : Fintype.card (Fin s) = Fintype.card (Σ i : Fin d, Fin (balanced d s i)) := by
    simp [ht.1]
  let e : Fin s ≃ (Σ i : Fin d, Fin (balanced d s i)) := Fintype.equivOfCardEq hcard
  let f (x : Fin s) : Fin d := (e x).1
  have hf (i : Fin d) : count f i = balanced d s i := by
    let ei : {x : Fin s // f x = i} ≃ {y : (Σ j : Fin d, Fin (balanced d s j)) // y.1 = i} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have he := Fintype.card_congr (ei.trans (Equiv.sigmaSubtype i))
    simpa [count, Fintype.card_subtype] using he
  exact ⟨f, by simpa only [hf] using ht.2⟩

private theorem sync_attains (n m : ℕ) (hm : 0 < m) (t : ℝ) :
    ∃ σ : Strategy n m, detScore t σ = balanceScore m n (1 + t) := by
  obtain ⟨f, hf⟩ := exists_balanced_table m n (Or.inl hm)
  refine ⟨(f, f), ?_⟩
  have ha : agreements (f, f) = n := by simp [agreements]
  have hcol : collisions (f, f) = B m n := by
    simpa only [collisions_eq, pow_two] using hf
  simp [detScore, balanceScore, ha, hcol]

private theorem common_attains {n m s : ℕ} (hm : 2 ≤ m) (hs : s ≤ n)
    (hf : 0 < m - 2 ∨ s = 0) (t : ℝ) :
    ∃ σ : Strategy n m, detScore t σ = balanceScore (m - 2) s (1 + t) := by
  obtain ⟨f, hf⟩ := exists_balanced_table (m - 2) s hf
  let c₀ : Fin m := ⟨0, by omega⟩
  let c₁ : Fin m := ⟨1, by omega⟩
  let shift (i : Fin (m - 2)) : Fin m := ⟨i.val + 2, by have := i.isLt; omega⟩
  have hshift : Function.Injective shift := by
    intro x y h
    have hh := congrArg Fin.val h
    apply Fin.ext
    change x.val + 2 = y.val + 2 at hh
    omega
  have h₀ (i : Fin (m - 2)) : shift i ≠ c₀ := by
    intro h
    have hh := congrArg Fin.val h
    change i.val + 2 = 0 at hh
    omega
  have h₁ (i : Fin (m - 2)) : shift i ≠ c₁ := by
    intro h
    have hh := congrArg Fin.val h
    change i.val + 2 = 1 at hh
    omega
  have h₀₁ : c₀ ≠ c₁ := by
    intro h
    have hh := congrArg Fin.val h
    change 0 = 1 at hh
    omega
  let A (x : Fin n) : Fin m := if h : x.val < s then shift (f ⟨x.val, h⟩) else c₀
  let C (x : Fin n) : Fin m := if h : x.val < s then shift (f ⟨x.val, h⟩) else c₁
  have h₀symm (i : Fin (m - 2)) : c₀ ≠ shift i := (h₀ i).symm
  have hmatch (x y : Fin n) :
      A x = C y ↔ ∃ (hx : x.val < s) (hy : y.val < s), f ⟨x.val, hx⟩ = f ⟨y.val, hy⟩ := by
    by_cases hx : x.val < s <;> by_cases hy : y.val < s <;>
      simp [A, C, hx, hy, h₀symm, h₁, h₀₁, hshift.eq_iff]
  have ha : agreements (A, C) = s := by
    have hfil : (univ.filter fun x : Fin n => A x = C x) =
        univ.filter fun x : Fin n => x.val < s := by
      ext x
      simp [hmatch]
    simp [agreements, hfil, Fin.card_filter_val_lt, Nat.min_eq_right hs]
  have hcol : collisions (A, C) = collisions (f, f) := by
    symm
    unfold collisions
    refine card_nbij (fun xy : Fin s × Fin s => (Fin.castLE hs xy.1, Fin.castLE hs xy.2))
      ?_ ?_ ?_
    · intro xy hxy
      have he := (mem_filter.mp hxy).2
      exact mem_filter.mpr ⟨mem_univ _, (hmatch _ _).mpr ⟨xy.1.isLt, xy.2.isLt, he⟩⟩
    · intro xy _ zw _ h
      exact Prod.ext (Fin.castLE_injective hs (congrArg Prod.fst h))
        (Fin.castLE_injective hs (congrArg Prod.snd h))
    · intro xy hxy
      obtain ⟨hx, hy, hxy'⟩ := (hmatch _ _).mp (mem_filter.mp hxy).2
      refine ⟨(⟨xy.1.val, hx⟩, ⟨xy.2.val, hy⟩), mem_filter.mpr ⟨mem_univ _, hxy'⟩, ?_⟩
      exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
  have hcol' : collisions (f, f) = B (m - 2) s := by
    simpa only [collisions_eq, pow_two] using hf
  exact ⟨(A, C), by simp [detScore, balanceScore, ha, hcol, hcol']⟩

/-- The winning probability of a point mass equals the deterministic winning probability. -/
private theorem mixedWin_single {n m : ℕ} (p : ℝ) (σ : Strategy n m) :
    mixedWin p (Convexity.StdSimplex.single σ) = detWin p σ := by
  classical
  unfold mixedWin
  rw [sum_eq_single σ]
  · simp
  · intro a _ ha
    simp [Finsupp.single_eq_of_ne ha]
  · simp

/-- The greatest classical winning probability on the low-diagonal interval, with both
deterministic scores attained and the ordered referee distribution normalized. -/
theorem result (n m : ℕ) (p : ℝ) (hm : 2 ≤ m) (hmn : m < n)
    (hp : 0 < p) (hlo : p < (2 : ℝ) / ((m : ℝ) + 2)) :
    let t := tParam n p
    let lam := 1 + t
    let d := m - 2
    let s := commonSize n d t
    let score₁ := lam * (n : ℝ) - (B m n : ℝ)
    let score₂ := lam * (s : ℝ) - (B d s : ℝ)
    IsGreatest (Set.range (mixedWin (n := n) (m := m) p))
      (probability n p (max score₁ score₂)) ∧
    (∃ σ τ : Strategy n m, detScore t σ = score₁ ∧ detScore t τ = score₂) ∧
    (∑ xy : Fin n × Fin n, inputWeight p xy) = 1 := by
  classical
  dsimp only
  set t := tParam n p
  set s := commonSize n (m - 2) t
  set score₁ := balanceScore m n (1 + t)
  set score₂ := balanceScore (m - 2) s (1 + t)
  change IsGreatest _ (probability n p (max score₁ score₂)) ∧
    (∃ σ τ : Strategy n m, detScore t σ = score₁ ∧ detScore t τ = score₂) ∧ _
  have hn : 1 < n := by omega
  have hnℝ : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmℝ : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp' : p < 1 := hlo.trans_le ((div_le_iff₀ (by linarith : (0 : ℝ) < m + 2)).2
    (by linarith))
  have hw : 0 ≤ offWeight n p := by
    unfold offWeight
    positivity
  have ht : 0 ≤ t := by
    dsimp [t, tParam]
    positivity
  have hs : s ≤ n := min_le_left _ _
  have hfeas : 0 < m - 2 ∨ s = 0 := by
    by_cases h : 0 < m - 2
    · exact Or.inl h
    · exact Or.inr (by simp [s, commonSize, show m - 2 = 0 by omega])
  obtain ⟨σ, hσ⟩ := sync_attains n m (by omega) t
  obtain ⟨τ, hτ⟩ := common_attains hm hs hfeas t
  refine ⟨⟨?_, ?_⟩, ⟨σ, τ, hσ, hτ⟩, inputWeight_total hn p⟩
  · rcases le_total score₁ score₂ with h | h
    · refine ⟨Convexity.StdSimplex.single τ, ?_⟩
      rw [mixedWin_single, detWin_eq hn p hp', hτ, max_eq_right h]
    · refine ⟨Convexity.StdSimplex.single σ, ?_⟩
      rw [mixedWin_single, detWin_eq hn p hp', hσ, max_eq_left h]
  · rintro _ ⟨w, rfl⟩
    have hd (ρ : Strategy n m) :
        detWin p ρ ≤ probability n p (max score₁ score₂) := by
      have h := residual_upper hm (count ρ.1) (count ρ.2) (count_total ρ.1)
        (count_total ρ.2) (agreements_le_overlap ρ) t ht
      rw [← collisions_eq] at h
      rw [detWin_eq hn p hp']
      exact add_le_add_right (mul_le_mul_of_nonneg_left h hw) _
    calc
      mixedWin p w ≤ ∑ ρ, w.weights ρ * probability n p (max score₁ score₂) :=
        sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hd ρ) (w.weights_nonneg ρ)
      _ = _ := by rw [← sum_mul, w.total_of_fintype, one_mul]

end D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue

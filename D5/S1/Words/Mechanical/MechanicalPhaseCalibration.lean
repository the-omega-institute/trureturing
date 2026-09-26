/- GID: D5/S1/Words/Mechanical/MechanicalPhaseCalibration
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalPhaseCalibration
   mirror-E: none(waiver:actual-mechanical-phase-calibration)
   anchors: []
   utility: none
   digest: Disjoint swept cuts give exact joint phase error and optimal calibration. -/

import D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalPhaseCalibration

open Set MeasureTheory
open scoped BigOperators

/-- Phases in one period where the two actual finite mechanical words differ. -/
def jointMismatchSet (alpha delta : ℝ) (n : ℕ) (u : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Ico 0 1 ∧ ∃ k : Fin n,
    lowerMechanicalWord (alpha + delta) (x + u) k.val ≠
      lowerMechanicalWord alpha x k.val}

/-- Moving the slope and phase sweeps pairwise disjoint cumulative-floor cuts,
including the time-zero endpoint. Centering these displacements attains the
least error in the permitted local phase class. -/
theorem joint_phase_calibration_law (alpha delta g : ℝ) (n : ℕ) (hn : 0 < n)
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hb0 : 0 ≤ alpha + delta) (hb1 : alpha + delta < 1)
    (hg : 0 < g)
    (hcuts : ∀ k : Fin n,
      g ≤ 1 - Int.fract (((k.val + 1 : ℕ) : ℝ) * alpha) ∧
      g ≤ Int.fract (((k.val + 1 : ℕ) : ℝ) * alpha))
    (hgaps : ∀ i j : Fin n, i ≠ j →
      g ≤ |Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha) -
        Int.fract (((j.val + 1 : ℕ) : ℝ) * alpha)|) :
    (∀ u : ℝ, (∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) →
      volume (jointMismatchSet alpha delta n u) =
        ENNReal.ofReal (∑ k : Fin (n + 1), |u + (k.val : ℝ) * delta|)) ∧
    ((n : ℝ) * |delta| ≤ g / 4 →
      (∀ k : Fin (n + 1), |-(n : ℝ) * delta / 2 + (k.val : ℝ) * delta| ≤ g / 4) ∧
      volume (jointMismatchSet alpha delta n (-(n : ℝ) * delta / 2)) =
        ENNReal.ofReal (|delta| * (((n + 1)^2 / 4 : ℕ) : ℝ)) ∧
      ∀ u : ℝ, (∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) →
        volume (jointMismatchSet alpha delta n (-(n : ℝ) * delta / 2)) ≤
          volume (jointMismatchSet alpha delta n u)) := by
  have hlaw (u : ℝ)
      (hmove : ∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) :
      volume (jointMismatchSet alpha delta n u) =
        ENNReal.ofReal (∑ k : Fin (n + 1), |u + (k.val : ℝ) * delta|) := by
    unfold jointMismatchSet
    classical
    have hg1 : g < 1 :=
      ((hcuts ⟨0, hn⟩).2).trans_lt (Int.fract_lt_one _)
    let e : Fin (n + 1) → ℝ := fun k => u + (k.val : ℝ) * delta
    let c : Fin (n + 1) → ℝ := fun k =>
      if k.val = 0 then (if 0 ≤ u then 1 else 0)
      else 1 - Int.fract ((k.val : ℝ) * alpha)
    let swept : Fin (n + 1) → Set ℝ := fun k =>
      Ico (min (c k - e k) (c k)) (max (c k - e k) (c k))
    let D : ℝ → ℕ → ℤ := fun x k =>
      ⌊x + u + (k : ℝ) * (alpha + delta)⌋ - ⌊x + (k : ℝ) * alpha⌋
    have hem (k : Fin (n + 1)) : -g / 4 ≤ e k ∧ e k ≤ g / 4 := by
      have h := abs_le.mp (hmove k)
      exact ⟨by dsimp [e]; linarith [h.1], h.2⟩
    have hc (k : Fin (n + 1)) (hk : k.val ≠ 0) :
        g ≤ c k ∧ c k ≤ 1 - g := by
      let j : Fin n := ⟨k.val - 1, by omega⟩
      have hj : j.val + 1 = k.val := by dsimp [j]; omega
      have h := hcuts j
      rw [hj] at h
      simp only [c, if_neg hk]
      constructor <;> linarith [h.1, h.2]
    have hc01 (k : Fin (n + 1)) : 0 ≤ c k ∧ c k ≤ 1 := by
      by_cases hk : k.val = 0
      · simp only [c, if_pos hk]
        split_ifs <;> norm_num
      · have h := hc k hk
        constructor <;> linarith [h.1, h.2]
    have hsep (i j : Fin (n + 1)) (hij : i ≠ j) : g ≤ |c i - c j| := by
      by_cases hi : i.val = 0
      · have hj : j.val ≠ 0 := by intro hj; apply hij; exact Fin.ext (hi.trans hj.symm)
        have hcj := hc j hj
        rw [show c i = (if 0 ≤ u then 1 else 0) by simp only [c, if_pos hi]]
        split_ifs with hu
        · rw [abs_of_nonneg (by linarith [hcj.2] : 0 ≤ 1 - c j)]
          linarith [hcj.2]
        · rw [zero_sub, abs_neg, abs_of_nonneg (hc01 j).1]
          exact hcj.1
      · by_cases hj : j.val = 0
        · have hci := hc i hi
          rw [show c j = (if 0 ≤ u then 1 else 0) by simp only [c, if_pos hj]]
          split_ifs with hu
          · rw [abs_of_nonpos (by linarith [hci.2] : c i - 1 ≤ 0)]
            linarith [hci.2]
          · rw [sub_zero, abs_of_nonneg (hc01 i).1]
            exact hci.1
        · let a : Fin n := ⟨i.val - 1, by omega⟩
          let b : Fin n := ⟨j.val - 1, by omega⟩
          have ha : a.val + 1 = i.val := by dsimp [a]; omega
          have hb : b.val + 1 = j.val := by dsimp [b]; omega
          have hab : a ≠ b := by
            intro h; apply hij; apply Fin.ext
            have h' := congrArg Fin.val h
            omega
          have h := hgaps a b hab
          rw [ha, hb] at h
          have heq : c i - c j =
              -(Int.fract ((i.val : ℝ) * alpha) -
                Int.fract ((j.val : ℝ) * alpha)) := by
            simp only [c, if_neg hi, if_neg hj]
            ring
          rw [heq, abs_neg]
          exact h
    have hs01 (k : Fin (n + 1)) {x : ℝ} (hx : x ∈ swept k) : x ∈ Ico (0 : ℝ) 1 := by
      change min (c k - e k) (c k) ≤ x ∧ x < max (c k - e k) (c k) at hx
      by_cases hk : k.val = 0
      · by_cases hu : 0 ≤ u
        · have hu1 : u < 1 := by have h := hem k; simp [e, hk] at h; linarith [h.2]
          simp only [c, if_pos hk, if_pos hu, e, hk, Nat.cast_zero, zero_mul, add_zero] at hx
          rw [min_eq_left (by linarith : 1-u ≤ 1), max_eq_right (by linarith : 1-u ≤ 1)] at hx
          constructor <;> linarith [hx.1, hx.2]
        · have hu1 : -u < 1 := by have h := hem k; simp [e, hk] at h; linarith [h.1]
          have hu' : u ≤ 0 := le_of_not_ge hu
          simp only [c, if_pos hk, if_neg hu, e, hk, Nat.cast_zero,
            zero_mul, add_zero, zero_sub] at hx
          rw [min_eq_right (neg_nonneg.mpr hu'), max_eq_left (neg_nonneg.mpr hu')] at hx
          constructor <;> linarith [hx.1, hx.2]
      · have hck := hc k hk
        have hek := hem k
        have hmin : 0 ≤ min (c k - e k) (c k) := by apply le_min <;> linarith
        have hmax : max (c k - e k) (c k) < 1 := by apply max_lt <;> linarith
        exact ⟨hmin.trans hx.1, hx.2.trans hmax⟩
    have hnear (k : Fin (n + 1)) {x : ℝ} (hx : x ∈ swept k) : |x - c k| ≤ g / 4 := by
      have he := hem k
      change min (c k - e k) (c k) ≤ x ∧ x < max (c k - e k) (c k) at hx
      apply abs_le.mpr
      constructor
      · have hmin : c k - g / 4 ≤ min (c k - e k) (c k) := by apply le_min <;> linarith
        linarith [hx.1]
      · have hmax : max (c k - e k) (c k) ≤ c k + g / 4 := by apply max_le <;> linarith
        linarith [hx.2]
    have hdisj : Pairwise (fun i j => Disjoint (swept i) (swept j)) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro x hxi hxj
      have hi := hnear i hxi
      have hj := hnear j hxj
      have htriangle := abs_sub_le (c i) x (c j)
      rw [abs_sub_comm (c i) x] at htriangle
      linarith [hsep i j hij]
    have hcarry (k : Fin (n + 1)) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
        D x k.val = (if c k - e k ≤ x then (1 : ℤ) else 0) -
          (if c k ≤ x then (1 : ℤ) else 0) := by
      have hk0 := hem k
      by_cases hk : k.val = 0
      · have hu : -1 < u ∧ u < 1 := by
          simp [e, hk] at hk0
          constructor <;> linarith [hk0.1, hk0.2]
        have hfx : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr hx
        have hcval : c k = if 0 ≤ u then 1 else 0 := by simp only [c, if_pos hk]
        have heval : e k = u := by simp only [e, hk, Nat.cast_zero, zero_mul, add_zero]
        change ⌊x + u + (k.val : ℝ) * (alpha + delta)⌋ - ⌊x + (k.val : ℝ) * alpha⌋ = _
        rw [hcval, heval, hk]
        simp only [Nat.cast_zero, zero_mul, add_zero, hfx, sub_zero]
        by_cases hu0 : 0 ≤ u
        · rw [if_pos hu0]
          rw [if_neg (not_le.mpr hx.2)]
          simp only [sub_zero]
          split_ifs with hxu
          · apply Int.floor_eq_iff.mpr
            norm_num
            constructor <;> linarith [hx.1, hx.2, hu.2]
          · apply Int.floor_eq_zero_iff.mpr
            constructor <;> linarith [hx.1, hx.2]
        · rw [if_neg hu0, if_pos hx.1]
          split_ifs with hxu
          · norm_num
            exact ⟨by linarith, by linarith [hx.2]⟩
          · apply Int.floor_eq_iff.mpr
            norm_num
            constructor <;> linarith [hx.1, hu.1]
      · let t : ℝ := (k.val : ℝ) * alpha
        have hck := hc k hk
        have hf (v : ℝ) (hv0 : -Int.fract t < v) (hv1 : v < 1 - Int.fract t) :
            ⌊x + t + v⌋ = ⌊t⌋ + if 1 - Int.fract t - v ≤ x then 1 else 0 := by
          have hdecomp : (⌊t⌋ : ℝ) + (x + Int.fract t + v) = x + t + v := by
            linarith [Int.floor_add_fract t]
          rw [← hdecomp, Int.floor_intCast_add]
          congr 1
          split_ifs with h
          all_goals rw [Int.floor_eq_iff]
          all_goals norm_num
          all_goals constructor <;> linarith [hx.1, hx.2]
        have hv0 : -Int.fract t < e k := by
          have h := hck.2
          simp only [c, if_neg hk] at h
          dsimp [t]
          linarith [hk0.1]
        have hv1 : e k < 1 - Int.fract t := by
          have h := hck.1
          simp only [c, if_neg hk] at h
          dsimp [t]
          linarith [hk0.2]
        have ht0 : -Int.fract t < (0 : ℝ) := by
          have h := hck.2
          simp only [c, if_neg hk] at h
          dsimp [t]
          linarith
        have ht1 : (0 : ℝ) < 1 - Int.fract t := by
          have h := hck.1
          simp only [c, if_neg hk] at h
          dsimp [t]
          linarith
        have harg : x + u + (k.val : ℝ) * (alpha + delta) = x + t + e k := by dsimp [t, e]; ring
        dsimp [D]
        rw [harg, hf (e k) hv0 hv1]
        have hbase := hf 0 ht0 ht1
        simp only [add_zero, sub_zero] at hbase
        rw [hbase]
        simp only [c, if_neg hk, t]
        omega
    have hnonzero (k : Fin (n + 1)) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
        D x k.val ≠ 0 ↔ x ∈ swept k := by
      rw [hcarry k x hx]
      change _ ↔ min (c k - e k) (c k) ≤ x ∧ x < max (c k - e k) (c k)
      simp only [min_le_iff, lt_max_iff]
      split_ifs <;> norm_num <;> grind
    have hword (x : ℝ) (k : ℕ) :
        lowerMechanicalWord (alpha + delta) (x + u) k = lowerMechanicalWord alpha x k ↔
        D x (k + 1) = D x k := by
      have hletter : lowerMechanicalWord (alpha + delta) (x + u) k = lowerMechanicalWord alpha x k ↔
          lowerMechanicalLetter (alpha + delta) (x + u) k = lowerMechanicalLetter alpha x k := by
        rcases lowerMechanicalLetter_eq_zero_or_one (rho := x+u) hb0 hb1 k with hb | hb <;>
          rcases lowerMechanicalLetter_eq_zero_or_one (rho := x) ha0 ha1 k with ha | ha <;>
          simp [lowerMechanicalWord, hb, ha]
      rw [hletter]
      dsimp [lowerMechanicalLetter, D]
      omega
    have hset : {x : ℝ | x ∈ Ico 0 1 ∧ ∃ k : Fin n,
        lowerMechanicalWord (alpha + delta) (x + u) k.val ≠ lowerMechanicalWord alpha x k.val} =
        ⋃ k, swept k := by
      ext x
      constructor
      · rintro ⟨hx, k, hk⟩
        by_contra hnone
        have hD (j : ℕ) (hj : j ≤ n) : D x j = 0 := by
          apply not_ne_iff.mp
          intro h
          exact hnone (Set.mem_iUnion.mpr ⟨⟨j, by omega⟩, (hnonzero ⟨j, by omega⟩ x hx).mp h⟩)
        apply hk
        apply (hword x k.val).mpr
        rw [hD (k.val + 1) (by omega), hD k.val (by omega)]
      · intro hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        have hx01 := hs01 i hi
        refine ⟨hx01, ?_⟩
        by_contra hnone
        push Not at hnone
        have hD : ∀ j : ℕ, j ≤ n → D x j = D x 0 := by
          intro j
          induction j with
          | zero => intro _; rfl
          | succ j ih =>
              intro hj
              exact ((hword x j).mp (hnone ⟨j, by omega⟩)).trans (ih (by omega))
        let j : Fin (n + 1) := if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
        have hji : j ≠ i := by
          intro heq
          have heq' := congrArg Fin.val heq
          by_cases hi0 : i.val = 0
          · have hj1 : j.val = 1 := by simp only [j, if_pos hi0]
            omega
          · have hj0 : j.val = 0 := by simp only [j, if_neg hi0]
            omega
        have hxj : x ∉ swept j := fun hh => (Set.disjoint_left.mp (hdisj hji)) hh hi
        have hjzero : D x j.val = 0 := not_ne_iff.mp (mt (hnonzero j x hx01).mp hxj)
        have hizero : D x i.val = 0 := by
          rw [hD i.val (by omega), ← hD j.val (by omega), hjzero]
        exact (hnonzero i x hx01).mpr hi hizero
    rw [hset, measure_iUnion hdisj (fun _ => measurableSet_Ico), tsum_fintype]
    simp only [swept, Real.volume_Ico]
    have hwidth (k : Fin (n + 1)) : max (c k - e k) (c k) - min (c k - e k) (c k) = |e k| := by
      rw [max_sub_min_eq_abs]
      simp
    simp_rw [hwidth]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => abs_nonneg (e k))]
  have hminimum :
      (∑ k : Fin (n + 1), |-(n : ℝ) * delta / 2 + (k.val : ℝ) * delta|) =
        |delta| * (((n + 1)^2 / 4 : ℕ) : ℝ) ∧
      ∀ u : ℝ, |delta| * (((n + 1)^2 / 4 : ℕ) : ℝ) ≤
        ∑ k : Fin (n + 1), |u + (k.val : ℝ) * delta| := by
    have hsum : ∀ N : ℕ, (∑ k : Fin (N + 1), |(k.val : ℝ) - (N : ℝ) / 2|) =
        (((N + 1)^2 / 4 : ℕ) : ℝ) := by
      apply Nat.twoStepInduction
      · norm_num
      · norm_num [Fin.sum_univ_succ]
      · intro N ih _
        rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
          Nat.cast_zero, Nat.cast_add, Nat.cast_one]
        have hmiddle (k : Fin (N + 1)) :
            |(k.val : ℝ) + 1 - ((N : ℝ) + 2) / 2| = |(k.val : ℝ) - (N : ℝ) / 2| := by
          congr 1
          ring
        have hquad : (N + 2 + 1)^2 = (N + 1)^2 + 4*(N + 2) := by ring
        have hdiv : (N + 2 + 1)^2 / 4 = (N + 1)^2 / 4 + (N + 2) := by omega
        have hleft : |0 - ((N : ℝ) + 2) / 2| = ((N : ℝ) + 2) / 2 := by
          rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]
        have hright : |(N : ℝ) + 1 + 1 - ((N : ℝ) + 2) / 2| = ((N : ℝ) + 2) / 2 := by
          rw [abs_of_nonneg (by linarith [(show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)])]
          ring
        norm_num only [Nat.cast_ofNat] at *
        simp_rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring,
          hmiddle, hleft] at *
        rw [ih]
        rw [hdiv]
        push_cast
        rw [abs_of_nonneg (by linarith [(show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)])]
        ring
    have hcenter (k : Fin (n + 1)) :
        |-(n : ℝ) * delta / 2 + (k.val : ℝ) * delta| =
          |delta| * |(k.val : ℝ) - (n : ℝ) / 2| := by
      rw [← abs_mul]
      congr 1
      ring
    constructor
    · simp_rw [hcenter]
      rw [← Finset.mul_sum, hsum n]
    · intro u
      let f : Fin (n + 1) → ℝ := fun k => |u + (k.val : ℝ) * delta|
      have hrev : (∑ k : Fin (n + 1), f k.rev) = ∑ k : Fin (n + 1), f k := by
        exact Equiv.sum_comp Fin.revPerm f
      have hpair (k : Fin (n + 1)) :
          2 * (|delta| * |(k.val : ℝ) - (n : ℝ) / 2|) ≤ f k + f k.rev := by
        have hk : k.val ≤ n := by omega
        have hrevval : (k.rev.val : ℝ) = (n : ℝ) - k.val := by
          rw [Fin.val_rev]
          rw [show n+1-(k.val+1) = n-k.val by omega, Nat.cast_sub hk]
        have h := abs_sub (u + (k.val : ℝ) * delta) (u + (k.rev.val : ℝ) * delta)
        have heq : |(u + (k.val : ℝ) * delta) - (u + (k.rev.val : ℝ) * delta)| =
            2 * (|delta| * |(k.val : ℝ) - (n : ℝ) / 2|) := by
          rw [hrevval]
          have harg : u + (k.val : ℝ) * delta - (u + ((n : ℝ) - k.val) * delta) =
              2 * (delta * ((k.val : ℝ) - (n : ℝ) / 2)) := by ring
          rw [harg, abs_mul, abs_mul]
          norm_num
        rw [heq] at h
        exact h
      have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpair k)
      rw [Finset.sum_add_distrib, hrev, ← Finset.mul_sum, ← Finset.mul_sum, hsum n] at h
      dsimp [f] at h
      linarith
  refine ⟨hlaw, ?_⟩
  intro hsmall
  have hcenter (k : Fin (n + 1)) :
      |-(n : ℝ) * delta / 2 + (k.val : ℝ) * delta| ≤ g / 4 := by
    have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    have hkn : (k.val : ℝ) ≤ n := by exact_mod_cast (show k.val ≤ n by omega)
    have hb : |(k.val : ℝ) - (n : ℝ)/2| ≤ n := by
      apply abs_le.mpr
      constructor <;> linarith [(show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    rw [show -(n : ℝ)*delta/2 + (k.val : ℝ)*delta =
      ((k.val : ℝ) - (n : ℝ)/2)*delta by ring, abs_mul]
    exact (mul_le_mul_of_nonneg_right hb (abs_nonneg delta)).trans hsmall
  have hvalue : volume (jointMismatchSet alpha delta n (-(n : ℝ) * delta / 2)) =
      ENNReal.ofReal (|delta| * (((n + 1)^2 / 4 : ℕ) : ℝ)) := by
    rw [hlaw _ hcenter, hminimum.1]
  refine ⟨hcenter, hvalue, ?_⟩
  intro u hu
  rw [hvalue, hlaw u hu]
  exact ENNReal.ofReal_le_ofReal (hminimum.2 u)

#print axioms joint_phase_calibration_law

end D5.S1.Words.Mechanical.MechanicalPhaseCalibration

/- GID: D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishingInduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishingInduction
   mirror-E: none(waiver:cyclotomic-zero-intervals)
   anchors: []
   utility: none
   digest: Periodic sparse-kernel induction proves the cyclotomic zero intervals. -/

import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelVanishing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelVanishingInduction

open CyclotomicDigitHankelDefs CyclotomicDigitHankelVanishing
open scoped Matrix

set_option maxHeartbeats 2000000 in
-- Periodic block partitions and simultaneous support bounds require a larger budget.
/-- Repeating the root-order blocks grows the trailing-zero bound geometrically,
and the odd carry kernel transfers each sparse kernel to its defining zero intervals. -/
theorem zero_direction (d : ℕ) (hd : 2 ≤ d) (ζ : ℂ) (hζ : ζ ^ d = 1)
    (n : ℕ) (hn : InZeroSet d n) : hankel n (2 * ζ) = 0 := by
  classical
  have digit_block (k v u : ℕ) (t : ℂ) (hu : u < 2 ^ k) :
    digitSum (2 ^ k * v + u) t = t ^ k * digitSum v t + digitSum u t := by
    let ev : List ℕ → ℂ := fun xs =>
      ((xs.map (Nat.cast : ℕ → ℂ)).mapIdx fun j e => e * t ^ j).sum
    have ev_append (xs ys : List ℕ) : ev (xs ++ ys) = ev xs + t ^ xs.length * ev ys := by
      dsimp [ev]
      rw [List.map_append, List.mapIdx_append, List.sum_append]
      simp only [List.length_map]
      have hm : ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ (i + xs.length)) =
          ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i).map
            (fun z => t ^ xs.length * z) := by
        apply List.ext_getElem
        · simp
        · intro i hi hi'
          simp only [List.getElem_map, List.getElem_mapIdx, pow_add]
          ring
      rw [hm]; congr 1
      simpa using List.sum_map_mul_left ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i)
        (fun z => z) (t ^ xs.length)
    have ev_zero (j : ℕ) : ev (List.replicate j 0) = 0 := by
      have hm : (((List.replicate j (0 : ℕ)).map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ i) =
          List.replicate j (0 : ℂ) := by
        apply List.ext_getElem <;> simp
      dsimp [ev]; rw [hm]; simp
    by_cases hv : v = 0
    · subst v
      simp [digitSum]
    · have hlength := (Nat.digits_length_le_iff (by omega : 1 < 2) u).2 hu
      have he : (Nat.digits 2 u).length + (k - (Nat.digits 2 u).length) = k := by omega
      have hc := Nat.digits_append_zeroes_append_digits (b := 2)
        (k := k - (Nat.digits 2 u).length) (m := v) (n := u) (by omega) (by omega)
      rw [he] at hc
      rw [show 2 ^ k * v + u = u + 2 ^ k * v by omega]
      unfold digitSum
      rw [← hc]
      change ((List.flatMap (fun e : ℕ => [(e : ℂ)])
          (Nat.digits 2 u ++ List.replicate (k - (Nat.digits 2 u).length) 0 ++
            Nat.digits 2 v)).mapIdx fun j e => e * t ^ j).sum =
        t ^ k * ((List.flatMap (fun e : ℕ => [(e : ℂ)]) (Nat.digits 2 v)).mapIdx
          fun j e => e * t ^ j).sum +
        ((List.flatMap (fun e : ℕ => [(e : ℂ)]) (Nat.digits 2 u)).mapIdx
          fun j e => e * t ^ j).sum
      rw [← List.map_eq_flatMap, ← List.map_eq_flatMap, ← List.map_eq_flatMap]
      change ev ((Nat.digits 2 u ++ List.replicate (k - (Nat.digits 2 u).length) 0) ++
        Nat.digits 2 v) = t ^ k * ev (Nat.digits 2 v) + ev (Nat.digits 2 u)
      rw [ev_append, ev_append, ev_zero]
      simp only [List.length_append, List.length_replicate, he]
      ring
  have hd0 : 0 < d := by omega
  let P := 2 ^ d
  have hp : 0 < P := by dsimp [P]; positivity
  have hp2 : 2 ≤ P := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ d)
  let t := 2 * ζ
  have zrec (l : ℕ) (hl : 2 * d < l) :
      zBound d l = (2 : ℤ) ^ (l - d) + zBound d (l - d) := by
    have hd0 : 0 < d := by omega
    let a := l - d
    let r := (a - 1) % d + 1
    let q := (a - 1) / d
    have ha : d + 1 ≤ a := by dsimp [a]; omega
    have hr : 1 ≤ r ∧ r ≤ d := by
      have := Nat.mod_lt (a - 1) hd0
      dsimp [r]; omega
    have haq : a = q * d + r := by
      have h := Nat.mod_add_div (a - 1) d
      rw [Nat.mul_comm d] at h
      dsimp [q, r]
      omega
    have he : (a - r) / d = q := by
      have h : a - r = q * d := by omega
      rw [h, Nat.mul_div_cancel _ hd0]
    have hlr : (l - 1) % d + 1 = r := by
      have h : l - 1 = d + (a - 1) := by dsimp [a]; omega
      rw [h, Nat.add_mod]
      simp [r]
    have hlq : (l - r) / d = q + 1 := by
      have h : l - r = d + (a - r) := by dsimp [a] at *; omega
      rw [h, Nat.add_div_left _ hd0, he]
    have hden : (2 : ℤ) ^ d - 1 ≠ 0 := by
      have h : (2 : ℤ) ^ 1 ≤ 2 ^ d := by gcongr <;> omega
      norm_num at h; omega
    have hpow : (2 : ℤ) ^ ((q + 1) * d) = 2 ^ (q * d) * 2 ^ d := by
      rw [Nat.add_mul, Nat.one_mul, pow_add]
    have hpow' : (2 : ℤ) ^ a = 2 ^ r * 2 ^ (q * d) := by
      rw [haq, pow_add]; ring
    have hnum : (2 : ℤ) ^ r * (2 ^ ((q + 1) * d) - 1) =
        2 ^ r * (2 ^ (q * d) - 1) + (2 ^ d - 1) * 2 ^ a := by
      rw [hpow, hpow']; ring
    unfold zBound
    change (2 : ℤ) ^ ((l - 1) % d + 1) *
        (2 ^ (((l - ((l - 1) % d + 1)) / d) * d) - 1) / (2 ^ d - 1) -
          (if (l - 1) % d + 1 < d then 2 else 1) =
      2 ^ a + (2 ^ r * (2 ^ (((a - r) / d) * d) - 1) / (2 ^ d - 1) -
        if r < d then 2 else 1)
    rw [hlr, hlq, he, hnum, Int.add_mul_ediv_left _ _ hden]
    ring
  have zbase (l : ℕ) (hl : d + 1 ≤ l) (hl' : l < 2 * d) :
      zBound d l = (2 : ℤ) ^ (l - d) - 2 := by
    have hmod : (l - 1) % d = l - d - 1 := by
      have he : l - 1 = d + (l - d - 1) := by omega
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show l - d - 1 < d by omega)]
    have hr : (l - 1) % d + 1 = l - d := by omega
    have hq : (l - (l - d)) / d = 1 := by
      rw [show l - (l - d) = d by omega, Nat.div_self hd0]
    have hden : (2 : ℤ) ^ d - 1 ≠ 0 := by
      have h : (2 : ℤ) ^ 1 ≤ 2 ^ d := by gcongr <;> omega
      norm_num at h; omega
    unfold zBound
    simp only [hr]
    rw [hq]
    simp only [one_mul, if_pos (show l - d < d by omega)]
    rw [Int.mul_ediv_cancel _ hden]
  have zdouble : zBound d (2 * d) = (2 : ℤ) ^ d - 1 := by
    have hmod : (2 * d - 1) % d = d - 1 := by
      have he : 2 * d - 1 = d + (d - 1) := by omega
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show d - 1 < d by omega)]
    have hr : (2 * d - 1) % d + 1 = d := by omega
    have hq : (2 * d - d) / d = 1 := by
      rw [show 2 * d - d = d by omega, Nat.div_self hd0]
    have hden : (2 : ℤ) ^ d - 1 ≠ 0 := by
      have h : (2 : ℤ) ^ 1 ≤ 2 ^ d := by gcongr <;> omega
      norm_num at h; omega
    unfold zBound
    simp only [hr]
    rw [hq]
    simp only [one_mul, lt_self_iff_false, if_false]
    rw [Int.mul_ediv_cancel _ hden]
  obtain ⟨_, _, _, _, _, row_sum⟩ := root_base_kernel d 1 hd0 (by decide) ζ hζ
  change ∀ i ≤ P, (∑ j ∈ Finset.range (2 ^ (d - 1)),
    (digitSum (i + 2 * j + 1) t - digitSum (i + 2 * j) t - 1)) = 0 at row_sum
  let E : ℕ → ℂ := fun a => if a % 2 = 0 then 1 else 0
  have hPeven : P % 2 = 0 := by
    have hd' : d = (d - 1) + 1 := by omega
    dsimp [P]; rw [hd', pow_succ]; omega
  have Ecarry (i : ℕ) (hi : i < P) : (∑ a ∈ Finset.range P, E a *
      (digitSum (i + a + 1) t - digitSum (i + a) t - 1)) = 0 := by
    have hP : P = 2 * 2 ^ (d - 1) := by
      dsimp [P]
      calc
        2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (d - 1) := by rw [pow_succ]; ring
    have pairs (b : ℕ) : (∑ a ∈ Finset.range (2 * b), E a *
        (digitSum (i + a + 1) t - digitSum (i + a) t - 1)) =
      ∑ a ∈ Finset.range b,
        (digitSum (i + 2 * a + 1) t - digitSum (i + 2 * a) t - 1) := by
      induction b with
      | zero => simp
      | succ b ih =>
          rw [show 2 * (b + 1) = 2 * b + 2 by omega, Finset.sum_range_add, ih,
            Finset.sum_range_succ]
          simp [Finset.sum_range_succ, E, Nat.add_mod]
          ring
    rw [hP, pairs]
    exact row_sum i (by omega)
  have lift (a z : ℕ) (hz : z < 2 ^ a) (V : ℕ → ℂ) (hv0 : V 0 = 1)
      (hvt : ∀ j, 2 ^ a - z ≤ j → V j = 0)
      (hvs : (∑ j ∈ Finset.range (2 ^ a), V j) = 0)
      (hvk : ∀ i < 2 ^ a,
        (∑ j ∈ Finset.range (2 ^ a), digitSum (i + j) t * V j) = 0) :
      ∃ W : ℕ → ℂ, W 0 = 1 ∧
        (∀ j, 2 ^ (a + d) - (2 ^ a + z) ≤ j → W j = 0) ∧
        (∑ j ∈ Finset.range (2 ^ (a + d)), W j) = 0 ∧
        (∀ i < 2 ^ (a + d),
          (∑ j ∈ Finset.range (2 ^ (a + d)), digitSum (i + j) t * W j) = 0) := by
    let Q := 2 ^ a
    have hq : 0 < Q := by dsimp [Q]; positivity
    have hz' : z < Q := hz
    change (∑ j ∈ Finset.range Q, V j) = 0 at hvs
    have hN : 2 ^ (a + d) = P * Q := by rw [pow_add, Nat.mul_comm]
    have hcut : P * Q - (Q + z) = (P - 2) * Q + (Q - z) := by
      have he : P * Q = (P - 2) * Q + 2 * Q := by
        rw [← Nat.add_mul, show P - 2 + 2 = P by omega]
      omega
    let W : ℕ → ℂ := fun j => if j < P * Q then E (j / Q) * V (j % Q) else 0
    have Wentry (b j : ℕ) (hb : b < P) (hj : j < Q) :
        W (b * Q + j) = E b * V j := by
      have hm := Nat.mul_le_mul_right Q (show b + 1 ≤ P by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      have hdiv : (b * Q + j) / Q = b := by
        rw [Nat.mul_comm b Q, Nat.mul_add_div hq, Nat.div_eq_of_lt hj, Nat.add_zero]
      simp [W, show b * Q + j < P * Q by omega, hdiv, Nat.add_mod, Nat.mod_eq_of_lt hj]
    have Wsum (f : ℕ → ℂ) :
        (∑ j ∈ Finset.range (P * Q), f j * W j) =
          ∑ b ∈ Finset.range P, E b *
            (∑ j ∈ Finset.range Q, f (b * Q + j) * V j) := by
      have blocks (b : ℕ) : (∑ j ∈ Finset.range (b * Q), f j * W j) =
          ∑ c ∈ Finset.range b, ∑ j ∈ Finset.range Q, f (c * Q + j) * W (c * Q + j) := by
        induction b with
        | zero => simp
        | succ b ih =>
            rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
      rw [blocks]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Wentry b j (Finset.mem_range.mp hb) (Finset.mem_range.mp hj)]
      ring
    have dot_split (q r : ℕ) (hr : r < Q) :
        (∑ j ∈ Finset.range Q, digitSum (Q * q + r + j) t * V j) =
          t ^ a * (digitSum (q + 1) t - digitSum q t - 1) *
            (∑ j ∈ Finset.range Q, if Q ≤ r + j then V j else 0) := by
      have split : (∑ j ∈ Finset.range Q, digitSum (Q * q + r + j) t * V j) =
          (∑ j ∈ Finset.range Q, digitSum (r + j) t * V j) +
            t ^ a * digitSum q t * (∑ j ∈ Finset.range Q, V j) +
            t ^ a * (digitSum (q + 1) t - digitSum q t - 1) *
              (∑ j ∈ Finset.range Q, if Q ≤ r + j then V j else 0) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < Q := Finset.mem_range.mp hj
        by_cases hc : Q ≤ r + j
        · have hrem : r + j - Q < Q := by omega
          have heq : Q * q + r + j = Q * (q + 1) + (r + j - Q) := by
            rw [Nat.mul_add, Nat.mul_one]; omega
          have heq' : r + j = Q * 1 + (r + j - Q) := by omega
          have hbig := digit_block a (q + 1) (r + j - Q) t hrem
          have hsmall := digit_block a 1 (r + j - Q) t hrem
          change digitSum (Q * (q + 1) + (r + j - Q)) t = _ at hbig
          change digitSum (Q * 1 + (r + j - Q)) t = _ at hsmall
          rw [← heq] at hbig
          rw [← heq'] at hsmall
          have hone : digitSum 1 t = 1 := by simp [digitSum]
          rw [hbig, hsmall, hone, if_pos hc]; ring
        · have hrem : r + j < Q := by omega
          rw [show Q * q + r + j = Q * q + (r + j) by omega,
            digit_block a q (r + j) t hrem, if_neg hc]; ring
      rw [split, hvs, hvk _ hr]; ring
    refine ⟨W, ?_, ?_, ?_, ?_⟩
    · simp [W, E, hp, hq, hv0]
    · intro j hj
      rw [hN, hcut] at hj
      by_cases hjN : j < P * Q
      · have hdiv : j / Q < P := (Nat.div_lt_iff_lt_mul hq).mpr hjN
        have he : j = Q * (j / Q) + j % Q := (Nat.div_add_mod j Q).symm
        have hr : j % Q < Q := Nat.mod_lt _ hq
        have hlow : P - 2 ≤ j / Q := (Nat.le_div_iff_mul_le hq).mpr (by omega)
        by_cases hlast : j / Q = P - 1
        · have hodd : (j / Q) % 2 ≠ 0 := by rw [hlast]; omega
          simp [W, E, hjN, hodd]
        · have hprev : j / Q = P - 2 := by omega
          rw [hprev, Nat.mul_comm Q (P - 2)] at he
          have ht : Q - z ≤ j % Q := by omega
          simp [W, hjN, hvt _ ht]
      · simp [W, hjN]
    · rw [hN]
      have h := Wsum (fun _ => 1)
      simpa only [one_mul, hvs, mul_zero, Finset.sum_const_zero] using h
    · intro i hi
      rw [hN] at hi ⊢
      rw [Wsum]
      let q := i / Q
      let r := i % Q
      have hr : r < Q := Nat.mod_lt _ hq
      have hqp : q < P := (Nat.div_lt_iff_lt_mul hq).mpr hi
      have hiqr : i = Q * q + r := (Nat.div_add_mod i Q).symm
      have hidx (b j : ℕ) : i + (b * Q + j) = Q * (q + b) + r + j := by
        rw [hiqr]; ring
      simp_rw [hidx, dot_split _ _ hr]
      have rearrange (b : ℕ) : E b * (t ^ a *
          (digitSum (q + b + 1) t - digitSum (q + b) t - 1) *
            (∑ j ∈ Finset.range Q, if Q ≤ r + j then V j else 0)) =
        (t ^ a * (∑ j ∈ Finset.range Q, if Q ≤ r + j then V j else 0)) *
          (E b * (digitSum (q + b + 1) t - digitSum (q + b) t - 1)) := by ring
      simp_rw [rearrange]
      rw [← Finset.mul_sum, Ecarry _ hqp, mul_zero]
  have kernels (l : ℕ) (hl : d + 1 ≤ l) :
      0 ≤ zBound d l ∧ zBound d l < (2 : ℤ) ^ l ∧
      ∃ V : ℕ → ℂ, V 0 = 1 ∧
        (∀ j, 2 ^ l - (zBound d l).toNat ≤ j → V j = 0) ∧
        (∑ j ∈ Finset.range (2 ^ l), V j) = 0 ∧
        (∀ i < 2 ^ l,
          (∑ j ∈ Finset.range (2 ^ l), digitSum (i + j) t * V j) = 0) := by
    induction l using Nat.strong_induction_on with
    | h l ih =>
      by_cases hlt : l < 2 * d
      · let a := l - d
        have ha : 0 < a := by dsimp [a]; omega
        have hla : d + a = l := by dsimp [a]; omega
        have haz : zBound d l = (2 : ℤ) ^ a - 2 := zbase l hl hlt
        have ha2 : 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ha
        have hanat : (zBound d l).toNat = 2 ^ a - 2 := by
          rw [haz]
          have hc : (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) := by norm_cast
          rw [hc]; omega
        have hal : a ≤ l := by dsimp [a]; omega
        have hapow : (2 : ℤ) ^ a ≤ 2 ^ l := by gcongr; omega
        refine ⟨by rw [haz]; exact_mod_cast Nat.zero_le (2 ^ a - 2), ?_, ?_⟩
        · rw [haz]; omega
        · obtain ⟨V, hv0, hvt, hvs, hvk, _⟩ := root_base_kernel d a hd0 ha ζ hζ
          rw [hla] at hvt hvs hvk
          rw [hanat]
          exact ⟨V, hv0, hvt, hvs, hvk⟩
      by_cases heq : l = 2 * d
      · subst l
        have hc : (2 : ℤ) ^ d = (P : ℤ) := by dsimp [P]
        have hanat : (zBound d (2 * d)).toNat = P - 1 := by rw [zdouble, hc]; omega
        have hb : (2 : ℤ) ^ d ≤ 2 ^ (2 * d) := by gcongr <;> omega
        refine ⟨by rw [zdouble, hc]; omega, ?_, ?_⟩
        · rw [zdouble]; omega
        · obtain ⟨V, hv0, hvt, hvs, hvk⟩ := root_second_kernel d hd0 ζ hζ
          rw [hanat]
          exact ⟨V, hv0, hvt, hvs, hvk⟩
      have hgt : 2 * d < l := by omega
      let a := l - d
      have ha : d + 1 ≤ a := by dsimp [a]; omega
      have hal : a < l := by dsimp [a]; omega
      obtain ⟨hz0, hzp, V, hv0, hvt, hvs, hvk⟩ := ih a hal ha
      have hc : (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) := by norm_cast
      have hz : (zBound d a).toNat < 2 ^ a := by rw [hc] at hzp; omega
      have hrec : zBound d l = (2 : ℤ) ^ a + zBound d a := zrec l hgt
      have hznat : (zBound d l).toNat = 2 ^ a + (zBound d a).toNat := by
        rw [hrec, Int.toNat_add (by positivity) hz0, hc, Int.toNat_natCast]
      have hla : a + d = l := by dsimp [a]; omega
      have hp4 : 4 ≤ P := by
        exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hd
      have hN : (2 : ℤ) ^ l = (P : ℤ) * 2 ^ a := by
        rw [← hla, pow_add]; dsimp [P]; norm_cast; ring
      have hznew : zBound d l < (2 : ℤ) ^ l := by
        rw [hrec, hN]
        have hc4 : (4 : ℤ) ≤ P := by exact_mod_cast hp4
        have hpos : (0 : ℤ) < 2 ^ a := by positivity
        nlinarith
      refine ⟨by rw [hrec]; positivity, hznew, ?_⟩
      obtain ⟨W, hw0, hwt, hws, hwk⟩ := lift a (zBound d a).toNat hz V hv0 hvt hvs hvk
      rw [hla] at hwt hws hwk
      rw [hznat]
      exact ⟨W, hw0, hwt, hws, hwk⟩
  obtain ⟨hnpos, l, s, hl, hs, hlo, hhi⟩ := hn
  obtain ⟨hz0, hzlt, V, hv0, hvt, hvs, hvk⟩ := kernels l hl
  let z := (zBound d l).toNat
  have hzcast : (z : ℤ) = zBound d l := Int.toNat_of_nonneg hz0
  have hPcast : (2 : ℤ) ^ l = ((2 ^ l : ℕ) : ℤ) := by norm_cast
  have hz : z < 2 ^ l := by rw [hPcast] at hzlt; omega
  have hspos : 0 < s := hs.pos
  have hnl : 2 ^ l * s - z ≤ n := by
    rw [hPcast] at hlo
    omega
  have hnu : n ≤ 2 ^ l * s + z + 1 := by
    rw [hPcast] at hhi
    omega
  have step (a : ℕ) : digitSum (2 * a + 1) t - digitSum (2 * a) t = 1 := by
    have h0 := digit_block 1 a 0 t (by decide)
    have h1 := digit_block 1 a 1 t (by decide)
    have h0' : digitSum (2 * a) t = t * digitSum a t := by simpa [digitSum] using h0
    have h1' : digitSum (2 * a + 1) t = t * digitSum a t + 1 := by
      simpa [digitSum] using h1
    rw [h0', h1']; ring
  obtain ⟨u, hune, huk⟩ := odd_carry_kernel (fun a => digitSum a t) step s hs
  let U : ℕ → ℂ := fun j => if hj : j < s then u ⟨j, hj⟩ else 0
  have hu : ∀ j, s ≤ j → U j = 0 := by intro j hj; simp [U, show ¬j < s by omega]
  have hu0 : ∃ j < s, U j ≠ 0 := by
    have h : ∃ j : Fin s, u j ≠ 0 := by
      by_contra h
      apply hune
      ext j
      exact not_not.mp (by simpa using (not_exists.mp h) j)
    obtain ⟨j, hj⟩ := h
    exact ⟨j.val, j.isLt, by simpa [U, j.isLt] using hj⟩
  have hUk : ∀ i < s, (∑ j ∈ Finset.range s,
      (digitSum (i + j + 1) t - digitSum (i + j) t - 1) * U j) = 0 := by
    intro i hi
    have h := huk ⟨i, hi⟩
    change (∑ j : Fin s,
      (digitSum (i + j.val + 1) t - digitSum (i + j.val) t - 1) * u j) = 0 at h
    have he : (∑ j : Fin s,
        (digitSum (i + j.val + 1) t - digitSum (i + j.val) t - 1) * u j) =
      ∑ j ∈ Finset.range s,
        (digitSum (i + j + 1) t - digitSum (i + j) t - 1) * U j := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [U, j.isLt]
    rw [← he]; exact h
  have hvne : ∃ j < 2 ^ l, V j ≠ 0 :=
    ⟨0, by positivity, by rw [hv0]; exact one_ne_zero⟩
  exact sparse_kernel_interval l s z n t hspos hz hnl hnu U V hu hvt hu0 hvne hvs hvk hUk

end D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelVanishingInduction

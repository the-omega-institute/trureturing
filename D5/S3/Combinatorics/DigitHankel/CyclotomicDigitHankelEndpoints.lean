/- GID: D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelEndpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelEndpoints
   mirror-E: none(waiver:phase-endpoint-induction)
   anchors: []
   utility: none
   digest: Phase induction identifies the auxiliary determinants at powers of two. -/

import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelDeletion
import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelVanishing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelEndpoints
open CyclotomicDigitHankelDefs CyclotomicDigitHankelVanishing
open CyclotomicDigitHankelDeletion

/-- At a power of two, auxiliary nonvanishing tests every phase encountered by deletion. -/
theorem phase_power_auxiliary (d : ℕ) (ζ : ℂ) (hd : 2 ≤ d)
    (hζ : IsPrimitiveRoot ζ d) :
    let t := 2 * ζ
    let F := fun k a s => digitSum (s % 2 ^ (k + 1)) t +
      2 * t ^ k * ζ ^ a * (s / 2 ^ (k + 1) : ℕ)
    let E := fun k a n => (Matrix.of fun i j : Fin n =>
      if j.val + 1 < n then F k a (i.val + j.val + 1) - F k a (i.val + j.val)
      else 1).det
    ∀ k : ℕ, 1 ≤ k → ∀ a : ℕ,
      (E (k - 1) a (2 ^ k) ≠ 0 ↔ ∀ j < k, ¬d ∣ a + j) := by
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
  intro t F E
  have ζne : ζ ≠ 0 := hζ.ne_zero (by omega)
  have tne : t ≠ 0 := mul_ne_zero (by norm_num) ζne
  have digits0 : digitSum 0 t = 0 := by simp [digitSum]
  have d1 : Nat.digits 2 1 = [1] := by decide
  have d2 : Nat.digits 2 2 = [0, 1] := by decide
  have d3 : Nat.digits 2 3 = [1, 1] := by decide
  have digits1 : digitSum 1 t = 1 := by norm_num [digitSum, d1]
  have splitDigit (k s : ℕ) (hs : s < 2 * 2 ^ k) :
      digitSum s t = digitSum (s % 2 ^ k) t + t ^ k * (s / 2 ^ k : ℕ) := by
    have hp : 0 < 2 ^ k := by positivity
    have hq : s / 2 ^ k < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    have h := digit_block k (s / 2 ^ k) (s % 2 ^ k) t (Nat.mod_lt _ hp)
    rw [show 2 ^ k * (s / 2 ^ k) + s % 2 ^ k = s by
      simpa [Nat.mul_comm] using Nat.div_add_mod s (2 ^ k)] at h
    have hq' : digitSum (s / 2 ^ k) t = (s / 2 ^ k : ℕ) := by
      have hn : 0 ≤ s / 2 ^ k := Nat.zero_le _
      rcases (by omega : s / 2 ^ k = 0 ∨ s / 2 ^ k = 1) with he | he
      · rw [he, digits0]; norm_num
      · rw [he, digits1]; norm_num
    rw [hq'] at h
    linear_combination h
  have Fsmall (k a s : ℕ) (hs : s < 2 ^ (k + 1)) : F k a s = digitSum s t := by
    dsimp [F]
    rw [Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs]
    simp
  have Fhigh (k a s : ℕ) (hs : s < 2 * 2 ^ k) :
      F k a (2 * 2 ^ k + s) = 2 * t ^ k * ζ ^ a + F k a s := by
    have hp : 0 < 2 ^ (k + 1) := by positivity
    have he : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; omega
    rw [he] at hs ⊢
    have hq : (2 ^ (k + 1) + s) / 2 ^ (k + 1) = 1 := by
      rw [Nat.add_div_left _ hp, Nat.div_eq_of_lt hs]
    have hm : (2 ^ (k + 1) + s) % 2 ^ (k + 1) = s := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hs]
    rw [Fsmall k a s hs]
    dsimp [F]
    rw [hq, hm]
    simp; ring
  have Flow (k a s : ℕ) (hs : s < 2 ^ k) :
      F k a (2 ^ k + s) = F k a s + t ^ k := by
    have hbig : 2 ^ k + s < 2 ^ (k + 1) := by rw [pow_succ]; omega
    have hsmall : s < 2 ^ (k + 1) := by rw [pow_succ]; omega
    rw [Fsmall k a _ hbig, Fsmall k a _ hsmall]
    have h := digit_block k 1 s t hs
    simpa [digits1, mul_one, add_comm] using h
  have Fchild (k a s : ℕ) (hk : 1 ≤ k) (hs : s < 2 * 2 ^ k) :
      F k a s + (2 * t ^ k * ζ ^ a / 2 - t ^ k) *
        (if 2 ^ k ≤ s then 1 else 0) = F (k - 1) (a + 1) s := by
    have he : k - 1 + 1 = k := by omega
    have hbig : s < 2 ^ (k + 1) := by rw [pow_succ]; omega
    rw [Fsmall k a s hbig, splitDigit k s hs]
    dsimp [F]
    rw [he]
    have hweight : 2 * t ^ (k - 1) * ζ ^ (a + 1) = t ^ k * ζ ^ a := by
      rw [pow_succ, show k = k - 1 + 1 by omega, pow_succ]
      dsimp [t]; ring
    rw [hweight]
    by_cases hle : 2 ^ k ≤ s
    · have hq : s / 2 ^ k = 1 := by
        have hl := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).mpr
          (show 1 * 2 ^ k ≤ s by omega)
        have hh := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)).mpr
          (show s < 2 * 2 ^ k from hs)
        omega
      rw [if_pos hle, hq]
      push_cast; ring
    · have hq : s / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
      rw [if_neg hle, hq]
      push_cast; ring
  have base2 (a : ℕ) : E 0 a 2 = 2 * (1 - ζ ^ a) := by
    dsimp [E]
    rw [Matrix.det_fin_two]
    norm_num [F, digitSum, d1, d2, d3]
    ring
  have base4 (a : ℕ) :
      E 1 a 4 = (4 * ζ * (ζ ^ a - 1)) ^ 2 * (4 * (ζ ^ (a + 1) - 1)) := by
    let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun i j =>
      if j.val + 1 < 4 then F 1 a (i.val + j.val + 1) - F 1 a (i.val + j.val)
      else 1
    change M.det = _
    rw [Matrix.det_succ_row M 0]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_two]
    simp only [Matrix.det_fin_three]
    norm_num [M, Matrix.submatrix_apply, Fin.succAbove, F, digitSum, d1, d2, d3]
    norm_num [d1, d2, d3, Nat.digits_zero, List.mapIdx_cons]
    rw [pow_succ]
    dsimp [t]
    norm_num [d1, d2, d3, Nat.digits_zero, List.mapIdx_cons]
    ring
  have step (k a : ℕ) (hk : 2 ≤ k) :
      E k a (2 ^ (k + 1)) ≠ 0 ↔ ζ ^ a ≠ 1 ∧ E (k - 1) (a + 1) (2 ^ k) ≠ 0 := by
    have hp : 4 ≤ 2 ^ k := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    have hn : 5 ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
    have hlo : 3 * 2 ^ k < 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
    have hhi : 2 ^ (k + 1) ≤ 2 * 2 ^ k := by rw [pow_succ]; omega
    have hz : F k a 0 = 0 := by rw [Fsmall k a 0 (by positivity), digits0]
    have h := (weighted_deletion (F k a) k (2 ^ (k + 1)) (t ^ k)
      (2 * t ^ k * ζ ^ a) hk hn hlo hhi hz (Flow k a) (Fhigh k a)).2
    change E k a (2 ^ (k + 1)) = _ at h
    have hsize : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by rw [pow_succ]; omega
    rw [hsize] at h
    have hchild : (Matrix.of fun i j : Fin (2 ^ k) =>
        if j.val + 1 < 2 ^ k then
          (F k a (i.val + j.val + 1) +
            (2 * t ^ k * ζ ^ a / 2 - t ^ k) *
              (if 2 ^ k ≤ i.val + j.val + 1 then 1 else 0)) -
          (F k a (i.val + j.val) +
            (2 * t ^ k * ζ ^ a / 2 - t ^ k) *
              (if 2 ^ k ≤ i.val + j.val then 1 else 0)) else 1) =
        Matrix.of fun i j : Fin (2 ^ k) =>
          if j.val + 1 < 2 ^ k then
            F (k - 1) (a + 1) (i.val + j.val + 1) -
              F (k - 1) (a + 1) (i.val + j.val) else 1 := by
      ext i j
      dsimp only [Matrix.of_apply]
      by_cases hj : j.val + 1 < 2 ^ k
      · rw [if_pos hj, if_pos hj]
        rw [Fchild k a _ (by omega) (by omega), Fchild k a _ (by omega) (by omega)]
      · rw [if_neg hj, if_neg hj]
    dsimp only at h
    rw [hchild] at h
    change E k a (2 ^ (k + 1)) =
      2 ^ (2 * 2 ^ (k + 1) - 3 * 2 ^ k - 1) *
        (2 * t ^ k * ζ ^ a - 2 * t ^ k) ^ (2 ^ k) *
          E (k - 1) (a + 1) (2 ^ k) at h
    rw [h]
    have hu : 2 * t ^ k * ζ ^ a - 2 * t ^ k ≠ 0 ↔ ζ ^ a ≠ 1 := by
      rw [show 2 * t ^ k * ζ ^ a - 2 * t ^ k = 2 * t ^ k * (ζ ^ a - 1) by ring]
      simp [mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (pow_ne_zero _ tne), sub_eq_zero]
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff (by positivity : 2 ^ k ≠ 0)]
    have htwo : (2 : ℂ) ^ (2 * 2 ^ (k + 1) - 3 * 2 ^ k - 1) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    tauto
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a
    by_cases h1 : k = 1
    · subst k
      rw [show 1 - 1 = 0 by omega, show (2 : ℕ) ^ 1 = 2 by norm_num, base2]
      have hz : ζ ^ a ≠ 1 ↔ ¬d ∣ a := not_congr (hζ.pow_eq_one_iff_dvd a)
      simp only [mul_ne_zero_iff, sub_ne_zero, ne_eq]
      constructor
      · intro h j hj
        have hj0 : j = 0 := by omega
        subst j
        simpa using hz.mp (Ne.symm h.2)
      · intro h
        exact ⟨by norm_num, Ne.symm (hz.mpr (by simpa using h 0 (by omega)))⟩
    · by_cases h2 : k = 2
      · subst k
        rw [show 2 - 1 = 1 by omega, show (2 : ℕ) ^ 2 = 4 by norm_num, base4]
        have hn4 : (4 : ℂ) ≠ 0 := by norm_num
        have hz0 := not_congr (hζ.pow_eq_one_iff_dvd a)
        have hz1 := not_congr (hζ.pow_eq_one_iff_dvd (a + 1))
        simp only [mul_ne_zero_iff, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
          sub_ne_zero]
        constructor
        · rintro ⟨⟨⟨h4, hz⟩, ha⟩, ⟨h4', ha'⟩⟩ j hj
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
          · simpa using hz0.mp ha
          · exact hz1.mp ha'
        · intro h
          exact ⟨⟨⟨hn4, ζne⟩, hz0.mpr (by simpa using h 0 (by omega))⟩,
            hn4, hz1.mpr (h 1 (by omega))⟩
      · have hk3 : 3 ≤ k := by omega
        have hstep := step (k - 1) a (by omega)
        rw [show k - 1 + 1 = k by omega] at hstep
        rw [hstep, ih (k - 1) (by omega) (by omega) (a + 1)]
        change (¬ζ ^ a = 1 ∧ _) ↔ _
        rw [not_congr (hζ.pow_eq_one_iff_dvd a)]
        constructor
        · rintro ⟨h0, ht⟩ j hj
          by_cases hj0 : j = 0
          · simpa [hj0] using h0
          · have h := ht (j - 1) (by omega)
            simpa [show a + 1 + (j - 1) = a + j by omega] using h
        · intro h
          exact ⟨by simpa using h 0 (by omega), fun j hj => by
            simpa [Nat.add_assoc, Nat.add_comm 1 j] using h (j + 1) (by omega)⟩

end D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelEndpoints

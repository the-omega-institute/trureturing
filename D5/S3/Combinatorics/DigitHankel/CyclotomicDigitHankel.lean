/- GID: D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/CyclotomicDigitHankel
   mirror-E: none(waiver:cyclotomic-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.RingTheory.Valuation.LocalSubring]
   utility: none
   digest: Every primitive doubled root has precisely the stated binary Hankel zero intervals. -/
import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelEndpoints
import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelValuation
import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelIntervals
import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelVanishingInduction
import Mathlib.RingTheory.Valuation.LocalSubring
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Matrix
namespace D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankel
open CyclotomicDigitHankelDefs CyclotomicDigitHankelVanishing
open CyclotomicDigitHankelReflection CyclotomicDigitHankelDeletion
open CyclotomicDigitHankelValuation CyclotomicDigitHankelIntervals
theorem result : CyclotomicDigitHankelDefs.claim := by
  intro d hd ζ hζ
  classical
  let t := 2 * ζ
  let scale := fun n => Nat.log 2 (n - 1)
  let F := fun k a s => digitSum (s % 2 ^ (k + 1)) t +
    2 * t ^ k * ζ ^ a * (s / 2 ^ (k + 1) : ℕ)
  let H := fun a n => (Matrix.of fun i j : Fin n => F (scale n) a (i.val + j.val)).det
  let E := fun a n => (Matrix.of fun i j : Fin n =>
    if j.val + 1 < n then F (scale n) a (i.val + j.val + 1) -
      F (scale n) a (i.val + j.val) else 1).det
  have scale_spec (n : ℕ) (hn : 2 ≤ n) : 2 ^ scale n < n ∧ n ≤ 2 ^ (scale n + 1) := by
    have h1 := Nat.pow_log_le_self 2 (show n - 1 ≠ 0 by omega)
    have h2 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n - 1)
    dsimp [scale]; omega
  have scale_eq (k n : ℕ) (hlo : 2 ^ k < n) (hhi : n ≤ 2 ^ (k + 1)) :
      scale n = k := Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  have digit_block (k v u : ℕ) (t : ℂ) (hu : u < 2 ^ k) :
      digitSum (2 ^ k * v + u) t = t ^ k * digitSum v t + digitSum u t := by
    let ev : List ℕ → ℂ := fun xs =>
      ((xs.map (Nat.cast : ℕ → ℂ)).mapIdx fun j e => e * t ^ j).sum
    have ev_append (xs ys : List ℕ) : ev (xs ++ ys) = ev xs + t ^ xs.length * ev ys := by
      dsimp [ev]; rw [List.map_append, List.mapIdx_append, List.sum_append]
      simp only [List.length_map]
      have hm : ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ (i + xs.length)) =
          ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i).map
            (fun z => t ^ xs.length * z) := by
        apply List.ext_getElem
        · simp
        · intro i hi hi'; simp only [List.getElem_map, List.getElem_mapIdx, pow_add]; ring
      rw [hm]; congr 1
      simpa using List.sum_map_mul_left
        ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i)
        (fun z => z) (t ^ xs.length)
    have ev_zero (j : ℕ) : ev (List.replicate j 0) = 0 := by
      have hm : (((List.replicate j (0 : ℕ)).map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ i) =
          List.replicate j (0 : ℂ) := by apply List.ext_getElem <;> simp
      dsimp [ev]; rw [hm]; simp
    by_cases hv : v = 0
    · subst v; simp [digitSum]
    · have hlength := (Nat.digits_length_le_iff (by omega : 1 < 2) u).2 hu
      have he : (Nat.digits 2 u).length + (k - (Nat.digits 2 u).length) = k := by omega
      have hc := Nat.digits_append_zeroes_append_digits (b := 2)
        (k := k - (Nat.digits 2 u).length) (m := v) (n := u) (by omega) (by omega)
      rw [he] at hc; rw [show 2 ^ k * v + u = u + 2 ^ k * v by omega]
      unfold digitSum; rw [← hc]
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
      rw [ev_append, ev_append, ev_zero]; simp only [List.length_append, List.length_replicate, he]
      ring
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
    rw [hq'] at h; linear_combination h
  have Fsmall (k a s : ℕ) (hs : s < 2 ^ (k + 1)) : F k a s = digitSum s t := by
    dsimp [F]; rw [Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs]; simp
  have Fhigh (k a s : ℕ) (hs : s < 2 * 2 ^ k) :
      F k a (2 * 2 ^ k + s) = 2 * t ^ k * ζ ^ a + F k a s := by
    have hp : 0 < 2 ^ (k + 1) := by positivity
    have he : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; omega
    rw [he] at hs ⊢
    have hq : (2 ^ (k + 1) + s) / 2 ^ (k + 1) = 1 := by
      rw [Nat.add_div_left _ hp, Nat.div_eq_of_lt hs]
    have hm : (2 ^ (k + 1) + s) % 2 ^ (k + 1) = s := by simp [Nat.add_mod, Nat.mod_eq_of_lt hs]
    rw [Fsmall k a s hs]; dsimp [F]; rw [hq, hm]; simp; ring
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
    rw [Fsmall k a s hbig, splitDigit k s hs]; dsimp [F]; rw [he]
    have hweight : 2 * t ^ (k - 1) * ζ ^ (a + 1) = t ^ k * ζ ^ a := by
      rw [pow_succ, show k = k - 1 + 1 by omega, pow_succ]; dsimp [t]; ring
    rw [hweight]
    by_cases hle : 2 ^ k ≤ s
    · have hq : s / 2 ^ k = 1 := by
        have hl := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).mpr
          (show 1 * 2 ^ k ≤ s by omega)
        have hh := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)).mpr hs
        omega
      rw [if_pos hle, hq]; push_cast; ring
    · have hq : s / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
      rw [if_neg hle, hq]; push_cast; ring
  have Fref (k a s : ℕ) (hk : 1 ≤ k) (hs : s < 2 * 2 ^ k) :
      F k a s = F (k - 1) 1 s := by
    have h := Fchild k 0 s hk hs
    norm_num at h
    have hbig : s < 2 ^ (k + 1) := by rw [pow_succ]; omega
    rw [Fsmall k 0 s hbig] at h; rw [Fsmall k a s hbig]; exact h
  have base (a : ℕ) :
      H a 2 = -1 ∧ E a 2 = 2 - 2 * ζ ^ a ∧
      H a 3 = -t ^ 3 + 2 * t ^ 2 + 2 * t - 2 * t * ζ ^ a ∧
      E a 3 = (2 * t * ζ ^ a - 2 * t) * (t - 2) ∧
      H a 4 = (2 * t * ζ ^ a - 2 * t) *
        (t ^ 2 * (2 * t * ζ ^ a) - 4 * t ^ 2 - 4 * t + 2 * (2 * t * ζ ^ a)) ∧
      E a 4 = (2 * t * ζ ^ a - 2 * t) ^ 2 * (2 * t * ζ ^ a - 4) := by
    have sc2 : scale 2 = 0 := scale_eq 0 2 (by norm_num) (by norm_num)
    have sc3 : scale 3 = 1 := scale_eq 1 3 (by norm_num) (by norm_num)
    have sc4 : scale 4 = 1 := scale_eq 1 4 (by norm_num) (by norm_num)
    constructor
    · dsimp [H]; rw [sc2, Matrix.det_fin_two]; norm_num [F, digitSum, d1, d2, d3]
    constructor
    · dsimp [E]; rw [sc2, Matrix.det_fin_two]; norm_num [F, digitSum, d1, d2, d3]; ring
    constructor
    · dsimp [H]; rw [sc3, Matrix.det_fin_three]; norm_num [F, digitSum, d1, d2, d3]
      norm_num [d1, d2, d3, Nat.digits_zero, List.mapIdx_cons]; ring
    constructor
    · dsimp [E]; rw [sc3, Matrix.det_fin_three]; norm_num [F, digitSum, d1, d2, d3]
      norm_num [d1, d2, d3, Nat.digits_zero, List.mapIdx_cons]; ring
    constructor
    · dsimp [H]; rw [sc4, Matrix.det_succ_row _ 0]
      simp only [Fin.sum_univ_succ, Matrix.det_fin_three]
      norm_num [Matrix.submatrix_apply, Fin.succAbove, Fin.lt_def, Fin.le_def,
        F, digitSum, d1, d2, d3]
      norm_num [d1, d2, d3, Nat.digits_zero, List.mapIdx_cons]; ring
    · dsimp [E]; rw [sc4, Matrix.det_succ_row _ 0]
      simp only [Fin.sum_univ_succ, Matrix.det_fin_three]
      norm_num [Matrix.submatrix_apply, Fin.succAbove, Fin.lt_def, Fin.le_def,
        F, digitSum, d1, d2, d3]
      norm_num [d1, d2, d3, Nat.digits_zero, List.mapIdx_cons]; ring
  have recR (k n a : ℕ) (hk : 1 ≤ k) (hn : 5 ≤ n)
      (hlo : 2 ^ k < n) (hhi : n ≤ 3 * 2 ^ (k - 1)) :
      let m := 2 ^ (k + 1) - n + 1
      let r := 2 * n - 2 ^ (k + 1) - 1
      let u := 2 * t ^ k * (ζ ^ a - 1)
      H a n = (-1) ^ (n + 1) * u ^ r * H 1 m + t ^ (2 * k) * u ^ (r - 1) * E 1 m ∧
        E a n = (-1) ^ n * u ^ r * E 1 m := by
    intro m r u
    have hp2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; omega
    have hi2 : n ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
    have scn := scale_eq k n hlo hi2
    have lom : 2 ^ (k - 1) < m := by dsimp [m]; rw [pow_succ]; omega
    have him : m ≤ 2 ^ k := by dsimp [m]; rw [pow_succ]; omega
    have scm := scale_eq (k - 1) m lom (by simpa [Nat.sub_add_cancel hk] using him)
    have hHchild : (Matrix.of fun i j : Fin m => F k a (i.val + j.val)).det = H 1 m := by
      dsimp [H]; rw [scm]; congr 1
      ext i j
      exact Fref k a _ hk (by omega)
    have hEchild : (Matrix.of fun i j : Fin m =>
        if j.val + 1 < m then F k a (i.val + j.val + 1) - F k a (i.val + j.val)
        else 1).det = E 1 m := by
      dsimp [E]; rw [scm]; congr 1
      ext i j
      dsimp only [Matrix.of_apply]
      by_cases hj : j.val + 1 < m
      · rw [if_pos hj, if_pos hj, Fref k a _ hk (by omega), Fref k a _ hk (by omega)]
      · rw [if_neg hj, if_neg hj]
    have hz : F k a 0 = 0 := by rw [Fsmall k a _ (by positivity), digits0]
    have h := weighted_reflection (F k a) k n (t ^ k) (2 * t ^ k * ζ ^ a)
      hk hn hlo hhi hz (Flow k a) (Fhigh k a)
    dsimp only at h; change ((Matrix.of fun i j : Fin n => F k a (i.val + j.val)).det = _) ∧
      ((Matrix.of fun i j : Fin n =>
        if j.val + 1 < n then F k a (i.val + j.val + 1) - F k a (i.val + j.val)
        else 1).det = _) at h
    have hun : 2 * t ^ k * ζ ^ a - 2 * t ^ k = u := by dsimp [u]; ring
    rw [hun, hHchild, hEchild] at h
    have hw : (t ^ k) ^ 2 = t ^ (2 * k) := by rw [← pow_mul]; congr 1; omega
    rw [hw] at h
    simpa only [H, E, scn] using h
  have recD (k n a : ℕ) (hk : 2 ≤ k) (hn : 5 ≤ n)
      (hlo : 3 * 2 ^ k < 2 * n) (hhi : n ≤ 2 * 2 ^ k) :
      let m := n - 2 ^ k
      let b := 2 * n - 3 * 2 ^ k - 1
      let u := 2 * t ^ k * (ζ ^ a - 1)
      H a n = 2 ^ b * u ^ (2 ^ k) * H (a + 1) m +
        (-1) ^ n * 2 ^ b * t ^ (2 * k) * u ^ (2 ^ k - 1) * E (a + 1) m ∧
        E a n = 2 ^ b * u ^ (2 ^ k) * E (a + 1) m := by
    intro m b u
    have hp2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; omega
    have lown : 2 ^ k < n := by omega
    have hin : n ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
    have scn := scale_eq k n lown hin
    have lom : 2 ^ (k - 1) < m := by dsimp [m]; omega
    have him : m ≤ 2 ^ k := by dsimp [m]; omega
    have scm := scale_eq (k - 1) m lom (by simpa [show k - 1 + 1 = k by omega] using him)
    let g := fun s => F k a s + (2 * t ^ k * ζ ^ a / 2 - t ^ k) *
      (if 2 ^ k ≤ s then 1 else 0)
    have hHchild : (Matrix.of fun i j : Fin m => g (i.val + j.val)).det = H (a + 1) m := by
      dsimp [H]; rw [scm]; congr 1
      ext i j
      exact Fchild k a _ (by omega) (by omega)
    have hEchild : (Matrix.of fun i j : Fin m =>
        if j.val + 1 < m then g (i.val + j.val + 1) - g (i.val + j.val)
        else 1).det = E (a + 1) m := by
      dsimp [E]; rw [scm]; congr 1
      ext i j
      dsimp only [Matrix.of_apply]
      by_cases hj : j.val + 1 < m
      · rw [if_pos hj, if_pos hj]
        dsimp only [g]; rw [Fchild k a _ (by omega) (by omega), Fchild k a _ (by omega) (by omega)]
      · rw [if_neg hj, if_neg hj]
    have hz : F k a 0 = 0 := by rw [Fsmall k a _ (by positivity), digits0]
    have h := weighted_deletion (F k a) k n (t ^ k) (2 * t ^ k * ζ ^ a)
      hk hn hlo hhi hz (Flow k a) (Fhigh k a)
    dsimp only at h; change ((Matrix.of fun i j : Fin n => F k a (i.val + j.val)).det = _) ∧
      ((Matrix.of fun i j : Fin n =>
        if j.val + 1 < n then F k a (i.val + j.val + 1) - F k a (i.val + j.val)
        else 1).det = _) at h
    have hun : 2 * t ^ k * ζ ^ a - 2 * t ^ k = u := by dsimp [u]; ring
    rw [hun, hHchild, hEchild] at h
    have hw : (t ^ k) ^ 2 = t ^ (2 * k) := by rw [← pow_mul]; congr 1; omega
    rw [hw] at h
    simpa only [H, E, scn] using h
  obtain ⟨V, hVtwo⟩ : ∃ V : ValuationSubring ℂ, V.valuation (2 : ℂ) < 1 := by
    let A := (Int.castRingHom ℂ).range
    let f : ℤ →+* A := (Int.castRingHom ℂ).rangeRestrict
    have hf : Function.Bijective f := by
      constructor
      · intro x y h
        have hc := congrArg Subtype.val h
        change (x : ℂ) = (y : ℂ) at hc; exact Int.cast_injective hc
      · exact RingHom.rangeRestrict_surjective _
    let e : ℤ ≃+* A := RingEquiv.ofBijective f hf
    let g : A →+* ZMod 2 := (Int.castRingHom (ZMod 2)).comp e.symm.toRingHom
    let I : Ideal A := RingHom.ker g
    have hI : I ≠ ⊤ := RingHom.ker_ne_top g
    obtain ⟨V, hA, hV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
    refine ⟨V, V.mem_nonunits_iff.mp (hV ?_)⟩
    refine ⟨e 2, ?_, ?_⟩
    · change ((e.symm (e 2) : ℤ) : ZMod 2) = 0; rw [e.symm_apply_apply]
      decide
    · change ((2 : ℤ) : ℂ) = 2; norm_num
  let v := V.valuation
  let W := fun a n => (-1 : ℂ) ^ n * H a n / E a n
  have hzu : v ζ = 1 := by
    apply (pow_eq_one_iff_of_nonneg zero_le (by omega : d ≠ 0)).1
    rw [← v.map_pow, hζ.pow_eq_one, map_one]
  have htwo_pos : 0 < v (2 : ℂ) := v.pos_iff.mpr (by norm_num)
  have phase_pow (a : ℕ) : (ζ ^ a) ^ d = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have fixed_ratio (a : ℕ) (ha : ζ ^ a ≠ 1) (C : ℂ)
      (hC : C = ζ - 1 ∨ C = ζ * ζ ^ a - 1) (hCne : C ≠ 0) :
      1 ≤ v (1 / (2 * C) + ζ / (ζ ^ a - 1)) ∧
      (v (1 / (2 * C) + ζ / (ζ ^ a - 1)) = 1 →
        ζ ^ a = -1 ∧ ζ ^ 3 = -1 ∧ v (ζ ^ 2 - 1) = 1) := by
    have hαu : v (ζ ^ a) = 1 := by rw [v.map_pow, hzu, one_pow]
    have hdiff := torsion_root_difference v hVtwo d (by omega) (ζ ^ a) (phase_pow a) ha
    have hCpos : 0 < v C := v.pos_iff.mpr hCne
    have hCbound : v C ≤ 1 := by
      rcases hC with h | h
      · rw [h]; simpa only [hzu, map_one, max_self] using v.map_sub ζ 1
      · rw [h]
        simpa only [map_mul, hzu, hαu, one_mul, map_one, max_self] using
          v.map_sub (ζ * ζ ^ a) 1
    have hfirst : v (1 / (2 * C)) = (v (2 : ℂ) * v C)⁻¹ := by rw [one_div, v.map_inv, map_mul]
    have hsecond : v (ζ / (ζ ^ a - 1)) = (v (ζ ^ a - 1))⁻¹ := by simp only [v.map_div, hzu, one_div]
    have hfirst_gt : 1 < v (1 / (2 * C)) := by
      rw [hfirst, ← one_div]; apply (one_lt_div₀ (mul_pos htwo_pos hCpos)).2
      simpa only [one_mul] using
        (mul_le_of_le_one_right zero_le hCbound).trans_lt hVtwo
    by_cases htie : v (1 / (2 * C)) = v (ζ / (ζ ^ a - 1))
    · have hAeq : v (ζ ^ a - 1) = v (2 : ℂ) * v C := by
        rw [hfirst, hsecond, _root_.inv_inj] at htie; exact htie.symm
      have hA2 : v (ζ ^ a - 1) = v (2 : ℂ) := by
        apply le_antisymm _ hdiff.1; rw [hAeq]; exact mul_le_of_le_one_right zero_le hCbound
      have hCunit : v C = 1 := by apply mul_left_cancel₀ htwo_pos.ne'; rw [mul_one, ← hAeq, hA2]
      have hαneg : ζ ^ a = -1 := hdiff.2.mp hA2
      have hBunit : v (ζ - 1) = 1 := by
        rcases hC with h | h
        · simpa only [h] using hCunit
        · have hplus : v (ζ + 1) = 1 := by
            have heq : C = -(ζ + 1) := by rw [h, hαneg]; ring
            simpa only [heq, v.map_neg] using hCunit
          have heq : ζ - 1 = (ζ + 1) - 2 := by ring
          rw [heq, v.map_sub_eq_of_lt_left]
          · exact hplus
          · simpa only [hplus] using hVtwo
      have hz_ne_one : ζ ≠ 1 := hζ.ne_one (by omega)
      have hz_ne_neg : ζ ≠ -1 := by
        intro h
        have : v (ζ - 1) = v (2 : ℂ) := by
          rw [h]
          have heq : (-1 : ℂ) - 1 = -(2 : ℂ) := by ring
          rw [heq, v.map_neg]
        rw [this] at hBunit; exact hVtwo.ne hBunit
      have hz3_ne : ζ ^ 3 ≠ 1 := by
        intro h
        have heq : (ζ ^ a) ^ 3 = (ζ ^ 3) ^ a := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        rw [hαneg, h] at heq; norm_num at heq
      have hz3pow := phase_pow 3
      have hFbound := torsion_root_difference v hVtwo d (by omega) (ζ ^ 3) hz3pow hz3_ne
      have hF : v (1 + ζ + ζ ^ 2) = v (ζ ^ 3 - 1) := by
        have heq : (1 + ζ + ζ ^ 2) * (ζ - 1) = ζ ^ 3 - 1 := by ring
        have hv := congrArg v heq
        simpa only [map_mul, hBunit, mul_one] using hv
      have hN : v (1 + ζ - ζ ^ 2) = v (1 + ζ + ζ ^ 2) := by
        by_cases heq : v (1 + ζ + ζ ^ 2) = v (2 : ℂ)
        · have hz3neg : ζ ^ 3 = -1 := hFbound.2.mp (hF.symm.trans heq)
          have hcyclo : ζ ^ 2 - ζ + 1 = 0 := by
            have hfactor : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by
              calc
                _ = ζ ^ 3 + 1 := by ring
                _ = 0 := by rw [hz3neg]; ring
            exact (mul_eq_zero.mp hfactor).resolve_left (by
              intro hzero; exact hz_ne_neg (eq_neg_of_add_eq_zero_left hzero))
          have hnum : 1 + ζ - ζ ^ 2 = (2 : ℂ) := by linear_combination -hcyclo
          rw [hnum, heq]
        · have hlt : v (2 : ℂ) < v (1 + ζ + ζ ^ 2) :=
            lt_of_le_of_ne (hF.symm ▸ hFbound.1) (Ne.symm heq)
          have hterm : v (2 * ζ ^ 2) = v (2 : ℂ) := by
            rw [map_mul, v.map_pow, hzu, one_pow, mul_one]
          have hid : 1 + ζ - ζ ^ 2 = (1 + ζ + ζ ^ 2) - 2 * ζ ^ 2 := by ring
          rw [hid, v.map_sub_eq_of_lt_left]
          simpa only [hterm] using hlt
      have hW : v (1 / (2 * C) + ζ / (ζ ^ a - 1)) =
          v (1 + ζ + ζ ^ 2) / v (2 : ℂ) := by
        rcases hC with h | h
        · have hid : 1 / (2 * C) + ζ / (ζ ^ a - 1) =
              (1 + ζ - ζ ^ 2) / (2 * (ζ - 1)) := by rw [h, hαneg]; field_simp; ring
          rw [hid, v.map_div, map_mul, hN, hBunit, mul_one]
        · have hplus : v (ζ + 1) = 1 := by
            have hid : C = -(ζ + 1) := by rw [h, hαneg]; ring
            simpa only [hid, v.map_neg] using hCunit
          have hid : 1 / (2 * C) + ζ / (ζ ^ a - 1) =
              -(1 + ζ + ζ ^ 2) / (2 * (ζ + 1)) := by
            have hCform : C = -(ζ + 1) := by rw [h, hαneg]; ring
            have hpne : ζ + 1 ≠ 0 := by
              intro hpzero; exact hz_ne_neg (eq_neg_of_add_eq_zero_left hpzero)
            rw [hCform, hαneg]; field_simp; ring
          rw [hid, v.map_div, v.map_neg, map_mul, hplus, mul_one]
      constructor
      · rw [hW]; exact (one_le_div₀ htwo_pos).2 (hF.symm ▸ hFbound.1)
      · intro heq
        have hplus_unit : v (ζ + 1) = 1 := by
          have hid : ζ + 1 = (ζ - 1) + 2 := by ring
          rw [hid, v.map_add_eq_of_lt_left]
          · exact hBunit
          · simpa only [hBunit] using hVtwo
        refine ⟨hαneg, hFbound.2.mp ?_, ?_⟩
        · rw [hW, div_eq_one_iff_eq htwo_pos.ne'] at heq; exact hF.symm.trans heq
        · have hid : ζ ^ 2 - 1 = (ζ - 1) * (ζ + 1) := by ring
          rw [hid, map_mul, hBunit, hplus_unit, one_mul]
    · rw [v.map_add_of_distinct_val htie]
      constructor
      · exact hfirst_gt.le.trans (le_max_left _ _)
      · intro h
        have hh : v (1 / (2 * C)) ≤ 1 := (le_max_left _ _).trans_eq h
        exact False.elim (not_le_of_gt hfirst_gt hh)
  have hbasepair (a n : ℕ) (hn : 2 ≤ n) (hn4 : n ≤ 4) (hE : E a n ≠ 0) :
      1 ≤ v (W a n) ∧ (v (W a n) = 1 →
        ζ ^ a = -1 ∧ ζ ^ 3 = -1 ∧ v (ζ ^ 2 - 1) = 1) := by
    have ba := base a
    rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl
    · have hphase : ζ ^ a ≠ 1 := by intro h; apply hE; rw [ba.2.1, h]; ring
      have hAne : ζ ^ a - 1 ≠ 0 := sub_ne_zero.mpr hphase
      have hw : W a 2 = 1 / (2 * (ζ ^ a - 1)) := by
        dsimp [W]; rw [ba.1, ba.2.1]; norm_num; field_simp; ring
      have hAunit : v (ζ ^ a) = 1 := by rw [v.map_pow, hzu, one_pow]
      have hAbound : v (ζ ^ a - 1) ≤ 1 := by
        simpa only [hAunit, map_one, max_self] using v.map_sub (ζ ^ a) 1
      have hApos : 0 < v (ζ ^ a - 1) := v.pos_iff.mpr hAne
      have hstrict : 1 < v (W a 2) := by
        rw [hw, one_div, v.map_inv, map_mul, ← one_div]
        apply (one_lt_div₀ (mul_pos htwo_pos hApos)).2
        simpa only [one_mul] using
          (mul_le_of_le_one_right zero_le hAbound).trans_lt hVtwo
      exact ⟨hstrict.le, fun h => False.elim (hstrict.ne' h)⟩
    · have hphase : ζ ^ a ≠ 1 := by intro h; apply hE; rw [ba.2.2.2.1, h]; ring
      have hB : ζ - 1 ≠ 0 := by
        intro h
        have hzone : ζ = 1 := sub_eq_zero.mp h
        apply hE; rw [ba.2.2.2.1]; simp [t, hzone]
      have hw : W a 3 = 1 / (2 * (ζ - 1)) + ζ / (ζ ^ a - 1) := by
        dsimp [W]; rw [ba.2.2.1, ba.2.2.2.1]; norm_num; dsimp [t]; field_simp; ring
      rw [hw]; exact fixed_ratio a hphase (ζ - 1) (Or.inl rfl) hB
    · have hphase : ζ ^ a ≠ 1 := by intro h; apply hE; rw [ba.2.2.2.2.2, h]; ring
      have hD : ζ * ζ ^ a - 1 ≠ 0 := by
        intro h
        have hzprod : ζ * ζ ^ a = 1 := sub_eq_zero.mp h
        apply hE; rw [ba.2.2.2.2.2]
        have hlast : 2 * t * ζ ^ a - 4 = 0 := by dsimp [t]; linear_combination 4 * hzprod
        rw [hlast, mul_zero]
      have hw : W a 4 = 1 / (2 * (ζ * ζ ^ a - 1)) + ζ / (ζ ^ a - 1) := by
        dsimp [W]; rw [ba.2.2.2.2.1, ba.2.2.2.2.2]; norm_num; dsimp [t]
        have hlarge : (-4 + ζ * ζ ^ a * 4 : ℂ) ≠ 0 := by
          intro hzlarge; apply hD; linear_combination hzlarge / 4
        have hsmall : (-1 + ζ * ζ ^ a : ℂ) ≠ 0 := by convert hD using 1 <;> ring
        field_simp [hlarge]; ring_nf; field_simp [hsmall]; ring
      rw [hw]; exact fixed_ratio a hphase (ζ * ζ ^ a - 1) (Or.inr rfl) hD
  have hstep (a n : ℕ) (hn : 5 ≤ n) (hE : E a n ≠ 0) :
      ∃ k m c, 2 ≤ k ∧ 2 ^ k < n ∧ n ≤ 2 ^ (k + 1) ∧
        2 ≤ m ∧ m < n ∧ E c m ≠ 0 ∧
        ((2 * n ≤ 3 * 2 ^ k ∧ m = 2 ^ (k + 1) - n + 1 ∧ c = 1) ∨
          (3 * 2 ^ k < 2 * n ∧ m = n - 2 ^ k ∧ c = a + 1)) ∧
        ζ ^ a ≠ 1 ∧ W a n = W c m + (2 * ζ) ^ k / (2 * (ζ ^ a - 1)) := by
    let k := scale n
    obtain ⟨hlo, hhi⟩ := scale_spec n (by omega)
    change 2 ^ k < n at hlo; change n ≤ 2 ^ (k + 1) at hhi
    have hk : 2 ≤ k := by
      by_contra h
      rcases (by omega : k = 0 ∨ k = 1) with hk | hk
      · rw [hk] at hhi; norm_num at hhi; omega
      · rw [hk] at hhi; norm_num at hhi; omega
    have hp2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; omega
    have hhalf : 2 ≤ 2 ^ (k - 1) := by
      have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ k - 1)
      norm_num at hpow; exact hpow
    let u := 2 * t ^ k * (ζ ^ a - 1)
    by_cases hbranch : 2 * n ≤ 3 * 2 ^ k
    · let m := 2 ^ (k + 1) - n + 1
      let r := 2 * n - 2 ^ (k + 1) - 1
      have hrec := recR k n a (by omega) hn hlo (by rw [hp2] at hbranch; omega)
      change H a n = (-1) ^ (n + 1) * u ^ r * H 1 m +
        t ^ (2 * k) * u ^ (r - 1) * E 1 m ∧
        E a n = (-1) ^ n * u ^ r * E 1 m at hrec
      have hr : 1 ≤ r := by dsimp [r]; rw [pow_succ]; omega
      have hu : u ≠ 0 := by
        intro hzero; apply hE; rw [hrec.2, hzero, zero_pow (by omega : r ≠ 0), mul_zero, zero_mul]
      have hEc : E 1 m ≠ 0 := by intro hzero; apply hE; rw [hrec.2, hzero, mul_zero]
      have hphase : ζ ^ a ≠ 1 := by intro hzero; apply hu; simp [u, hzero]
      have hmlo : 2 ≤ m := by dsimp [m]; rw [pow_succ]; omega
      have hmhi : m < n := by dsimp [m]; rw [pow_succ]; omega
      refine ⟨k, m, 1, hk, hlo, hhi, hmlo, hmhi, hEc,
        Or.inl ⟨hbranch, rfl, rfl⟩, hphase, ?_⟩
      have hparity : m % 2 = (n + 1) % 2 := by
        have hsum : n + m = 2 * 2 ^ k + 1 := by dsimp [m]; rw [pow_succ]; omega
        omega
      have hsign : (-1 : ℂ) ^ m = -((-1 : ℂ) ^ n) := by
        calc
          (-1 : ℂ) ^ m = (-1 : ℂ) ^ (n + 1) := by
            rw [neg_one_pow_eq_pow_mod_two m, neg_one_pow_eq_pow_mod_two (n + 1), hparity]
          _ = -((-1 : ℂ) ^ n) := by rw [pow_succ]; ring
      have hupow : u ^ r = u ^ (r - 1) * u := by rw [← pow_succ]; congr 1; omega
      have hunorm : (-(t ^ k * 2) + t ^ k * ζ ^ a * 2 : ℂ) ≠ 0 := by
        intro hzero; apply hu; dsimp [u]; linear_combination hzero
      have ht2 : t ^ (2 * k) = (t ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
      have hcancel : (-(t ^ k * 2) + t ^ k * ζ ^ a * 2)⁻¹ ^ (r - 1) *
          (-(t ^ k * 2) + t ^ k * ζ ^ a * 2) ^ (r - 1) = (1 : ℂ) := by
        rw [← mul_pow, inv_mul_cancel₀ hunorm, one_pow]
      dsimp [W]; rw [hrec.1, hrec.2, hsign, hupow, ht2, pow_succ]
      rcases neg_one_pow_eq_or ℂ n with hsignn | hsignn
      · rw [hsignn]; dsimp [u]; change _ = _ + t ^ k / (2 * (ζ ^ a - 1)); field_simp
        linear_combination (t ^ k * E 1 m - 2 * ζ ^ a * H 1 m + 2 * H 1 m) * hcancel
      · rw [hsignn]; dsimp [u]; change _ = _ + t ^ k / (2 * (ζ ^ a - 1)); field_simp
        linear_combination (t ^ k * E 1 m + 2 * ζ ^ a * H 1 m - 2 * H 1 m) * hcancel
    · let m := n - 2 ^ k
      let b := 2 * n - 3 * 2 ^ k - 1
      have hrec := recD k n a hk hn (by omega) (by rw [pow_succ] at hhi; omega)
      change H a n = 2 ^ b * u ^ (2 ^ k) * H (a + 1) m +
        (-1) ^ n * 2 ^ b * t ^ (2 * k) * u ^ (2 ^ k - 1) * E (a + 1) m ∧
        E a n = 2 ^ b * u ^ (2 ^ k) * E (a + 1) m at hrec
      have hp : 0 < 2 ^ k := by positivity
      have hu : u ≠ 0 := by
        intro hzero; apply hE
        rw [hrec.2, hzero, zero_pow (by omega : 2 ^ k ≠ 0), mul_zero, zero_mul]
      have hEc : E (a + 1) m ≠ 0 := by intro hzero; apply hE; rw [hrec.2, hzero, mul_zero]
      have hphase : ζ ^ a ≠ 1 := by intro hzero; apply hu; simp [u, hzero]
      have hmlo : 2 ≤ m := by dsimp [m]; omega
      have hmhi : m < n := by dsimp [m]; omega
      refine ⟨k, m, a + 1, hk, hlo, hhi, hmlo, hmhi, hEc,
        Or.inr ⟨by omega, rfl, rfl⟩, hphase, ?_⟩
      have hparity : m % 2 = n % 2 := by
        have hsum : n = m + 2 * 2 ^ (k - 1) := by dsimp [m]; omega
        omega
      have hsign : (-1 : ℂ) ^ m = (-1 : ℂ) ^ n := by
        rw [neg_one_pow_eq_pow_mod_two m, neg_one_pow_eq_pow_mod_two n, hparity]
      have hupow : u ^ (2 ^ k) = u ^ (2 ^ k - 1) * u := by rw [← pow_succ]; congr 1; omega
      have hunorm : (-(t ^ k * 2) + t ^ k * ζ ^ a * 2 : ℂ) ≠ 0 := by
        intro hzero; apply hu; dsimp [u]; linear_combination hzero
      have ht2 : t ^ (2 * k) = (t ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
      have hcancel : (-(t ^ k * 2) + t ^ k * ζ ^ a * 2)⁻¹ ^ (2 ^ k - 1) *
          (-(t ^ k * 2) + t ^ k * ζ ^ a * 2) ^ (2 ^ k - 1) = (1 : ℂ) := by
        rw [← mul_pow, inv_mul_cancel₀ hunorm, one_pow]
      dsimp [W]; rw [hrec.1, hrec.2, hsign, hupow, ht2]
      rcases neg_one_pow_eq_or ℂ n with hsignn | hsignn
      · rw [hsignn]; dsimp [u]; change _ = _ + t ^ k / (2 * (ζ ^ a - 1)); field_simp
        linear_combination
          (t ^ k * E (a + 1) m + 2 * ζ ^ a * H (a + 1) m - 2 * H (a + 1) m) * hcancel
      · rw [hsignn]; dsimp [u]; change _ = _ + t ^ k / (2 * (ζ ^ a - 1)); field_simp
        linear_combination
          (t ^ k * E (a + 1) m - 2 * ζ ^ a * H (a + 1) m + 2 * H (a + 1) m) * hcancel
  have noncancel := CyclotomicDigitHankelValuation.recursive_noncancellation v hVtwo
    d (by omega) ζ hζ.pow_eq_one H E
    (fun a n hn hn4 hE => (hbasepair a n hn hn4 hE).1)
    (fun a n hn hn4 hE => (hbasepair a n hn hn4 hE).2) hstep
  have powerAux (k : ℕ) (hk : 1 ≤ k) : E 1 (2 ^ k) ≠ 0 ↔ k < d := by
    have hp : 0 < 2 ^ (k - 1) := by positivity
    have hkpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]; ring
    have scm := scale_eq (k - 1) (2 ^ k) (by omega)
      (by simp [Nat.sub_add_cancel hk])
    have h := CyclotomicDigitHankelEndpoints.phase_power_auxiliary d ζ hd hζ k hk 1
    change ((Matrix.of fun i j : Fin (2 ^ k) =>
      if j.val + 1 < 2 ^ k then F (k - 1) 1 (i.val + j.val + 1) -
        F (k - 1) 1 (i.val + j.val) else 1).det ≠ 0 ↔ ∀ j < k, ¬d ∣ 1 + j) at h
    change ((Matrix.of fun i j : Fin (2 ^ k) =>
      if j.val + 1 < 2 ^ k then F (scale (2 ^ k)) 1 (i.val + j.val + 1) -
        F (scale (2 ^ k)) 1 (i.val + j.val) else 1).det ≠ 0 ↔ k < d)
    rw [scm, h]
    constructor
    · intro hall
      by_contra hge
      exact hall (d - 1) (by omega) (by simpa [show 1 + (d - 1) = d by omega])
    · intro hlt j hj hdvd
      have h := Nat.le_of_dvd (by omega : 0 < 1 + j) hdvd
      omega
  have singular (a n : ℕ) (hn : 3 ≤ n) (ha : d ∣ a) :
      E a n = 0 ∧ (H a n ≠ 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ k < d ∧ n = 2 ^ k + 1) := by
    have hα : ζ ^ a = 1 := (hζ.pow_eq_one_iff_dvd a).mpr ha
    have hB : t - 2 ≠ 0 := by
      intro h
      have hζ1 : ζ = 1 := by dsimp [t] at h; linear_combination h / 2
      exact hζ.ne_one (by omega) hζ1
    by_cases hn3 : n = 3
    · subst n
      rw [(base a).2.2.2.1, (base a).2.2.1, hα]
      have ht : -t ^ 3 + 2 * t ^ 2 + 2 * t - 2 * t * 1 ≠ 0 := by
        rw [show -t ^ 3 + 2 * t ^ 2 + 2 * t - 2 * t * 1 = -t ^ 2 * (t - 2) by ring]
        exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ tne)) hB
      constructor
      · ring
      · constructor
        · intro h; exact ⟨1, by omega, by omega, by norm_num⟩
        · intro h; exact ht
    by_cases hn4 : n = 4
    · subst n
      have hH : H a 4 = 0 := by rw [(base a).2.2.2.2.1, hα]; ring
      have hE : E a 4 = 0 := by rw [(base a).2.2.2.2.2, hα]; ring
      refine ⟨hE, ?_⟩
      rw [hH]; simp only [ne_eq, not_true_eq_false, false_iff]; rintro ⟨j, hj, hjd, he⟩
      have hlow : 2 ^ j < 4 := by omega
      have hsc := scale_eq j 4 hlow (by rw [pow_succ]; omega)
      have hs4 := scale_eq 1 4 (by norm_num) (by norm_num)
      have hj1 : j = 1 := hsc.symm.trans hs4
      rw [hj1] at he; norm_num at he
    have hn5 : 5 ≤ n := by omega
    let k := scale n
    have hs := scale_spec n (by omega)
    change 2 ^ k < n ∧ n ≤ 2 ^ (k + 1) at hs
    have hk : 2 ≤ k := by
      by_contra h
      have hcase : k = 0 ∨ k = 1 := by omega
      rcases hcase with hk0 | hk1
      · simp [hk0] at hs; omega
      · simp [hk1] at hs; omega
    have hp2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]; ring
    have endpoint_unique : ∀ j, 1 ≤ j → n = 2 ^ j + 1 → j = k := by
      intro j hj hn
      have hp : 0 < 2 ^ j := by positivity
      have hsc := scale_eq j n (by omega) (by rw [pow_succ]; omega)
      exact hsc.symm
    by_cases hbr : n ≤ 3 * 2 ^ (k - 1)
    · have h := recR k n a (by omega) hn5 hs.1 hbr
      dsimp only at h; rw [hα, sub_self, mul_zero] at h
      let r := 2 * n - 2 ^ (k + 1) - 1
      have hr : 1 ≤ r := by dsimp [r]; rw [pow_succ]; omega
      have hE : E a n = 0 := by
        rw [h.2]; change (-1) ^ n * 0 ^ r * E 1 (2 ^ (k + 1) - n + 1) = 0
        simp [show r ≠ 0 by omega]
      refine ⟨hE, ?_⟩
      by_cases hr1 : r = 1
      · have hnp : n = 2 ^ k + 1 := by dsimp [r] at hr1; rw [pow_succ] at hr1; omega
        have hm : 2 ^ (k + 1) - n + 1 = 2 ^ k := by rw [pow_succ]; omega
        have hH : H a n = t ^ (2 * k) * E 1 (2 ^ k) := by
          rw [h.1, hm]; change (-1) ^ (n + 1) * 0 ^ r * H 1 (2 ^ k) +
            t ^ (2 * k) * 0 ^ (r - 1) * E 1 (2 ^ k) = _
          simp [hr1]
        rw [hH, mul_ne_zero_iff]
        rw [and_iff_right (pow_ne_zero (2 * k) tne), powerAux k (by omega)]
        constructor
        · intro hkd; exact ⟨k, by omega, hkd, hnp⟩
        · rintro ⟨j, hj, hjd, he⟩
          simpa [endpoint_unique j hj he] using hjd
      · have hH : H a n = 0 := by
          rw [h.1]; change (-1) ^ (n + 1) * 0 ^ r * H 1 (2 ^ (k + 1) - n + 1) +
            t ^ (2 * k) * 0 ^ (r - 1) * E 1 (2 ^ (k + 1) - n + 1) = 0
          simp [show r ≠ 0 by omega, show r - 1 ≠ 0 by omega]
        rw [hH]; simp only [ne_eq, not_true_eq_false, false_iff]; rintro ⟨j, hj, hjd, he⟩
        have heq := endpoint_unique j hj he
        subst j
        have : r = 1 := by dsimp [r]; rw [he, pow_succ]; omega
        exact hr1 this
    · have hlo : 3 * 2 ^ k < 2 * n := by omega
      have h := recD k n a hk hn5 hlo (by simpa [pow_succ, Nat.mul_comm] using hs.2)
      dsimp only at h; rw [hα, sub_self, mul_zero] at h
      have hp : 2 ≤ 2 ^ k := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      have hH : H a n = 0 := by rw [h.1]; simp [show 2 ^ k - 1 ≠ 0 by omega]
      have hE : E a n = 0 := by rw [h.2]; simp
      refine ⟨hE, ?_⟩
      rw [hH]; simp only [ne_eq, not_true_eq_false, false_iff]; rintro ⟨j, hj, hjd, he⟩
      have heq := endpoint_unique j hj he
      subst j
      rw [he] at hlo; omega
  have regularR (NC : ∀ a n, 2 ≤ n → E a n ≠ 0 → H a n ≠ 0)
      (a k n : ℕ) (hk : 1 ≤ k) (hn : 3 ≤ n) (hlo : 2 ^ k < n)
      (hhi : n ≤ 3 * 2 ^ (k - 1)) (ha : ¬d ∣ a) :
      H a n ≠ 0 ↔ H 1 (2 ^ (k + 1) - n + 1) ≠ 0 := by
    have hα : ζ ^ a ≠ 1 := mt (hζ.pow_eq_one_iff_dvd a).mp ha
    let u := 2 * t ^ k * (ζ ^ a - 1)
    have hu : u ≠ 0 := by
      dsimp [u]; exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ tne))
        (sub_ne_zero.mpr hα)
    have hp2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]; ring
    by_cases hn5 : 5 ≤ n
    · let m := 2 ^ (k + 1) - n + 1
      have hm : 2 ≤ m := by
        have hp : 0 < 2 ^ (k - 1) := by positivity
        dsimp [m]; rw [pow_succ]; omega
      obtain ⟨hH, hE⟩ := recR k n a hk hn5 hlo hhi
      try dsimp only at hH hE
      change H a n = (-1) ^ (n + 1) * u ^ _ * H 1 m + _ at hH
      by_cases he : E 1 m = 0
      · rw [he, mul_zero, add_zero] at hH; rw [hH]
        change ((-1) ^ (n + 1) * u ^ _ * H 1 m ≠ 0 ↔ H 1 m ≠ 0); rw [mul_ne_zero_iff]
        exact and_iff_right (mul_ne_zero (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ hu))
      · have hen : E a n ≠ 0 := by
          rw [hE]; exact mul_ne_zero
            (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hu)) he
        exact ⟨fun _ => NC 1 m hm he, fun _ => NC a n (by omega) hen⟩
    · have hcase : n = 3 ∨ n = 4 := by omega
      have hi2 : n ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
      have scn := scale_eq k n hlo hi2
      have hk1 : k = 1 := by
        rcases hcase with rfl | rfl
        · exact scn.symm.trans (scale_eq 1 3 (by norm_num) (by norm_num))
        · exact scn.symm.trans (scale_eq 1 4 (by norm_num) (by norm_num))
      clear scn
      subst k
      have hn3 : n = 3 := by norm_num at hhi hlo; omega
      subst n
      have he3 : E a 3 ≠ 0 := by
        rw [(base a).2.2.2.1]
        have hB : t - 2 ≠ 0 := by
          intro h; apply hζ.ne_one (by omega); dsimp [t] at h; linear_combination h / 2
        apply mul_ne_zero _ hB; change 2 * t * ζ ^ a - 2 * t ≠ 0
        convert hu using 1 <;> dsimp [u] <;> ring
      have hh2 : H 1 2 ≠ 0 := by rw [(base 1).1]; norm_num
      norm_num; exact ⟨fun _ => hh2, fun _ => NC a 3 (by omega) he3⟩
  have regularD (NC : ∀ a n, 2 ≤ n → E a n ≠ 0 → H a n ≠ 0)
      (a k n : ℕ) (hk : 1 ≤ k) (hn : 4 ≤ n) (hlo : 3 * 2 ^ k < 2 * n)
      (hhi : n ≤ 2 * 2 ^ k) (ha : ¬d ∣ a) :
      H a n ≠ 0 ↔ H (a + 1) (n - 2 ^ k) ≠ 0 := by
    have hα : ζ ^ a ≠ 1 := mt (hζ.pow_eq_one_iff_dvd a).mp ha
    let u := 2 * t ^ k * (ζ ^ a - 1)
    have hu : u ≠ 0 := by
      dsimp [u]; exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ tne))
        (sub_ne_zero.mpr hα)
    by_cases hn5 : 5 ≤ n
    · have hk2 : 2 ≤ k := by
        by_contra h
        have hk1 : k = 1 := by omega
        simp [hk1] at hhi; omega
      let m := n - 2 ^ k
      have hp : 4 ≤ 2 ^ k := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk2
      have hm : 2 ≤ m := by dsimp [m]; omega
      obtain ⟨hH, hE⟩ := recD k n a hk2 hn5 hlo hhi
      try dsimp only at hH hE
      change H a n = 2 ^ _ * u ^ _ * H (a + 1) m + _ at hH
      by_cases he : E (a + 1) m = 0
      · rw [he, mul_zero, add_zero] at hH; rw [hH]
        change (2 ^ _ * u ^ _ * H (a + 1) m ≠ 0 ↔ H (a + 1) m ≠ 0); rw [mul_ne_zero_iff]
        exact and_iff_right (mul_ne_zero (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ hu))
      · have hen : E a n ≠ 0 := by
          rw [hE]; exact mul_ne_zero
            (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hu)) he
        exact ⟨fun _ => NC (a + 1) m hm he, fun _ => NC a n (by omega) hen⟩
    · have hn4 : n = 4 := by omega
      subst n
      have hk1 : k = 1 := by
        have hkp : 2 ^ k < 4 := by omega
        have hsc := scale_eq k 4 hkp (by rw [pow_succ]; omega)
        exact hsc.symm.trans (scale_eq 1 4 (by norm_num) (by norm_num))
      cases hk1
      let U := 2 * t * (ζ ^ a - 1)
      have hU : U ≠ 0 := by
        dsimp [U]; exact mul_ne_zero (mul_ne_zero (by norm_num) tne) (sub_ne_zero.mpr hα)
      have hH : H a 4 = -(2 * U ^ 2 * H (a + 1) 2 +
          2 * t ^ 2 * U * E (a + 1) 2) := by
        rw [(base a).2.2.2.2.1, (base (a + 1)).1, (base (a + 1)).2.1]
        dsimp [U, t]; rw [pow_succ]; ring
      have hE : E a 4 = -2 * U ^ 2 * E (a + 1) 2 := by
        rw [(base a).2.2.2.2.2, (base (a + 1)).2.1]; dsimp [U, t]; rw [pow_succ]; ring
      have hh2 : H (a + 1) 2 ≠ 0 := by rw [(base (a + 1)).1]; norm_num
      have hh4 : H a 4 ≠ 0 := by
        by_cases he : E (a + 1) 2 = 0
        · rw [hH, he, mul_zero, add_zero]
          exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num)
            (pow_ne_zero _ hU)) hh2)
        · apply NC a 4 (by omega); rw [hE]
          exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hU)) he
      norm_num; exact ⟨fun _ => hh2, fun _ => hh4⟩
  have support (rs : List ℕ) (hrs : ∀ e ∈ rs, 0 < e) (hne : rs ≠ []) :
      H 1 (runValue true rs + 1) ≠ 0 ↔ RunAdmissible d rs := by
    let P := fun a n => H a n ≠ 0
    have ht : ∀ a, P a 2 := by intro a; dsimp [P]; rw [(base a).1]; norm_num
    have NC : ∀ a n, 2 ≤ n → E a n ≠ 0 → H a n ≠ 0 :=
      fun a n hn he => (noncancel a n hn he).1
    have hR := regularR NC
    have hD := regularD NC
    have hS : ∀ a n, 3 ≤ n → d ∣ a →
        (P a n ↔ ∃ k, 1 ≤ k ∧ k < d ∧ n = 2 ^ k + 1) := by
      intro a n hn ha; exact (singular a n hn ha).2
    have rv : ∀ (ss : List ℕ),
        runValue false ss + runValue true ss + 1 = 2 ^ ss.sum ∧
        runValue false ss < 2 ^ ss.sum ∧ runValue true ss < 2 ^ ss.sum := by
      intro ss
      induction ss with
      | nil => simp [runValue]
      | cons L tail ih =>
        have hL : 0 < (2 : ℕ) ^ L := by positivity
        have ht : 0 < (2 : ℕ) ^ tail.sum := by positivity
        have hs : 2 ^ L - 1 + 1 = 2 ^ L := by omega
        have hm := congrArg (· * 2 ^ tail.sum) hs
        simp only [runValue, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          if_false, if_true, zero_mul, zero_add, List.sum_cons, pow_add]
        constructor
        · nlinarith [ih.1]
        · constructor <;> nlinarith [ih.2.1, ih.2.2]
    have rvpos : ∀ (ss : List ℕ), (∀ e ∈ ss, 0 < e) → ss ≠ [] →
        0 < runValue true ss := by
      intro ss hp hn
      cases ss with
      | nil => exact (hn rfl).elim
      | cons L tail =>
        have hL : 0 < L := hp L (by simp)
        have he : 2 ≤ (2 : ℕ) ^ L := by
          have hh : (2 : ℕ) ^ 1 ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
          simpa using hh
        have ht : 0 < (2 : ℕ) ^ tail.sum := by positivity
        simp only [runValue, Bool.not_true, if_true]
        have hprod : 0 < (2 ^ L - 1) * 2 ^ tail.sum :=
          Nat.mul_pos (by omega) ht
        omega
    have scale : ∀ (L : ℕ) (tail : List ℕ), 0 < L →
        2 ^ ((L :: tail).sum - 1) ≤ runValue true (L :: tail) ∧
        runValue true (L :: tail) < 2 ^ (L :: tail).sum := by
      intro L tail hL
      have hl : L = (L - 1) + 1 := by omega
      have hx : (L :: tail).sum - 1 = (L - 1) + tail.sum := by simp only [List.sum_cons]; omega
      have hp : (2 : ℕ) ^ L = 2 * 2 ^ (L - 1) := by
        calc
          2 ^ L = 2 ^ ((L - 1) + 1) := congrArg (2 ^ ·) hl
          _ = _ := by rw [pow_succ']
      have hs : 2 ^ L - 1 + 1 = 2 ^ L := by
        have hh : 0 < (2 : ℕ) ^ L := by positivity
        omega
      have hm := congrArg (· * 2 ^ tail.sum) hs
      have hpt : 0 < (2 : ℕ) ^ tail.sum := by positivity
      have hpl : 0 < (2 : ℕ) ^ (L - 1) := by positivity
      constructor
      · rw [hx, pow_add]; simp only [runValue, Bool.not_true, if_true]
        nlinarith
      · exact (rv (L :: tail)).2.2
    apply run_survival d hd (fun a ss => P a (runValue true ss + 1))
    · intro a; simpa [runValue] using ht a
    · intro a L tail hpos hL hregular
      let k := (L :: tail).sum - 1
      let n := runValue true (L :: tail) + 1
      have hLpos : 0 < L := hpos L (by simp)
      have htpos : 0 < (2 : ℕ) ^ tail.sum := by positivity
      have hk : k = (L - 1) + tail.sum := by dsimp [k]; omega
      have hkpos : 1 ≤ k := by omega
      have hl : L = (L - 1) + 1 := by omega
      have hp : (2 : ℕ) ^ L = 2 * 2 ^ (L - 1) := by
        calc
          2 ^ L = 2 ^ ((L - 1) + 1) := congrArg (2 ^ ·) hl
          _ = _ := by rw [pow_succ']
      have hs : 2 ^ L - 1 + 1 = 2 ^ L := by
        have hh : 0 < (2 : ℕ) ^ L := by positivity
        omega
      have hm := congrArg (· * 2 ^ tail.sum) hs
      have hpchild : 2 ≤ (2 : ℕ) ^ (L - 1) := by
        have hh : (2 : ℕ) ^ 1 ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        simpa using hh
      have hn : 4 ≤ n := by
        dsimp [n]; simp only [runValue, Bool.not_true, if_true]
        nlinarith
      have hbound : 3 * 2 ^ k < 2 * n := by
        rw [hk, pow_add]; dsimp [n]; simp only [runValue, Bool.not_true, if_true]
        nlinarith
      have hupper : n ≤ 2 * 2 ^ k := by
        have hv := (rv (L :: tail)).2.2
        have he : (L :: tail).sum = k + 1 := by dsimp [k]; omega
        rw [he, pow_succ'] at hv; dsimp [n]; omega
      have hsub : n - 2 ^ k = runValue true ((L - 1) :: tail) + 1 := by
        have hsc := (scale L tail hLpos).1
        change 2 ^ k ≤ runValue true (L :: tail) at hsc
        have hb : 2 ^ k ≤ n := by dsimp [n]; omega
        have he : n - 2 ^ k + 2 ^ k = n := Nat.sub_add_cancel hb
        have hc : 2 ^ (L - 1) - 1 + 1 = 2 ^ (L - 1) := by omega
        have hmc := congrArg (· * 2 ^ tail.sum) hc
        rw [hk, pow_add] at he ⊢; dsimp [n] at he ⊢
        simp only [runValue, Bool.not_true, if_true] at he ⊢
        nlinarith
      simpa only [hsub] using hD a k n hkpos hn hbound hupper hregular
    · intro a tail hpos hne hregular
      cases tail with
      | nil => exact (hne rfl).elim
      | cons L rest =>
        have hL : 0 < L := hpos L (by simp)
        let k := (L :: rest).sum
        let n := runValue true (1 :: L :: rest) + 1
        have hk : 1 ≤ k := by dsimp [k]; omega
        have he : runValue true (1 :: L :: rest) = 2 ^ k + runValue false (L :: rest) := by
          simp [runValue, k]
        have hn : 3 ≤ n := by
          have hp : 2 ≤ (2 : ℕ) ^ k := by
            have hh : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
            simpa using hh
          dsimp [n]; rw [he]; omega
        have hlower : 2 ^ k < n := by dsimp [n]; rw [he]; omega
        have htail : runValue false (L :: rest) < 2 ^ (k - 1) := by
          have hv := (rv rest).2.2
          have hx : rest.sum ≤ k - 1 := by dsimp [k]; omega
          have hb : (2 : ℕ) ^ rest.sum ≤ 2 ^ (k - 1) :=
            Nat.pow_le_pow_right (by omega) hx
          simpa only [runValue, Bool.not_false, Bool.false_eq_true, if_false,
            zero_mul, zero_add] using hv.trans_le hb
        have hpow : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
          have hh : k = (k - 1) + 1 := by omega
          calc
            2 ^ k = 2 ^ ((k - 1) + 1) := congrArg (2 ^ ·) hh
            _ = _ := by rw [pow_succ']
        have hupper : n ≤ 3 * 2 ^ (k - 1) := by dsimp [n]; rw [he, hpow]; omega
        have hsub : 2 ^ (k + 1) - n + 1 = runValue true (L :: rest) + 1 := by
          have hc := (rv (L :: rest)).1
          change _ = 2 ^ k at hc
          have hnupper : n ≤ 2 ^ (k + 1) := by dsimp [n]; rw [he, pow_succ']; omega
          have hs := Nat.sub_add_cancel hnupper
          dsimp [n] at hs; rw [he, pow_succ'] at hs; omega
        simpa only [hsub] using hR a k n hk hn hlower hupper hregular
    · intro a L tail hpos hsing
      have hL : 0 < L := hpos L (by simp)
      have htp : ∀ e ∈ tail, 0 < e := by intro e he; exact hpos e (by simp [he])
      by_cases hbase : L = 1 ∧ tail = []
      · rcases hbase with ⟨rfl, rfl⟩
        simp [runValue, ht]
      · have hn : 3 ≤ runValue true (L :: tail) + 1 := by
          have hc := scale L tail hL
          have hlen : 2 ≤ (L :: tail).sum := by
            cases tail with
            | nil =>
              have hh : L ≠ 1 := by intro he; exact hbase ⟨he, rfl⟩
              simpa using (show 2 ≤ L by omega)
            | cons K rest => have hK := htp K (by simp); simp only [List.sum_cons]; omega
          have hp : (2 : ℕ) ^ 1 ≤ 2 ^ ((L :: tail).sum - 1) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          norm_num at hp; simp only [List.sum_cons] at hc; omega
        rw [hS a _ hn hsing]
        constructor
        · rintro ⟨k, hk, hkd, hn⟩
          have he : runValue true (L :: tail) = 2 ^ k := by omega
          have hs := scale L tail hL
          have hklo : (L :: tail).sum - 1 ≤ k := by
            by_contra hh
            have hp : (2 : ℕ) ^ k < 2 ^ ((L :: tail).sum - 1) :=
              Nat.pow_lt_pow_right (by omega) (by omega)
            omega
          have hkhi : k < (L :: tail).sum := by
            by_contra hh
            have hp : (2 : ℕ) ^ (L :: tail).sum ≤ 2 ^ k :=
              Nat.pow_le_pow_right (by omega) (by omega)
            omega
          have hkexact : k = (L :: tail).sum - 1 := by omega
          have hlone : L = 1 := by
            by_contra hh
            have hL2 : 2 ≤ L := by omega
            have hl : L = (L - 1) + 1 := by omega
            have hp : (2 : ℕ) ^ L = 2 * 2 ^ (L - 1) := by
              calc
                2 ^ L = 2 ^ ((L - 1) + 1) := congrArg (2 ^ ·) hl
                _ = _ := by rw [pow_succ']
            have hc : 2 ≤ (2 : ℕ) ^ (L - 1) := by
              have hh : (2 : ℕ) ^ 1 ≤ 2 ^ (L - 1) :=
                Nat.pow_le_pow_right (by omega) (by omega)
              simpa using hh
            have hs : 2 ^ L - 1 + 1 = 2 ^ L := by
              have hh : 0 < (2 : ℕ) ^ L := by positivity
              omega
            have hm := congrArg (· * 2 ^ tail.sum) hs
            have ht : 0 < (2 : ℕ) ^ tail.sum := by positivity
            have hx : (L :: tail).sum - 1 = (L - 1) + tail.sum := by
              simp only [List.sum_cons]; omega
            rw [hkexact, hx, pow_add] at he; simp only [runValue, Bool.not_true, if_true] at he
            nlinarith
          subst L
          refine ⟨rfl, Or.inr ?_⟩
          cases tail with
          | nil => exact (hbase ⟨rfl, rfl⟩).elim
          | cons K rest =>
            have hzero : runValue true rest = 0 := by
              simp only [runValue, Bool.not_true, Bool.not_false, if_true,
                Bool.false_eq_true, if_false, zero_mul, zero_add] at he
              have hx : k = (K :: rest).sum := by simpa using hkexact
              rw [hx] at he; omega
            have hrnil : rest = [] := by
              by_contra hrest
              have hposrest : ∀ e ∈ rest, 0 < e := by intro e he; exact htp e (by simp [he])
              have hp := rvpos rest hposrest hrest
              omega
            subst rest
            refine ⟨K, rfl, ?_⟩
            have hx : k = K := by simpa using hkexact
            omega
        · rintro ⟨rfl, htail⟩
          rcases htail with rfl | ⟨K, rfl, hK⟩
          · exact (hbase ⟨rfl, rfl⟩).elim
          · refine ⟨K, hpos K (by simp), hK, ?_⟩; simp [runValue]
    · exact hrs
    · exact hne
  have original (n : ℕ) (hn : 2 ≤ n) : H 1 n = hankel n t := by
    have hs := scale_spec n hn
    dsimp [H, hankel]; congr 1
    ext i j
    dsimp only [Matrix.of_apply]
    have hb : i.val + j.val < 2 * 2 ^ (scale n + 1) := by omega
    rw [splitDigit (scale n + 1) _ hb]; dsimp [F]; simp only [pow_one]; rw [pow_succ]
    dsimp [t]; ring
  intro n hn
  constructor
  · intro hz
    have hbad (rs : List ℕ) (hne : rs ≠ []) (hrs : ∀ a ∈ rs, 0 < a)
        (heq : runValue true rs = n - 1) : ¬RunAdmissible d rs := by
      intro hgood
      have h := (support rs hrs hne).mpr hgood
      have hv : runValue true rs + 1 = n := by omega
      rw [hv, original n hn] at h; exact h hz
    have h := forbidden_runs_mem d hd (n - 1) (by omega) hbad
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using h
  · exact CyclotomicDigitHankelVanishingInduction.zero_direction d hd ζ hζ.pow_eq_one n
end D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankel

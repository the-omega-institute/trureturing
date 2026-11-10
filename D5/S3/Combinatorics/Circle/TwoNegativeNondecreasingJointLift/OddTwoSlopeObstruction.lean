/- GID: D5/S3/Combinatorics/Circle/TwoNegativeNondecreasingJointLift/OddTwoSlopeObstruction
   generality: I
   mirror-B: none(waiver:consumed-symbolic-support)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: The two-slope arithmetic obstruction excludes the odd physical joint order. -/
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.NarrowChristoffelJointRefutation
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private ear_prefix from D5.S3.Combinatorics.Circle.RunFirstEarTransport

private theorem odd_two_slope_values (k : ℕ) (hk : 2 ≤ k) :
    let h : ℤ := 2 ^ k
    let t : ℤ := 2 ^ (k - 1)
    let r := 2 * k + 1
    let Q := 2 ^ (2 * k) + 2 ^ k
    modulus r / 2 = h ^ 2 - 1 ∧
    modulus (r + 1) / 2 = 2 * h ^ 2 - 1 ∧
    (∀ i : Fin r,
      actualSource r Q i =
        (if i.val = 0 then -(h ^ 2 - h - 1)
         else if i.val = k then -(h ^ 2 - t - 1)
         else if i.val < k then (2 * h + 1) * 2 ^ (i.val - 1)
         else (h + 1) * 2 ^ (i.val - k - 1)) ∧
      actualSource (r + 1) (2 * Q) i.castSucc =
        (if i.val = 0 then -(2 * h ^ 2 - 2 * h - 1)
         else if i.val = k then -(2 * h ^ 2 - t - 1)
         else if i.val < k then (4 * h + 1) * 2 ^ (i.val - 1)
         else (h + 1) * 2 ^ (i.val - k - 1))) ∧
    actualSource (r + 1) (2 * Q) (Fin.last r) = h ^ 2 + h := by
  dsimp only
  let h : ℤ := 2 ^ k
  let t : ℤ := 2 ^ (k - 1)
  let r := 2 * k + 1
  let Q := 2 ^ (2 * k) + 2 ^ k
  let N := modulus r
  let M := modulus (r + 1)
  have hh4 : 4 ≤ h := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hk
    norm_num at this
    exact this
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hht : h = 2 * t := by
    dsimp [h, t]
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hQ : (Q : ℤ) = h ^ 2 + h := by
    dsimp [Q, h]
    push_cast
    rw [show 2 * k = k + k by omega, pow_add]
    ring
  have hN : N = 2 * h ^ 2 - 1 := by
    dsimp [N, modulus, r, h]
    rw [pow_add, show 2 * k = k + k by omega, pow_add]
    norm_num
    ring
  have hM : M = 4 * h ^ 2 - 1 := by
    dsimp [M, modulus, r, h]
    rw [show 2 * k + 1 + 1 = (k + k) + 2 by omega, pow_add, pow_add]
    norm_num
    ring
  have hNP : 0 < N := by rw [hN]; nlinarith
  have hMP : 0 < M := by rw [hM]; nlinarith
  have hNO : N % 2 = 1 := by rw [hN]; omega
  have hMO : M % 2 = 1 := by rw [hM]; omega
  have hNH : N / 2 = h ^ 2 - 1 := by rw [hN]; omega
  have hMH : M / 2 = N := by rw [hM, hN]; omega
  have old_value (i : Fin r) (x m : ℤ)
      (hx : -(h ^ 2 - 1) ≤ x ∧ x ≤ h ^ 2 - 1)
      (he : (2 : ℤ) ^ i.val * (Q : ℤ) = x + m * N) :
      actualSource r Q i = x := by
    apply centered_unique hNP hNO (centered_bounds hNP hNO _)
      (by simpa only [hNH] using hx)
    rw [centered_mod, he]
    simp [Int.add_emod]
  have new_value (i : Fin (r + 1)) (x m : ℤ)
      (hx : -N ≤ x ∧ x ≤ N)
      (he : (2 : ℤ) ^ i.val * ((2 * Q : ℕ) : ℤ) = x + m * M) :
      actualSource (r + 1) (2 * Q) i = x := by
    apply centered_unique hMP hMO (centered_bounds hMP hMO _)
      (by simpa only [hMH] using hx)
    rw [centered_mod, he]
    simp [Int.add_emod]
  refine ⟨hNH, hMH.trans hN, ?_, ?_⟩
  · intro i
    by_cases hi0 : i.val = 0
    · simp only [hi0, if_pos]
      constructor
      · apply old_value i _ 1 (by constructor <;> nlinarith)
        rw [hi0, pow_zero, hQ, hN]; ring
      · apply new_value i.castSucc _ 1 (by rw [hN]; constructor <;> nlinarith)
        simp only [Fin.val_castSucc, hi0, pow_zero, Nat.cast_mul, Nat.cast_ofNat, hQ]
        rw [hM]; ring
    by_cases hik : i.val = k
    · simp only [if_neg hi0, if_pos hik]
      constructor
      · apply old_value i _ (t + 1) (by constructor <;> nlinarith)
        rw [hik]
        change h * (Q : ℤ) = -(h ^ 2 - t - 1) + (t + 1) * N
        rw [hQ, hN, hht]; ring
      · apply new_value i.castSucc _ (t + 1)
          (by rw [hN]; constructor <;> nlinarith)
        simp only [Fin.val_castSucc, hik, Nat.cast_mul, Nat.cast_ofNat, hQ]
        change h * (2 * (h ^ 2 + h)) = -(2 * h ^ 2 - t - 1) + (t + 1) * M
        rw [hM, hht]; ring
    by_cases hik' : i.val < k
    · simp only [hi0, hik, hik', if_false, if_pos]
      let z : ℤ := 2 ^ (i.val - 1)
      have hz0 : 0 < z := by dsimp [z]; positivity
      have hz : 4 * z ≤ h := by
        have he := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (i.val - 1) + 2 ≤ k by omega)
        simpa [pow_add, h, z, mul_comm] using he
      have hp : (2 : ℤ) ^ i.val = 2 * z := by
        rw [show i.val = (i.val - 1) + 1 by omega, pow_succ]
        dsimp [z]; ring
      have hb : (2 * h + 1) * z ≤ h ^ 2 - 1 ∧ (4 * h + 1) * z ≤ N := by
        have h1 := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * h + 1 by omega)
        have h2 := mul_le_mul_of_nonneg_left hz (show 0 ≤ 4 * h + 1 by omega)
        rw [hN]; constructor <;> nlinarith
      constructor
      · apply old_value i _ z (by change _ ≤ (2 * h + 1) * z ∧ _; constructor <;> nlinarith [hb.1])
        rw [hp, hQ, hN]; dsimp [z]; ring
      · apply new_value i.castSucc _ z
          (by change _ ≤ (4 * h + 1) * z ∧ _; constructor <;> nlinarith [hb.2])
        simp only [Fin.val_castSucc, Nat.cast_mul, Nat.cast_ofNat, hQ]
        rw [hp, hM]; dsimp [z]; ring
    · simp only [hi0, hik, hik', if_false]
      let z : ℤ := 2 ^ (i.val - k - 1)
      have hz0 : 0 < z := by dsimp [z]; positivity
      have hz : 2 * z ≤ h := by
        have he := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (i.val - k - 1) + 1 ≤ k by have := i.isLt; change i.val < 2 * k + 1 at this; omega)
        simpa [pow_add, h, z, mul_comm] using he
      have hp : (2 : ℤ) ^ i.val = 2 * h * z := by
        rw [show i.val = k + 1 + (i.val - k - 1) by omega, pow_add, pow_add]
        dsimp [h, z]; norm_num; ring
      have hb : (h + 1) * z ≤ h ^ 2 - 1 := by
        have he := mul_le_mul_of_nonneg_left hz (show 0 ≤ h + 1 by omega)
        nlinarith
      constructor
      · apply old_value i _ ((h + 1) * z)
          (by change _ ≤ (h + 1) * z ∧ _; constructor <;> nlinarith)
        rw [hp, hQ, hN]; dsimp [z]; ring
      · apply new_value i.castSucc _ ((h + 1) * z)
          (by rw [hN]; change _ ≤ (h + 1) * z ∧ _; constructor <;> nlinarith)
        simp only [Fin.val_castSucc, Nat.cast_mul, Nat.cast_ofNat, hQ]
        rw [hp, hM]; dsimp [z]; ring
  · apply new_value (Fin.last r) _ (Q : ℤ)
      (by rw [hN]; constructor <;> nlinarith)
    have hp : (2 : ℤ) ^ r = N + 1 := by dsimp [N, modulus]; ring
    simp only [Fin.val_last, Nat.cast_mul, Nat.cast_ofNat]
    rw [hp, hQ, hN, hM]; ring

private def laneWeight {r : ℕ} (start n : ℕ) (i : Fin r) : ℕ :=
  if start ≤ i.val ∧ i.val < start + n then 2 ^ (i.val - start) else 0

private theorem lane_bound {r : ℕ} (S : Finset (Fin r)) (start n : ℕ) :
    (∑ i ∈ S, laneWeight start n i) < 2 ^ n := by
  classical
  let T := S.filter (fun i => start ≤ i.val ∧ i.val < start + n)
  have hi : ∀ i ∈ T, ∀ j ∈ T, i.val - start = j.val - start → i = j := by
    intro i hi j hj he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    omega
  calc
    (∑ i ∈ S, laneWeight start n i) = ∑ i ∈ T, 2 ^ (i.val - start) := by
      simp only [T, Finset.sum_filter, laneWeight]
    _ = ∑ j ∈ T.image (fun i => i.val - start), 2 ^ j :=
      (Finset.sum_image hi).symm
    _ < 2 ^ n := by
      apply Nat.geomSum_lt (by decide)
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      have := (Finset.mem_filter.mp hi).2
      omega

private theorem first_marked {α : Type*} (p : α → Prop) [DecidablePred p]
    (l : List α) (h : ∃ i ∈ l, p i) :
    ∃ pre i post, l = pre ++ i :: post ∧ p i ∧ ∀ j ∈ pre, ¬p j := by
  revert h
  induction l with
  | nil => intro h; simpa using h
  | cons a l ih =>
    intro h
    by_cases ha : p a
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · have h' : ∃ i ∈ l, p i := by
        obtain ⟨i, hi, hp⟩ := h
        rcases List.mem_cons.mp hi with rfl | hi
        · exact (ha hp).elim
        · exact ⟨i, hi, hp⟩
      obtain ⟨pre, i, post, he, hp, hn⟩ := ih h'
      refine ⟨a :: pre, i, post, by simp [he], hp, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ha
      · exact hn j hj

private theorem two_slope_arithmetic (h t x y : ℤ)
    (hh : 4 ≤ h) (ht : h = 2 * t)
    (hx0 : 0 ≤ x) (hx : x ≤ t - 1)
    (hp0 : h ^ 2 - h - 1 ≤ (2 * h + 1) * x + (h + 1) * y)
    (hp : (2 * h + 1) * x + (h + 1) * y ≤ h ^ 2 - 1) :
    ¬ ((4 * h + 1) * x + (h + 1) * y ≤ h ^ 2 - h - 1 ∨
       2 * h ^ 2 - 2 * h - 1 ≤ (4 * h + 1) * x + (h + 1) * y) := by
  intro he
  have hh0 : 0 < h + 1 := by omega
  have hfac : 0 < 2 * h := by omega
  have hxx : 0 ≤ 2 * h * x := mul_nonneg (by omega) hx0
  rcases he with he | he
  · have hx' : x = 0 := by
      apply le_antisymm _ hx0
      apply (mul_le_mul_iff_right₀ hfac).mp
      nlinarith
    subst x
    have hy : (h + 1) * y = (h + 1) * (h - 2) + 1 := by nlinarith
    have hya : h - 2 < y := by
      apply (mul_lt_mul_iff_right₀ hh0).mp
      nlinarith [hy]
    have hyb : y < h - 1 := by
      apply (mul_lt_mul_iff_right₀ hh0).mp
      nlinarith [hy]
    omega
  · have hprod := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * h by omega)
    have hsq : 2 * h * t = h ^ 2 := by nlinarith [ht]
    have hx' : x = t - 1 := by
      apply le_antisymm hx
      apply (mul_le_mul_iff_right₀ hfac).mp
      nlinarith [hsq]
    rw [hx'] at hp0 hp he
    have hy : (h + 1) * y = 3 * t := by nlinarith [hsq]
    have hya : 1 < y := by
      apply (mul_lt_mul_iff_right₀ hh0).mp
      rw [hy]; nlinarith [ht]
    have hyb : y < 2 := by
      apply (mul_lt_mul_iff_right₀ hh0).mp
      rw [hy]; nlinarith [ht]
    omega

theorem odd_two_slope_no_joint (k : ℕ) (hk : 2 ≤ k) :
    ¬ ∃ sigma : List (Fin (2 * k + 1)), ∃ cut : ℕ,
      cut ≤ 2 * k + 1 ∧
      OriginalOrder (2 * k + 1) (2 ^ (2 * k) + 2 ^ k) sigma ∧
      OriginalOrder (2 * k + 1 + 1) (2 * (2 ^ (2 * k) + 2 ^ k))
        (earWord (2 * k + 1) sigma cut) := by
  classical
  let h : ℤ := 2 ^ k
  let t : ℤ := 2 ^ (k - 1)
  let r := 2 * k + 1
  let Q := 2 ^ (2 * k) + 2 ^ k
  let f := actualSource r Q
  let g := fun i : Fin r => actualSource (r + 1) (2 * Q) i.castSucc
  have hh4 : 4 ≤ h := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hk
    norm_num at this
    exact this
  have hht : h = 2 * t := by
    dsimp [h, t]
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]; ring
  obtain ⟨hH, hN, hvalues, hfresh⟩ := odd_two_slope_values k hk
  intro ⟨sigma, cut, hcut, hold, hnew⟩
  have hlen : sigma.length = r := by simpa using hold.1.length_eq
  have hz : (⟨0, by dsimp [r]; omega⟩ : Fin r) ∈ sigma :=
    hold.1.mem_iff.mpr (by simp)
  obtain ⟨pre, i, post, hs, hi, hpre⟩ :=
    first_marked (fun j : Fin r => j.val = 0 ∨ j.val = k) sigma
      ⟨⟨0, by dsimp [r]; omega⟩, hz, Or.inl rfl⟩
  have hnd : sigma.Nodup := hold.1.nodup_iff.mpr (List.nodup_finRange r)
  rw [hs] at hnd
  have hpreND : pre.Nodup := (List.nodup_append.mp hnd).1
  let S := pre.toFinset
  let xN := ∑ j ∈ S, laneWeight 1 (k - 1) j
  let yN := ∑ j ∈ S, laneWeight (k + 1) k j
  let x : ℤ := xN
  let y : ℤ := yN
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxlt : x < t := by
    dsimp only [x, xN, t]
    exact_mod_cast lane_bound S 1 (k - 1)
  have hx : x ≤ t - 1 := by omega
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hylt : y < h := by
    dsimp only [y, yN, h]
    exact_mod_cast lane_bound S (k + 1) k
  have hy : y ≤ h - 1 := by omega
  have hsum (v : Fin r → ℤ) : (pre.map v).sum = ∑ j ∈ S, v j := by
    exact (List.sum_toFinset v hpreND).symm
  have hlinear (j : Fin r) (hj : j ∈ S) :
      f j = (2 * h + 1) * (laneWeight 1 (k - 1) j : ℤ) +
          (h + 1) * (laneWeight (k + 1) k j : ℤ) ∧
      g j = (4 * h + 1) * (laneWeight 1 (k - 1) j : ℤ) +
          (h + 1) * (laneWeight (k + 1) k j : ℤ) := by
    have hp := hpre j (List.mem_toFinset.mp hj)
    have hj0 : j.val ≠ 0 := fun he => hp (Or.inl he)
    have hjk : j.val ≠ k := fun he => hp (Or.inr he)
    have hv := hvalues j
    by_cases hjl : j.val < k
    · have hc : 1 ≤ j.val ∧ j.val < 1 + (k - 1) := by omega
      have hc' : ¬(k + 1 ≤ j.val ∧ j.val < k + 1 + k) := by omega
      simpa only [f, g, h, t, r, Q, hj0, hjk, hjl, if_false, if_pos, laneWeight,
        hc, hc', and_self, ite_true, ite_false, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero]
        using hv
    · have hc : ¬(1 ≤ j.val ∧ j.val < 1 + (k - 1)) := by omega
      have hc' : k + 1 ≤ j.val ∧ j.val < k + 1 + k := by
        have := j.isLt
        dsimp [r] at this
        omega
      simpa only [f, g, h, t, r, Q, hj0, hjk, hjl, if_false, if_pos, laneWeight,
        hc, hc', and_self, ite_true, ite_false, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero, mul_zero,
        zero_add, Nat.sub_sub] using hv
  have hcastX : (∑ j ∈ S, (laneWeight 1 (k - 1) j : ℤ)) = x := by
    simp [x, xN]
  have hcastY : (∑ j ∈ S, (laneWeight (k + 1) k j : ℤ)) = y := by
    simp [y, yN]
  have hsumF : (pre.map f).sum = (2 * h + 1) * x + (h + 1) * y := by
    rw [hsum]
    calc
      (∑ j ∈ S, f j) = ∑ j ∈ S,
          ((2 * h + 1) * (laneWeight 1 (k - 1) j : ℤ) +
           (h + 1) * (laneWeight (k + 1) k j : ℤ)) :=
        Finset.sum_congr rfl (fun j hj => (hlinear j hj).1)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hcastX, hcastY]
  have hsumG : (pre.map g).sum = (4 * h + 1) * x + (h + 1) * y := by
    rw [hsum]
    calc
      (∑ j ∈ S, g j) = ∑ j ∈ S,
          ((4 * h + 1) * (laneWeight 1 (k - 1) j : ℤ) +
           (h + 1) * (laneWeight (k + 1) k j : ℤ)) :=
        Finset.sum_congr rfl (fun j hj => (hlinear j hj).2)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hcastX, hcastY]
  have htake : sigma.take pre.length = pre := by rw [hs]; simp
  have htake' : sigma.take (pre.length + 1) = pre ++ [i] := by
    rw [hs]; simp [List.take_append]
  have hp := (hold.2.2 pre.length).2
  rw [htake, hH] at hp
  change (pre.map f).sum ≤ h ^ 2 - 1 at hp
  rw [hsumF] at hp
  have hfi : f i ≤ -(h ^ 2 - h - 1) := by
    have hv := (hvalues i).1
    change f i = _ at hv
    rw [hv]
    rcases hi with hi | hi
    · simp [hi, h]
    · have hi0 : i.val ≠ 0 := by omega
      simp only [if_neg hi0, if_pos hi]
      change -(h ^ 2 - t - 1) ≤ _
      nlinarith [hht]
  have hgi : g i ≤ -(2 * h ^ 2 - 2 * h - 1) := by
    have hv := (hvalues i).2
    change g i = _ at hv
    rw [hv]
    rcases hi with hi | hi
    · simp [hi, h]
    · have hi0 : i.val ≠ 0 := by omega
      simp only [if_neg hi0, if_pos hi]
      change -(2 * h ^ 2 - t - 1) ≤ _
      nlinarith [hht]
  have hp0 := (hold.2.2 (pre.length + 1)).1
  rw [htake', List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton] at hp0
  change 0 ≤ (pre.map f).sum + f i at hp0
  rw [hsumF] at hp0
  have hpB : h ^ 2 - h - 1 ≤ (2 * h + 1) * x + (h + 1) * y := by
    linarith
  apply two_slope_arithmetic h t x y hh4 hht hx0 hx hpB hp
  have hcut' : cut ≤ sigma.length := by omega
  have he := ear_prefix r sigma cut hcut' (actualSource (r + 1) (2 * Q))
    (pre.length + 1)
  by_cases hc : cut ≤ pre.length
  · left
    have hn := (hnew.2.2 (pre.length + 1)).2
    rw [he] at hn
    have hc' : ¬pre.length + 1 ≤ cut := by omega
    simp only [if_neg hc', Nat.add_sub_cancel] at hn
    rw [htake, hfresh, hN] at hn
    change (pre.map g).sum + (h ^ 2 + h) ≤ 2 * h ^ 2 - 1 at hn
    rw [hsumG] at hn
    linarith
  · right
    have hn := (hnew.2.2 (pre.length + 1)).1
    rw [he] at hn
    have hc' : pre.length + 1 ≤ cut := by omega
    simp only [if_pos hc', add_zero] at hn
    rw [htake', List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton] at hn
    change 0 ≤ (pre.map g).sum + g i at hn
    rw [hsumG] at hn
    linarith

end D5.S3.Combinatorics.Circle.NarrowChristoffelJointRefutation

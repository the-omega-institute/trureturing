/- GID: D5/S3/Combinatorics/Circle/TwoNegativeNondecreasingJointLift/HighPhaseTwoNegativeClassification
   generality: I
   mirror-B: none(waiver:consumed-symbolic-support)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.Coprime.Basic]
   utility: none
   digest: A bounded-mask criterion for high-phase physical two-negative joint orders. -/
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.TwoNegativeJointLift
import D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift.OddTwoSlopeObstruction

/-! Exact physical high-phase classification via a shared bounded-mask bridge.
The construction keeps every Fin label distinct and uses one old permutation
and one literal fresh insertion for both complete prefix conditions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.HighPhaseTwoNegativeClassification
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private two_blocks split_perm source_total inserted_perm from
  D5.S3.Combinatorics.Circle.TwoNegativeJointLift
open private ear_prefix from D5.S3.Combinatorics.Circle.RunFirstEarTransport
open private first_marked laneWeight lane_bound from
  D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift.OddTwoSlopeObstruction

private theorem odd_modulus_dvd_iff (p L : ℤ) :
    (2 * L + 1) ∣ (2 * p - L) ↔ (2 * L + 1) ∣ (4 * p + 1) := by
  have hodd : Odd (2 * L + 1) := ⟨L, rfl⟩
  have hid : 4 * p + 1 = 2 * (2 * p - L) + (2 * L + 1) := by ring
  constructor
  · intro h
    rw [hid]
    exact dvd_add (h.mul_left 2) (dvd_refl _)
  · intro h
    apply hodd.isCoprime_two.dvd_of_dvd_mul_left
    have hsub := dvd_sub h (dvd_refl (2 * L + 1))
    convert hsub using 1 <;> ring

/-- Both exact gates hold for a bounded integer mask precisely in the two
divisibility branches. `e = true` means that the fresh charge is already present. -/
private theorem exact_two_bank_mask_criterion (p L : ℤ) (hL : 2 ≤ L) (hLp : L ≤ p) :
    let B := 2 * p * L - p - 1
    let H := 2 * p * L - 1
    let D := 4 * p * L - 2 * p - 1
    let N := 4 * p * L - 1
    let Q := 2 * p * L + p
    (∃ (x y : ℤ) (e : Bool),
      let P := (2 * p + 1) * x + (2 * L + 1) * y
      let G := P + 2 * p * x
      0 ≤ x ∧ x < L ∧ 0 ≤ y ∧ y < p ∧
        B ≤ P ∧ P ≤ H ∧
        D ≤ G + (if e then Q else 0) ∧ G + (if e then Q else 0) ≤ N) ↔
      (2 * L + 1) ∣ (2 * p + 1) ∨ (2 * L + 1) ∣ (4 * p + 1) := by
  dsimp only
  have hp2 : 2 ≤ p := hL.trans hLp
  have hp : 0 < p := by omega
  have hM : 0 < 2 * L + 1 := by omega
  have hpL : p ≤ p * L := by
    nlinarith only [mul_nonneg hp.le (show 0 ≤ L - 1 by omega)]
  constructor
  · rintro ⟨x, y, e, hx0, hxL, _hy0, _hyp, hBP, hPH, hDG, hGN⟩
    cases e with
    | false =>
      simp at hDG hGN
      have hcap := mul_le_mul_of_nonneg_left
        (show x ≤ L - 1 by omega) (show 0 ≤ 2 * p by omega)
      have hGexact : (2 * p + 1) * x + (2 * L + 1) * y + 2 * p * x =
          4 * p * L - 2 * p - 1 := by
        nlinarith only [hDG, hPH, hcap]
      have hPexact : (2 * p + 1) * x + (2 * L + 1) * y = 2 * p * L - 1 := by
        nlinarith only [hGexact, hPH, hcap]
      have hprod : (2 * p) * (L - 1 - x) = 0 := by
        nlinarith only [hGexact, hPexact]
      have hxeq : x = L - 1 := by
        have hz : L - 1 - x = 0 :=
          (mul_eq_zero.mp hprod).resolve_left (by omega)
        omega
      rw [hxeq] at hPexact
      right
      apply (odd_modulus_dvd_iff p L).mp
      exact ⟨y, by nlinarith only [hPexact]⟩
    | true =>
      simp at hDG hGN
      have hpx : 0 ≤ 2 * p * x := mul_nonneg (by omega) hx0
      have hGexact : (2 * p + 1) * x + (2 * L + 1) * y + 2 * p * x =
          2 * p * L - p - 1 := by
        nlinarith only [hBP, hGN, hpx]
      have hprod : 2 * p * x = 0 := by
        nlinarith only [hGexact, hBP, hpx]
      have hxeq : x = 0 := (mul_eq_zero.mp hprod).resolve_left (by omega)
      have hPexact : (2 * p + 1) * x + (2 * L + 1) * y =
          2 * p * L - p - 1 := by
        nlinarith only [hGexact, hprod]
      rw [hxeq] at hPexact
      left
      exact ⟨p - y, by nlinarith only [hPexact]⟩
  · rintro (hdiv | hdiv)
    · obtain ⟨k, hk⟩ := hdiv
      let y := p - k
      have hyEq : (2 * L + 1) * y = 2 * p * L - p - 1 := by
        dsimp only [y]
        nlinarith only [hk]
      have hy0 : 0 ≤ y := (mul_nonneg_iff_of_pos_left hM).mp (by
        nlinarith only [hyEq, hpL, hp2])
      have hyp : y < p := (mul_lt_mul_iff_right₀ hM).mp (by
        nlinarith only [hyEq, hp])
      refine ⟨0, y, true, by omega, by omega, hy0, hyp, ?_, ?_, ?_, ?_⟩ <;>
        simp <;> nlinarith only [hyEq, hp]
    · obtain ⟨y, hyEq⟩ := (odd_modulus_dvd_iff p L).mpr hdiv
      have hy0 : 0 ≤ y := (mul_nonneg_iff_of_pos_left hM).mp (by
        nlinarith only [hyEq, hLp, hp])
      have hyp : y < p := (mul_lt_mul_iff_right₀ hM).mp (by
        nlinarith only [hyEq, hpL, hL, hp])
      have hPexact : (2 * p + 1) * (L - 1) + (2 * L + 1) * y =
          2 * p * L - 1 := by
        nlinarith only [hyEq]
      refine ⟨L - 1, y, false, by omega, by omega, hy0, hyp, ?_, ?_, ?_, ?_⟩ <;>
        simp <;> nlinarith only [hPexact, hp]

private theorem half_pow_facts (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    let L : ℤ := 2 ^ (a - 1)
    let p : ℤ := 2 ^ (b - 1)
    2 ≤ L ∧ L ≤ p ∧ (2 : ℤ) ^ a = 2 * L ∧
      (2 : ℤ) ^ b = 2 * p ∧ (2 : ℤ) ^ (b + 1) = 4 * p := by
  dsimp only
  have hL := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    (show 1 ≤ a - 1 by omega)
  have hLp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    (show a - 1 ≤ b - 1 by omega)
  have haE : (2 : ℤ) ^ a = 2 * 2 ^ (a - 1) := by
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  have hbE : (2 : ℤ) ^ b = 2 * 2 ^ (b - 1) := by
    calc
      (2 : ℤ) ^ b = 2 ^ ((b - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (b - 1) := by rw [pow_succ]; ring
  refine ⟨by simpa using hL, hLp, haE, hbE, ?_⟩
  rw [pow_succ, hbE]; ring

set_option maxHeartbeats 2000000 in
private theorem high_phase_values (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    let L : ℤ := 2 ^ (a - 1)
    let p : ℤ := 2 ^ (b - 1)
    let r := a + b
    let Q := 2 ^ (r - 1) + 2 ^ (b - 1)
    modulus r / 2 = 2 * p * L - 1 ∧
    modulus (r + 1) / 2 = 4 * p * L - 1 ∧
    (∀ i : Fin r,
      actualSource r Q i =
        (if i.val = 0 then -(2 * p * L - p - 1)
         else if i.val = a then -(2 * p * L - L - 1)
         else if i.val < a then (2 * p + 1) * 2 ^ (i.val - 1)
         else (2 * L + 1) * 2 ^ (i.val - a - 1)) ∧
      actualSource (r + 1) (2 * Q) i.castSucc =
        (if i.val = 0 then -(4 * p * L - 2 * p - 1)
         else if i.val = a then -(4 * p * L - L - 1)
         else if i.val < a then (4 * p + 1) * 2 ^ (i.val - 1)
         else (2 * L + 1) * 2 ^ (i.val - a - 1))) ∧
    actualSource (r + 1) (2 * Q) (Fin.last r) = 2 * p * L + p := by
  dsimp only
  let L : ℤ := 2 ^ (a - 1)
  let p : ℤ := 2 ^ (b - 1)
  let r := a + b
  let Q := 2 ^ (r - 1) + 2 ^ (b - 1)
  let N := modulus r
  let M := modulus (r + 1)
  obtain ⟨hL, _, haE, _, _⟩ := half_pow_facts a a ha le_rfl
  obtain ⟨hp, _, hbE, _, _⟩ := half_pow_facts b b hb le_rfl
  change 2 ≤ L at hL
  change 2 ≤ p at hp
  change (2 : ℤ) ^ a = 2 * L at haE
  change (2 : ℤ) ^ b = 2 * p at hbE
  have hPL : 2 * L ≤ p * L := mul_le_mul_of_nonneg_right hp (by omega)
  have hLP : 2 * p ≤ p * L := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hL (show 0 ≤ p by omega)
  have hrE : (2 : ℤ) ^ r = 4 * p * L := by
    dsimp only [r]
    rw [pow_add, haE, hbE]; ring
  have hhalf : (2 : ℤ) ^ (r - 1) = 2 * p * L := by
    have he : (2 : ℤ) ^ r = 2 ^ (r - 1) * 2 := by
      calc
        (2 : ℤ) ^ r = 2 ^ ((r - 1) + 1) :=
          congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by dsimp [r]; omega)
        _ = 2 ^ (r - 1) * 2 := by rw [pow_succ]
    nlinarith only [he, hrE]
  have hQ : (Q : ℤ) = 2 * p * L + p := by
    simp only [Q, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    rw [hhalf]
  have hN : N = 4 * p * L - 1 := by dsimp only [N, modulus]; rw [hrE]
  have hM : M = 8 * p * L - 1 := by
    dsimp only [M, modulus]
    rw [pow_succ, hrE]; ring
  have hNP : 0 < N := by rw [hN]; nlinarith
  have hMP : 0 < M := by rw [hM]; nlinarith
  have hN2 : N = 2 * (2 * p * L) - 1 := by rw [hN]; ring
  have hMrel : M = 2 * N + 1 := by rw [hM, hN]; ring
  have hNO : N % 2 = 1 := by rw [hN2]; omega
  have hMO : M % 2 = 1 := by rw [hMrel]; omega
  have hNH : N / 2 = 2 * p * L - 1 := by rw [hN2]; omega
  have hMH : M / 2 = N := by rw [hMrel]; omega
  have old_value (i : Fin r) (x m : ℤ)
      (hx : -(2 * p * L - 1) ≤ x ∧ x ≤ 2 * p * L - 1)
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
    by_cases hia : i.val = a
    · simp only [if_neg hi0, if_pos hia]
      change actualSource r Q i = -(2 * p * L - L - 1) ∧
        actualSource (r + 1) (2 * Q) i.castSucc = -(4 * p * L - L - 1)
      constructor
      · apply old_value i _ (L + 1) (by constructor <;> nlinarith)
        rw [hia, haE, hQ, hN]; ring
      · apply new_value i.castSucc _ (L + 1)
          (by rw [hN]; constructor <;> nlinarith)
        simp only [Fin.val_castSucc, hia, Nat.cast_mul, Nat.cast_ofNat, hQ]
        rw [haE, hM]; ring
    by_cases hia' : i.val < a
    · simp only [hi0, hia, hia', if_false, if_pos]
      let z : ℤ := 2 ^ (i.val - 1)
      have hz0 : 0 < z := by dsimp [z]; positivity
      have hz : 2 * z ≤ L := by
        have he := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (i.val - 1) + 1 ≤ a - 1 by omega)
        simpa only [pow_succ, mul_comm, L, z] using he
      have hiE : (2 : ℤ) ^ i.val = 2 * z := by
        calc
          (2 : ℤ) ^ i.val = 2 ^ ((i.val - 1) + 1) :=
            congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
          _ = 2 * z := by rw [pow_succ]; dsimp only [z]; ring
      have hOld : (2 * p + 1) * z ≤ 2 * p * L - 1 := by
        have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * p + 1 by omega)
        nlinarith
      have hNew : (4 * p + 1) * z ≤ N := by
        have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ 4 * p + 1 by omega)
        rw [hN]; nlinarith
      constructor
      · apply old_value i _ z
          (by change _ ≤ (2 * p + 1) * z ∧ _; constructor <;> nlinarith)
        rw [hiE, hQ, hN]; ring
      · apply new_value i.castSucc _ z
          (by change _ ≤ (4 * p + 1) * z ∧ _; rw [hN] at *; constructor <;> nlinarith)
        simp only [Fin.val_castSucc, Nat.cast_mul, Nat.cast_ofNat, hQ]
        rw [hiE, hM]; ring
    · simp only [hi0, hia, hia', if_false]
      let z : ℤ := 2 ^ (i.val - a - 1)
      have hz0 : 0 < z := by dsimp [z]; positivity
      have hz : 2 * z ≤ p := by
        have he := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (i.val - a - 1) + 1 ≤ b - 1 by
            have := i.isLt; change i.val < a + b at this; omega)
        simpa only [pow_succ, mul_comm, p, z] using he
      have hiE : (2 : ℤ) ^ i.val = 4 * L * z := by
        rw [show i.val = (a + 1) + (i.val - a - 1) by omega,
          pow_add, pow_succ, haE]
        dsimp only [z]; ring
      have hOld : (2 * L + 1) * z ≤ 2 * p * L - 1 := by
        have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * L + 1 by omega)
        nlinarith
      constructor
      · apply old_value i _ ((2 * L + 1) * z)
          (by change _ ≤ (2 * L + 1) * z ∧ _; constructor <;> nlinarith)
        rw [hiE, hQ, hN]; ring
      · apply new_value i.castSucc _ ((2 * L + 1) * z)
          (by rw [hN]; change _ ≤ (2 * L + 1) * z ∧ _; constructor <;> nlinarith)
        simp only [Fin.val_castSucc, Nat.cast_mul, Nat.cast_ofNat, hQ]
        rw [hiE, hM]; ring
  · apply new_value (Fin.last r) _ (Q : ℤ)
      (by rw [hN]; constructor <;> nlinarith)
    simp only [Fin.val_last, Nat.cast_mul, Nat.cast_ofNat]
    rw [hrE, hQ, hM]; ring

-- `reverse = true` selects label a's smaller pair (C,E); false keeps (B,D).
private def Mask (a b : ℕ) (reverse : Bool := false) : Prop :=
  let L : ℤ := 2 ^ (a - 1)
  let p : ℤ := 2 ^ (b - 1)
  ∃ (x y : ℤ) (e : Bool),
    let P := (2 * p + 1) * x + (2 * L + 1) * y
    let G := P + 2 * p * x
    0 ≤ x ∧ x < L ∧ 0 ≤ y ∧ y < p ∧
      2 * p * L - (if reverse then L else p) - 1 ≤ P ∧ P ≤ 2 * p * L - 1 ∧
      4 * p * L - (if reverse then L else 2 * p) - 1 ≤
        G + (if e then 2 * p * L + p else 0) ∧
      G + (if e then 2 * p * L + p else 0) ≤ 4 * p * L - 1

set_option maxHeartbeats 2000000 in
private theorem joint_implies_mask (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (reverse : Bool)
    (hbank : if reverse then 2 * (2 : ℤ) ^ (b - 1) ≤ 2 ^ (a - 1)
      else (2 : ℤ) ^ (a - 1) ≤ 2 ^ (b - 1))
    (sigma : List (Fin (a + b))) (cut : ℕ) (hcut : cut ≤ a + b)
    (hold : OriginalOrder (a + b) (2 ^ (a + b - 1) + 2 ^ (b - 1)) sigma)
    (hnew : OriginalOrder (a + b + 1)
      (2 * (2 ^ (a + b - 1) + 2 ^ (b - 1))) (earWord (a + b) sigma cut)) :
    Mask a b reverse := by
  classical
  let r := a + b
  let Q := 2 ^ (r - 1) + 2 ^ (b - 1)
  let L : ℤ := 2 ^ (a - 1)
  let p : ℤ := 2 ^ (b - 1)
  let f := actualSource r Q
  let g := fun i : Fin r => actualSource (r + 1) (2 * Q) i.castSucc
  change (if reverse then 2 * p ≤ L else L ≤ p) at hbank
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  obtain ⟨hH, hN, hvalues, hfresh⟩ := high_phase_values a b ha hb
  have hlen : sigma.length = r := by simpa only [r, List.length_finRange] using hold.1.length_eq
  have hzero : (⟨0, by dsimp [r]; omega⟩ : Fin r) ∈ sigma :=
    hold.1.mem_iff.mpr (by simp)
  obtain ⟨pre, i, post, hs, hi, hpre⟩ :=
    first_marked (fun j : Fin r => j.val = 0 ∨ j.val = a) sigma
      ⟨⟨0, by dsimp [r]; omega⟩, hzero, Or.inl rfl⟩
  have hnd : sigma.Nodup := hold.1.nodup_iff.mpr (List.nodup_finRange r)
  rw [hs] at hnd
  have hpreND : pre.Nodup := (List.nodup_append.mp hnd).1
  let S := pre.toFinset
  let xN := ∑ j ∈ S, laneWeight 1 (a - 1) j
  let yN := ∑ j ∈ S, laneWeight (a + 1) (b - 1) j
  let x : ℤ := xN
  let y : ℤ := yN
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hxL : x < L := by
    dsimp only [x, xN, L]
    exact_mod_cast lane_bound S 1 (a - 1)
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hyp : y < p := by
    dsimp only [y, yN, p]
    exact_mod_cast lane_bound S (a + 1) (b - 1)
  have hsum (v : Fin r → ℤ) : (pre.map v).sum = ∑ j ∈ S, v j :=
    (List.sum_toFinset v hpreND).symm
  have hlinear (j : Fin r) (hj : j ∈ S) :
      f j = (2 * p + 1) * (laneWeight 1 (a - 1) j : ℤ) +
        (2 * L + 1) * (laneWeight (a + 1) (b - 1) j : ℤ) ∧
      g j = (4 * p + 1) * (laneWeight 1 (a - 1) j : ℤ) +
        (2 * L + 1) * (laneWeight (a + 1) (b - 1) j : ℤ) := by
    have hpj := hpre j (List.mem_toFinset.mp hj)
    have hj0 : j.val ≠ 0 := fun he => hpj (Or.inl he)
    have hja : j.val ≠ a := fun he => hpj (Or.inr he)
    have hv := hvalues j
    by_cases hjl : j.val < a
    · have hc : 1 ≤ j.val ∧ j.val < 1 + (a - 1) := by omega
      have hc' : ¬(a + 1 ≤ j.val ∧ j.val < a + 1 + (b - 1)) := by omega
      simpa only [f, g, p, L, hj0, hja, hjl, if_false, if_pos, laneWeight,
        hc, hc', and_self, ite_true, ite_false, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero] using hv
    · have hc : ¬(1 ≤ j.val ∧ j.val < 1 + (a - 1)) := by omega
      have hc' : a + 1 ≤ j.val ∧ j.val < a + 1 + (b - 1) := by
        have := j.isLt; dsimp only [r] at this; omega
      simpa only [f, g, p, L, hj0, hja, hjl, if_false, if_pos, laneWeight,
        hc, hc', and_self, ite_true, ite_false, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero, mul_zero,
        zero_add, Nat.sub_sub] using hv
  have hcastX : (∑ j ∈ S, (laneWeight 1 (a - 1) j : ℤ)) = x := by
    simp only [x, xN, Nat.cast_sum]
  have hcastY : (∑ j ∈ S, (laneWeight (a + 1) (b - 1) j : ℤ)) = y := by
    simp only [y, yN, Nat.cast_sum]
  have hsumF : (pre.map f).sum = (2 * p + 1) * x + (2 * L + 1) * y := by
    rw [hsum]
    calc
      (∑ j ∈ S, f j) = ∑ j ∈ S,
          ((2 * p + 1) * (laneWeight 1 (a - 1) j : ℤ) +
           (2 * L + 1) * (laneWeight (a + 1) (b - 1) j : ℤ)) :=
        Finset.sum_congr rfl (fun j hj => (hlinear j hj).1)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hcastX, hcastY]
  have hsumG : (pre.map g).sum =
      ((2 * p + 1) * x + (2 * L + 1) * y) + 2 * p * x := by
    rw [hsum]
    calc
      (∑ j ∈ S, g j) = ∑ j ∈ S,
          ((4 * p + 1) * (laneWeight 1 (a - 1) j : ℤ) +
           (2 * L + 1) * (laneWeight (a + 1) (b - 1) j : ℤ)) :=
        Finset.sum_congr rfl (fun j hj => (hlinear j hj).2)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hcastX, hcastY]; ring
  have htake : sigma.take pre.length = pre := by rw [hs]; simp
  have htake' : sigma.take (pre.length + 1) = pre ++ [i] := by
    rw [hs]; simp [List.take_append]
  have hfi : f i ≤ -(2 * p * L - (if reverse then L else p) - 1) := by
    have hv := (hvalues i).1
    change f i = _ at hv
    rw [hv]
    rcases hi with hi | hi
    · simp only [if_pos hi]
      change -(2 * p * L - p - 1) ≤ _
      cases reverse <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at hbank ⊢ <;> omega
    · have hi0 : i.val ≠ 0 := by omega
      simp only [if_neg hi0, if_pos hi]
      change -(2 * p * L - L - 1) ≤ _
      cases reverse <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at hbank ⊢ <;> omega
  have hgi : g i ≤ -(4 * p * L - (if reverse then L else 2 * p) - 1) := by
    have hv := (hvalues i).2
    change g i = _ at hv
    rw [hv]
    rcases hi with hi | hi
    · simp only [if_pos hi]
      change -(4 * p * L - 2 * p - 1) ≤ _
      cases reverse <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at hbank ⊢ <;> omega
    · have hi0 : i.val ≠ 0 := by omega
      simp only [if_neg hi0, if_pos hi]
      change -(4 * p * L - L - 1) ≤ _
      cases reverse <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at hbank ⊢ <;> omega
  have hPH := (hold.2.2 pre.length).2
  rw [htake, hH] at hPH
  change (pre.map f).sum ≤ 2 * p * L - 1 at hPH
  rw [hsumF] at hPH
  have hBP := (hold.2.2 (pre.length + 1)).1
  rw [htake', List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton] at hBP
  change 0 ≤ (pre.map f).sum + f i at hBP
  rw [hsumF] at hBP
  have hB : 2 * p * L - (if reverse then L else p) - 1 ≤
      (2 * p + 1) * x + (2 * L + 1) * y := by
    linarith only [hBP, hfi]
  have hcut' : cut ≤ sigma.length := by omega
  by_cases hc : cut ≤ pre.length
  · -- The new prefix before the first negative contains fresh exactly once.
    have hUpper := (hnew.2.2 (pre.length + 1)).2
    have he := ear_prefix r sigma cut hcut' (actualSource (r + 1) (2 * Q))
      (pre.length + 1)
    rw [he] at hUpper
    have hc' : ¬ pre.length + 1 ≤ cut := by omega
    simp only [if_neg hc', Nat.add_sub_cancel] at hUpper
    rw [htake, hfresh, hN] at hUpper
    change (pre.map g).sum + (2 * p * L + p) ≤ 4 * p * L - 1 at hUpper
    rw [hsumG] at hUpper
    have hLower := (hnew.2.2 (pre.length + 2)).1
    have he' := ear_prefix r sigma cut hcut' (actualSource (r + 1) (2 * Q))
      (pre.length + 2)
    rw [he'] at hLower
    have hc'' : ¬ pre.length + 2 ≤ cut := by omega
    simp only [if_neg hc'', show pre.length + 2 - 1 = pre.length + 1 by omega] at hLower
    rw [htake', List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, hfresh] at hLower
    change 0 ≤ (pre.map g).sum + g i + (2 * p * L + p) at hLower
    rw [hsumG] at hLower
    refine ⟨x, y, true, hx0, hxL, hy0, hyp, hB, hPH, ?_, ?_⟩
    · change 4 * p * L - (if reverse then L else 2 * p) - 1 ≤
        ((2 * p + 1) * x + (2 * L + 1) * y) + 2 * p * x + (2 * p * L + p)
      linarith only [hLower, hgi]
    · simpa using hUpper
  · -- Before-first-negative old labels are unchanged when fresh is later.
    have hc' : pre.length + 1 ≤ cut := by omega
    have hLower := (hnew.2.2 (pre.length + 1)).1
    have he := ear_prefix r sigma cut hcut' (actualSource (r + 1) (2 * Q))
      (pre.length + 1)
    rw [he] at hLower
    simp only [if_pos hc', add_zero] at hLower
    rw [htake', List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton] at hLower
    change 0 ≤ (pre.map g).sum + g i at hLower
    rw [hsumG] at hLower
    have hUpper := (hnew.2.2 pre.length).2
    have he' := ear_prefix r sigma cut hcut' (actualSource (r + 1) (2 * Q)) pre.length
    rw [he'] at hUpper
    simp only [if_pos (show pre.length ≤ cut by omega), add_zero] at hUpper
    rw [htake, hN] at hUpper
    change (pre.map g).sum ≤ 4 * p * L - 1 at hUpper
    rw [hsumG] at hUpper
    refine ⟨x, y, false, hx0, hxL, hy0, hyp, hB, hPH, ?_, ?_⟩
    · change 4 * p * L - (if reverse then L else 2 * p) - 1 ≤
        ((2 * p + 1) * x + (2 * L + 1) * y) + 2 * p * x + 0
      linarith only [hLower, hgi]
    · simpa using hUpper

set_option maxHeartbeats 2000000 in
private theorem mask_implies_joint (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (reverse : Bool) (hm : Mask a b reverse) :
    ∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ (a + b - 1) + 2 ^ (b - 1)) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ (a + b - 1) + 2 ^ (b - 1)))
        (earWord (a + b) sigma cut) := by
  classical
  let r := a + b
  let Q := 2 ^ (r - 1) + 2 ^ (b - 1)
  let L : ℤ := 2 ^ (a - 1)
  let p : ℤ := 2 ^ (b - 1)
  let H := 2 * p * L - 1
  let N := 4 * p * L - 1
  let B := 2 * p * L - p - 1
  let C := 2 * p * L - L - 1
  let D := 4 * p * L - 2 * p - 1
  let A := 4 * p * L - L - 1
  let f := actualSource r Q
  let gn := actualSource (r + 1) (2 * Q)
  let g := fun i : Fin r => gn i.castSucc
  let alpha : Fin r := ⟨0, by dsimp [r]; omega⟩
  let beta : Fin r := ⟨a, by dsimp [r]; omega⟩
  let fresh : Fin (r + 1) := Fin.last r
  have hL : 2 ≤ L := (half_pow_facts a a ha le_rfl).1
  have hp : 2 ≤ p := (half_pow_facts b b hb le_rfl).1
  have hPL : 2 * L ≤ p * L := mul_le_mul_of_nonneg_right hp (by omega)
  have hLP : 2 * p ≤ p * L := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hL (show 0 ≤ p by omega)
  obtain ⟨hH, hN, hvalues, hfresh⟩ := high_phase_values a b ha hb
  change modulus r / 2 = H at hH
  change modulus (r + 1) / 2 = N at hN
  have hAlpha : f alpha = -B := by
    simpa only [f, alpha, Fin.val_mk, if_pos, B, p, L] using (hvalues alpha).1
  have hBeta : f beta = -C := by
    have hne : a ≠ 0 := by omega
    simpa only [f, beta, Fin.val_mk, hne, if_false, if_pos, C, p, L] using (hvalues beta).1
  have hAlphaNew : g alpha = -D := by
    simpa only [g, gn, alpha, Fin.val_mk, if_pos, D, p, L] using (hvalues alpha).2
  have hBetaNew : g beta = -A := by
    have hne : a ≠ 0 := by omega
    simpa only [g, gn, beta, Fin.val_mk, hne, if_false, if_pos, A, p, L] using (hvalues beta).2
  have hFresh : gn fresh = 2 * p * L + p := hfresh
  have hB0 : 0 ≤ (if reverse then C else B) := by
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> dsimp only [B, C] <;> nlinarith
  have hD0 : 0 ≤ (if reverse then A else D) := by
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> dsimp only [D, A] <;> nlinarith
  have hCcap : 0 ≤ (if reverse then B else C) ∧ (if reverse then B else C) ≤ H := by
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> dsimp only [B, C, H] <;> constructor <;> nlinarith
  have hAcap : 0 ≤ (if reverse then D else A) ∧ (if reverse then D else A) ≤ N := by
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> dsimp only [D, A, N] <;> constructor <;> nlinarith
  have habLabel : alpha ≠ beta := by
    intro he
    have he' := congrArg Fin.val he
    dsimp only [alpha, beta] at he'; omega
  obtain ⟨x, y, e, hx0, hxL, hy0, hyp, hBP, hPH, hDG, hGN⟩ := hm
  change x < L at hxL
  change y < p at hyp
  let P := (2 * p + 1) * x + (2 * L + 1) * y
  let G := P + 2 * p * x
  have hBP : (if reverse then C else B) ≤ P := by
    cases reverse <;> simpa only [Bool.false_eq_true, ↓reduceIte, B, C] using hBP
  change P ≤ H at hPH
  have hDG : (if reverse then A else D) ≤ G + (if e then 2 * p * L + p else 0) := by
    cases reverse <;> simpa only [Bool.false_eq_true, ↓reduceIte, A, D] using hDG
  change G + (if e then 2 * p * L + p else 0) ≤ N at hGN
  have hxNat : x.toNat < 2 ^ (a - 1) := by
    have hxCast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
    exact_mod_cast (show (x.toNat : ℤ) < (2 : ℤ) ^ (a - 1) by rw [hxCast]; exact hxL)
  have hyNat : y.toNat < 2 ^ (b - 1) := by
    have hyCast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
    exact_mod_cast (show (y.toNat : ℤ) < (2 : ℤ) ^ (b - 1) by rw [hyCast]; exact hyp)
  let maskU := DyadicPrefix.bitSubset (a - 1) x.toNat hxNat
  let maskV := DyadicPrefix.bitSubset (b - 1) y.toNat hyNat
  let labelU : Fin (a - 1) → Fin r := fun i => ⟨i.val + 1, by dsimp [r]; omega⟩
  let labelV : Fin (b - 1) → Fin r := fun i => ⟨a + 1 + i.val, by dsimp [r]; omega⟩
  have injU : Function.Injective labelU := by
    intro i j hij; apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp only [labelU] at he; omega
  have injV : Function.Injective labelV := by
    intro i j hij; apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp only [labelV] at he; omega
  have hU (i : Fin (a - 1)) :
      f (labelU i) = (2 * p + 1) * 2 ^ i.val ∧
      g (labelU i) = (4 * p + 1) * 2 ^ i.val := by
    have h0 : (labelU i).val ≠ 0 := by dsimp only [labelU]; omega
    have hA : (labelU i).val ≠ a := by have := i.isLt; dsimp only [labelU]; omega
    have hlt : (labelU i).val < a := by have := i.isLt; dsimp only [labelU]; omega
    simpa only [f, g, gn, h0, hA, hlt, if_false, if_pos, labelU, Fin.val_mk,
      Nat.add_sub_cancel, p, L] using hvalues (labelU i)
  have hV (i : Fin (b - 1)) :
      f (labelV i) = (2 * L + 1) * 2 ^ i.val ∧
      g (labelV i) = (2 * L + 1) * 2 ^ i.val := by
    have h0 : (labelV i).val ≠ 0 := by dsimp only [labelV]; omega
    have hA : (labelV i).val ≠ a := by dsimp only [labelV]; omega
    have hlt : ¬(labelV i).val < a := by dsimp only [labelV]; omega
    have hsub : (labelV i).val - a - 1 = i.val := by dsimp only [labelV]; omega
    simpa only [f, g, gn, h0, hA, hlt, if_false, hsub, p, L] using hvalues (labelV i)
  let EU := maskU.image labelU
  let EV := maskV.image labelV
  let ES := EU ∪ EV
  let FS := Finset.univ \ (ES ∪ {alpha, beta})
  let E := ES.toList
  let F := FS.toList
  have hdisj : Disjoint EU EV := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hj
    have he := congrArg Fin.val (hui.trans hvi.symm)
    have := u.isLt
    dsimp only [labelU, labelV] at he; omega
  have outside (i : Fin r) (hi : i ∈ ES) : i ≠ alpha ∧ i ≠ beta := by
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
      have := u.isLt
      constructor <;> intro he
      all_goals have he' := congrArg Fin.val he
      all_goals dsimp only [labelU, alpha, beta] at he'; omega
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      constructor <;> intro he
      all_goals have he' := congrArg Fin.val he
      all_goals dsimp only [labelV, alpha, beta] at he'; omega
  have hEa : alpha ∉ ES := fun hi => (outside alpha hi).1 rfl
  have hEb : beta ∉ ES := fun hi => (outside beta hi).2 rfl
  have hperm : (E ++ F ++ [alpha, beta]).Perm (List.finRange r) :=
    split_perm ES alpha beta habLabel hEa hEb
  have hmaskU : (∑ i ∈ maskU, (2 : ℤ) ^ i.val) = x := by
    have hh : (∑ i ∈ maskU, (2 : ℤ) ^ i.val) = (x.toNat : ℤ) := by
      exact_mod_cast DyadicPrefix.bit_subset_sum hxNat
    exact hh.trans (Int.toNat_of_nonneg hx0)
  have hmaskV : (∑ i ∈ maskV, (2 : ℤ) ^ i.val) = y := by
    have hh : (∑ i ∈ maskV, (2 : ℤ) ^ i.val) = (y.toNat : ℤ) := by
      exact_mod_cast DyadicPrefix.bit_subset_sum hyNat
    exact hh.trans (Int.toNat_of_nonneg hy0)
  have hEold : (E.map f).sum = P := by
    change (ES.toList.map f).sum = P
    rw [← List.sum_toFinset _ ES.nodup_toList, Finset.toList_toFinset]
    change (∑ i ∈ EU ∪ EV, f i) = P
    rw [Finset.sum_union hdisj]
    dsimp only [EU, EV]
    rw [Finset.sum_image (fun i _ j _ hij => injU hij),
      Finset.sum_image (fun i _ j _ hij => injV hij)]
    simp_rw [show ∀ i, f (labelU i) = (2 * p + 1) * 2 ^ i.val from fun i => (hU i).1,
      show ∀ i, f (labelV i) = (2 * L + 1) * 2 ^ i.val from fun i => (hV i).1]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hmaskU, hmaskV]
  have hEnew : (E.map g).sum = G := by
    change (ES.toList.map g).sum = G
    rw [← List.sum_toFinset _ ES.nodup_toList, Finset.toList_toFinset]
    change (∑ i ∈ EU ∪ EV, g i) = G
    rw [Finset.sum_union hdisj]
    dsimp only [EU, EV]
    rw [Finset.sum_image (fun i _ j _ hij => injU hij),
      Finset.sum_image (fun i _ j _ hij => injV hij)]
    simp_rw [show ∀ i, g (labelU i) = (4 * p + 1) * 2 ^ i.val from fun i => (hU i).2,
      show ∀ i, g (labelV i) = (2 * L + 1) * 2 ^ i.val from fun i => (hV i).2]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hmaskU, hmaskV]
    dsimp only [G, P]; ring
  have pos (i : Fin r) (hi : i ≠ alpha ∧ i ≠ beta) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hi0 : i.val ≠ 0 := fun he => hi.1 (Fin.ext he)
    have hia : i.val ≠ a := fun he => hi.2 (Fin.ext he)
    have hv := hvalues i
    by_cases hlt : i.val < a
    · simp only [hi0, hia, hlt, if_false, if_pos] at hv
      change f i = _ ∧ g i = _ at hv
      rw [hv.1, hv.2]; constructor <;> positivity
    · simp only [hi0, hia, hlt, if_false] at hv
      change f i = _ ∧ g i = _ at hv
      rw [hv.1, hv.2]; constructor <;> positivity
  have Epos : ∀ i ∈ E, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; exact pos i (outside i (Finset.mem_toList.mp hi))
  have Fpos : ∀ i ∈ F, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hh := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)).2
    apply pos i
    constructor <;> intro he <;> apply hh <;> simp [he]
  -- Reverse uses beta FIRST and alpha LAST; all other Fin labels are unchanged.
  let first := if reverse then beta else alpha
  let last := if reverse then alpha else beta
  have hFirst : f first = -(if reverse then C else B) := by
    cases reverse <;> simp only [first, Bool.false_eq_true, ↓reduceIte, hAlpha, hBeta]
  have hLast : f last = -(if reverse then B else C) := by
    cases reverse <;> simp only [last, Bool.false_eq_true, ↓reduceIte, hAlpha, hBeta]
  have hFirstNew : g first = -(if reverse then A else D) := by
    cases reverse <;> simp only [first, Bool.false_eq_true, ↓reduceIte, hAlphaNew, hBetaNew]
  have hLastNew : g last = -(if reverse then D else A) := by
    cases reverse <;> simp only [last, Bool.false_eq_true, ↓reduceIte, hAlphaNew, hBetaNew]
  let sigma := E ++ [first] ++ F ++ [last]
  have hsperm : sigma.Perm (List.finRange r) := by
    have hswap : sigma.Perm (E ++ F ++ [first, last]) := by
      simpa only [sigma, List.append_assoc, List.cons_append, List.nil_append] using
        ((List.perm_append_comm (l₁ := [first]) (l₂ := F)).append_right [last]).append_left E
    have hends : [first, last].Perm [alpha, beta] := by
      cases reverse with
      | false => exact List.Perm.refl _
      | true => exact List.Perm.swap alpha beta []
    have hends' : (E ++ F ++ [first, last]).Perm (E ++ F ++ [alpha, beta]) := by
      simpa only [List.append_assoc] using (hends.append_left F).append_left E
    exact hswap.trans (hends'.trans hperm)
  have hOldZero : (sigma.map f).sum = 0 :=
    source_total (show 0 < r by dsimp [r]; omega) sigma hsperm
  have hs : InStrip f H 0 sigma := by
    apply two_blocks f H E F first last (fun i hi => (Epos i hi).1)
      (fun i hi => (Fpos i hi).1)
    · simpa only [sigma, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, add_assoc] using hOldZero
    · rw [hEold]; exact ⟨hB0.trans hBP, hPH⟩
    · rw [hEold, hFirst]; linarith only [hBP]
    · rw [hLast]; simpa only [neg_neg] using hCcap
  let EN := E.map Fin.castSucc
  let FN := F.map Fin.castSucc
  have hEN : (EN.map gn).sum = G := by
    change ((E.map Fin.castSucc).map gn).sum = G
    rw [List.map_map]; exact hEnew
  have ENpos : ∀ i ∈ EN, 0 ≤ gn i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact (Epos j hj).2
  have FNpos : ∀ i ∈ FN, 0 ≤ gn i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact (Fpos j hj).2
  have freshPos : 0 ≤ gn fresh := by rw [hFresh]; positivity
  have complete (cut : ℕ) (hc : cut ≤ r)
      (hn : InStrip gn N 0 (earWord r sigma cut)) :
      ∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
        OriginalOrder (a + b) (2 ^ (a + b - 1) + 2 ^ (b - 1)) sigma ∧
        OriginalOrder (a + b + 1) (2 * (2 ^ (a + b - 1) + 2 ^ (b - 1)))
          (earWord (a + b) sigma cut) := by
    have hnp := inserted_perm sigma cut hsperm
    refine ⟨sigma, cut, hc, ⟨hsperm, hOldZero, ?_⟩,
      ⟨hnp, source_total (show 0 < r + 1 by omega) _ hnp, ?_⟩⟩
    · intro n
      change 0 ≤ ((sigma.take n).map f).sum ∧
        ((sigma.take n).map f).sum ≤ modulus r / 2
      rw [hH]
      simpa only [zero_add] using inStrip_prefix hs n
    · intro n
      change 0 ≤ (((earWord r sigma cut).take n).map gn).sum ∧
        (((earWord r sigma cut).take n).map gn).sum ≤ modulus (r + 1) / 2
      rw [hN]
      simpa only [zero_add] using inStrip_prefix hn n
  cases e with
  | true =>
    simp only [ite_true] at hDG hGN
    have hc : E.length ≤ r := by
      have hh := hsperm.length_eq
      simp only [sigma, List.length_append, List.length_singleton,
        List.length_finRange] at hh
      omega
    have hear : earWord r sigma E.length =
        (EN ++ [fresh]) ++ [first.castSucc] ++ FN ++ [last.castSucc] := by
      simp only [sigma, List.append_assoc]
      unfold earWord
      rw [List.take_left, List.drop_left]
      simp only [EN, FN, fresh, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
    apply complete E.length hc
    have hnp := inserted_perm sigma E.length hsperm
    have hz := source_total (t := 2 * Q) (show 0 < r + 1 by omega) _ hnp
    rw [hear] at hz ⊢
    apply two_blocks gn N (EN ++ [fresh]) FN first.castSucc last.castSucc
      (by
        intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact ENpos i hi
        · have he := List.mem_singleton.mp hi
          subst i
          exact freshPos)
      FNpos
    · simpa only [List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, add_assoc] using hz
    · simp only [List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, hEN, hFresh]
      exact ⟨hD0.trans hDG, hGN⟩
    · simp only [List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, hEN, hFresh]
      change 0 ≤ G + (2 * p * L + p) + g first
      rw [hFirstNew]; linarith only [hDG]
    · change 0 ≤ -g last ∧ -g last ≤ N
      rw [hLastNew]; simpa only [neg_neg] using hAcap
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hDG hGN
    let before := E ++ [first] ++ F
    have hsigma : sigma = before ++ [last] := by
      simp only [sigma, before, List.append_assoc]
    have hc : before.length ≤ r := by
      have hh := hsperm.length_eq
      rw [hsigma] at hh
      simp only [List.length_append, List.length_singleton, List.length_finRange] at hh
      omega
    have hear : earWord r sigma before.length =
        EN ++ [first.castSucc] ++ (FN ++ [fresh]) ++ [last.castSucc] := by
      rw [hsigma]
      unfold earWord
      rw [List.take_left, List.drop_left]
      simp only [before, EN, FN, fresh, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
    apply complete before.length hc
    have hnp := inserted_perm sigma before.length hsperm
    have hz := source_total (t := 2 * Q) (show 0 < r + 1 by omega) _ hnp
    rw [hear] at hz ⊢
    apply two_blocks gn N EN (FN ++ [fresh]) first.castSucc last.castSucc ENpos
      (by
        intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact FNpos i hi
        · have he := List.mem_singleton.mp hi
          subst i
          exact freshPos)
    · simpa only [List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, add_assoc] using hz
    · rw [hEN]; exact ⟨hD0.trans hDG, hGN⟩
    · rw [hEN]
      change 0 ≤ G + g first
      rw [hFirstNew]; linarith only [hDG]
    · change 0 ≤ -g last ∧ -g last ≤ N
      rw [hLastNew]; simpa only [neg_neg] using hAcap

/-- Complete physical high-phase classification on the original domain.
Every old Fin label appears once, and the same sigma and literal cut serve
both OriginalOrder clauses, including their zero sums and all natural takes.
-/
theorem actualSource_high_phase_two_negative_joint_iff (a b : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) :
    (∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ (a + b - 1) + 2 ^ (b - 1)) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ (a + b - 1) + 2 ^ (b - 1)))
        (earWord (a + b) sigma cut)) ↔
      ((2 : ℕ) ^ a + 1) ∣ (2 ^ b + 1) ∨ (2 ^ a + 1) ∣ (2 ^ (b + 1) + 1) := by
  let L : ℤ := 2 ^ (a - 1)
  let p : ℤ := 2 ^ (b - 1)
  obtain ⟨hL, hLp, haE, hbE, hbE'⟩ := half_pow_facts a b ha hab
  have hm : Mask a b ↔ (2 * L + 1) ∣ (2 * p + 1) ∨
      (2 * L + 1) ∣ (4 * p + 1) := by
    exact exact_two_bank_mask_criterion p L hL hLp
  have hd : ((2 * L + 1) ∣ (2 * p + 1) ∨ (2 * L + 1) ∣ (4 * p + 1)) ↔
      ((2 : ℕ) ^ a + 1) ∣ (2 ^ b + 1) ∨ (2 ^ a + 1) ∣ (2 ^ (b + 1) + 1) := by
    change ((2 * (2 : ℤ) ^ (a - 1) + 1) ∣ (2 * (2 : ℤ) ^ (b - 1) + 1) ∨
      (2 * (2 : ℤ) ^ (a - 1) + 1) ∣ (4 * (2 : ℤ) ^ (b - 1) + 1)) ↔ _
    rw [← haE, ← hbE, ← hbE']
    norm_cast
  constructor
  · rintro ⟨sigma, cut, hc, ho, hn⟩
    exact hd.mp (hm.mp (joint_implies_mask a b ha (ha.trans hab) false hLp sigma cut hc ho hn))
  · intro h
    exact mask_implies_joint a b ha (ha.trans hab) false (hm.mpr (hd.mpr h))

end D5.S3.Combinatorics.Circle.HighPhaseTwoNegativeClassification



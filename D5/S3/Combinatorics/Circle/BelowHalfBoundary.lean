/- Explicit physical-label construction.
Fixed compatible library pin: 1d7563a7afc3c179b50e46b14c30e3d8338e5aa5.
The centered-value setup is adapted from the authorized pre-dispatch candidate;
the selection layer follows the four cases of the advisory Pro conclusion.
Native validation evidence is recorded separately from this candidate source. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.TwoNegativeJointLift

/-! Explicit physical-label below-half boundary and uniform common-cut transport. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.BelowHalfBoundary
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private two_blocks split_perm source_total inserted_perm from
  D5.S3.Combinatorics.Circle.TwoNegativeJointLift

private def ascending {r : ℕ} (S : Finset (Fin r)) : List (Fin r) :=
  (List.finRange r).filter (fun i => i ∈ S)

private theorem ascending_perm {r : ℕ} (S : Finset (Fin r)) :
    (ascending S).Perm S.toList := by
  classical
  apply (List.perm_ext_iff_of_nodup
    ((List.nodup_finRange r).filter _) S.nodup_toList).mpr
  intro i
  simp

private theorem ascending_sum {r : ℕ} (S : Finset (Fin r)) (f : Fin r → ℤ) :
    ((ascending S).map f).sum = ∑ i ∈ S, f i := by
  rw [((ascending_perm S).map f).sum_eq,
    ← List.sum_toFinset _ S.nodup_toList, Finset.toList_toFinset]

private def window (r lo n : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i => lo ≤ i.val ∧ i.val < lo + n)

private theorem pow_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℤ) ^ j) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

private theorem window_sum (r lo n : ℕ) (h : lo + n ≤ r)
    (f : Fin r → ℤ) (c : ℤ)
    (hf : ∀ i ∈ window r lo n, f i = c * 2 ^ (i.val - lo)) :
    (∑ i ∈ window r lo n, f i) = c * (2 ^ n - 1) := by
  classical
  calc
    _ = ∑ j ∈ Finset.range n, c * (2 : ℤ) ^ j := by
      refine Finset.sum_bij (fun i _ => i.val - lo) ?_ ?_ ?_ ?_
      · intro i hi
        have hh : lo ≤ i.val ∧ i.val < lo + n := by simpa [window] using hi
        exact Finset.mem_range.mpr (by omega)
      · intro i hi j hj hij
        have hi' : lo ≤ i.val ∧ i.val < lo + n := by simpa [window] using hi
        have hj' : lo ≤ j.val ∧ j.val < lo + n := by simpa [window] using hj
        apply Fin.ext; omega
      · intro j hj
        have hj' := Finset.mem_range.mp hj
        refine ⟨⟨lo + j, by omega⟩, ?_, ?_⟩
        · simpa [window] using hj'
        · simp
      · intro i hi; exact hf i hi
    _ = c * (2 ^ n - 1) := by rw [← Finset.mul_sum, pow_sum]

private theorem half_pow_facts (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    let L : ℤ := 2 ^ (a - 1)
    let p : ℤ := 2 ^ (b - 1)
    2 ≤ L ∧ 2 ≤ p ∧ (2 : ℤ) ^ a = 2 * L ∧
      (2 : ℤ) ^ b = 2 * p ∧
      (2 : ℤ) ^ (a - 2) * 2 = L ∧
      (2 : ℤ) ^ (b - 2) * 2 = p := by
  dsimp only
  have hL := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    (show 1 ≤ a - 1 by omega)
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    (show 1 ≤ b - 1 by omega)
  have haE : (2 : ℤ) ^ a = 2 * 2 ^ (a - 1) := by
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 1) + 1) := congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  have hbE : (2 : ℤ) ^ b = 2 * 2 ^ (b - 1) := by
    calc
      (2 : ℤ) ^ b = 2 ^ ((b - 1) + 1) := congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (b - 1) := by rw [pow_succ]; ring
  have ha2 : (2 : ℤ) ^ (a - 2) * 2 = 2 ^ (a - 1) := by
    rw [show a - 1 = (a - 2) + 1 by omega, pow_succ]
  have hb2 : (2 : ℤ) ^ (b - 2) * 2 = 2 ^ (b - 1) := by
    rw [show b - 1 = (b - 2) + 1 by omega, pow_succ]
  refine ⟨by simpa using hL, by simpa using hp, haE, hbE, ha2, hb2⟩

set_option maxHeartbeats 2000000 in
-- The complete centered-representative and four-case construction shares this budget.
private theorem boundary_joint (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ (a + b - 2) + 2 ^ (b - 2)) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ (a + b - 2) + 2 ^ (b - 2)))
        (earWord (a + b) sigma cut) := by
  classical
  let r := a + b
  let L : ℤ := 2 ^ (a - 1)
  let p : ℤ := 2 ^ (b - 1)
  let q : ℤ := 2 ^ (r - 2) + 2 ^ (b - 2)
  let H := 2 * p * L - 1
  let N := 4 * p * L - 1
  let B := 2 * p * L - p - 1
  let C := 2 * p * L - L - 1
  let D := 4 * p * L - 2 * p - 1
  let E := 4 * p * L - L - 1
  let f := actualSource r (2 ^ (r - 2) + 2 ^ (b - 2))
  let gn := actualSource (r + 1) (2 * (2 ^ (r - 2) + 2 ^ (b - 2)))
  let g := fun i : Fin r => gn i.castSucc
  let one : Fin r := ⟨1, by dsimp [r]; omega⟩
  let atA : Fin r := ⟨a + 1, by dsimp [r]; omega⟩
  let fresh : Fin (r + 1) := Fin.last r
  obtain ⟨hL, hp, haE, hbE, ha2, hb2⟩ := half_pow_facts a b ha hb
  change 2 ≤ L at hL
  change 2 ≤ p at hp
  change (2 : ℤ) ^ a = 2 * L at haE
  change (2 : ℤ) ^ b = 2 * p at hbE
  have hprodL : 2 * L ≤ p * L :=
    mul_le_mul_of_nonneg_right hp (show 0 ≤ L by omega)
  have hprodp : 2 * p ≤ p * L := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hL (show 0 ≤ p by omega)
  have hpow : (2 : ℤ) ^ (r - 2) = p * L := by
    have he : r - 2 = (a - 1) + (b - 1) := by dsimp [r]; omega
    dsimp [p, L]
    rw [he, pow_add]
    ring
  have hpowb : (2 : ℤ) ^ (b - 2) = p / 2 := by
    have := hb2
    dsimp [p] at this ⊢
    omega
  have hpHalf : 2 * (p / 2) = p := by
    have hh := hb2
    change (2 : ℤ) ^ (b - 2) * 2 = p at hh
    omega
  have hhalfProduct : 2 * L * (p / 2) = p * L := by
    linear_combination L * hpHalf
  have hq : q = p * L + p / 2 := by
    dsimp [q]
    rw [hpow, hpowb]
  have hqv : q = p * L + (2 : ℤ) ^ (b - 2) := by
    rw [hq, hpowb]
  have hqNat : ((2 ^ (r - 2) + 2 ^ (b - 2) : ℕ) : ℤ) = q := by simp [q]
  have hrpow : (2 : ℤ) ^ r = 4 * p * L := by
    dsimp [r]
    rw [pow_add, haE, hbE]
    ring
  have hN : modulus r = 4 * p * L - 1 := by
    dsimp [modulus]
    rw [hrpow]
  have hM : modulus (r + 1) = 8 * p * L - 1 := by
    dsimp [modulus]
    rw [pow_succ, hrpow]
    ring
  obtain ⟨hNpos, hNodd⟩ := TwoRunSource.modulus_positive_odd r (by dsimp [r]; omega)
  obtain ⟨hMpos, hModd⟩ := TwoRunSource.modulus_positive_odd (r + 1) (by omega)
  have hHalfOld : modulus r = 2 * H + 1 := by rw [hN]; dsimp only [H]; ring
  have hHalfNew : modulus (r + 1) = 2 * N + 1 := by rw [hM]; dsimp only [N]; ring
  have hNH : modulus r / 2 = H := by omega
  have hMH : modulus (r + 1) / 2 = N := by omega
  have old_value (i : Fin r) (x m : ℤ)
      (hx : -(modulus r / 2) ≤ x ∧ x ≤ modulus r / 2)
      (he : (2 : ℤ) ^ i.val * (q : ℤ) = x + m * modulus r) : f i = x := by
    apply centered_unique hNpos hNodd (centered_bounds hNpos hNodd _)
      (by simpa [hNH] using hx)
    change centered (modulus r) ((2 : ℤ) ^ i.val *
      ((2 ^ (r - 2) + 2 ^ (b - 2) : ℕ) : ℤ)) % modulus r = x % modulus r
    rw [hqNat]
    rw [centered_mod, he]
    simp [Int.add_emod]
  have new_value (i : Fin (r + 1)) (x m : ℤ)
      (hx : -N ≤ x ∧ x ≤ N)
      (he : (2 : ℤ) ^ i.val * ((2 * q : ℤ)) = x + m * modulus (r + 1)) : gn i = x := by
    apply centered_unique hMpos hModd (centered_bounds hMpos hModd _)
      (by simpa [hMH] using hx)
    change centered (modulus (r + 1)) ((2 : ℤ) ^ i.val *
      ((2 * (2 ^ (r - 2) + 2 ^ (b - 2)) : ℕ) : ℤ)) % modulus (r + 1) = x % modulus (r + 1)
    rw [show ((2 * (2 ^ (r - 2) + 2 ^ (b - 2)) : ℕ) : ℤ) = 2 * q by
      norm_num [hqNat]]
    rw [centered_mod, he]
    simp [Int.add_emod]
  have hvalues (i : Fin r) :
      f i = (if i.val = 0 then q else if i.val = 1 then -B
        else if i.val < a + 1 then (2 * p + 1) * 2 ^ (i.val - 2)
        else if i.val = a + 1 then -C else (2 * L + 1) * 2 ^ (i.val - a - 2)) ∧
      g i = (if i.val = 0 then 2 * q else if i.val = 1 then -D
        else if i.val < a + 1 then (4 * p + 1) * 2 ^ (i.val - 2)
        else if i.val = a + 1 then -E else (2 * L + 1) * 2 ^ (i.val - a - 2)) := by
    by_cases h0 : i.val = 0
    · simp only [h0, ite_true]
      constructor
      · apply old_value i _ 0 (by
          rw [hNH, hq]
          dsimp only [H]
          constructor <;> linarith only [hp, hprodp, hpHalf])
        simp [h0]
      · apply new_value i.castSucc _ 0 (by
          rw [hq]
          dsimp only [N]
          constructor <;> linarith only [hp, hprodp, hpHalf])
        simp [h0]
    by_cases h1 : i.val = 1
    · simp only [h1, show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true]
      constructor
      · apply old_value i _ 1 (by
          rw [hNH]
          dsimp only [H, B]
          constructor <;> linarith only [hp, hprodp])
        rw [show (2 : ℤ) ^ i.val = 2 by simp [h1], hq, hN]
        dsimp [B]
        linear_combination hpHalf
      · apply new_value i.castSucc _ 1 (by
          dsimp only [N, D]
          constructor <;> linarith only [hp, hprodp])
        simp only [Fin.val_castSucc]
        rw [show (2 : ℤ) ^ i.val = 2 by simp [h1], hq, hM]
        dsimp [D]
        linear_combination 2 * hpHalf
    by_cases hlt : i.val < a + 1
    · have hi2 : 2 ≤ i.val := by omega
      simp only [h0, h1, ite_false, hlt, ite_true]
      let z : ℤ := 2 ^ (i.val - 2)
      have hz : 0 < z := by dsimp [z]; positivity
      have hiE : (2 : ℤ) ^ i.val = 4 * z := by
        rw [show i.val = (i.val - 2) + 2 by omega, pow_add]
        dsimp [z]
        norm_num [mul_comm]
      have hzL : 2 * z ≤ L := by
        have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (i.val - 2) + 1 ≤ a - 1 by omega)
        simpa only [pow_succ, z, L, mul_comm] using hh
      have hpz : 2 * p * z ≤ p * L := by
        calc
          2 * p * z = p * (2 * z) := by ring
          _ ≤ p * L := mul_le_mul_of_nonneg_left hzL (show 0 ≤ p by omega)
      have hpL : 2 * L ≤ p * L :=
        mul_le_mul_of_nonneg_right hp (show 0 ≤ L by omega)
      have hOldBank : -H ≤ (2 * p + 1) * z ∧ (2 * p + 1) * z ≤ H := by
        have ht : 0 ≤ (2 * p + 1) * z := by positivity
        dsimp only [H]; constructor <;> linarith only [ht, hpz, hzL, hpL, hL]
      have hNewBank : -N ≤ (4 * p + 1) * z ∧ (4 * p + 1) * z ≤ N := by
        have ht : 0 ≤ (4 * p + 1) * z := by positivity
        dsimp only [N]; constructor <;> linarith only [ht, hpz, hzL, hpL, hL]
      constructor
      · apply old_value i _ z (by simpa only [hNH] using hOldBank)
        rw [hiE, hq, hN]
        linear_combination 2 * z * hpHalf
      · apply new_value i.castSucc _ z hNewBank
        simp only [Fin.val_castSucc]
        rw [hiE, hq, hM]
        linear_combination 4 * z * hpHalf
    by_cases ha1 : i.val = a + 1
    · simp only [ha1, show a + 1 ≠ 0 by omega, show a + 1 ≠ 1 by omega,
        Nat.lt_irrefl, ite_false, ite_true]
      constructor
      · apply old_value i _ (L + 1) (by
          rw [hNH]
          dsimp only [H, C]
          constructor <;> linarith only [hL, hprodL])
        rw [ha1, pow_succ, haE, hq, hN]
        dsimp [C]
        linear_combination 2 * L * hpHalf
      · apply new_value i.castSucc _ (L + 1) (by
          dsimp only [N, E]
          constructor <;> linarith only [hL, hprodL])
        simp only [Fin.val_castSucc]
        rw [ha1, pow_succ, haE, hq, hM]
        dsimp [E]
        linear_combination 4 * L * hpHalf
    · simp only [h0, h1, hlt, ite_false, ha1, ite_false]
      let z : ℤ := 2 ^ (i.val - a - 2)
      have hz : 0 < z := by dsimp [z]; positivity
      have hiE : (2 : ℤ) ^ i.val = 8 * L * z := by
        calc
          (2 : ℤ) ^ i.val = 2 ^ ((a - 1) + 3 + (i.val - a - 2)) :=
            congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
          _ = 8 * L * z := by
            dsimp only [L, z]
            rw [pow_add, pow_add]
            norm_num <;> ring
      have hltb : i.val - a - 2 < b - 2 := by
        have hi := i.isLt
        dsimp [r] at hi
        omega
      have hzbound : 2 * z ≤ p / 2 := by
        have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (i.val - a - 2) + 1 ≤ b - 2 by omega)
        rw [hpowb] at hh
        simpa only [pow_succ, z, mul_comm] using hh
      have hbank : 0 ≤ (2 * L + 1) * z ∧ (2 * L + 1) * z ≤ H := by
        have hh := mul_le_mul_of_nonneg_left
          (show z ≤ p / 2 - 1 by omega) (show 0 ≤ 2 * L + 1 by omega)
        dsimp [H]
        constructor
        · positivity
        · linarith only [hh, hhalfProduct, hpHalf, hprodp, hL, hp]
      constructor
      · apply old_value i _ ((2 * L + 1) * z) (by rw [hNH]; constructor <;> linarith only [hbank.1, hbank.2])
        rw [hiE, hq, hN]
        linear_combination 4 * L * z * hpHalf
      · apply new_value i.castSucc _ ((2 * L + 1) * z) (by
          have hHN : H ≤ N := by dsimp only [H, N]; linarith only [hprodL, hL]
          constructor <;> linarith only [hHN, hbank.1, hbank.2])
        simp only [Fin.val_castSucc]
        rw [hiE, hq, hM]
        linear_combination 8 * L * z * hpHalf
  have hFresh : gn fresh = q := by
    apply new_value fresh q q (by
      rw [hq]
      dsimp only [N]
      constructor <;> linarith only [hp, hprodp, hpHalf])
    change (2 : ℤ) ^ r * (2 * q) = q + q * modulus (r + 1)
    rw [show (2 : ℤ) ^ r = 4 * p * L by exact hrpow, hq, hM]
    ring

  let zero : Fin r := ⟨0, by dsimp [r]; omega⟩
  let top : Fin r := ⟨a, by dsimp [r]; omega⟩
  have hne : one ≠ atA := by
    intro h; have hh := congrArg Fin.val h; dsimp [one, atA] at hh; omega
  have hneg : f one = -B ∧ g one = -D ∧ f atA = -C ∧ g atA = -E := by
    have h1 := hvalues one
    have hA := hvalues atA
    simp [one] at h1
    simp [atA, show a ≠ 0 by omega] at hA
    exact ⟨h1.1, h1.2, hA.1, hA.2⟩
  have hzero : f zero = q ∧ g zero = 2 * q := by simpa [zero] using hvalues zero
  have hmag : (0 ≤ B ∧ B ≤ H) ∧ (0 ≤ C ∧ C ≤ H) ∧
      (0 ≤ D ∧ D ≤ N) ∧ (0 ≤ E ∧ E ≤ N) := by
    have hPL := mul_le_mul_of_nonneg_right hp (show 0 ≤ L by omega)
    have hLP := mul_le_mul_of_nonneg_left hL (show 0 ≤ p by omega)
    dsimp only [B, C, D, E, H, N]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      linarith only [hL, hp, hPL, hLP]
  have hBdef : B = H - p := by dsimp only [B, H]; ring
  have hCdef : C = H - L := by dsimp only [C, H]; ring
  have hDdef : D = N - 2 * p := by dsimp only [D, N]; ring
  have hEdef : E = N - L := by dsimp only [E, N]; ring
  have pos (i : Fin r) (hi : i ≠ one ∧ i ≠ atA) : 0 ≤ f i ∧ 0 ≤ g i := by
    have h1 : i.val ≠ 1 := fun h => hi.1 (Fin.ext h)
    have hA : i.val ≠ a + 1 := fun h => hi.2 (Fin.ext h)
    rw [(hvalues i).1, (hvalues i).2]
    simp only [h1, hA, ite_false]
    split_ifs <;> constructor <;> positivity

  /- All interior-prefix and zero-total arguments are supplied by the pinned
     library. The only input specific to a case is its physical S and two seams. -/
  have build (S : Finset (Fin r)) (rev before : Bool)
      (hS : ∀ i ∈ S, i ≠ one ∧ i ≠ atA)
      (hF : (if rev then C else B) ≤ ∑ i ∈ S, f i ∧ (∑ i ∈ S, f i) ≤ H)
      (hG : (if rev then E else D) ≤
          (∑ i ∈ S, g i) + (if before then q else 0) ∧
        (∑ i ∈ S, g i) + (if before then q else 0) ≤ N) :
      ∃ sigma : List (Fin r), ∃ cut : ℕ, cut ≤ r ∧
        OriginalOrder r (2 ^ (r - 2) + 2 ^ (b - 2)) sigma ∧
        OriginalOrder (r + 1) (2 * (2 ^ (r - 2) + 2 ^ (b - 2)))
          (earWord r sigma cut) := by
    let alpha := if rev then atA else one
    let beta := if rev then one else atA
    let FS := Finset.univ \ (S ∪ {alpha, beta})
    let E0 := ascending S
    let F0 := ascending FS
    let EN := E0.map Fin.castSucc
    let FN := F0.map Fin.castSucc
    let sigma := E0 ++ [alpha] ++ F0 ++ [beta]
    have hab : alpha ≠ beta := by cases rev <;> simp [alpha, beta, hne, Ne.symm hne]
    have haS : alpha ∉ S := by
      intro hi; have hh := hS alpha hi; cases rev <;> simp_all [alpha]
    have hbS : beta ∉ S := by
      intro hi; have hh := hS beta hi; cases rev <;> simp_all [beta]
    have hbase : (E0 ++ F0 ++ [alpha, beta]).Perm (List.finRange r) :=
      (((ascending_perm S).append (ascending_perm FS)).append_right [alpha, beta]).trans
        (split_perm S alpha beta hab haS hbS)
    have hp : sigma.Perm (List.finRange r) := by
      have hs := ((List.perm_append_comm (l₁ := [alpha]) (l₂ := F0)).append_right
        [beta]).append_left E0
      have hswap : sigma.Perm (E0 ++ F0 ++ [alpha, beta]) := by
        simpa [sigma, List.append_assoc] using hs
      exact hswap.trans hbase
    have hEa : ∀ i ∈ E0, 0 ≤ f i ∧ 0 ≤ g i := by
      intro i hi; apply pos i; exact hS i (by simpa [E0, ascending] using hi)
    have hFa : ∀ i ∈ F0, 0 ≤ f i ∧ 0 ≤ g i := by
      intro i hi
      have hh : i ∉ S ∧ i ≠ alpha ∧ i ≠ beta := by
        simpa [F0, ascending, FS, and_assoc, and_comm, and_left_comm] using hi
      apply pos i
      cases rev <;> simpa [alpha, beta, and_comm] using hh.2
    have hENpos : ∀ i ∈ EN, 0 ≤ gn i := by
      intro i hi; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi; exact (hEa j hj).2
    have hFNpos : ∀ i ∈ FN, 0 ≤ gn i := by
      intro i hi; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi; exact (hFa j hj).2
    have hEN : (EN.map gn).sum = ∑ i ∈ S, g i := by
      simpa [EN, E0, List.map_map, g, Function.comp_def] using ascending_sum S g
    have hv : f alpha = -(if rev then C else B) ∧
        f beta = -(if rev then B else C) ∧
        g alpha = -(if rev then E else D) ∧ g beta = -(if rev then D else E) := by
      cases rev <;> simp [alpha, beta, hneg.1, hneg.2.1, hneg.2.2.1, hneg.2.2.2]
    have hm : (0 ≤ (if rev then C else B)) ∧
        (0 ≤ (if rev then B else C) ∧ (if rev then B else C) ≤ H) ∧
        (0 ≤ (if rev then E else D)) ∧
        (0 ≤ (if rev then D else E) ∧ (if rev then D else E) ≤ N) := by
      cases rev
      · exact ⟨hmag.1.1, hmag.2.1, hmag.2.2.1.1, hmag.2.2.2⟩
      · exact ⟨hmag.2.1.1, hmag.1, hmag.2.2.2.1, hmag.2.2.1⟩
    have holdZero := source_total (t := 2 ^ (r - 2) + 2 ^ (b - 2))
      (show 0 < r by dsimp [r]; omega) sigma hp
    have hs : InStrip f H 0 sigma := by
      apply two_blocks f H E0 F0 alpha beta (fun i hi => (hEa i hi).1)
        (fun i hi => (hFa i hi).1)
      · simpa [sigma, add_assoc] using holdZero
      · rw [show (E0.map f).sum = ∑ i ∈ S, f i from ascending_sum S f]
        exact ⟨le_trans hm.1 hF.1, hF.2⟩
      · rw [show (E0.map f).sum = ∑ i ∈ S, f i from ascending_sum S f, hv.1]
        linarith only [hF.1]
      · rw [hv.2.1, neg_neg]; exact hm.2.1
    have finish (cut : ℕ) (hc : cut ≤ r)
        (hn : InStrip gn N 0 (earWord r sigma cut)) :
        ∃ sigma : List (Fin r), ∃ cut : ℕ, cut ≤ r ∧
          OriginalOrder r (2 ^ (r - 2) + 2 ^ (b - 2)) sigma ∧
          OriginalOrder (r + 1) (2 * (2 ^ (r - 2) + 2 ^ (b - 2)))
            (earWord r sigma cut) := by
      have hnp := inserted_perm sigma cut hp
      refine ⟨sigma, cut, hc, ⟨hp, holdZero, ?_⟩,
        ⟨hnp, source_total (show 0 < r + 1 by omega) _ hnp, ?_⟩⟩
      · intro n; change _ ∈ Set.Icc (0 : ℤ) (modulus r / 2)
        rw [hNH]; simpa only [Set.mem_Icc, zero_add] using inStrip_prefix hs n
      · intro n; change _ ∈ Set.Icc (0 : ℤ) (modulus (r + 1) / 2)
        rw [hMH]; simpa only [Set.mem_Icc, zero_add] using inStrip_prefix hn n
    have hlen : E0.length + 1 ≤ r := by
      have hh := hp.length_eq
      simp only [sigma, List.length_append, List.length_singleton, List.length_finRange] at hh
      omega
    have freshPos : 0 ≤ gn fresh := by rw [hFresh]; dsimp [q]; positivity
    cases before
    · simp at hG
      have hear : earWord r sigma (E0.length + 1) =
          EN ++ [alpha.castSucc] ++ ([fresh] ++ FN) ++ [beta.castSucc] := by
        rw [show sigma = (E0 ++ [alpha]) ++ (F0 ++ [beta]) by
          simp [sigma, List.append_assoc],
          show E0.length + 1 = (E0 ++ [alpha]).length by simp]
        unfold earWord
        rw [List.take_left, List.drop_left]
        simp [EN, FN, fresh, List.map_append, List.append_assoc]
      apply finish (E0.length + 1) hlen
      have hz := source_total (t := 2 * (2 ^ (r - 2) + 2 ^ (b - 2)))
        (show 0 < r + 1 by omega) _ (inserted_perm sigma (E0.length + 1) hp)
      rw [hear] at hz ⊢
      apply two_blocks gn N EN ([fresh] ++ FN) alpha.castSucc beta.castSucc hENpos
        (by intro i hi; rcases List.mem_append.mp hi with hi | hi
            · have he := List.mem_singleton.mp hi; subst i; exact freshPos
            · exact hFNpos i hi)
      · simpa only [List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, add_assoc] using hz
      · rw [hEN]; simpa using And.intro (le_trans hm.2.2.1 hG.1) hG.2
      · change 0 ≤ (EN.map gn).sum + g alpha
        rw [hEN, hv.2.2.1]; simpa [sub_eq_add_neg] using (sub_nonneg.mpr hG.1)
      · change 0 ≤ -g beta ∧ -g beta ≤ N
        rw [hv.2.2.2, neg_neg]; exact hm.2.2.2
    · simp at hG
      have hear : earWord r sigma E0.length =
          (EN ++ [fresh]) ++ [alpha.castSucc] ++ FN ++ [beta.castSucc] := by
        rw [show sigma = E0 ++ ([alpha] ++ F0 ++ [beta]) by
          simp [sigma, List.append_assoc]]
        unfold earWord
        rw [List.take_left, List.drop_left]
        simp [EN, FN, fresh, List.map_append, List.append_assoc]
      apply finish E0.length (by omega)
      have hz := source_total (t := 2 * (2 ^ (r - 2) + 2 ^ (b - 2)))
        (show 0 < r + 1 by omega) _ (inserted_perm sigma E0.length hp)
      rw [hear] at hz ⊢
      apply two_blocks gn N (EN ++ [fresh]) FN alpha.castSucc beta.castSucc
        (by intro i hi; rcases List.mem_append.mp hi with hi | hi
            · exact hENpos i hi
            · have he := List.mem_singleton.mp hi; subst i; exact freshPos) hFNpos
      · simpa only [List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, add_assoc] using hz
      · simp only [List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, hEN, hFresh]
        exact ⟨le_trans hm.2.2.1 hG.1, hG.2⟩
      · change 0 ≤ ((EN ++ [fresh]).map gn).sum + g alpha
        simp only [List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, hEN, hFresh, hv.2.2.1]
        linarith only [hG.1]
      · change 0 ≤ -g beta ∧ -g beta ≤ N
        rw [hv.2.2.2, neg_neg]; exact hm.2.2.2

  let l : ℤ := 2 ^ (a - 2)
  let d : ℤ := 2 ^ (b - 2)
  have hl : 1 ≤ l := by
    have h : 0 < l := by dsimp [l]; positivity
    omega
  have hd : 1 ≤ d := by
    have h : 0 < d := by dsimp [d]; positivity
    omega
  have hL2 : L = 2 * l := by change L = 2 * (2 : ℤ) ^ (a - 2); linarith only [ha2]
  have hp2 : p = 2 * d := by change p = 2 * (2 : ℤ) ^ (b - 2); linarith only [hb2]
  have hqd : q = p * L + d := hqv
  have bank (n : ℕ) (hn : n ≤ a - 1) :
      (∑ i ∈ window r 2 n, f i) = (2 * p + 1) * (2 ^ n - 1) ∧
      (∑ i ∈ window r 2 n, g i) = (4 * p + 1) * (2 ^ n - 1) := by
    constructor
    · apply window_sum r 2 n (by dsimp [r]; omega)
      intro i hi
      have hh : 2 ≤ i.val ∧ i.val < 2 + n := by simpa [window] using hi
      rw [(hvalues i).1]
      simp [show i.val ≠ 0 by omega, show i.val ≠ 1 by omega,
        show i.val < a + 1 by omega]
    · apply window_sum r 2 n (by dsimp [r]; omega)
      intro i hi
      have hh : 2 ≤ i.val ∧ i.val < 2 + n := by simpa [window] using hi
      rw [(hvalues i).2]
      simp [show i.val ≠ 0 by omega, show i.val ≠ 1 by omega,
        show i.val < a + 1 by omega]
  let T := window r (a + 2) (b - 2)
  have tailSum : (∑ i ∈ T, f i) = (2 * L + 1) * (d - 1) ∧
      (∑ i ∈ T, g i) = (2 * L + 1) * (d - 1) := by
    constructor <;> apply window_sum r (a + 2) (b - 2) (by dsimp [r]; omega)
    all_goals
      intro i hi
      have hh : a + 2 ≤ i.val ∧ i.val < a + 2 + (b - 2) := by simpa [window] using hi
      first | rw [(hvalues i).1] | rw [(hvalues i).2]
      simp [show i.val ≠ 0 by omega, show i.val ≠ 1 by omega,
        show ¬i.val < a + 1 by omega, show i.val ≠ a + 1 by omega, Nat.sub_sub]
  have htop : f top = (2 * p + 1) * l ∧ g top = (4 * p + 1) * l := by
    simpa [top, l, show a ≠ 0 by omega, show a ≠ 1 by omega] using hvalues top

  by_cases hab : a < b
  · let t : ℤ := 2 ^ (b - a - 1)
    let special : Fin r := ⟨b + 1, by dsimp [r]; omega⟩
    let W := window r 2 (a - 2)
    let S := insert zero (insert special W)
    have ht : 1 ≤ t := by
      have ht0 : 0 < t := by dsimp [t]; positivity
      omega
    have hdt : d = L * t := by
      dsimp [d, L, t]
      rw [show b - 2 = (a - 1) + (b - a - 1) by omega, pow_add]
    have hspecial : f special = (2 * L + 1) * t ∧
        g special = (2 * L + 1) * t := by
      simpa [special, t, show b ≠ 0 by omega, show b ≠ a by omega,
        show ¬b + 1 < a + 1 by omega, show b + 1 ≠ a + 1 by omega,
        show b + 1 - a - 2 = b - a - 1 by omega] using hvalues special
    have hsW : special ∉ W := by simp [W, window, special] <;> omega
    have hzW : zero ∉ insert special W := by simp [W, window, zero, special, Fin.ext_iff]
    have hW := bank (a - 2) (by omega)
    have hFS : (∑ i ∈ S, f i) = q + (2 * p + 1) * (l - 1) + (2 * L + 1) * t := by
      dsimp only [S]
      rw [Finset.sum_insert hzW, Finset.sum_insert hsW, hzero.1, hspecial.1, hW.1]
      dsimp [l]; ring
    have hGS : (∑ i ∈ S, g i) = 2 * q + (4 * p + 1) * (l - 1) + (2 * L + 1) * t := by
      dsimp only [S]
      rw [Finset.sum_insert hzW, Finset.sum_insert hsW, hzero.2, hspecial.2, hW.2]
      dsimp [l]; ring
    have hS : ∀ i ∈ S, i ≠ one ∧ i ≠ atA := by
      intro i hi
      constructor <;> intro h <;> subst i
      all_goals (simp [S, W, window, one, atA, zero, special, Fin.ext_iff] at hi <;> omega)
    have hu : 0 ≤ d - l - t := by
      rw [hdt, hL2]
      linarith only [mul_nonneg (show 0 ≤ l by omega) (show 0 ≤ t - 1 by omega),
        mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ l - 1 by omega)]
    have hFdef : H - (∑ i ∈ S, f i) = d - l - t := by
      dsimp only [H]; rw [hFS, hqd]; simp only [hp2, hdt, hL2]; ring
    have hGdef : N - (∑ i ∈ S, g i) = 4 * d - l - t := by
      dsimp only [N]; rw [hGS, hqd]; simp only [hp2, hdt, hL2]; ring
    apply build S false false hS
    · change B ≤ (∑ i ∈ S, f i) ∧ (∑ i ∈ S, f i) ≤ H
      rw [hBdef]
      constructor <;> linarith only [hFdef, hu, hp2, hd, hl, ht]
    · change D ≤ (∑ i ∈ S, g i) + 0 ∧ (∑ i ∈ S, g i) + 0 ≤ N
      rw [hDdef]
      constructor <;> linarith only [hGdef, hu, hp2, hd, hl, ht]
  · by_cases heq : a = b
    · let S := insert top T
      have htT : top ∉ T := by simp [T, window, top] <;> omega
      have hFS : (∑ i ∈ S, f i) = (2 * p + 1) * l + (2 * L + 1) * (d - 1) := by
        dsimp only [S]; rw [Finset.sum_insert htT, htop.1, tailSum.1]
      have hGS : (∑ i ∈ S, g i) = (4 * p + 1) * l + (2 * L + 1) * (d - 1) := by
        dsimp only [S]; rw [Finset.sum_insert htT, htop.2, tailSum.2]
      have hS : ∀ i ∈ S, i ≠ one ∧ i ≠ atA := by
        intro i hi; constructor <;> intro h <;> subst i
        all_goals (simp [S, T, window, one, atA, top, Fin.ext_iff] at hi <;> omega)
      have hpl : p = L := by dsimp [p, L]; rw [heq]
      have hdl : d = l := by dsimp [d, l]; rw [heq]
      have hFdef : H - (∑ i ∈ S, f i) = L := by
        dsimp only [H]; rw [hFS]; simp only [hpl, hdl, hL2]; ring
      have hGdef : N - ((∑ i ∈ S, g i) + q) = l := by
        dsimp only [N]; rw [hGS, hqd]; simp only [hpl, hdl, hL2]; ring
      apply build S true true hS
      · change C ≤ (∑ i ∈ S, f i) ∧ (∑ i ∈ S, f i) ≤ H
        rw [hCdef]
        constructor <;> linarith only [hFdef, hL]
      · change E ≤ (∑ i ∈ S, g i) + q ∧ (∑ i ∈ S, g i) + q ≤ N
        rw [hEdef]
        constructor <;> linarith only [hGdef, hl, hL2]
    · by_cases hadj : a = b + 1
      · let S := window r 2 (a - 1)
        have hS : ∀ i ∈ S, i ≠ one ∧ i ≠ atA := by
          intro i hi; constructor <;> intro h <;> subst i
          all_goals (simp [S, window, one, atA] at hi <;> omega)
        have hFS := (bank (a - 1) (by omega)).1
        have hGS := (bank (a - 1) (by omega)).2
        have hLp : L = 2 * p := by
          dsimp [L, p]
          rw [show a - 1 = (b - 1) + 1 by omega, pow_succ]; ring
        have hFdef : H - (∑ i ∈ S, f i) = 0 := by
          dsimp only [S]; rw [hFS]; change 2 * p * L - 1 - (2 * p + 1) * (L - 1) = 0
          rw [hLp]; ring
        have hGdef : N - (∑ i ∈ S, g i) = L := by
          dsimp only [S]; rw [hGS]; change 4 * p * L - 1 - (4 * p + 1) * (L - 1) = L
          rw [hLp]; ring
        apply build S true false hS
        · change C ≤ (∑ i ∈ S, f i) ∧ (∑ i ∈ S, f i) ≤ H
          rw [hCdef]
          constructor <;> linarith only [hFdef, hL]
        · change E ≤ (∑ i ∈ S, g i) + 0 ∧ (∑ i ∈ S, g i) + 0 ≤ N
          rw [hEdef]
          constructor <;> linarith only [hGdef, hL]
      · have hab2 : b + 2 ≤ a := by omega
        let h : ℤ := 2 ^ (a - b - 2)
        let low : Fin r := ⟨a - b, by dsimp [r]; omega⟩
        let S := insert low (insert top T)
        have hh : 1 ≤ h := by
          have hh0 : 0 < h := by dsimp [h]; positivity
          omega
        have hlp : l = 2 * p * h := by
          dsimp [l, p, h]
          rw [show a - 2 = (b - 1) + ((a - b - 2) + 1) by omega, pow_add, pow_succ]
          ring
        have hlow : f low = (2 * p + 1) * h ∧ g low = (4 * p + 1) * h := by
          simpa [low, h, show a - b ≠ 0 by omega, show a - b ≠ 1 by omega,
            show a - b < a + 1 by omega] using hvalues low
        have htT : top ∉ T := by simp [T, window, top] <;> omega
        have hlT : low ∉ insert top T := by simp [T, window, low, top, Fin.ext_iff] <;> omega
        have hFS : (∑ i ∈ S, f i) = (2 * p + 1) * (l + h) + (2 * L + 1) * (d - 1) := by
          dsimp only [S]
          rw [Finset.sum_insert hlT, Finset.sum_insert htT, hlow.1, htop.1, tailSum.1]; ring
        have hGS : (∑ i ∈ S, g i) = (4 * p + 1) * (l + h) + (2 * L + 1) * (d - 1) := by
          dsimp only [S]
          rw [Finset.sum_insert hlT, Finset.sum_insert htT, hlow.2, htop.2, tailSum.2]; ring
        have hS : ∀ i ∈ S, i ≠ one ∧ i ≠ atA := by
          intro i hi; constructor <;> intro he <;> subst i
          all_goals (simp [S, T, window, low, top, one, atA, Fin.ext_iff] at hi <;> omega)
        have hFdef : H - (∑ i ∈ S, f i) = L - d - h := by
          dsimp only [H]; rw [hFS]; simp only [hL2, hlp, hp2]; ring
        have hGdef : N - ((∑ i ∈ S, g i) + q) = l - p - h := by
          dsimp only [N]; rw [hGS, hqd]; simp only [hL2, hlp, hp2]; ring
        have hbase : p + h ≤ l := by
          have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ p by omega)
          have h2 := mul_le_mul_of_nonneg_right hp (show 0 ≤ h by omega)
          linarith only [h1, h2, hlp, hh]
        apply build S true true hS
        · change C ≤ (∑ i ∈ S, f i) ∧ (∑ i ∈ S, f i) ≤ H
          rw [hCdef]
          constructor <;> linarith only [hFdef, hL2, hp2, hbase, hd, hh]
        · change E ≤ (∑ i ∈ S, g i) + q ∧ (∑ i ∈ S, g i) + q ≤ N
          rw [hEdef]
          constructor <;> linarith only [hGdef, hbase, hL2, hl, hp, hh]

theorem actualSource_below_half_two_bit_uniform_cut (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
      ∀ j : ℕ, j ≤ b - 2 →
        let sigma_j := sigma.map
          ((finRotate (a + b) : Equiv.Perm (Fin (a + b))) ^ (b - 2 - j))
        OriginalOrder (a + b) (2 ^ j * (2 ^ a + 1)) sigma_j ∧
        OriginalOrder (a + b + 1) (2 * (2 ^ j * (2 ^ a + 1)))
          (earWord (a + b) sigma_j cut) := by
  obtain ⟨sigma, cut, hcut, hold, hnew⟩ := boundary_joint a b ha hb
  refine ⟨sigma, cut, hcut, ?_⟩
  intro j hj
  let h : ℕ := b - 2 - j
  let s : ℕ := 2 ^ j * (2 ^ a + 1)
  have hh : 2 ^ h * s = 2 ^ (a + b - 2) + 2 ^ (b - 2) := by
    dsimp only [s]
    rw [← mul_assoc, ← pow_add,
      show h + j = b - 2 by dsimp [h]; omega,
      mul_add, mul_one, ← pow_add,
      show (b - 2) + a = a + b - 2 by omega]
  have hlt : 2 ^ h * s < 2 ^ ((a + b) - 1) := by
    rw [hh]
    have hsmall : (2 : ℕ) ^ (b - 2) < 2 ^ (a + b - 2) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 2) (by omega)
    have hstep : (2 : ℕ) ^ (a + b - 1) = 2 ^ (a + b - 2) * 2 := by
      rw [show a + b - 1 = (a + b - 2) + 1 by omega, pow_succ]
    rw [hstep]
    omega
  have hspos : 1 ≤ s := by
    have hs : 0 < s := by dsimp only [s]; positivity
    omega
  have hd : 2 ≤ a + b := by omega
  have holdScaled : OriginalOrder (a + b) (2 ^ h * s) sigma := by
    rw [hh]
    exact hold
  have hnewScaled : OriginalOrder (a + b + 1) (2 * (2 ^ h * s))
      (earWord (a + b) sigma cut) := by
    rw [hh]
    exact hnew
  obtain ⟨holdT, hnewT, _⟩ :=
    native_dyadic_joint_transport (a + b) s h hd hspos hlt sigma cut hcut
      holdScaled hnewScaled
  dsimp only at holdT hnewT ⊢
  simpa only [h, s] using And.intro holdT hnewT

end D5.S3.Combinatorics.Circle.BelowHalfBoundary

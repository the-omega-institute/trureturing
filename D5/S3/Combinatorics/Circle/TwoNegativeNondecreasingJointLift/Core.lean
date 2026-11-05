/- GID: D5/S3/Combinatorics/Circle/TwoNegativeNondecreasingJointLift/Core
   generality: I
   mirror-B: none(waiver:private-consumed-core)
   mirror-E: none(waiver:private-consumed-core)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Physical two-bank binary-mask construction with a literal common ear cut. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.TwoNegativeJointLift

/-! Independent binary masks realized as two full physical orders at one literal cut. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private positive_strip two_blocks split_perm source_total inserted_perm from
  D5.S3.Combinatorics.Circle.TwoNegativeJointLift

set_option maxHeartbeats 2000000 in
private theorem realize (a b u v : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hu : u < 2 ^ (b - 1)) (hv : v < 2 ^ (a - 1))
    (hseam :
      let q : ℤ := 2 ^ a
      let r : ℤ := 2 ^ b
      let R : ℤ := 2 ^ (b - 1)
      let p : ℤ := (q + 1) * u + (r + 1) * v
      let h : ℤ := q * R - 1 - p
      0 ≤ h ∧ h ≤ R ∧ q ≤ 2 * h + v ∧ 2 * h + v ≤ q + r) :
    ∃ sigma : List (Fin (a + b)), ∃ j : ℕ, j ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ a + 1) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ a + 1))
        (earWord (a + b) sigma j) := by
  classical
  let k := a + b
  let q : ℤ := 2 ^ a
  let r : ℤ := 2 ^ b
  let Q : ℤ := 2 ^ (a - 1)
  let R : ℤ := 2 ^ (b - 1)
  let w : ℕ := 2 ^ a + 1
  let N := modulus k
  let C := N / 2
  let A := 2 * r + 1
  let alpha : Fin k := ⟨b - 1, by dsimp [k]; omega⟩
  let beta : Fin k := ⟨k - 1, by dsimp [k]; omega⟩
  let f := actualSource k w
  let gn := actualSource (k + 1) (2 * w)
  let g := fun i : Fin k => actualSource (k + 1) (2 * w) i.castSucc
  let fresh : Fin (k + 1) := Fin.last k
  have hq : q = 2 * Q := by
    dsimp [q, Q]
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  have hr : r = 2 * R := by
    dsimp [r, R]
    calc
      (2 : ℤ) ^ b = 2 ^ ((b - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (b - 1) := by rw [pow_succ]; ring
  have hr4 : 4 ≤ r := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb
    norm_num at h
    exact h
  have hq4 : 4 ≤ q := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
    norm_num at h
    exact h
  have hqr4r : 4 * r ≤ q * r := mul_le_mul_of_nonneg_right hq4 (by omega)
  have hqr4 : 4 * q ≤ q * r := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hr4 (show 0 ≤ q by omega)
  have hQR : 0 < Q ∧ 0 < R := by dsimp [Q, R]; constructor <;> positivity
  have hvc : (w : ℤ) = q + 1 := by simp [w, q]
  have hN : N = q * r - 1 := by dsimp [N, modulus, k, q, r]; rw [pow_add]
  have hC : C = q * R - 1 := by
    have hn : N = 2 * (q * R) - 1 := by rw [hN, hr]; ring
    dsimp [C]; rw [hn]; omega
  have hC2 : 2 * C = N - 1 := by rw [hC, hN, hr]; ring
  have hNpos : 0 < N := by rw [hN]; nlinarith
  have hNodd : N % 2 = 1 := by
    have hn : N = 2 * (q * R) - 1 := by rw [hN, hr]; ring
    rw [hn]; omega
  have hM : modulus (k + 1) = 2 * N + 1 := by
    dsimp [N, modulus]; rw [pow_succ]; ring
  have hMH : modulus (k + 1) / 2 = N := by rw [hM]; omega
  have hMP : 0 < modulus (k + 1) := by rw [hM]; omega
  have hMO : modulus (k + 1) % 2 = 1 := by rw [hM]; omega
  have hpk : (2 : ℤ) ^ (k - 1) = Q * r := by
    have he : k - 1 = (a - 1) + b := by dsimp [k]; omega
    dsimp [Q, r]; rw [he, pow_add]
  have old_value (i : Fin k) (x m : ℤ) (hx : -C ≤ x ∧ x ≤ C)
      (he : (2 : ℤ) ^ i.val * (w : ℤ) = x + m * N) : f i = x := by
    apply centered_unique hNpos hNodd (centered_bounds hNpos hNodd _) hx
    change centered N _ % N = x % N
    rw [centered_mod, he]
    simp [Int.add_emod]
  have new_value (i : Fin (k + 1)) (x m : ℤ) (hx : -N ≤ x ∧ x ≤ N)
      (he : (2 : ℤ) ^ i.val * ((2 * w : ℕ) : ℤ) =
        x + m * modulus (k + 1)) : actualSource (k + 1) (2 * w) i = x := by
    apply centered_unique hMP hMO (centered_bounds hMP hMO _) (by simpa [hMH] using hx)
    rw [centered_mod, he]
    simp [Int.add_emod]
  have U (i : ℕ) (hi : i < b - 1) :
      f ⟨i, by dsimp [k]; omega⟩ = (q + 1) * 2 ^ i ∧
      g ⟨i, by dsimp [k]; omega⟩ = 2 * (q + 1) * 2 ^ i := by
    have ht : 4 * (2 : ℤ) ^ i ≤ r := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show i + 2 ≤ b by omega)
      simpa [r, pow_add, mul_comm] using h
    have ht0 : 0 < (2 : ℤ) ^ i := by positivity
    have hs0 : 0 ≤ (q + 1) * (2 : ℤ) ^ i := by positivity
    have hs20 : 0 ≤ 2 * (q + 1) * (2 : ℤ) ^ i := by positivity
    have hbnd : 2 * ((q + 1) * (2 : ℤ) ^ i) ≤ N - 1 := by
      have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ q + 1 by nlinarith)
      rw [hN]
      nlinarith
    constructor
    · apply old_value _ _ 0 (by constructor <;> nlinarith)
      simp only [hvc]; ring
    · apply new_value _ _ 0 (by constructor <;> nlinarith)
      simp only [Fin.val_castSucc, Nat.cast_mul, Nat.cast_ofNat, hvc]; ring
  have V (i : ℕ) (hi : i < a - 1) :
      f ⟨b + i, by dsimp [k]; omega⟩ = (r + 1) * 2 ^ i ∧
      g ⟨b + i, by dsimp [k]; omega⟩ = A * 2 ^ i := by
    have ht : 4 * (2 : ℤ) ^ i ≤ q := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show i + 2 ≤ a by omega)
      simpa [q, pow_add, mul_comm] using h
    have ht0 : 0 < (2 : ℤ) ^ i := by positivity
    have hs0 : 0 ≤ (r + 1) * (2 : ℤ) ^ i := by positivity
    have hsA0 : 0 ≤ A * (2 : ℤ) ^ i := by dsimp [A]; positivity
    have hbnd : 2 * ((r + 1) * (2 : ℤ) ^ i) ≤ N - 1 ∧
        A * (2 : ℤ) ^ i ≤ N := by
      have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ r + 1 by omega)
      have hm' := mul_le_mul_of_nonneg_left ht (show 0 ≤ A by dsimp [A]; omega)
      rw [hN]
      dsimp [A] at *
      constructor <;> nlinarith
    constructor
    · apply old_value _ _ ((2 : ℤ) ^ i) (by constructor <;> nlinarith)
      simp only [pow_add, hvc]
      change r * 2 ^ i * (q + 1) = _
      rw [hN]; ring
    · apply new_value _ _ ((2 : ℤ) ^ i) (by dsimp [A] at *; constructor <;> nlinarith)
      simp only [Fin.val_castSucc, pow_add, Nat.cast_mul, Nat.cast_ofNat, hvc]
      change r * 2 ^ i * (2 * (q + 1)) = _
      rw [hM, hN]; dsimp [A]; ring
  have hAlpha : f alpha = -C + R := by
    apply old_value _ _ 1 (by rw [hC]; constructor <;> nlinarith)
    change R * (w : ℤ) = _
    rw [hvc, hC, hN, hr]; ring
  have hBeta : f beta = -C + Q := by
    apply old_value _ _ (Q + 1) (by rw [hC]; constructor <;> nlinarith)
    change (2 : ℤ) ^ (k - 1) * (w : ℤ) = _
    rw [hpk, hvc, hC, hN, hr, hq]; ring
  have hAlphaNew : g alpha = -N + r := by
    apply new_value _ _ 1 (by rw [hN]; constructor <;> nlinarith)
    change R * ((2 * w : ℕ) : ℤ) = _
    rw [Nat.cast_mul, Nat.cast_ofNat, hvc, hM, hN, hr]; ring
  have hBetaNew : g beta = -N + Q := by
    apply new_value _ _ (Q + 1) (by rw [hN]; constructor <;> nlinarith)
    change (2 : ℤ) ^ (k - 1) * ((2 * w : ℕ) : ℤ) = _
    rw [hpk, Nat.cast_mul, Nat.cast_ofNat, hvc, hM, hN, hq]; ring
  have hFresh : gn fresh = (w : ℤ) := by
    apply new_value _ _ (w : ℤ) (by rw [hvc, hN]; constructor <;> nlinarith)
    change (2 : ℤ) ^ k * ((2 * w : ℕ) : ℤ) = _
    have he : (2 : ℤ) ^ k = N + 1 := by dsimp [N, modulus]; ring
    rw [he, Nat.cast_mul, Nat.cast_ofNat, hM]; ring
  let maskU := DyadicPrefix.bitSubset (b - 1) u hu
  let maskV := DyadicPrefix.bitSubset (a - 1) v hv
  let labelU : Fin (b - 1) → Fin k := fun i => ⟨i.val, by dsimp [k]; omega⟩
  let labelV : Fin (a - 1) → Fin k := fun i => ⟨b + i.val, by dsimp [k]; omega⟩
  have injU : Function.Injective labelU := by
    intro i j hij; apply Fin.ext
    exact congrArg (fun x : Fin k => x.val) hij
  have injV : Function.Injective labelV := by
    intro i j hij; apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp [labelV] at he; omega
  let EU := maskU.image labelU
  let EV := maskV.image labelV
  let ES := EU ∪ EV
  let FS := Finset.univ \ (ES ∪ {alpha,beta})
  let E := ES.sort (· ≤ ·)
  let F := FS.toList
  have hElist : E.Perm ES.toList := Finset.sort_perm_toList ES (· ≤ ·)
  have hdisj : Disjoint EU EV := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
    obtain ⟨y, hy, hyi⟩ := Finset.mem_image.mp hj
    have he := congrArg Fin.val (hxi.trans hyi.symm)
    dsimp [labelU, labelV] at he
    have := x.isLt
    omega
  have outside (i : Fin k) (hi : i ∈ ES) : i ≠ alpha ∧ i ≠ beta := by
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
      have := x.isLt
      constructor <;> intro he
      all_goals have he' := congrArg Fin.val he
      all_goals dsimp [labelU, alpha, beta, k] at he'; omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
      have := x.isLt
      constructor <;> intro he
      all_goals have he' := congrArg Fin.val he
      all_goals dsimp [labelV, alpha, beta, k] at he'; omega
  have hEa : alpha ∉ ES := fun hi => (outside alpha hi).1 rfl
  have hEb : beta ∉ ES := fun hi => (outside beta hi).2 rfl
  have hab : alpha ≠ beta := by
    intro he
    have he' := congrArg Fin.val he
    dsimp [alpha, beta, k] at he'; omega
  have hperm : (E ++ F ++ [alpha,beta]).Perm (List.finRange k) :=
    ((hElist.append_right F).append_right [alpha,beta]).trans
      (split_perm ES alpha beta hab hEa hEb)
  have hmaskU : (∑ i ∈ maskU, (2 : ℤ) ^ i.val) = (u : ℤ) := by
    exact_mod_cast DyadicPrefix.bit_subset_sum hu
  have hmaskV : (∑ i ∈ maskV, (2 : ℤ) ^ i.val) = (v : ℤ) := by
    exact_mod_cast DyadicPrefix.bit_subset_sum hv
  have hEold : (E.map f).sum = (q + 1) * u + (r + 1) * v := by
    rw [(hElist.map f).sum_eq]
    rw [← List.sum_toFinset _ ES.nodup_toList, Finset.toList_toFinset]
    change (∑ i ∈ EU ∪ EV, f i) = _
    rw [Finset.sum_union hdisj]
    dsimp [EU, EV]
    rw [Finset.sum_image (fun i _ j _ hij => injU hij),
      Finset.sum_image (fun i _ j _ hij => injV hij)]
    simp_rw [show ∀ i, f (labelU i) = (q + 1) * 2 ^ i.val from
      fun i => (U i.val i.isLt).1,
      show ∀ i, f (labelV i) = (r + 1) * 2 ^ i.val from
      fun i => (V i.val i.isLt).1]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hmaskU, hmaskV]
  have hEnew : (E.map g).sum = 2 * ((q + 1) * u + (r + 1) * v) - v := by
    rw [(hElist.map g).sum_eq]
    rw [← List.sum_toFinset _ ES.nodup_toList, Finset.toList_toFinset]
    change (∑ i ∈ EU ∪ EV, g i) = _
    rw [Finset.sum_union hdisj]
    dsimp [EU, EV]
    rw [Finset.sum_image (fun i _ j _ hij => injU hij),
      Finset.sum_image (fun i _ j _ hij => injV hij)]
    simp_rw [show ∀ i, g (labelU i) = 2 * (q + 1) * 2 ^ i.val from
      fun i => (U i.val i.isLt).2,
      show ∀ i, g (labelV i) = A * 2 ^ i.val from
      fun i => (V i.val i.isLt).2]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hmaskU, hmaskV]
    dsimp [A]; ring
  have pos (i : Fin k) (hi : i ≠ alpha ∧ i ≠ beta) : 0 ≤ f i ∧ 0 ≤ g i := by
    by_cases hu' : i.val < b - 1
    · have hv' := U i.val hu'
      have he : i = ⟨i.val, by dsimp [k]; omega⟩ := Fin.ext rfl
      rw [he, hv'.1, hv'.2]
      constructor <;> positivity
    · have hai : i.val ≠ b - 1 := fun h => hi.1 (Fin.ext h)
      have hbi : i.val ≠ k - 1 := fun h => hi.2 (Fin.ext h)
      have hlt : i.val - b < a - 1 := by dsimp [k] at *; omega
      have he : i = labelV ⟨i.val - b, hlt⟩ := Fin.ext (by dsimp [labelV]; omega)
      rw [he, (V _ hlt).1, (V _ hlt).2]
      dsimp [A]
      constructor <;> positivity
  have Epos : ∀ i ∈ E, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    apply pos i (outside i (Finset.mem_toList.mp (hElist.mem_iff.mp hi)))
  have Fpos : ∀ i ∈ F, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hm := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)).2
    apply pos i
    constructor <;> intro he <;> apply hm <;> simp [he]
  let p : ℤ := (q + 1) * u + (r + 1) * v
  let z : ℤ := 2 * p - v
  let h : ℤ := C - p
  have hh : 0 ≤ h ∧ h ≤ R ∧ q ≤ 2 * h + v ∧ 2 * h + v ≤ q + r := by
    simpa only [h, p, hC, q, r, R] using hseam
  let EN := E.map Fin.castSucc
  let FN := F.map Fin.castSucc
  have ENpos : ∀ i ∈ EN, 0 ≤ gn i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact (Epos j hj).2
  have FNpos : ∀ i ∈ FN, 0 ≤ gn i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact (Fpos j hj).2
  have hEN : (EN.map gn).sum = z := by
    change ((E.map Fin.castSucc).map gn).sum = z
    rw [List.map_map]
    exact hEnew
  have hp0 : 0 ≤ p := by
    change 0 ≤ (q + 1) * (u : ℤ) + (r + 1) * (v : ℤ)
    positivity
  have hz0 : 0 ≤ z := by
    rw [← hEN]
    exact List.sum_nonneg (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact ENpos i hi)
  have hseamOld : p = C - h ∧ p + f alpha = R - h := by
    rw [hAlpha]; dsimp [h]; constructor <;> ring
  have hseamNew : z + (w : ℤ) = N + q - 2 * h - v ∧
      z + (w : ℤ) + g alpha = q + r - 2 * h - v := by
    rw [hvc, hAlphaNew]
    dsimp [z, h]
    constructor <;> linarith [hC2]
  have hOldZero := source_total (t := w) (show 0 < k by dsimp [k]; omega) _ hperm
  have hOldMass : (F.map f).sum = 2 * C - R - Q - p := by
    change ((E ++ F ++ [alpha,beta]).map f).sum = 0 at hOldZero
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hEold, hAlpha, hBeta] at hOldZero
    dsimp [p]; linarith
  have hNewPerm : (EN ++ FN ++ [alpha.castSucc,beta.castSucc,fresh]).Perm
      (List.finRange (k + 1)) := by
    have hp := (hperm.map Fin.castSucc).append_right [fresh]
    simpa [EN, FN, List.map_append, List.finRange_succ_last, fresh, List.append_assoc] using hp
  have hNewZero := source_total (t := 2 * w) (show 0 < k + 1 by omega) _ hNewPerm
  have hNewMass : (FN.map gn).sum = 2 * N - r - Q - (w : ℤ) - z := by
    change ((EN ++ FN ++ [alpha.castSucc,beta.castSucc,fresh]).map gn).sum = 0 at hNewZero
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hEN] at hNewZero
    change z + (FN.map gn).sum + (g alpha + (g beta + (gn fresh + 0))) = 0 at hNewZero
    rw [hAlphaNew, hBetaNew, hFresh] at hNewZero
    linarith
  let sigma := E ++ [alpha] ++ F ++ [beta]
  have hsperm : sigma.Perm (List.finRange k) := by
    have hswap : sigma.Perm (E ++ F ++ [alpha,beta]) := by
      simpa only [sigma, List.append_assoc, List.cons_append, List.nil_append] using
        ((List.perm_append_comm (l₁ := [alpha]) (l₂ := F)).append_right [beta]).append_left E
    exact hswap.trans hperm
  have hcut : E.length ≤ k := by
    have he := hsperm.length_eq
    simp only [sigma,List.length_append,List.length_cons,List.length_nil,List.length_finRange] at he
    omega
  have hear : earWord k sigma E.length =
      (EN ++ [fresh]) ++ [alpha.castSucc] ++ FN ++ [beta.castSucc] := by
    simp only [sigma, List.append_assoc]
    unfold earWord
    rw [List.take_left, List.drop_left]
    simp only [EN, FN, fresh, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]
  have hs : InStrip f C 0 sigma := by
    apply two_blocks f C E F alpha beta (fun i hi => (Epos i hi).1)
      (fun i hi => (Fpos i hi).1)
    · rw [hEold,hOldMass,hAlpha,hBeta]; change p + (-C+R) + (2*C-R-Q-p) + (-C+Q) = 0; ring
    · rw [hEold]
      change 0 ≤ p ∧ p ≤ C
      rw [hseamOld.1]; omega
    · rw [hEold]
      change 0 ≤ p + f alpha
      rw [hseamOld.2]; omega
    · rw [hBeta]; constructor <;> nlinarith [hC2]
  have hn : InStrip gn N 0 (earWord k sigma E.length) := by
    rw [hear]
    apply two_blocks gn N (EN ++ [fresh]) FN alpha.castSucc beta.castSucc
      (by intro i hi; rcases List.mem_append.mp hi with hi | hi
          · exact ENpos i hi
          · have he := List.mem_singleton.mp hi
            subst i; rw [hFresh, hvc]; omega)
      FNpos
    · simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
      change (EN.map gn).sum + gn fresh + g alpha + (FN.map gn).sum + g beta = 0
      rw [hEN,hFresh,hAlphaNew,hNewMass,hBetaNew]; ring
    · simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
      rw [hEN,hFresh]
      constructor
      · rw [hvc]; omega
      · rw [hseamNew.1]; omega
    · simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
      change 0 ≤ (EN.map gn).sum + gn fresh + g alpha
      rw [hEN,hFresh,hseamNew.2]; omega
    · change 0 ≤ -g beta ∧ -g beta ≤ N
      rw [hBetaNew]; constructor <;> nlinarith [hN]
  have hnp := inserted_perm sigma E.length hsperm
  refine ⟨sigma, E.length, hcut,
    ⟨hsperm, source_total (show 0 < k by dsimp [k]; omega) _ hsperm, ?_⟩,
    ⟨hnp, source_total (by omega) _ hnp, ?_⟩⟩
  · intro n
    change 0 ≤ ((sigma.take n).map f).sum ∧ ((sigma.take n).map f).sum ≤ C
    simpa only [zero_add] using inStrip_prefix hs n
  · intro n
    change 0 ≤ (((earWord k sigma E.length).take n).map gn).sum ∧
      (((earWord k sigma E.length).take n).map gn).sum ≤ modulus (k + 1) / 2
    rw [hMH]
    simpa only [zero_add] using inStrip_prefix hn n

#print axioms realize

end D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift

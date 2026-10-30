/- GID: D5/S3/Combinatorics/Circle/TwoNegativeJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoNegativeJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Native common-cut two-negative lift for the asymmetric dyadic source.
-/

import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.DyadicPrefix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoNegativeJointLift
open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport
open scoped BigOperators

private theorem nonneg_strip {α : Type*} (f : α → ℤ) (B : ℤ) (l : List α)
    (hpos : ∀ x ∈ l, 0 ≤ f x) (hsum : (l.map f).sum ≤ B) :
    InStrip f B 0 l := by
  induction l with
  | nil => simp [InStrip]
  | cons x xs ih =>
    have hx := hpos x (by simp)
    have hrest : ∀ y ∈ xs, 0 ≤ f y := fun y hy => hpos y (by simp [hy])
    have htail : 0 ≤ (xs.map f).sum := List.sum_nonneg (by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact hrest z hz)
    have hsum' : (xs.map f).sum ≤ B - f x := by
      simp only [List.map_cons, List.sum_cons] at hsum
      omega
    refine ⟨by omega, by omega, ?_⟩
    exact ih hrest (by omega)

private theorem sum_scale {α : Type*} (l : List α) (f : α → ℤ) (c : ℤ) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem actualSource_two_negative_joint_lift (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hba : b < a) :
    ∃ sigma : List (Fin (a + b)), ∃ j : ℕ, j ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ a + 1) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ a + 1))
        (earWord (a + b) sigma j) := by
  classical
  let k := a + b
  let q := 2 ^ a
  let r := 2 ^ b
  let v := q + 1
  let A := 2 * r + 1
  let N : ℤ := modulus k
  let C : ℤ := N / 2
  let alpha : Fin k := ⟨b - 1, by dsimp [k]; omega⟩
  let beta : Fin k := ⟨k - 1, by dsimp [k]; omega⟩
  let fresh : Fin (k + 1) := Fin.last k
  let U : List (Fin k) := (List.finRange (b - 1)).map (fun i =>
    ⟨i.val, by dsimp [k]; omega⟩)
  let V : List (Fin k) := (List.finRange (a - 1)).map (fun i =>
    ⟨b + i.val, by dsimp [k]; omega⟩)
  have hqr : (q : ℤ) * r = (2 : ℤ) ^ k := by
    dsimp [q, r, k]
    rw [← pow_add]
  have hq2r : 2 * (r : ℤ) ≤ q := by
    have hp : (2 : ℕ) ^ (b + 1) ≤ 2 ^ a := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast (show 2 * r ≤ q by simpa [r, Nat.pow_succ] using hp)
  have hr4 : (4 : ℤ) ≤ r := by
    have := Nat.one_le_two_pow (n := b - 2)
    dsimp [r]
    rw [show b = (b - 2) + 2 by omega, pow_add]
    norm_num at *
    nlinarith
  have hN : N = (q : ℤ) * r - 1 := by
    dsimp [N, modulus]
    rw [← hqr]
    norm_num
  have hNpos : 0 < N := by
    rw [hN]
    have hqNat : 2 ≤ q := by
      dsimp [q]
      rw [show a = (a - 1) + 1 by omega, pow_succ]
      have hpow : 1 ≤ (2 : ℕ) ^ (a - 1) := Nat.one_le_two_pow
      omega
    nlinarith [show (2 : ℤ) ≤ q by exact_mod_cast hqNat]
  have hq2 : (q : ℤ) % 2 = 0 := by
    have hqNat : 2 ∣ q := by
      refine ⟨2 ^ (a - 1), ?_⟩
      dsimp [q]
      rw [show a = (a - 1) + 1 by omega, pow_succ]
      ring
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast hqNat)
  have hr2 : (r : ℤ) % 2 = 0 := by
    have hrNat : 2 ∣ r := by
      refine ⟨2 ^ (b - 1), ?_⟩
      dsimp [r]
      rw [show b = (b - 1) + 1 by omega, pow_succ]
      ring
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast hrNat)
  have hprodmod : ((q : ℤ) * r) % 2 = 0 := by
    rw [Int.mul_emod, hq2]
    norm_num
  have hNodd : N % 2 = 1 := by
    rw [hN, Int.sub_emod, hprodmod]
    norm_num
  have hC : 2 * C = N - 1 := by dsimp [C]; omega
  have hM : modulus (k + 1) = 2 * N + 1 := by
    dsimp [N, modulus]
    rw [show k + 1 = (a + b) + 1 by rfl, pow_succ, hqr]
    ring
  have hMhalf : modulus (k + 1) / 2 = N := by rw [hM]; omega
  have hMpos : 0 < modulus (k + 1) := by rw [hM]; omega
  have hModd : modulus (k + 1) % 2 = 1 := by rw [hM]; omega
  have old_centered (i : Fin k) (x : ℤ)
      (hx : -C ≤ x ∧ x ≤ C)
      (hmod : x % N = ((2 : ℤ) ^ i.val * (v : ℕ)) % N) :
      actualSource k v i = x := by
    unfold actualSource
    apply centered_unique hNpos hNodd (centered_bounds hNpos hNodd _) hx
    rw [centered_mod]
    exact hmod.symm
  have new_centered (i : Fin (k + 1)) (x : ℤ)
      (hx : -N ≤ x ∧ x ≤ N)
      (hmod : x % modulus (k + 1) =
        ((2 : ℤ) ^ i.val * (2 * (v : ℕ))) % modulus (k + 1)) :
      actualSource (k + 1) (2 * v) i = x := by
    unfold actualSource
    apply centered_unique hMpos hModd (centered_bounds hMpos hModd _) hx
    rw [centered_mod]
    exact hmod.symm
  have hUval (i : Fin (b - 1)) :
      actualSource k v ⟨i.val, by dsimp [k]; omega⟩ =
        (q + 1 : ℤ) * 2 ^ i.val := by
    have hi : i.val ≤ b - 2 := by omega
    have hpowi : (2 : ℤ) ^ i.val ≤ (2 : ℤ) ^ (b - 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hhalf : (q + 1 : ℤ) * 2 ^ i.val ≤ C := by
      rw [hC, hN, ← hqr]
      nlinarith [hpowi, hq2r, hr4]
    apply old_centered _ _ ⟨by positivity, hhalf⟩
    rw [Int.emod_eq_of_lt (by positivity)]
    · congr 1
      norm_num [v]
    · rw [← hqr]
      nlinarith [hpowi, hq2r]
  have hVval (i : Fin (a - 1)) :
      actualSource k v ⟨b + i.val, by dsimp [k]; omega⟩ =
        (r + 1 : ℤ) * 2 ^ i.val := by
    have hi : i.val ≤ a - 2 := by omega
    have hpowi : (2 : ℤ) ^ i.val ≤ (2 : ℤ) ^ (a - 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hhalf : (r + 1 : ℤ) * 2 ^ i.val ≤ C := by
      rw [hC, hN]
      nlinarith [hpowi, hq2r, hr4]
    apply old_centered _ _ ⟨by positivity, hhalf⟩
    rw [Int.emod_eq_of_lt (by positivity)]
    · rw [show (2 : ℤ) ^ (b + i.val) * (v : ℕ) =
          ((q : ℤ) * r - 1) * 2 ^ i.val + (r + 1) * 2 ^ i.val by
          rw [← hqr]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring]
      rw [Int.add_emod_self_left]
    · rw [← hqr]
      nlinarith [hpowi, hq2r]
  have hAlphaval : actualSource k v alpha = -C + r / 2 := by
    apply old_centered alpha _
      (by rw [hC]; constructor <;> nlinarith [hr4])
    rw [show (2 : ℤ) ^ (b - 1) * (v : ℕ) =
      N + (r - N + 1) / 2 by rw [hN, ← hqr]; simp only [Nat.cast_add, Nat.cast_one,
      Nat.cast_pow]; ring]
    rw [Int.add_emod_self_left]
    rw [show (-C + r / 2) = (r - N + 1) / 2 by rw [hC]; ring]
    omega
  have hBetaval : actualSource k v beta = -C + q / 2 := by
    apply old_centered beta _
      (by rw [hC]; constructor <;> nlinarith [hq2r, hr4])
    rw [show (2 : ℤ) ^ (k - 1) * (v : ℕ) =
      (q + 2) / 2 * N + (-C + q / 2) by
      rw [hN, hC, ← hqr]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_mul_emod_self_left]
  have hUnew (i : Fin (b - 1)) :
      actualSource (k + 1) (2 * v) (⟨i.val, by dsimp [k]; omega⟩ : Fin (k + 1)) =
        2 * ((q + 1 : ℤ) * 2 ^ i.val) := by
    apply new_centered _ _
      (by rw [hMhalf]; constructor <;> nlinarith [hUval i])
    rw [show (2 : ℤ) ^ i.val * (2 * (v : ℕ)) =
      2 * ((q + 1 : ℤ) * 2 ^ i.val) by norm_num [v]; ring]
  have hVnew (i : Fin (a - 1)) :
      actualSource (k + 1) (2 * v) (⟨b + i.val, by dsimp [k]; omega⟩ : Fin (k + 1)) =
        A * 2 ^ i.val := by
    have hi : i.val ≤ a - 2 := by omega
    have hpowi : (2 : ℤ) ^ i.val ≤ (2 : ℤ) ^ (a - 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    apply new_centered _ _
      (by rw [hMhalf]; constructor <;> nlinarith [hq2r, hr4, hpowi])
    rw [show (2 : ℤ) ^ (b + i.val) * (2 * (v : ℕ)) =
      A * 2 ^ i.val + modulus (k + 1) * 2 ^ i.val by
      rw [hM, ← hqr]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_mul_emod_self_right]
  have hAlphanew : actualSource (k + 1) (2 * v)
      (⟨b - 1, by dsimp [k]; omega⟩ : Fin (k + 1)) = -N + r := by
    apply new_centered _ _ ⟨by rw [hN]; nlinarith [hq2r], by rw [hN]; nlinarith [hq2r, hr4]⟩
    rw [show (2 : ℤ) ^ (b - 1) * (2 * (v : ℕ)) =
      (-N + r) + modulus (k + 1) by rw [hM, ← hqr]; simp only [Nat.cast_add,
      Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_emod_self_right]
  have hBetanew : actualSource (k + 1) (2 * v)
      (⟨k - 1, by dsimp [k]; omega⟩ : Fin (k + 1)) = -N + q / 2 := by
    apply new_centered _ _ ⟨by rw [hN]; nlinarith [hq2r], by rw [hN]; nlinarith [hq2r]⟩
    rw [show (2 : ℤ) ^ (k - 1) * (2 * (v : ℕ)) =
      (q / 2 + 1) * modulus (k + 1) + (-N + q / 2) by
      rw [hM, hN, ← hqr]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_mul_emod_self_left]
  have hFresh : actualSource (k + 1) (2 * v) fresh = v := by
    apply new_centered _ _ ⟨by positivity, by rw [hN]; nlinarith [hq2r]⟩
    rw [show (2 : ℤ) ^ k * (2 * (v : ℕ)) =
      (v : ℤ) + modulus (k + 1) * (v : ℕ) by rw [hM, ← hqr]; simp only [Nat.cast_add,
      Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_mul_emod_self_right]
  let w : ℕ := ((N - (v : ℤ)) / (A : ℤ)).toNat
  have hv0 : 0 ≤ N - (v : ℤ) := by
    rw [hN]
    dsimp [v]
    nlinarith [hq2r, hr4]
  have hApos : (0 : ℤ) < A := by dsimp [A]; omega
  have hwcast : (w : ℤ) = (N - (v : ℤ)) / (A : ℤ) := by
    dsimp [w]
    rw [Int.toNat_of_nonneg hv0]
  have hwfloor : (w : ℤ) * A ≤ N - (v : ℤ) ∧
      N - (v : ℤ) < ((w : ℤ) + 1) * A := by
    have h := Int.ediv_emod (N - (v : ℤ)) (A : ℤ)
    have hrm := Int.emod_nonneg (N - (v : ℤ)) (ne_of_gt hApos)
    have hrl := Int.emod_lt_of_pos (N - (v : ℤ)) hApos
    rw [← hwcast] at h
    constructor <;> omega
  have hwupper : (w : ℤ) < (q : ℤ) / 2 := by
    have hnum : N - (v : ℤ) < (A : ℤ) * (q : ℤ) / 2 := by
      rw [hN]
      dsimp [v, A]
      nlinarith [hq2r, hr4]
    nlinarith [hwfloor.1, hApos]
  have hwbits : w < 2 ^ (a - 1) := by
    have hqhalf : (q : ℤ) / 2 = (2 : ℤ) ^ (a - 1) := by
      dsimp [q]
      rw [show a = (a - 1) + 1 by omega, pow_succ]
      omega
    exact_mod_cast (show (w : ℤ) < (2 : ℤ) ^ (a - 1) by rw [← hqhalf]; exact hwupper)
  have hdyadic : Dyadic (fun x : Fin k => actualSource k v x)
      (r + 1 : ℤ) V := by
    dsimp [V]
    induction (a - 1) with
    | zero => simp [Dyadic]
    | succ n ih =>
      rw [List.finRange_succ_last]
      simp only [List.map_append, List.map_cons, List.map_nil, Dyadic]
      constructor
      · simpa using hVval ⟨n, by omega⟩
      · simpa [pow_succ] using ih
  obtain ⟨E, Vr, hEV, hEsum⟩ := dyadic_select hdyadic w hwbits
  let F := U ++ Vr
  have hphysical : (U ++ V ++ [alpha, beta]).Perm (List.finRange k) := by
    have hUn : U.Nodup := by
      apply (List.nodup_finRange (b - 1)).map
      intro i j hij
      exact Fin.ext (congrArg Fin.val hij)
    have hVn : V.Nodup := by
      apply (List.nodup_finRange (a - 1)).map
      intro i j hij
      exact Fin.ext (congrArg Fin.val hij)
    have hUV : List.Disjoint U V := by
      apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
      obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
      have hh := congrArg Fin.val (hi.trans hj.symm)
      simp only [Fin.val_mk] at hh
      omega
    have hUa : List.Disjoint U [alpha] := by
      apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
      simp only [List.mem_singleton] at hy
      subst x
      have hh := congrArg Fin.val hi
      simp only [Fin.val_mk] at hh
      omega
    have hVa : List.Disjoint V [alpha] := by
      apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
      simp only [List.mem_singleton] at hy
      subst x
      have hh := congrArg Fin.val hi
      simp only [Fin.val_mk] at hh
      omega
    have hUb : List.Disjoint U [beta] := by
      apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
      simp only [List.mem_singleton] at hy
      subst x
      have hh := congrArg Fin.val hi
      simp only [Fin.val_mk] at hh
      omega
    have hVb : List.Disjoint V [beta] := by
      apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
      simp only [List.mem_singleton] at hy
      subst x
      have hh := congrArg Fin.val hi
      simp only [Fin.val_mk] at hh
      omega
    have habnd : ([alpha, beta] : List (Fin k)).Nodup := by simp [alpha, beta]
    have hUVab : List.Disjoint (U ++ V) ([alpha, beta] : List (Fin k)) := by
      apply List.disjoint_left.mpr
      intro x hx hy
      simp only [List.mem_append] at hx
      simp only [List.mem_cons, List.mem_singleton] at hy
      rcases hx with hx | hx
      · rcases hy with rfl | rfl
        · exact hUa x hx (by simp)
        · exact hUb x hx (by simp)
      · rcases hy with rfl | rfl
        · exact hVa x hx (by simp)
        · exact hVb x hx (by simp)
    have hallnd : (U ++ V ++ [alpha, beta]).Nodup := by
      apply List.nodup_append.mpr
      exact ⟨List.nodup_append.mpr ⟨hUn, hVn, hUV⟩, habnd, hUVab⟩
    have hmem : ∀ x : Fin k, x ∈ U ++ V ++ [alpha, beta] ↔ x ∈ List.finRange k := by
      intro x
      constructor
      · intro hx
        exact List.mem_finRange x
      · intro hx
        simp only [List.mem_finRange] at hx
        by_cases h₁ : x.val < b - 1
        · apply List.mem_append_left
          apply List.mem_map.mpr
          refine ⟨⟨x.val, h₁⟩, List.mem_finRange _, ?_⟩
          exact Fin.ext rfl
        · by_cases h₂ : x.val = b - 1
          · apply List.mem_append_left
            apply List.mem_append_right
            simp [alpha, h₂]
          · by_cases h₃ : x.val < k - 1
            · apply List.mem_append_left
              apply List.mem_append_right
              apply List.mem_map.mpr
              refine ⟨⟨x.val - b, by dsimp [k] at *; omega⟩, List.mem_finRange _, ?_⟩
              exact Fin.ext (by dsimp; omega)
            · apply List.mem_append_right
              right
              apply Fin.ext
              dsimp [beta]
              omega
    apply (List.perm_ext_iff_of_nodup hallnd (List.nodup_finRange k)).mpr
    exact hmem
  have hposperm' : (E ++ U ++ Vr ++ [alpha, beta]).Perm
      (U ++ V ++ [alpha, beta]) := by
    calc
      E ++ U ++ Vr ++ [alpha, beta] ~r U ++ (E ++ Vr) ++ [alpha, beta] := by
        simpa [List.append_assoc] using
          (List.perm_append_comm E U |>.append_right (Vr ++ [alpha, beta]))
      _ ~r U ++ V ++ [alpha, beta] := by
        exact (hEV.append_left U).append_right [alpha, beta]
      _ ~r List.finRange k := hphysical
  have hposperm : (E ++ F ++ [alpha, beta]).Perm (List.finRange k) := by
    simpa [F, List.append_assoc] using hposperm'
  have hEsub (x : Fin k) (hx : x ∈ E) : x.val ≥ b ∧ x.val ≤ k - 2 := by
    have hx' : x ∈ V := hEV.mem_iff.mp (by simp [F, hx])
    simp only [V, List.mem_map, List.mem_finRange] at hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    simp only [Fin.val_mk]
    omega
  let powV : Fin k → ℤ := fun x => (2 : ℤ) ^ (x.val - b)
  have hEold : (E.map (actualSource k v)).sum =
      (r + 1 : ℤ) * (E.map powV).sum := by
    have hmap : E.map (actualSource k v) =
        E.map (fun x => (r + 1 : ℤ) * powV x) := by
      apply List.map_congr_left
      intro x hx
      have hbounds := hEsub x hx
      obtain ⟨i, hi, hxi⟩ := List.mem_map.mp (hEV.mem_iff.mp (by simp [F, hx]))
      have heq : x.val - b = i.val := by
        have := congrArg Fin.val hxi
        simp only [V, Fin.val_mk] at this
        omega
      rw [show x = ⟨b + i.val, by dsimp [k]; omega⟩ by exact Fin.ext (by omega), hVval i]
      simp [powV, heq, mul_comm]
    rw [hmap]
    exact sum_scale E powV (r + 1)
  have hEpow : (E.map powV).sum = (w : ℤ) := by
    rw [hEold] at hEsum
    nlinarith [hEsum]
  have hEnew :
      (E.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum = (A : ℤ) * w := by
    have hmap : E.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc) =
        E.map (fun x => (A : ℤ) * powV x) := by
      apply List.map_congr_left
      intro x hx
      have hbounds := hEsub x hx
      obtain ⟨i, hi, hxi⟩ := List.mem_map.mp (hEV.mem_iff.mp (by simp [F, hx]))
      have heq : x.val - b = i.val := by
        have := congrArg Fin.val hxi
        simp only [V, Fin.val_mk] at this
        omega
      rw [show x = ⟨b + i.val, by dsimp [k]; omega⟩ by exact Fin.ext (by omega)]
      simpa [Function.comp_def, powV, heq] using hVnew i
    rw [hmap, sum_scale]
    rw [hEpow]
    ring
  have hUpos : ∀ x ∈ U, 0 < actualSource k v x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hUval i]
    positivity
  have hVpos : ∀ x ∈ V, 0 < actualSource k v x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hVval i]
    positivity
  have hEpos : ∀ x ∈ E, 0 < actualSource k v x := by
    intro x hx
    exact hVpos x (hEV.mem_iff.mp (by simp [F, hx]))
  have hVrpos : ∀ x ∈ Vr, 0 < actualSource k v x := by
    intro x hx
    exact hVpos x (hEV.mem_iff.mp (by simp [F, hx]))
  have hFpos : ∀ x ∈ F, 0 < actualSource k v x := by
    intro x hx
    simp only [F, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hUpos x hx
    · exact hVrpos x hx
  have hnewFpos : ∀ x ∈ F, 0 < actualSource (k + 1) (2 * v) x.castSucc := by
    intro x hx
    simp only [F, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rw [hUnew i]
      positivity
    · obtain ⟨i, hi, hxi⟩ := List.mem_map.mp (hEV.mem_iff.mp (by simp [F, hx]))
      subst x
      rw [hVnew i]
      positivity
  have hnewFpos' : ∀ y ∈ F.map Fin.castSucc,
      0 < actualSource (k + 1) (2 * v) y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hnewFpos x hx
  have hOldPerm : (E ++ F ++ [alpha, beta]).Perm (List.finRange k) := hposperm
  have hOldTotal : ((E ++ F ++ [alpha, beta]).map (actualSource k v)).sum = 0 := by
    rw [(hOldPerm.map (actualSource k v)).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact (ZeroSumSubsets.source_cycle (by dsimp [k]; omega) v).2.1
  have hFsum : (F.map (actualSource k v)).sum =
      -(E.map (actualSource k v)).sum - actualSource k v alpha - actualSource k v beta := by
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hOldTotal
    linarith
  have hNewPermBase :
      (E.map Fin.castSucc ++ F.map Fin.castSucc ++
        [alpha.castSucc, beta.castSucc, fresh]).Perm (List.finRange (k + 1)) := by
    have hp := hOldPerm.map Fin.castSucc
    calc
      E.map Fin.castSucc ++ F.map Fin.castSucc ++
          [alpha.castSucc, beta.castSucc, fresh] ~r
          (E ++ F ++ [alpha, beta]).map Fin.castSucc ++ [fresh] := by
            simp only [List.map_append, List.map_cons, List.map_nil]
            exact List.Perm.refl _
      _ ~r (List.finRange k).map Fin.castSucc ++ [fresh] := by
            exact hp.append_right [fresh]
      _ ~r List.finRange (k + 1) := by
            simpa only [List.finRange_succ_last] using
              (List.Perm.refl (List.finRange k).map Fin.castSucc).append_right [fresh]
  have hNewTotal :
      ((E.map Fin.castSucc ++ F.map Fin.castSucc ++
        [alpha.castSucc, beta.castSucc, fresh]).map
        (actualSource (k + 1) (2 * v))).sum = 0 := by
    rw [(hNewPermBase.map (actualSource (k + 1) (2 * v))).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact (ZeroSumSubsets.source_cycle (by dsimp [k]; omega) (2 * v)).2.1
  have hnewFsum : (F.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum =
      -(E.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum -
        actualSource (k + 1) (2 * v) alpha.castSucc -
        actualSource (k + 1) (2 * v) beta.castSucc -
        actualSource (k + 1) (2 * v) fresh := by
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Function.comp_def] at hNewTotal
    linarith
  have hp : (E.map (actualSource k v)).sum = (r + 1 : ℤ) * w := by
    simpa [mul_comm] using hEsum
  have hz : (E.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum =
      (A : ℤ) * w := hEnew
  have hcase : a = b + 1 ∨ b + 2 ≤ a := by omega
  rcases hcase with hq2case | hq4case
  · have hqeq : (q : ℤ) = 2 * r := by
      dsimp [q, r]
      rw [hq2case, show b + 1 = b + 1 by rfl, pow_succ]
      norm_num
    have hNq : N = 2 * r ^ 2 - 1 := by rw [hN, hqeq]; ring
    have hwq : (w : ℤ) = r - 2 := by
      apply le_antisymm
      · have := hwfloor.2
        rw [hNq, hqeq] at this ⊢
        dsimp [A, v] at this ⊢
        nlinarith
      · have := hwfloor.1
        rw [hNq, hqeq] at this ⊢
        dsimp [A, v] at this ⊢
        nlinarith
    have hpq : (E.map (actualSource k v)).sum = C - r - 1 := by
      rw [hp, hwq, hqeq, hNq, hC]
      ring
    have hzq : (E.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum =
        N - r := by
      rw [hz, hwq, hqeq, hNq, A]
      ring
    have hFq : (F.map (actualSource k v)).sum = C - r / 2 + 1 := by
      rw [hFsum, hpq, hAlphaval, hBetaval]
      ring
    have hnewFq : (F.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum =
        N - r := by
      rw [hnewFsum, hzq, hAlphanew, hBetanew, hFresh, hqeq]
      ring
    have hOldStrip : InStrip (actualSource k v) C 0
        (F ++ [alpha] ++ E ++ [beta]) := by
      have hFstrip : InStrip (actualSource k v) C 0 F :=
        nonneg_strip _ _ _ (fun x hx => le_of_lt (hFpos x hx))
          (by rw [hFq]; rw [hC]; nlinarith [hr4])
      have haStrip : InStrip (actualSource k v) C (F.map (actualSource k v)).sum [alpha] := by
        simp only [InStrip, hAlphaval]
        rw [hFq]
        rw [hC]
        constructor <;> nlinarith [hr4]
      have heStrip : InStrip (actualSource k v) C
          ((F.map (actualSource k v)).sum + actualSource k v alpha) E := by
        rw [hFq, hAlphaval]
        exact nonneg_strip _ _ _ (fun x hx => le_of_lt (hEpos x hx))
          (by rw [hpq]; rw [hC]; nlinarith [hr4])
      have hbStrip : InStrip (actualSource k v) C
          ((F.map (actualSource k v)).sum + actualSource k v alpha +
            (E.map (actualSource k v)).sum) [beta] := by
        simp only [InStrip, hBetaval]
        rw [hFq, hAlphaval, hpq]
        rw [hC]
        constructor <;> nlinarith [hr4]
      simpa [List.append_assoc, List.map_map, Function.comp_def] using inStrip_append hFstrip
        (inStrip_append haStrip (inStrip_append heStrip hbStrip))
    have hNewStrip : InStrip (actualSource (k + 1) (2 * v)) N 0
        (F.map Fin.castSucc ++ [alpha.castSucc] ++ E.map Fin.castSucc ++
          [fresh, beta.castSucc]) := by
      have hFstrip : InStrip (actualSource (k + 1) (2 * v)) N 0
          (F.map Fin.castSucc) := by
        apply nonneg_strip _ _ _ (fun x hx => le_of_lt (hnewFpos' x hx))
        have hbound :
            (F.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum ≤ N := by
          rw [hnewFq, hNq]
          nlinarith [hr4]
        simpa only [List.map_map, Function.comp_def] using hbound
      have haStrip : InStrip (actualSource (k + 1) (2 * v)) N hnewFq
          [alpha.castSucc] := by
        simp only [InStrip, hAlphanew]
        rw [hnewFq]
        constructor <;> nlinarith [hr4]
      have heStrip : InStrip (actualSource (k + 1) (2 * v)) N 0
          (E.map Fin.castSucc) := by
        apply nonneg_strip _ _ _
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨i, hi, hxi⟩ := List.mem_map.mp (hEV.mem_iff.mp (by simp [F, hy]))
          subst y
          rw [hVnew i]
          positivity
        · have hbound :
              (E.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum ≤ N := by
            rw [hzq, hNq]
            nlinarith [hr4]
          simpa only [List.map_map, Function.comp_def] using hbound
      have hfreshStrip : InStrip (actualSource (k + 1) (2 * v)) N hzq [fresh] := by
        simp only [InStrip, hFresh]
        rw [hzq, hNq]
        constructor <;> nlinarith [hr4]
      have hbetaStrip : InStrip (actualSource (k + 1) (2 * v)) N (hzq + v) [beta.castSucc] := by
        simp only [InStrip, hBetanew]
        rw [hzq, hNq, hFresh]
        constructor <;> nlinarith [hr4]
      simpa [List.append_assoc, List.map_map, Function.comp_def] using inStrip_append hFstrip
        (inStrip_append haStrip (inStrip_append heStrip
          (inStrip_append hfreshStrip hbetaStrip)))
    let sigma := F ++ [alpha] ++ E ++ [beta]
    let j := k - 1
    have hsigma : sigma.Perm (List.finRange k) := by
      have horder : (F ++ [alpha] ++ E ++ [beta]).Perm
          (E ++ F ++ [alpha, beta]) := by
        calc
          F ++ [alpha] ++ E ++ [beta] ~r F ++ E ++ [alpha] ++ [beta] := by
            simpa [List.append_assoc] using
              ((List.perm_append_comm [alpha] E).append_right [beta]).append_left F
          _ ~r E ++ F ++ [alpha] ++ [beta] := by
            simpa [List.append_assoc] using
              (List.perm_append_comm F E).append_right ([alpha] ++ [beta])
          _ ~r E ++ F ++ [alpha, beta] := by rfl
      exact horder.trans hOldPerm
    have hneweq : earWord k sigma j =
        (F.map Fin.castSucc ++ [alpha.castSucc] ++ E.map Fin.castSucc ++
          [fresh, beta.castSucc]) := by
      simp [earWord, sigma, j, List.length_append, hsigma.length_eq]
    have hOldTotalSigma : (sigma.map (actualSource k v)).sum = 0 := by
      rw [((hsigma.trans hOldPerm.symm).map (actualSource k v)).sum_eq]
      exact hOldTotal
    have hneworder :
        (F.map Fin.castSucc ++ [alpha.castSucc] ++ E.map Fin.castSucc ++
          [fresh, beta.castSucc]).Perm
          (E.map Fin.castSucc ++ F.map Fin.castSucc ++
            [alpha.castSucc, beta.castSucc, fresh]) := by
      let X := E.map Fin.castSucc
      let Y := F.map Fin.castSucc
      let x := alpha.castSucc
      let y := beta.castSucc
      let z := fresh
      calc
        Y ++ [x] ++ X ++ [z, y] ~r
            Y ++ X ++ [x] ++ [z, y] := by
              simpa [List.append_assoc] using
                ((List.perm_append_comm [x] X).append_right [z, y]).append_left Y
        _ ~r X ++ Y ++ [x] ++ [z, y] := by
              simpa [List.append_assoc] using
                (List.perm_append_comm Y X).append_right ([x] ++ [z, y])
        _ ~r X ++ Y ++ [x] ++ [y, z] := by
              simpa [List.append_assoc] using
                (List.Perm.swap z y []).append_left (X ++ Y ++ [x])
        _ ~r X ++ Y ++ [x, y, z] := by rfl
    have hNewTotalDesired :
        ((F.map Fin.castSucc ++ [alpha.castSucc] ++ E.map Fin.castSucc ++
          [fresh, beta.castSucc]).map (actualSource (k + 1) (2 * v))).sum = 0 := by
      rw [(hneworder.map (actualSource (k + 1) (2 * v))).sum_eq]
      exact hNewTotal
    refine ⟨sigma, j, by dsimp [j]; omega, ?_, ?_⟩
    · exact ⟨hsigma, hOldTotalSigma, by simpa [Set.mem_Icc, sigma] using (by
        intro n; exact inStrip_prefix hOldStrip n)⟩
    · rw [hneweq]
      exact ⟨hneworder.trans hNewPermBase, hNewTotalDesired, by
        intro n
        simpa [Set.mem_Icc] using inStrip_prefix hNewStrip n⟩
  · have hq4 : (4 : ℤ) * r ≤ q := by
      have hp : (2 : ℕ) ^ (b + 2) ≤ 2 ^ a := by
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hpow : (2 : ℕ) ^ (b + 2) = 4 * r := by
        dsimp [r]
        rw [show b + 2 = b + 2 by rfl, pow_add]
        norm_num
      exact_mod_cast (show 4 * r ≤ q by simpa [hpow, q] using hp)
    have hp_lower : C - q / 2 ≤ (r + 1 : ℤ) * w := by
      have hh := mul_lt_mul_of_pos_left hwfloor.2 (by positivity : (0 : ℤ) < r + 1)
      rw [hN, hC, hN] at hh ⊢
      dsimp [v, A] at hh
      nlinarith [hq4, hr4]
    have hp_upper : (r + 1 : ℤ) * w ≤ C := by
      have hh := mul_le_mul_of_nonneg_left hwfloor.1 (by positivity : (0 : ℤ) ≤ r + 1)
      rw [hN, hC, hN] at hh ⊢
      dsimp [v, A] at hh
      nlinarith [hq4, hr4]
    have hz_lower : N - q / 2 ≤ (A : ℤ) * w + v := by
      have hh := hwfloor.2
      dsimp [A] at hh ⊢
      nlinarith [hq4]
    have hz_upper : (A : ℤ) * w + v ≤ N := by
      have hh := hwfloor.1
      dsimp [A] at hh ⊢
      nlinarith
    have hFsum4 : (F.map (actualSource k v)).sum =
        -(r + 1 : ℤ) * w + C - r / 2 + C - q / 2 := by
      rw [hFsum, hp, hAlphaval, hBetaval]
      ring
    have hnewFsum4 :
        (F.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum =
        -A * w + N - r + N - q / 2 + v := by
      rw [hnewFsum, hz, hAlphanew, hBetanew, hFresh]
      ring
    have hOldStrip : InStrip (actualSource k v) C 0
        (E ++ [beta] ++ F ++ [alpha]) := by
      have hEstrip : InStrip (actualSource k v) C 0 E :=
        nonneg_strip _ _ _ (fun x hx => le_of_lt (hEpos x hx))
          (by rw [hp]; exact hp_upper)
      have hbStrip : InStrip (actualSource k v) C hp [beta] := by
        simp only [InStrip, hBetaval]
        rw [hC]
        constructor <;> nlinarith [hp_lower, hp_upper]
      have hFstrip : InStrip (actualSource k v) C (hp + actualSource k v beta) F := by
        rw [hBetaval]
        apply nonneg_strip _ _ _ (fun x hx => le_of_lt (hFpos x hx))
        rw [hFsum4, hC]
        constructor <;> nlinarith [hp_lower, hp_upper]
      have haStrip : InStrip (actualSource k v) C
          (hp + actualSource k v beta + (F.map (actualSource k v)).sum) [alpha] := by
        simp only [InStrip, hAlphaval]
        rw [hFsum4, hC]
        constructor <;> nlinarith [hp_lower, hp_upper]
      simpa [List.append_assoc, List.map_map, Function.comp_def] using inStrip_append hEstrip
        (inStrip_append hbStrip (inStrip_append hFstrip haStrip))
    have hNewStrip : InStrip (actualSource (k + 1) (2 * v)) N 0
        (E.map Fin.castSucc ++ [fresh, beta.castSucc] ++ F.map Fin.castSucc ++
          [alpha.castSucc]) := by
      have hEstrip : InStrip (actualSource (k + 1) (2 * v)) N 0
          (E.map Fin.castSucc) := by
        apply nonneg_strip _ _ _
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨i, hi, hxi⟩ := List.mem_map.mp (hEV.mem_iff.mp (by simp [F, hy]))
          subst y
          rw [hVnew i]
          positivity
        · have hbound :
              (E.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum ≤ N := by
            rw [hz]
            exact hz_upper
          simpa only [List.map_map, Function.comp_def] using hbound
      have hfreshStrip : InStrip (actualSource (k + 1) (2 * v)) N hz [fresh] := by
        simp only [InStrip, hFresh]
        rw [hMhalf]
        constructor <;> nlinarith [hz_lower, hz_upper]
      have hbetaStrip : InStrip (actualSource (k + 1) (2 * v)) N (hz + v)
          [beta.castSucc] := by
        simp only [InStrip, hBetanew]
        rw [hMhalf]
        constructor <;> nlinarith [hz_lower, hz_upper]
      have hFstrip : InStrip (actualSource (k + 1) (2 * v)) N
          (hz + v + actualSource (k + 1) (2 * v) beta.castSucc)
          (F.map Fin.castSucc) := by
        rw [hBetanew]
        apply nonneg_strip _ _ _ (fun x hx => le_of_lt (hnewFpos' x hx))
        have hbound :
            (F.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum ≤ N := by
          rw [hnewFsum4, hMhalf]
          constructor <;> nlinarith [hz_lower, hz_upper]
        simpa only [List.map_map, Function.comp_def] using hbound
      have haStrip : InStrip (actualSource (k + 1) (2 * v)) N
          (hz + v + actualSource (k + 1) (2 * v) beta.castSucc +
            (F.map (actualSource (k + 1) (2 * v) ∘ Fin.castSucc)).sum)
          [alpha.castSucc] := by
        simp only [InStrip, hAlphanew]
        rw [hnewFsum4, hMhalf]
        constructor <;> nlinarith [hz_lower, hz_upper]
      simpa [List.append_assoc, List.map_map, Function.comp_def] using inStrip_append hEstrip
        (inStrip_append hfreshStrip (inStrip_append hbetaStrip
          (inStrip_append hFstrip haStrip)))
    let sigma := E ++ [beta] ++ F ++ [alpha]
    let j := E.length
    have hsigma : sigma.Perm (List.finRange k) := by
      have horder : (E ++ [beta] ++ F ++ [alpha]).Perm
          (E ++ F ++ [alpha, beta]) := by
        calc
          E ++ [beta] ++ F ++ [alpha] ~r E ++ F ++ [beta] ++ [alpha] := by
            simpa [List.append_assoc] using
              ((List.perm_append_comm [beta] F).append_right [alpha]).append_left E
          _ ~r E ++ F ++ [alpha] ++ [beta] := by
            simpa [List.append_assoc] using
              (List.Perm.swap beta alpha []).append_left (E ++ F)
          _ ~r E ++ F ++ [alpha, beta] := by rfl
      exact horder.trans hOldPerm
    have hnewperm :
        (E.map Fin.castSucc ++ [fresh, beta.castSucc] ++ F.map Fin.castSucc ++
          [alpha.castSucc]).Perm (List.finRange (k + 1)) := by
      have hbase := hNewPermBase
      let X := E.map Fin.castSucc
      let Y := F.map Fin.castSucc
      let x := alpha.castSucc
      let y := beta.castSucc
      let z := fresh
      have horder : X ++ [z, y] ++ Y ++ [x] ~r
          X ++ Y ++ [x, y, z] := by
        calc
          X ++ [z, y] ++ Y ++ [x] ~r
              X ++ Y ++ [z, y] ++ [x] := by
                simpa [List.append_assoc] using
                  ((List.perm_append_comm [z, y] Y).append_right [x]).append_left X
          _ ~r Y ++ X ++ [z, y] ++ [x] := by
                simpa [List.append_assoc] using
                  (List.perm_append_comm X Y).append_right ([z, y] ++ [x])
          _ ~r Y ++ X ++ [x] ++ [z, y] := by
                simpa [List.append_assoc] using
                  (List.perm_append_comm [z, y] [x]).append_left (Y ++ X)
          _ ~r X ++ Y ++ [x] ++ [z, y] := by
                simpa [List.append_assoc] using
                  (List.perm_append_comm Y X).append_right ([x] ++ [z, y])
          _ ~r X ++ Y ++ [x, y, z] := by
                simpa [List.append_assoc] using
                  (List.Perm.swap z y []).append_left (X ++ Y ++ [x])
      calc
        E.map Fin.castSucc ++ [fresh, beta.castSucc] ++ F.map Fin.castSucc ++
            [alpha.castSucc] ~r
            E.map Fin.castSucc ++ F.map Fin.castSucc ++
              [alpha.castSucc, beta.castSucc, fresh] := horder
        _ ~r List.finRange (k + 1) := by
          exact hbase
    have hneweq : earWord k sigma j =
        (E.map Fin.castSucc ++ [fresh, beta.castSucc] ++ F.map Fin.castSucc ++
          [alpha.castSucc]) := by
      simp [earWord, sigma, j]
    have hOldTotalSigma : (sigma.map (actualSource k v)).sum = 0 := by
      rw [((hsigma.trans hOldPerm.symm).map (actualSource k v)).sum_eq]
      exact hOldTotal
    have hNewTotalDesired :
        ((E.map Fin.castSucc ++ [fresh, beta.castSucc] ++ F.map Fin.castSucc ++
          [alpha.castSucc]).map (actualSource (k + 1) (2 * v))).sum = 0 := by
      have hperm := hnewperm.trans hNewPermBase.symm
      rw [(hperm.map (actualSource (k + 1) (2 * v))).sum_eq]
      exact hNewTotal
    refine ⟨sigma, j, by dsimp [j]; omega, ?_, ?_⟩
    · exact ⟨hsigma, hOldTotalSigma, by
        intro n
        simpa [Set.mem_Icc] using inStrip_prefix hOldStrip n⟩
    · rw [hneweq]
      exact ⟨hnewperm, hNewTotalDesired, by
        intro n
        simpa [Set.mem_Icc] using inStrip_prefix hNewStrip n⟩

end D5.S3.Combinatorics.Circle.TwoNegativeJointLift

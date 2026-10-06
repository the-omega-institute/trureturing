/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer
   mirror-E: none(waiver:dual-number-monodromy)
   anchors: [mathlib/module/Mathlib.Algebra.DualNumber, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Triple induction computes the metallic continuants through their linear terms. -/

import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.Ring
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedTransfer

open TrivSqZeroExt MetallicHankelData PowerSeries

/-- The two highest reversed denominator coefficients, retaining the cyclic sign. -/
noncomputable def jetWord (n : ℕ) : List (DualNumber ℤ × ℤ) :=
  if n = 1 then
    [(inl 1 + inr 1, -1), (inl 1 + inr 1, 1), (inl (-1) + inr 1, -1)]
  else (cycle n).map (fun a =>
    (inl (coeff ((fractionData n a).1 + 1) (fractionData n a).2.2) +
      inr (coeff (fractionData n a).1 (fractionData n a).2.2),
      (fractionData n a).2.1))

/-- The reversed-denominator recurrence in the ring of dual numbers. -/
def jetStep (z : DualNumber ℤ × DualNumber ℤ) (a : DualNumber ℤ × ℤ) :
    DualNumber ℤ × DualNumber ℤ := (a.1 * z.1 - inl a.2 * z.2, z.1)

/-- Induction over the repeated triples computes the whole dual-number period. -/
theorem cycle_transfer (n : ℕ) (hn : 1 ≤ n)
    (state : ℕ → DualNumber ℤ × DualNumber ℤ)
    (initial : state 0 = (1, 0))
    (recurrence : ∀ p, state (p + 1) =
      jetStep (state p) ((jetWord n)[p % (jetWord n).length]!)) (k : ℕ) :
    state (k * (jetWord n).length) =
      (inl 1 - inr ((k : ℤ) * (if n = 1 then 1 else 2 * (n : ℤ) + 1)),
        inr (2 * (k : ℤ) * (if n = 1 then 1 else 2 * (n : ℤ) + 1))) := by
  have fold_result :
      ((List.replicate k (jetWord n)).flatten).foldl jetStep (1, 0) =
        (inl 1 - inr ((k : ℤ) * (if n = 1 then 1 else 2 * (n : ℤ) + 1)),
          inr (2 * (k : ℤ) * (if n = 1 then 1 else 2 * (n : ℤ) + 1))) := by
    let A : DualNumber ℤ × ℤ := (inl 1 + inr 1, -1)
    let C : DualNumber ℤ × ℤ := (inl (-1) + inr 1, -1)
    let Z : DualNumber ℤ × ℤ := (inr 1, -1)
    let Y : DualNumber ℤ × ℤ := (inl 1, -1)
    let L := [A, A, C]
    let reps (r : ℕ) := (List.replicate r L).flatten
    let B := [Y, A, C]
    let F := [A, Z, C]
    let G := [A, Y, C]
    let J : List (DualNumber ℤ × ℤ) := [(inl 2 + inr 1, -1), (inr 1, 1)]
    let H : List (DualNumber ℤ × ℤ) :=
      [A, A, Z, (inl 2 + inr 1, 1), (inl (-1) + inr 2, -1)]
    let K := B ++ [Z] ++ F ++ G
    have repeated (r : ℕ) (z : DualNumber ℤ × DualNumber ℤ) :
        (reps (2 * r)).foldl jetStep z =
          (inl (fst z.1) + inr (snd z.1 - 2 * (r : ℤ) * fst z.1),
            inl (fst z.2) + inr (snd z.2 + 2 * (r : ℤ) *
              (2 * fst z.1 + fst z.2))) ∧
        (reps (2 * r + 1)).foldl jetStep z =
          (inl (-fst z.1) + inr (-snd z.1 + (2 * (r : ℤ) + 1) * fst z.1),
            inl (2 * fst z.1 + fst z.2) +
              inr (2 * snd z.1 + snd z.2 + 2 * fst z.1 +
                (2 * (r : ℤ) + 1) * fst z.2)) := by
      induction r generalizing z with
      | zero =>
        simp only [Nat.cast_zero, mul_zero, zero_add, reps, List.replicate_zero,
          List.replicate_one, List.flatten_nil, List.flatten_cons,
          List.nil_append, List.append_nil, List.foldl_nil]
        constructor
        · apply Prod.ext <;> apply TrivSqZeroExt.ext <;> simp
        · simp only [L, List.foldl_cons, List.foldl_nil, jetStep]
          apply Prod.ext <;> apply TrivSqZeroExt.ext <;>
          simp [jetStep, A, C, -DualNumber.inr_eq_smul_eps] <;>
          norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd] <;> ring
      | succ r ih =>
        have he : 2 * (r + 1) = 2 * r + 1 + 1 := by omega
        have ho : 2 * (r + 1) + 1 = 2 * r + 1 + 1 + 1 := by omega
        have append (m : ℕ) : reps (m + 1) = reps m ++ L := by
          simp [reps, List.replicate_succ', List.flatten_append]
        have re : reps (2 * (r + 1)) = reps (2 * r + 1) ++ L := by
          rw [he, append]
        have ro : reps (2 * (r + 1) + 1) = (reps (2 * r + 1) ++ L) ++ L := by
          rw [ho, append, append]
        rw [re, ro]
        simp only [List.foldl_append]
        rw [(ih z).2]
        constructor <;>
          simp only [L, List.foldl_cons, List.foldl_nil, jetStep] <;>
          apply Prod.ext <;> apply TrivSqZeroExt.ext <;>
          simp [jetStep, A, C, Nat.cast_add, Nat.cast_one,
            -DualNumber.inr_eq_smul_eps] <;> norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd] <;>
            ring
    have layout : jetWord n =
        if n = 1 then [A, (inl 1 + inr 1, 1), C]
        else if n = 2 then
          [(inl 2, -1), (inr 1, 1), Z, A, Z, Z, (inl 2, 1),
            (inl (-1) + inr 2, -1)]
        else if n = 3 then J ++ [Y, A, C] ++ [Z] ++ F ++ [A, Y, Z] ++
          [(inl 2 + inr 1, 1), (inl (-1) + inr 2, -1)]
        else J ++ reps (n - 3) ++ K ++ reps (n - 4) ++ H := by
      by_cases hn1 : n = 1
      · simp [jetWord, hn1, A, C]
      have hn2 : 2 ≤ n := by omega
      let I : PowerSeries ℤ := invOfUnit (1 - X) 1
      have hI : (1 - X : PowerSeries ℤ) * I = 1 := mul_invOfUnit _ _ (by simp)
      have coeffI (r : ℕ) : coeff r I = 1 := by
        induction r with
        | zero => simp [I]
        | succ r ih =>
          have hc := congrArg (coeff (r + 1)) hI
          rw [sub_mul, one_mul, map_sub] at hc
          have hx : coeff (r + 1) (X * I) = coeff r I := by
            simpa only [pow_one, Nat.add_sub_cancel] using coeff_X_pow_mul I 1 r
          rw [hx, ih] at hc
          simp only [coeff_one, Nat.succ_ne_zero, ite_false] at hc
          omega
      have geom (m r : ℕ) :
          coeff r ((1 - X ^ m) * I) = if r < m then 1 else 0 := by
        rw [sub_mul, one_mul, map_sub, coeffI, coeff_X_pow_mul']
        split_ifs <;> simp_all <;> omega
      have geom' := geom
      dsimp only [I] at geom'
      let scalar (a : TailState) : DualNumber ℤ × ℤ :=
        (inl (coeff ((fractionData n a).1 + 1) (fractionData n a).2.2) +
          inr (coeff (fractionData n a).1 (fractionData n a).2.2),
          (fractionData n a).2.1)
      have vt : scalar .v₂ = (inl 2 + inr (if n = 2 then 0 else 1), -1) ∧
          scalar .v₃ = (inr 1, 1) ∧
          scalar .v₀ = (inl 2 + inr (if n = 2 then 0 else 1), 1) ∧
          scalar .v₁ = (inl (-1) + inr 2, -1) := by
        have hk : n - 1 + 1 = n := by omega
        have hT (r : ℕ) : coeff r
            ((X : PowerSeries ℤ) * (1 - X ^ n) * I + (1 + X ^ n) * (1 - X)) =
            (if 1 ≤ r then if r - 1 < n then 1 else 0 else 0) +
              (if r = 0 then 1 else 0) - (if r = 1 then 1 else 0) +
              (if r = n then 1 else 0) - (if r = n + 1 then 1 else 0) := by
          rw [mul_assoc, map_add]
          rw [show (X : PowerSeries ℤ) * ((1 - X ^ n) * I) =
            X ^ 1 * ((1 - X ^ n) * I) by simp, coeff_X_pow_mul']
          simp only [geom, mul_sub, add_mul, mul_one, one_mul,
            ← pow_succ, map_add, map_sub, coeff_one, coeff_X, coeff_X_pow]
          split_ifs <;> simp_all <;> omega
        have hE (r : ℕ) : coeff r
            ((X : PowerSeries ℤ) * (1 - X ^ n) * I +
              (1 + X ^ n) * (1 - X) + X ^ (n + 1)) =
            coeff r ((X : PowerSeries ℤ) * (1 - X ^ n) * I +
              (1 + X ^ n) * (1 - X)) + (if r = n + 1 then 1 else 0) := by
          rw [map_add, coeff_X_pow]
        dsimp only [I] at hT hE
        simp only [scalar, fractionData, hk, hE, hT, coeff_one]
        have h0 : n ≠ 0 := by omega
        have h1 : n ≠ 1 := by omega
        by_cases h2 : n = 2
        · subst n; norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd]
        · simp [h0, h1, h2, hn, show n - 1 - 1 < n by omega,
            show n - 1 ≠ 0 by omega,
            show n - 1 ≠ 1 by omega, show n - 1 < n by omega,
            show n - 1 ≠ n + 1 by omega, show n - 2 < n by omega,
            show 1 ≤ n - 1 by omega, show n - 1 ≠ n by omega]
      have u (i : ℕ) (hi : i ≤ n - 2) :
          [.u₀ i, .u₁ i, .u₂ i].map scalar =
            [(inl 1 + inr 1, -1),
              (inl (if i = 0 then 0 else 1) + inr (if i = 1 then 0 else 1), -1),
              (if i = n - 2 then Z else C)] := by
        have hd : n - i - 2 + 1 < n - i := by omega
        have he : n - i - 2 < n - i := by omega
        simp only [List.map_cons, List.map_nil, scalar, fractionData,
          map_sub, geom', coeff_X, coeff_one]
        simp [hd, he, show i + 1 < i + 2 by omega, show i < i + 2 by omega,
          show n - i - 2 + 1 ≠ 1 ↔ i ≠ n - 2 by omega, Z, C]
        split_ifs <;> simp_all [map_sub, coeff_X, coeff_one]
      have w (i : ℕ) (hi : i < n - 2) :
          [.w₀ i, .w₁ i, .w₂ i].map scalar =
            [(inl 1 + inr (if i = n - 3 then 0 else 1), -1), A, C] := by
        have hd : n - i - 2 + 1 < n - i := by omega
        have he : n - i - 2 < n - i := by omega
        simp only [List.map_cons, List.map_nil, scalar, fractionData,
          map_sub, geom', coeff_X, coeff_one]
        simp [hd, he, A, C, show i + 1 < i + 2 by omega, show i < i + 2 by omega,
          show n - i - 2 + 1 ≠ 1 by omega,
          show n - i - 2 = 1 ↔ i = n - 3 by omega,
          show n - i - 2 ≠ 0 by omega]
        split_ifs <;> simp_all
      have wend : scalar (.w₀ (n - 2)) = Z := by
        have hk : n - (n - 2) - 2 = 0 := by omega
        have hd : n - (n - 2) = 2 := by omega
        simp [scalar, fractionData, hk, hd, map_sub, geom', coeff_X, coeff_one, Z]
      simp only [jetWord, if_neg hn1]
      change (cycle n).map scalar = _
      by_cases hn₂ : n = 2
      · subst n
        have hu := u 0 (by omega)
        simp only [cycle, Nat.reduceSub, List.range_zero, List.range_succ,
          List.flatMap_nil, List.flatMap_cons, List.nil_append, List.append_nil,
          List.map_append, List.map_cons, List.map_nil]
        rw [vt.1, vt.2.1, vt.2.2.1, vt.2.2.2, wend]
        simpa [A, Z] using hu
      · by_cases hn₃ : n = 3
        · subst n
          have hu0 := u 0 (by omega)
          have hu1 := u 1 (by omega)
          have hw0 := w 0 (by omega)
          simp only [cycle, Nat.reduceSub, List.range_succ, List.range_zero,
            List.flatMap_append, List.flatMap_singleton, List.flatMap_nil,
            List.nil_append, List.map_append]
          rw [hu0, hu1, hw0]
          simp only [List.map_cons, List.map_nil, vt.1, vt.2.1,
            vt.2.2.1, vt.2.2.2, wend]
          simp [J, F, A, C, Y, Z]
        · have hn4 : 4 ≤ n := by omega
          have ws (r : ℕ) (hr : r ≤ n - 3) :
              (((List.range r).flatMap (fun i => [.w₀ i, .w₁ i, .w₂ i])).map scalar) =
                reps r := by
            induction r with
            | zero => simp [reps]
            | succ r ih =>
              rw [List.range_succ, List.flatMap_append, List.map_append, ih (by omega)]
              simp only [List.flatMap_singleton]
              rw [w r (by omega)]
              simp [show r ≠ n - 3 by omega, A, L, reps,
                List.replicate_succ', List.flatten_append]
          have us (r : ℕ) (hr : r ≤ n - 4) :
              (((List.range' 2 r).flatMap (fun i => [.u₀ i, .u₁ i, .u₂ i])).map scalar) =
                reps r := by
            induction r with
            | zero => simp [reps]
            | succ r ih =>
              rw [List.range'_concat, List.flatMap_append, List.map_append, ih (by omega)]
              simp only [List.flatMap_singleton, one_mul]
              rw [u (2 + r) (by omega)]
              simp [show 2 + r ≠ 0 by omega, show 2 + r ≠ 1 by omega,
                show 2 + r ≠ n - 2 by omega, A, L, reps,
                List.replicate_succ', List.flatten_append]
          have wr : n - 2 = n - 3 + 1 := by omega
          have ur : n - 1 = 2 + (n - 4) + 1 := by omega
          have rangeu : List.range (n - 1) =
              [0, 1] ++ List.range' 2 (n - 4) ++ [n - 2] := by
            rw [ur, List.range_succ]
            have hx : List.range (2 + (n - 4)) = [0, 1] ++ List.range' 2 (n - 4) := by
              rw [List.range_eq_range', ← List.range'_append_1]
              rfl
            rw [hx]
            rw [show 2 + (n - 4) = n - 2 by omega]
          simp only [cycle, wr, List.range_succ, List.flatMap_append,
            List.flatMap_singleton, List.map_append]
          rw [ws _ (by omega)]
          rw [rangeu]
          simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.flatMap_singleton, List.append_nil, List.map_append]
          rw [show n - 3 + 1 = n - 2 by omega]
          rw [w (n - 3) (by omega), u 0 (by omega), u 1 (by omega),
            us _ (by omega), u (n - 2) (by omega)]
          simp only [List.map_cons, List.map_nil, vt.1, vt.2.1,
            vt.2.2.1, vt.2.2.2, wend]
          simp [hn1, hn₂, hn₃, J, K, H, B, F, G, A, C, Z, Y,
            show n - 2 ≠ 0 by omega, show n - 2 ≠ 1 by omega, show 0 ≠ n - 2 by omega,
            show 1 ≠ n - 2 by omega, List.append_assoc]
    have monodromy (z : DualNumber ℤ × DualNumber ℤ) :
        (jetWord n).foldl jetStep z =
          (inl (fst z.1) + inr (snd z.1 -
            (if n = 1 then 1 else 2 * (n : ℤ) + 1) * fst z.1),
            inl (fst z.2) + inr (snd z.2 +
              (if n = 1 then 1 else 2 * (n : ℤ) + 1) * (2 * fst z.1 + fst z.2))) := by
      rw [layout]
      by_cases hn1 : n = 1
      · simp only [hn1, ite_true, List.foldl_cons, List.foldl_nil, jetStep]
        apply Prod.ext <;> apply TrivSqZeroExt.ext <;>
        simp [jetStep, A, C, -DualNumber.inr_eq_smul_eps] <;>
        norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd] <;> ring
      · by_cases hn2 : n = 2
        · simp only [if_neg hn1, if_pos hn2, List.foldl_cons,
            List.foldl_nil, jetStep]
          apply Prod.ext <;> apply TrivSqZeroExt.ext <;>
          simp [jetStep, A, Z, hn2, -DualNumber.inr_eq_smul_eps] <;>
          norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd] <;> ring
        · by_cases hn3 : n = 3
          · simp only [if_neg hn1, if_neg hn2, if_pos hn3, List.foldl_append]
            simp only [J, F, List.foldl_cons, List.foldl_nil, jetStep]
            apply Prod.ext <;> apply TrivSqZeroExt.ext <;>
            simp [jetStep, A, C, Z, Y, hn3, -DualNumber.inr_eq_smul_eps] <;>
            norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd] <;> ring
          · have hn4 : 4 ≤ n := by omega
            simp only [if_neg hn1, if_neg hn2, if_neg hn3, List.foldl_append]
            rcases Nat.even_or_odd (n - 4) with he | ho
            · obtain ⟨r, hr⟩ := he
              have h4 : n - 4 = 2 * r := by omega
              have h3 : n - 3 = 2 * r + 1 := by omega
              have hnr : (n : ℤ) = 2 * (r : ℤ) + 4 := by
                exact_mod_cast (by omega : n = 2 * r + 4)
              rw [h4, h3, (repeated r _).2]
              simp only [K, List.foldl_append, B, F, G, List.foldl_cons, List.foldl_nil]
              rw [(repeated r _).1]
              simp only [J, H, List.foldl_cons, List.foldl_nil, jetStep]
              apply Prod.ext <;> apply TrivSqZeroExt.ext <;>
                simp [jetStep, A, C, Z, Y, hnr, -DualNumber.inr_eq_smul_eps] <;>
                norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd] <;> ring
            · obtain ⟨r, hr⟩ := ho
              have h4 : n - 4 = 2 * r + 1 := by omega
              have h3 : n - 3 = 2 * (r + 1) := by omega
              have hnr : (n : ℤ) = 2 * (r : ℤ) + 5 := by
                exact_mod_cast (by omega : n = 2 * r + 5)
              rw [h4, h3, (repeated (r + 1) _).1]
              simp only [K, List.foldl_append, B, F, G, List.foldl_cons, List.foldl_nil]
              rw [(repeated r _).2]
              simp only [J, H, List.foldl_cons, List.foldl_nil, jetStep]
              apply Prod.ext <;> apply TrivSqZeroExt.ext <;>
                simp [jetStep, A, C, Z, Y, hnr, Nat.cast_add, Nat.cast_one,
                  -DualNumber.inr_eq_smul_eps] <;>
                  norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd] <;>
                  ring
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [List.replicate_succ', List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.foldl_append]
      rw [ih, monodromy]
      by_cases hn1 : n = 1 <;>
        apply Prod.ext <;> apply TrivSqZeroExt.ext <;>
        simp [hn1, Nat.cast_add, Nat.cast_one, -DualNumber.inr_eq_smul_eps] <;>
        norm_num [TrivSqZeroExt.fst, TrivSqZeroExt.snd] <;> ring
  have length_pos : 0 < (jetWord n).length := by
    by_cases hn1 : n = 1
    · simp [jetWord, hn1]
    · have hn2 : 2 ≤ n := by omega
      have hl := (cycle_data n hn2).1
      simp only [jetWord, if_neg hn1, List.length_map]
      omega
  have segment (r i : ℕ) (hi : i ≤ (jetWord n).length) :
      state (r * (jetWord n).length + i) =
        ((jetWord n).take i).foldl jetStep (state (r * (jetWord n).length)) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hil : i < (jetWord n).length := by omega
      rw [show r * (jetWord n).length + (i + 1) =
        (r * (jetWord n).length + i) + 1 by omega, recurrence]
      have hm : (r * (jetWord n).length + i) % (jetWord n).length = i := by
        simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hil]
      rw [hm, getElem!_pos (jetWord n) i hil,
        List.take_succ_eq_append_getElem hil, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by omega)]
  have periods (r : ℕ) : state (r * (jetWord n).length) =
      ((List.replicate r (jetWord n)).flatten).foldl jetStep (1, 0) := by
    induction r with
    | zero => simpa using initial
    | succ r ih =>
      rw [show (r + 1) * (jetWord n).length =
        r * (jetWord n).length + (jetWord n).length by ring]
      rw [segment r (jetWord n).length (by omega), List.take_length, ih]
      simp only [List.replicate_succ', List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.foldl_append]
  rw [periods k]
  exact fold_result

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedTransfer

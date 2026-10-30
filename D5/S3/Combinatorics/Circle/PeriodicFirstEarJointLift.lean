/- GID: D5/S3/Combinatorics/Circle/PeriodicFirstEarJointLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/PeriodicFirstEarJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical repeated one-bit periods admit a literal first-ear joint order.
-/
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import D5.S3.Combinatorics.Circle.ThreeRowSource
import D5.S3.Combinatorics.Circle.DyadicResetSource
import D5.S3.Combinatorics.Circle.ZeroSumSubsets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift
open SourceWidth PeriodicShortening PeriodicShorteningArithmetic RunFirstEarTransport
open ThreeRowSource ZeroSumSubsets
open scoped BigOperators

private def baseValue (d a : ℕ) : ℤ :=
  if a = d - 1 then -((2 : ℤ) ^ (d - 1) - 1) else (2 : ℤ) ^ a

private theorem base_source (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    actualSource d 1 i = baseValue d i.val := by
  obtain ⟨hN, hodd⟩ := TwoRunSource.modulus_positive_odd d (by omega)
  by_cases hi : i.val = d - 1
  · have hpow : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
      rw [show d = (d - 1) + 1 by omega, pow_succ]
      ring
    have hhalf : modulus d / 2 = (2 : ℤ) ^ (d - 1) - 1 := by
      unfold modulus
      rw [hpow]
      omega
    unfold actualSource baseValue
    simp only [hi, if_pos]
    apply centered_unique hN hodd
    · rw [hhalf]
      constructor <;> omega
    · exact centered_bounds hN hodd _
    rw [centered_mod]
    have he : -((2 : ℤ) ^ (d - 1) - 1) + modulus d = (2 : ℤ) ^ (d - 1) := by
      unfold modulus
      rw [hpow]
      ring
    rw [← he, Int.add_emod_right]
  · have hi' : i.val ≤ d - 2 := by omega
    have hhalf : modulus d / 2 = (2 : ℤ) ^ (d - 1) - 1 := by
      unfold modulus
      have hpow : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
        rw [show d = (d - 1) + 1 by omega, pow_succ]
        ring
      rw [hpow]
      omega
    unfold actualSource baseValue
    simp only [hi, if_neg]
    apply centered_unique hN hodd
    · exact centered_bounds hN hodd _
    · rw [hhalf]
      have hp : 0 < (2 : ℤ) ^ i.val := by positivity
      have hle : (2 : ℤ) ^ i.val ≤ (2 : ℤ) ^ (d - 2) := by
        exact pow_le_pow_right₀ (by norm_num) hi'
      constructor <;> omega
    rfl

private theorem quotient_relation (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    ((2 : ℤ) ^ d - 1) *
        (((2 ^ (d * m) - 1) / (2 ^ d - 1) : ℕ) : ℤ) =
      (2 : ℤ) ^ (d * m) - 1 := by
  have h := geom_mul d m (by omega)
  simpa [geom, pow_mul] using h

private theorem quotient_bounds (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let k := d * m
    let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
    0 < k ∧ t < 2 ^ (k - 1) ∧ t ≤ 2 ^ (k - 1) - 1 := by
  dsimp only
  have hk : 2 ≤ d * m := by nlinarith
  have hden : (3 : ℕ) ≤ 2 ^ d - 1 := by
    have hp : 4 ≤ (2 : ℕ) ^ d := by
      exact pow_le_pow_right₀ (by decide) hd
    omega
  have hrel := quotient_relation d m hd hm
  have hpow : (2 : ℤ) ^ (d * m) = 2 * (2 : ℤ) ^ (d * m - 1) := by
    rw [show d * m = (d * m - 1) + 1 by omega, pow_succ]
    ring
  have hT : 0 ≤ (((2 ^ (d * m) - 1) / (2 ^ d - 1) : ℕ) : ℤ) :=
    Int.natCast_nonneg _
  have hA : 0 < (2 : ℤ) ^ (d * m - 1) := by positivity
  have hltZ : (((2 ^ (d * m) - 1) / (2 ^ d - 1) : ℕ) : ℤ) <
      (2 : ℤ) ^ (d * m - 1) := by
    rw [hpow] at hrel
    have hdZ : (3 : ℤ) ≤ (2 : ℤ) ^ d - 1 := by exact_mod_cast hden
    nlinarith
  have hlt : (2 ^ (d * m) - 1) / (2 ^ d - 1) < 2 ^ (d * m - 1) := by
    exact_mod_cast hltZ
  exact ⟨by omega, hlt, Nat.le_pred_of_lt hlt⟩

private theorem old_source (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (i : Fin (d * m)) :
    actualSource (d * m) ((2 ^ (d * m) - 1) / (2 ^ d - 1)) i =
      (((2 ^ (d * m) - 1) / (2 ^ d - 1) : ℕ) : ℤ) *
        baseValue d (i.val % d) := by
  have hrep := repeated_source d m 1 (by omega) (by omega)
    (⟨i.val, by simpa [Nat.mul_comm] using i.isLt⟩ : Fin (m * d))
  have hquot := multiplier_quotient d m (by omega)
  have hlt : (2 ^ (d * m) - 1) / (2 ^ d - 1) < 2 ^ (d * m) - 1 := by
    obtain ⟨_, hh, _⟩ := quotient_bounds d m hd hm
    have hk : 1 ≤ d * m := by omega
    have hp : 0 < (2 : ℕ) ^ (d * m - 1) := pow_pos (by decide) _
    have hpow : 2 ^ (d * m) = 2 * 2 ^ (d * m - 1) := by
      rw [show d * m = (d * m - 1) + 1 by omega, pow_succ]
    omega
  rw [hquot] at hrep
  rw [Nat.mul_one, Nat.mod_eq_of_lt hlt] at hrep
  have hbase := base_source d hd ⟨i.val % d, Nat.mod_lt _ (by omega)⟩
  simpa [Nat.mul_comm] using hrep.trans
    (congrArg (fun z : ℤ =>
      (((2 ^ (d * m) - 1) / (2 ^ d - 1) : ℕ) : ℤ) * z) hbase)

private theorem sum_linear {α : Type*} (l : List α) (f g : α → ℤ) (u v : ℤ) :
    (l.map (fun x => u * f x + v * g x)).sum =
      u * (l.map f).sum + v * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem prefix_formula (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) (n : ℕ) :
    let k := d * m
    let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
    (((List.finRange k).take n).map (actualSource k t)).sum =
      if n ≤ k then (t : ℤ) * ((2 : ℤ) ^ (n % d) - 1) else 0 := by
  dsimp only
  let k := d * m
  let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n < k
    · have ht := List.take_append_getElem (List.finRange k) n (by simp; omega)
      rw [← ht, List.map_append, List.sum_append]
      have hi := old_source d m hd hm ⟨n, hn⟩
      rw [ih, if_pos (by omega), hi]
      by_cases hwrap : n % d = d - 1
      · have hnext : (n + 1) % d = 0 := by omega
        simp [hwrap, hnext, baseValue]
      · have hlt : n % d < d - 1 := by omega
        have hnext : (n + 1) % d = n % d + 1 := by omega
        simp [hwrap, hnext, baseValue]
        rw [pow_succ]
        ring
    · have hnk : k ≤ n := by omega
      have htake : (List.finRange k).take n = List.finRange k :=
        List.take_of_length_le (by simp; omega)
      have htake' : (List.finRange k).take (n + 1) = List.finRange k :=
        List.take_of_length_le (by simp; omega)
      rw [htake, htake', if_neg (by omega)] at ih ⊢
      rw [source_cycle (by omega) t |>.2.1]
      exact ih

private theorem prefix_bounds (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) (n : ℕ) :
    let k := d * m
    let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
    let H := (((List.finRange k).take n).map (actualSource k t)).sum
    0 ≤ H ∧ 2 * H + (t : ℤ) ≤ modulus k := by
  dsimp only
  let k := d * m
  let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
  rw [prefix_formula d m hd hm n]
  by_cases hn : n ≤ k
  · simp only [if_pos hn]
    have hj : n % d ≤ d - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ (by omega))
    have hp : (2 : ℤ) ^ (n % d) ≤ (2 : ℤ) ^ (d - 1) :=
      pow_le_pow_right₀ (by norm_num) hj
    have hrel := quotient_relation d m hd hm
    have hpow : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
      rw [show d = (d - 1) + 1 by omega, pow_succ]
      ring
    have ht0 : 0 ≤ (t : ℤ) := Int.natCast_nonneg _
    constructor
    · positivity
    · unfold modulus
      rw [hpow] at hrel
      nlinarith
  · have hrel := quotient_relation d m hd hm
    have ht0 : 0 ≤ (t : ℤ) := Int.natCast_nonneg _
    have hN : 0 ≤ modulus k := by
      unfold modulus
      have : 1 ≤ (2 : ℤ) ^ k := by positivity
      omega
    simp only [if_neg hn]
    constructor <;> nlinarith

private theorem charge_prefix_bound (k t : ℕ) (hk : 2 ≤ k)
    (ht : t ≤ 2 ^ (k - 1) - 1) (n : ℕ) :
    0 ≤ (((List.finRange k).take n).map (charge k t)).sum ∧
      (((List.finRange k).take n).map (charge k t)).sum ≤ (t : ℤ) := by
  have hq := charge_sum k t hk ht
  have hnonneg : ∀ i : Fin k, 0 ≤ charge k t i :=
    fun i => (digit_data k t hk ht i).1
  have hp : 0 ≤ (((List.finRange k).take n).map (charge k t)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hnonneg i
  have hd : 0 ≤ ((List.finRange k).drop n).map (charge k t) |>.sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hnonneg i
  have he := congrArg (fun l : List (Fin k) => (l.map (charge k t)).sum)
    (List.take_append_drop n (List.finRange k))
  simp only [List.map_append, List.sum_append] at he
  rw [← hq] at he
  exact ⟨hp, by omega⟩

private theorem fresh_value (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let k := d * m
    let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
    actualSource (k + 1) (2 * t) (Fin.last k) = (t : ℤ) := by
  dsimp only
  let k := d * m
  let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
  have hq := quotient_bounds d m hd hm
  have hk : 2 ≤ k := by omega
  have hN : 0 < modulus (k + 1) := (TwoRunSource.modulus_positive_odd (k + 1) (by omega)).1
  have hodd := (TwoRunSource.modulus_positive_odd (k + 1) (by omega)).2
  have hhalf : modulus (k + 1) / 2 = modulus k := by
    unfold modulus
    rw [pow_succ]
    omega
  have htN : 0 ≤ (t : ℤ) ∧ (t : ℤ) ≤ modulus (k + 1) / 2 := by
    rw [hhalf]
    constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast (show t ≤ 2 ^ (k - 1) - 1 by exact hq.2.2)
  change centered (modulus (k + 1))
      ((2 : ℤ) ^ k * ((2 * t : ℕ) : ℤ)) = (t : ℤ)
  calc
    _ = centered (modulus (k + 1)) ((2 : ℤ) ^ (k + 1) * (t : ℤ)) := by
      rw [pow_succ]
      norm_num [Nat.cast_mul]
      ring
    _ = centered (modulus (k + 1)) (t : ℤ) := centered_full_period (k + 1) t
    _ = (t : ℤ) := by
      apply centered_unique hN hodd htN (centered_bounds hN hodd _)
      rfl

set_option maxHeartbeats 2000000 in
public theorem periodic_first_ear_joint_lift (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let k := d * m
    let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
    OriginalOrder k t (List.finRange k) ∧
      OriginalOrder (k + 1) (2 * t) (earWord k (List.finRange k) 0) := by
  dsimp only
  let k := d * m
  let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
  have hq := quotient_bounds d m hd hm
  have hk : 2 ≤ k := by omega
  have hsum : ((List.finRange k).map (actualSource k t)).sum = 0 :=
    (source_cycle (by omega) t).2.1
  have hold : OriginalOrder k t (List.finRange k) := by
    refine ⟨List.Perm.refl _, hsum, ?_⟩
    intro n
    have hh := prefix_bounds d m hd hm n
    change 0 ≤ (((List.finRange k).take n).map (actualSource k t)).sum ∧
      (((List.finRange k).take n).map (actualSource k t)).sum ≤ modulus k / 2
    constructor
    · exact hh.1
    · nlinarith [hh.2]
  have hnewperm : (earWord k (List.finRange k) 0).Perm (List.finRange (k + 1)) := by
    have hp := (List.Perm.refl (List.finRange k)).map Fin.castSucc
    have hp' := hp.append_right [Fin.last k]
    simpa [earWord, List.finRange_succ_last] using hp'
  have hdigits := fun i : Fin k => digit_data k t hk (by exact hq.3) i
  have hnew : OriginalOrder (k + 1) (2 * t) (earWord k (List.finRange k) 0) := by
    refine ⟨hnewperm, ?_, ?_⟩
    · rw [hnewperm.map (actualSource (k + 1) (2 * t)).sum_eq]
      exact (source_cycle (by omega) (2 * t)).2.1
    · intro n
      cases n with
      | zero => simp [earWord]
      | succ n =>
        have hqpref := charge_prefix_bound k t hk hq.3 n
        have holdpref := prefix_bounds d m hd hm n
        have hrel :
            ((((List.finRange k).take n).map
              (fun i => actualSource (k + 1) (2 * t) i.castSucc)).sum) =
              2 * (((List.finRange k).take n).map (actualSource k t)).sum -
                (((List.finRange k).take n).map (charge k t)).sum := by
          rw [← List.map_take, List.map_map]
          have hmapp := List.map_congr_left (l := List.finRange k)
            (fun i hi => (hdigits i).2.2)
          rw [hmapp]
          have hs := sum_linear ((List.finRange k).take n)
            (actualSource k t) (charge k t) 2 (-1)
          simpa [sub_eq_add_neg] using hs
        simp only [earWord, List.map_nil, List.nil_append, List.take_succ_cons,
          List.map_cons, List.sum_cons, List.take_map]
        rw [hrel]
        have hf := fresh_value d m hd hm
        rw [hf]
        have hhalf : modulus (k + 1) / 2 = modulus k := by
          unfold modulus
          rw [pow_succ]
          omega
        rw [hhalf]
        constructor <;> nlinarith [holdpref.1, holdpref.2, hqpref.1, hqpref.2]
  exact ⟨hold, hnew⟩

end D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift

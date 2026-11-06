/- GID: D5/S3/Combinatorics/Circle/MersennePhaseNoncyclicFamily
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/MersennePhaseNoncyclicFamily
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.GCD.Basic]
   utility: none
   digest: Exact physical zero classification and count for the admissible three-phase family. -/
module

public import D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets
import all D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets
import all D5.S3.Combinatorics.Circle.TwoBitZeroSubsets
public import D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace
public import D5.S3.Combinatorics.Circle.TernaryPhaseZeroCount
public import Mathlib.Data.Nat.Prime.Basic

/-! # The admissible three-phase Mersenne family

Every original label is retained in the unique classification and exact count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily

open scoped BigOperators
open SourceWidth ZeroSumSubsets

open private actual_zero_iff_reduced_dvd
  from D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets

open private rotate_val
  from D5.S3.Combinatorics.Circle.TwoBitZeroSubsets

/-- Select complete physical phase fibres. All three labels of a selected
phase remain distinct, regardless of equality between source values. -/
def phaseLift (d : ℕ) (B : Finset (Fin d)) : Finset (Fin (3 * d)) :=
  Finset.univ.filter (fun i => ∃ j ∈ B, i.val % d = j.val)

/- Read a phase selection at the first physical representative. This is used
both to force the unique classification witness and to invert the count map. -/
private def phaseRead (d : ℕ) (hd : 0 < d)
    (A : Finset (Fin (3 * d))) : Finset (Fin d) :=
  Finset.univ.filter (fun j =>
    (⟨j.val, by have := j.isLt; omega⟩ : Fin (3 * d)) ∈ A)

private theorem mem_phaseLift {d : ℕ} (hd : 0 < d)
    (B : Finset (Fin d)) (i : Fin (3 * d)) :
    i ∈ phaseLift d B ↔ (⟨i.val % d, Nat.mod_lt _ hd⟩ : Fin d) ∈ B := by
  classical
  simp only [phaseLift, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' : (⟨i.val % d, Nat.mod_lt _ hd⟩ : Fin d) = j := Fin.ext he
    simpa only [hj'] using hj
  · intro hi
    exact ⟨⟨i.val % d, Nat.mod_lt _ hd⟩, hi, rfl⟩

private theorem phaseRead_phaseLift (d : ℕ) (hd : 0 < d)
    (B : Finset (Fin d)) : phaseRead d hd (phaseLift d B) = B := by
  classical
  apply Finset.ext
  intro j
  let i : Fin (3 * d) := ⟨j.val, by have := j.isLt; omega⟩
  have he : (⟨i.val % d, Nat.mod_lt _ hd⟩ : Fin d) = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  simp only [phaseRead, Finset.mem_filter, Finset.mem_univ, true_and]
  change i ∈ phaseLift d B ↔ j ∈ B
  rw [mem_phaseLift hd, he]

/- New physical-orbit inference: an invariant set contains either all or none
of j, j+d, j+2d. No binary-mask or general cyclic-permutation library is rebuilt. -/
private theorem rotation_eq_phaseLift (d : ℕ) (hd : 0 < d)
    (A : Finset (Fin (3 * d)))
    (hA : A.image ((finRotate (3 * d) : Equiv.Perm (Fin (3 * d))) ^ d) = A) :
    A = phaseLift d (phaseRead d hd A) := by
  classical
  let R : Equiv.Perm (Fin (3 * d)) := finRotate (3 * d)
  have hstep (i : Fin (3 * d)) : (R ^ d) i ∈ A ↔ i ∈ A := by
    constructor
    · intro hi
      have hi' : (R ^ d) i ∈ A.image (R ^ d) := by
        rw [hA]
        exact hi
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hi'
      have hxi : x = i := (R ^ d).injective he
      simpa only [hxi] using hx
    · intro hi
      rw [← hA]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  apply Finset.ext
  intro i
  let j : Fin d := ⟨i.val % d, Nat.mod_lt _ hd⟩
  let p0 : Fin (3 * d) := ⟨j.val, by have := j.isLt; omega⟩
  let p1 : Fin (3 * d) := ⟨j.val + d, by have := j.isLt; omega⟩
  let p2 : Fin (3 * d) := ⟨j.val + 2 * d, by have := j.isLt; omega⟩
  have h01 : (R ^ d) p0 = p1 := by
    apply Fin.ext
    change (((finRotate (3 * d) : Equiv.Perm (Fin (3 * d))) ^ d) p0).val =
      j.val + d
    rw [rotate_val (by omega) (by omega)]
    exact Nat.mod_eq_of_lt (by dsimp [p0]; have := j.isLt; omega)
  have h12 : (R ^ d) p1 = p2 := by
    apply Fin.ext
    change (((finRotate (3 * d) : Equiv.Perm (Fin (3 * d))) ^ d) p1).val =
      j.val + 2 * d
    rw [rotate_val (by omega) (by omega)]
    have he : p1.val + d = j.val + 2 * d := by dsimp [p1]; omega
    rw [he, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  have hm1 : p1 ∈ A ↔ p0 ∈ A := by simpa only [h01] using hstep p0
  have hm21 : p2 ∈ A ↔ p1 ∈ A := by simpa only [h12] using hstep p1
  have hm2 : p2 ∈ A ↔ p0 ∈ A := hm21.trans hm1
  have hmem : i ∈ A ↔ p0 ∈ A := by
    have hquot : i.val / d < 3 := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using i.isLt)
    have hcases : i.val / d = 0 ∨ i.val / d = 1 ∨ i.val / d = 2 := by
      have exhaustive : ∀ q : Fin 3, q.val = 0 ∨ q.val = 1 ∨ q.val = 2 := by decide
      exact exhaustive ⟨i.val / d, hquot⟩
    have he := Nat.mod_add_div i.val d
    rcases hcases with h | h | h
    · have hi : i = p0 := by
        apply Fin.ext
        dsimp [p0, j]
        simp only [h, mul_zero, add_zero] at he
        omega
      rw [hi]
    · have hi : i = p1 := by
        apply Fin.ext
        dsimp [p1, j]
        simp only [h, mul_one] at he
        omega
      rw [hi]
      exact hm1
    · have hi : i = p2 := by
        apply Fin.ext
        dsimp [p2, j]
        simp only [h, mul_two] at he
        omega
      rw [hi]
      exact hm2
  rw [mem_phaseLift hd]
  change i ∈ A ↔ j ∈ phaseRead d hd A
  simpa only [phaseRead, Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/- Copied only as a consumed private helper from the supplied ArithmeticSupport.lean
(SHA256 f6323979fcaee41712bb9f735f30ce2d7eb74107ab564d962957b5ac061fc622).
This arithmetic argument is checked as part of the composition. -/
private lemma phase_scaled_gcd (d : ℕ) (hd : 0 < d) :
    Nat.gcd ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) (2 ^ (3 * d) - 1) =
      (2 ^ d - 1) * Nat.gcd (2 ^ (d + 1) - 3) 19 := by
  let B : ℕ := 2 ^ d
  let m : ℕ := 2 ^ (d + 1) - 3
  let q : ℕ := B ^ 2 + B + 1
  have hB : 2 ≤ B := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    change 2 ≤ (2 : ℕ) ^ (k + 1)
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
    omega
  have hm : m + 3 = 2 * B := by
    have hmul : 3 ≤ 2 * B := by omega
    have hpow : (2 : ℕ) ^ (d + 1) = 2 * B := by
      change (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d
      rw [pow_succ, Nat.mul_comm]
    change (2 ^ (d + 1) - 3) + 3 = 2 * B
    rw [hpow, Nat.sub_add_cancel hmul]
  have hodd : Odd m := by
    exact ⟨B - 2, by omega⟩
  have htwo : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hodd
  have hfour : Nat.Coprime 4 m := by
    simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using htwo.pow_left 2
  have hpoly : m ^ 2 + 8 * m + 19 = 4 * q := by
    have hs : (m + 3) ^ 2 = (2 * B) ^ 2 :=
      congrArg (fun x : ℕ => x ^ 2) hm
    change m ^ 2 + 8 * m + 19 = 4 * (B ^ 2 + B + 1)
    nlinarith only [hm, hs]
  have hpow3 : (2 : ℕ) ^ (3 * d) = B ^ 3 := by
    change (2 : ℕ) ^ (3 * d) = (2 ^ d) ^ 3
    rw [← pow_mul, Nat.mul_comm 3 d]
  have hfactor : (2 : ℕ) ^ (3 * d) - 1 = (B - 1) * q := by
    rw [hpow3]
    change B ^ 3 - 1 = (B - 1) * (B ^ 2 + B + 1)
    rw [Nat.sub_mul, one_mul]
    have hexpand : B * (B ^ 2 + B + 1) = B ^ 3 + (B ^ 2 + B) := by ring
    rw [hexpand]
    omega
  have hmq : Nat.gcd m q = Nat.gcd m 19 := by
    calc
      Nat.gcd m q = Nat.gcd m (4 * q) := by
        rw [Nat.gcd_comm m q, Nat.gcd_comm m (4 * q)]
        exact (Nat.Coprime.gcd_mul_left_cancel q hfour).symm
      _ = Nat.gcd m (m ^ 2 + 8 * m + 19) :=
        congrArg (Nat.gcd m) hpoly.symm
      _ = Nat.gcd m (19 + (m + 8) * m) := by
        congr 1
        ring
      _ = Nat.gcd m 19 := Nat.gcd_add_mul_right_right m 19 (m + 8)
  change Nat.gcd ((B - 1) * m) (2 ^ (3 * d) - 1) =
    (B - 1) * Nat.gcd m 19
  rw [hfactor, Nat.gcd_mul_left, hmq]

/- The literal signed trace coefficients, still indexed by every phase label. -/
private def phaseWeight (d : ℕ) (j : Fin d) : ℤ :=
  (if j.val = d - 3 then 1 else 0) - (if j.val = d - 1 then 1 else 0)

/- Physical fibre transport, using the fixed public trace API verbatim. -/
private theorem phaseLift_sum (d : ℕ) (hd : 3 ≤ d) (B : Finset (Fin d)) :
    (∑ i ∈ phaseLift d B,
      actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) =
        modulus (3 * d) * ∑ j ∈ B, phaseWeight d j := by
  classical
  have hdpos : 0 < d := by omega
  let rho : Fin (3 * d) → Fin d := fun i => ⟨i.val % d, Nat.mod_lt _ hdpos⟩
  have hlift : Finset.univ.filter (fun i : Fin (3 * d) => rho i ∈ B) =
      phaseLift d B := by
    apply Finset.ext
    intro i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (mem_phaseLift hdpos B i).symm
  have hfibre (j : Fin d) :
      Finset.univ.filter (fun i : Fin (3 * d) => rho i = j) =
        Finset.univ.filter (fun i : Fin (3 * d) => i.val % d = j.val) := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        congrArg Fin.val (Finset.mem_filter.mp hi).2⟩
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Fin.ext (Finset.mem_filter.mp hi).2⟩
  calc
    _ = ∑ j ∈ B, ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * d) => rho i = j),
        actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i := by
      rw [← hlift]
      exact (Finset.sum_fiberwise_eq_sum_filter Finset.univ B rho
        (actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)))).symm
    _ = ∑ j ∈ B, modulus (3 * d) * phaseWeight d j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hfibre j]
      exact MersennePhaseThreeTrace.actual_phase_trace d hd j
    _ = _ := (Finset.mul_sum B (phaseWeight d) (modulus (3 * d))).symm

private theorem phaseLift_zero_iff (d : ℕ) (hd : 3 ≤ d) (B : Finset (Fin d)) :
    (∑ i ∈ phaseLift d B,
      actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0 ↔
        (∑ j ∈ B, phaseWeight d j) = 0 := by
  have hpow : (2 : ℤ) ≤ 2 ^ (3 * d) := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (by omega : 1 ≤ 3 * d))
  have hN : modulus (3 * d) ≠ 0 := by dsimp [modulus]; omega
  rw [phaseLift_sum d hd B, mul_eq_zero, or_iff_right hN]

private theorem phaseWeight_zero_iff_pair (d : ℕ) (hd : 3 ≤ d)
    (B : Finset (Fin d)) :
    (∑ j ∈ B, phaseWeight d j) = 0 ↔
      ((⟨d - 3, by omega⟩ : Fin d) ∈ B ↔ (⟨d - 1, by omega⟩ : Fin d) ∈ B) := by
  classical
  let p : Fin d := ⟨d - 3, by omega⟩
  let m : Fin d := ⟨d - 1, by omega⟩
  have hp (j : Fin d) : j.val = d - 3 ↔ j = p := by
    change j.val = p.val ↔ j = p
    exact Fin.ext_iff.symm
  have hm (j : Fin d) : j.val = d - 1 ↔ j = m := by
    change j.val = m.val ↔ j = m
    exact Fin.ext_iff.symm
  have hsum : (∑ j ∈ B, phaseWeight d j) =
      (if p ∈ B then (1 : ℤ) else 0) - (if m ∈ B then (1 : ℤ) else 0) := by
    simp only [phaseWeight, Finset.sum_sub_distrib, hp, hm]
    simp
  rw [hsum]
  change ((if p ∈ B then (1 : ℤ) else 0) - (if m ∈ B then (1 : ℤ) else 0) = 0) ↔
    (p ∈ B ↔ m ∈ B)
  by_cases hpB : p ∈ B <;> by_cases hmB : m ∈ B <;> simp [hpB, hmB]

/-- Every physical integer-zero subset is uniquely a union of complete phases,
and selects the two exceptional phases together. The domain is all admissible
d ≥ 3 and all subsets of the original 3*d physical labels. -/
theorem actual_zero_iff_phase_pair (d : ℕ) (hd : 3 ≤ d)
    (h19 : ¬19 ∣ (2 ^ (d + 1) - 3)) (A : Finset (Fin (3 * d))) :
    (∑ i ∈ A, actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0 ↔
      ∃! B : Finset (Fin d), A = phaseLift d B ∧
        ((⟨d - 3, by omega⟩ : Fin d) ∈ B ↔ (⟨d - 1, by omega⟩ : Fin d) ∈ B) := by
  classical
  have hdpos : 0 < d := by omega
  have hk : 0 < 3 * d := by omega
  constructor
  · intro hz
    have hN : 0 < (2 : ℕ) ^ (3 * d) - 1 := by
      have hp := Nat.one_lt_two_pow (ne_of_gt hk)
      omega
    have hprime : Nat.Prime 19 := by norm_num
    have hgcd19 : Nat.gcd (2 ^ (d + 1) - 3) 19 = 1 :=
      (hprime.coprime_iff_not_dvd.mpr h19).symm
    have hgcd : Nat.gcd ((2 ^ d - 1) * (2 ^ (d + 1) - 3))
        (2 ^ (3 * d) - 1) = 2 ^ d - 1 := by
      rw [phase_scaled_gcd d hdpos, hgcd19, Nat.mul_one]
    have hq := quotient_dvd hN (zero_mask_dvd A hz)
    rw [hgcd] at hq
    have hgd : Nat.gcd d (3 * d) = d := by
      simp [Nat.mul_comm]
    have hgminus : Nat.gcd (2 ^ d - 1) (2 ^ (3 * d) - 1) = 2 ^ d - 1 := by
      rw [Nat.pow_sub_one_gcd_pow_sub_one, hgd]
    /- Consumed local composition of the two existing minus-seed bridges.
    Modular zero is used only to force phase unions, never as integer zero. -/
    have hminus := (actual_zero_iff_reduced_dvd (3 * d) d hk A).mpr
      (by simpa only [hgminus] using hq)
    have hrot :=
      (MersenneDifferenceZeroSubsets.actual_zero_iff_rotation (3 * d) d hk A).mp hminus
    have hAB := rotation_eq_phaseLift d hdpos A hrot
    let B := phaseRead d hdpos A
    have hpair :
        ((⟨d - 3, by omega⟩ : Fin d) ∈ B ↔ (⟨d - 1, by omega⟩ : Fin d) ∈ B) := by
      apply (phaseWeight_zero_iff_pair d hd B).mp
      apply (phaseLift_zero_iff d hd B).mp
      rw [← hAB]
      exact hz
    refine ⟨B, ⟨hAB, hpair⟩, ?_⟩
    intro C hC
    calc
      C = phaseRead d hdpos (phaseLift d C) := (phaseRead_phaseLift d hdpos C).symm
      _ = phaseRead d hdpos A := congrArg (phaseRead d hdpos) hC.1.symm
      _ = B := rfl
  · rintro ⟨B, ⟨hAB, hpair⟩, _⟩
    rw [hAB]
    exact (phaseLift_zero_iff d hd B).mpr ((phaseWeight_zero_iff_pair d hd B).mpr hpair)

/-- Exact count over all original physical subsets, obtained by the phase
fibre bijection and the existing general ternary-label zero-subset count. -/
theorem actual_zero_subsets_card (d : ℕ) (hd : 3 ≤ d)
    (h19 : ¬19 ∣ (2 ^ (d + 1) - 3)) :
    (Finset.univ.filter (fun A : Finset (Fin (3 * d)) =>
      (∑ i ∈ A, actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0)).card =
        2 ^ (d - 1) := by
  classical
  have hdpos : 0 < d := by omega
  let p : Fin d := ⟨d - 3, by omega⟩
  let m : Fin d := ⟨d - 1, by omega⟩
  have hpm : p ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [p, m] at hv
    omega
  have hdiff : d - 3 ≠ d - 1 := by omega
  have hpositive (j : Fin d) : phaseWeight d j = 1 ↔ j = p := by
    by_cases hp : j.val = d - 3 <;> by_cases hm : j.val = d - 1
    · omega
    · simp [phaseWeight, hp, hm, Fin.ext_iff, p, hdiff, Ne.symm hdiff]
    · simp [phaseWeight, hp, hm, Fin.ext_iff, p, hdiff, Ne.symm hdiff]
    · simp [phaseWeight, hp, hm, Fin.ext_iff, p, hdiff, Ne.symm hdiff]
  have hnegative (j : Fin d) : phaseWeight d j = -1 ↔ j = m := by
    by_cases hp : j.val = d - 3 <;> by_cases hm : j.val = d - 1
    · omega
    · simp [phaseWeight, hp, hm, Fin.ext_iff, m, hdiff, Ne.symm hdiff]
    · simp [phaseWeight, hp, hm, Fin.ext_iff, m, hdiff, Ne.symm hdiff]
    · simp [phaseWeight, hp, hm, Fin.ext_iff, m, hdiff, Ne.symm hdiff]
  have hu (j : Fin d) :
      phaseWeight d j = -1 ∨ phaseWeight d j = 0 ∨ phaseWeight d j = 1 := by
    by_cases hp : j.val = d - 3 <;> by_cases hm : j.val = d - 1 <;>
      simp [phaseWeight, hp, hm, hdiff, Ne.symm hdiff]
  have hzero (j : Fin d) : phaseWeight d j = 0 ↔ j ≠ p ∧ j ≠ m := by
    constructor
    · intro hz
      constructor
      · intro hj
        have hp := (hpositive j).mpr hj
        omega
      · intro hj
        have hm := (hnegative j).mpr hj
        omega
    · rintro ⟨hp, hm⟩
      rcases hu j with hn | hz | hpos
      · exact False.elim (hm ((hnegative j).mp hn))
      · exact hz
      · exact False.elim (hp ((hpositive j).mp hpos))
  have hpfilter : Finset.univ.filter (fun j : Fin d => phaseWeight d j = 1) = {p} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, hpositive]
  have hmfilter : Finset.univ.filter (fun j : Fin d => phaseWeight d j = -1) = {m} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, hnegative]
  have hzfilter : Finset.univ.filter (fun j : Fin d => phaseWeight d j = 0) =
      Finset.univ \ {p, m} := by
    ext j
    simp [hzero, not_or]
  have hpcard : (Finset.univ.filter (fun j : Fin d => phaseWeight d j = 1)).card = 1 := by
    rw [hpfilter]
    simp
  have hmcard : (Finset.univ.filter (fun j : Fin d => phaseWeight d j = -1)).card = 1 := by
    rw [hmfilter]
    simp
  have hzcard : (Finset.univ.filter (fun j : Fin d => phaseWeight d j = 0)).card =
      d - 2 := by
    rw [hzfilter, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hpm]
  have htransport :
      (Finset.univ.filter (fun A : Finset (Fin (3 * d)) =>
        (∑ i ∈ A, actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0)).card =
          (Finset.univ.filter (fun B : Finset (Fin d) =>
            (∑ j ∈ B, phaseWeight d j) = 0)).card := by
    refine Finset.card_nbij' (phaseRead d hdpos) (phaseLift d) ?_ ?_ ?_ ?_
    · intro A hA
      have hz := (Finset.mem_filter.mp hA).2
      obtain ⟨B, ⟨hAB, hpair⟩, _⟩ := (actual_zero_iff_phase_pair d hd h19 A).mp hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hAB, phaseRead_phaseLift]
      exact (phaseWeight_zero_iff_pair d hd B).mpr hpair
    · intro B hB
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (phaseLift_zero_iff d hd B).mpr (Finset.mem_filter.mp hB).2⟩
    · intro A hA
      have hz := (Finset.mem_filter.mp hA).2
      obtain ⟨B, ⟨hAB, _⟩, _⟩ := (actual_zero_iff_phase_pair d hd h19 A).mp hz
      rw [hAB, phaseRead_phaseLift]
    · intro B _
      exact phaseRead_phaseLift d hdpos B
  calc
    _ = (Finset.univ.filter (fun B : Finset (Fin d) =>
        (∑ j ∈ B, phaseWeight d j) = 0)).card := htransport
    _ = 2 ^ (Finset.univ.filter (fun j : Fin d => phaseWeight d j = 0)).card *
        Nat.choose
          ((Finset.univ.filter (fun j : Fin d => phaseWeight d j = 1)).card +
            (Finset.univ.filter (fun j : Fin d => phaseWeight d j = -1)).card)
          (Finset.univ.filter (fun j : Fin d => phaseWeight d j = 1)).card :=
      TernaryPhaseZeroCount.zero_subsets_card d (phaseWeight d) hu
    _ = 2 ^ (d - 1) := by
      rw [hzcard, hpcard, hmcard]
      norm_num [show d - 1 = (d - 2) + 1 by omega, pow_succ]

end D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily

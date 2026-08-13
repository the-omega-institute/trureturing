/- GID: D5/S1/Deficit/FixedModulusNoncongruence
   generality: I
   mirror-B: D5/B/S1/Deficit/FixedModulusNoncongruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden-addition deficit is not determined by any fixed modulus at least two. -/

import D5.S1.Deficit.DeficitInteger
import D5.S1.Deficit.DoubleFaceLength
import D5.S1.Deficit.GoldenPhaseDeficit
import D5.S1.Deficit.ZeckendorfDisplacementReading
import D5.S1.Scale.Fibonacci
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

namespace D5.S1.Deficit.FixedModulusNoncongruence

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Deficit
open D5.S1.Deficit.DoubleFaceLength
open D5.S1.Deficit.GoldenPhaseDeficit
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Digit
open D5.S1.Scale
open Set

local instance : IsTrans ℕ (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem betaDigits_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
  · simp
  · push_cast
    ring

@[simp] private theorem betaDigits_single (i : ℕ) :
    betaDigits (Finsupp.single i 1) = phi ^ (i + 2) := by
  classical
  simp [betaDigits]

private theorem betaDigits_rawOfZeckendorf_a {digits : List ℕ}
    (hmin : ∀ k ∈ digits, 2 ≤ k) :
    (betaDigits (rawOfZeckendorf digits)).a =
      ((digits.map fun k => Nat.fib (k + 1)).sum : ℤ) -
        ((digits.map Nat.fib).sum : ℤ) := by
  induction digits with
  | nil => simp [rawOfZeckendorf, betaDigits]
  | cons k digits ih =>
      have hk : 2 ≤ k := hmin k (by simp)
      have htail : ∀ j ∈ digits, 2 ≤ j := by
        intro j hj
        exact hmin j (by simp [hj])
      have hraw : rawOfZeckendorf (k :: digits) =
          Finsupp.single (k - 2) 1 + rawOfZeckendorf digits := by
        rw [rawOfZeckendorf, List.map_cons]
        change Multiset.toFinsupp ({k - 2} + (digits.map fun j => j - 2 : Multiset ℕ)) = _
        rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
        rfl
      rw [hraw, betaDigits_add, a_add, betaDigits_single, ih htail]
      rw [show k - 2 + 2 = k by omega]
      rw [show k = (k - 1) + 1 by omega, golden_phi_pow_a_eq_fib]
      simp only [List.map_cons, List.sum_cons]
      have hk1 : k - 1 + 1 = k := by omega
      have hk2 : k - 1 + 2 = k + 1 := by omega
      simp only [hk1]
      rw [show Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib k by
        simpa only [hk1, hk2] using Nat.fib_add_two (n := k - 1)]
      push_cast
      ring

private theorem canonical_two_le {digits : List ℕ} (h : digits.IsZeckendorfRep) :
    ∀ k ∈ digits, 2 ≤ k := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at h
  intro k hk
  exact (List.pairwise_append.mp h).2.2 k hk 0 (by simp)

private theorem betaGolden_a (v : ℕ) :
    (betaGolden v).a = (displacementDecode v : ℤ) - v := by
  rw [betaGolden, toRaw, Z, wEncoding]
  change (betaDigits (rawOfZeckendorf (wdigits v))).a = _
  rw [betaDigits_rawOfZeckendorf_a]
  · simp [displacementDecode, decode_wdigits]
  · intro k hk
    exact canonical_two_le (wdigits_isCanonical v) k hk

private theorem betaReal_eq_displacement (v : ℕ) :
    betaReal v = (displacementDecode v : ℝ) - (v : ℝ) * Real.goldenConj := by
  rw [betaReal, embedding_apply, betaGolden_a, betaGolden_b]
  push_cast
  rw [show Real.goldenRatio = 1 - Real.goldenConj by
    linarith [Real.goldenRatio_add_goldenConj]]
  ring

private theorem deficit_eq_beattyDeficit (v₁ v₂ : ℕ) :
    deficit v₁ v₂ = (beattyDeficit v₁ v₂ : ℝ) := by
  have hshift (v : ℕ) : (displacementDecode v : ℤ) = goldenShift v := by
    exact displacement_decode_eq_beatty_floor v
  have hshiftReal (v : ℕ) : (displacementDecode v : ℝ) = (goldenShift v : ℝ) := by
    exact_mod_cast hshift v
  rw [deficit, betaReal_eq_displacement, betaReal_eq_displacement,
    betaReal_eq_displacement, beattyDeficit]
  rw [hshiftReal, hshiftReal, hshiftReal]
  push_cast
  ring

private theorem dense_nsmul_golden (m : ℕ) (hm : m ≠ 0) :
    DenseRange fun n : ℕ => n • ((m : ℝ) * Real.goldenRatio : AddCircle (1 : ℝ)) := by
  rw [← denseRange_zsmul_iff_nsmul]
  rw [AddCircle.denseRange_zsmul_coe_iff]
  simpa using Real.goldenRatio_irrational.natCast_mul hm

private theorem dense_progression_phase (m r : ℕ) (hm : m ≠ 0) :
    DenseRange fun n : ℕ =>
      ((((r + m * n : ℕ) : ℝ) + 1) * Real.goldenRatio : AddCircle (1 : ℝ)) := by
  let a : AddCircle (1 : ℝ) := ((m : ℝ) * Real.goldenRatio : ℝ)
  let b : AddCircle (1 : ℝ) := (((r : ℝ) + 1) * Real.goldenRatio : ℝ)
  have ha : DenseRange fun n : ℕ => n • a := dense_nsmul_golden m hm
  have hb : DenseRange (Homeomorph.addLeft b) :=
    (Homeomorph.addLeft b).surjective.denseRange
  have hcomp := hb.comp ha (Homeomorph.addLeft b).continuous
  have heq : (fun n : ℕ =>
      ((((r + m * n : ℕ) : ℝ) + 1) * Real.goldenRatio : AddCircle (1 : ℝ))) =
      (Homeomorph.addLeft b ∘ fun n : ℕ => n • a) := by
    funext n
    change (((((r + m * n : ℕ) : ℝ) + 1) * Real.goldenRatio : ℝ) :
        AddCircle (1 : ℝ)) = b + n • a
    dsimp [a, b]
    calc
      (((((r + m * n : ℕ) : ℝ) + 1) * Real.goldenRatio : ℝ) :
          AddCircle (1 : ℝ)) =
          ((((r : ℝ) + 1) * Real.goldenRatio +
            n • ((m : ℝ) * Real.goldenRatio) : ℝ) : AddCircle (1 : ℝ)) := by
            congr 1
            push_cast
            simp only [nsmul_eq_mul]
            ring
      _ = ((((r : ℝ) + 1) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) +
          n • ((((m : ℝ) * Real.goldenRatio : ℝ)) : AddCircle (1 : ℝ)) := by
            rw [AddCircle.coe_add, AddCircle.coe_nsmul]
  exact heq.symm ▸ hcomp

private theorem exists_multiple_phase_mem_Ioo (m : ℕ) (hm : m ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ n : ℕ, goldenPhase (m * n) ∈ Ioo a b := by
  let U : Set (AddCircle (1 : ℝ)) :=
    ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b
  have hUopen : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hUne : U.Nonempty := (nonempty_Ioo.mpr hab).image _
  obtain ⟨n, hn⟩ := (dense_progression_phase m 0 hm).exists_mem_open hUopen hUne
  rcases hn with ⟨x, hx, hnx⟩
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨ha.trans hx.1.le, hx.2.trans_le hb⟩
  have hphaseIco : goldenPhase (m * n) ∈ Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hcoe : (goldenPhase (m * n) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
    rw [goldenPhase, AddCircle.coe_fract]
    simpa using hnx.symm
  have heq : goldenPhase (m * n) = x :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      (by simpa only [zero_add] using hphaseIco)
      (by simpa only [zero_add] using hxIco)).mp hcoe
  exact ⟨n, heq.symm ▸ hx⟩

private theorem goldenPhase_one : goldenPhase 1 = 2 * Real.goldenRatio - 3 := by
  rw [goldenPhase, Int.fract]
  have hfloor : ⌊(((1 : ℕ) : ℝ) + 1) * Real.goldenRatio⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_num
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    · norm_num
      linarith [Real.goldenRatio_lt_two]
  rw [hfloor]
  norm_num

/-- For every modulus at least two, two congruent input pairs have different deficits.

This is an honest partial closure of proposition 6.28(ii). It strengthens the finite
certificate range from moduli 2 through 60 to all fixed moduli at least two. It does not assert
prime-classification blindness or either claimed slice frequency. -/
theorem deficit_not_determined_by_fixed_modulus (m : ℕ) (hm : 2 ≤ m) :
    ∃ v₁ v₂ v₁' v₂' : ℕ,
      Nat.ModEq m v₁ v₁' ∧ Nat.ModEq m v₂ v₂' ∧
        deficit v₁ v₂ ≠ deficit v₁' v₂' := by
  have hm0 : m ≠ 0 := by omega
  let posUpper : ℝ := (2 - Real.goldenRatio) / 2
  let zeroLower : ℝ := 2 - Real.goldenRatio
  let zeroUpper : ℝ := (3 - Real.goldenRatio) / 2
  have hposUpper : 0 < posUpper := by
    dsimp [posUpper]
    linarith [Real.goldenRatio_lt_two]
  have hzeroLower : 0 ≤ zeroLower := by
    dsimp [zeroLower]
    linarith [Real.goldenRatio_lt_two]
  have hzeroInterval : zeroLower < zeroUpper := by
    dsimp [zeroLower, zeroUpper]
    linarith [Real.one_lt_goldenRatio]
  have hzeroUpper : zeroUpper ≤ 1 := by
    dsimp [zeroUpper]
    linarith [Real.one_lt_goldenRatio]
  obtain ⟨n, hn⟩ := exists_multiple_phase_mem_Ioo m hm0 (le_refl 0) hposUpper
    (by dsimp [posUpper]; linarith [Real.goldenRatio_pos])
  obtain ⟨n', hn'⟩ := exists_multiple_phase_mem_Ioo m hm0 hzeroLower hzeroInterval hzeroUpper
  have hphaseOne := goldenPhase_one
  have hpositive : beattyDeficit 1 (m * n) = 1 := by
    rw [(golden_phase_deficit 1 (m * n)).1]
    rw [hphaseOne, Real.inv_goldenRatio]
    dsimp [posUpper] at hn
    linarith [hn.2, Real.goldenRatio_add_goldenConj]
  have hzero : beattyDeficit 1 (m * n') = 0 := by
    rw [(golden_phase_deficit 1 (m * n')).2.2]
    rw [hphaseOne, Real.inv_goldenRatio]
    dsimp [zeroLower, zeroUpper] at hn'
    constructor
    · linarith [hn'.1, Real.goldenRatio_add_goldenConj]
    · linarith [hn'.2, Real.goldenRatio_lt_two]
  refine ⟨1, m * n, 1, m * n', Nat.ModEq.refl 1, ?_, ?_⟩
  · simp [Nat.ModEq]
  · rw [deficit_eq_beattyDeficit, deficit_eq_beattyDeficit, hpositive, hzero]
    norm_num

end D5.S1.Deficit.FixedModulusNoncongruence

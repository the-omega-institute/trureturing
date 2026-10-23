/- GID: D5/S3/Fourier/GeneratorRowOrderNecessity
   generality: G
   mirror-B: D5/B/S3/Fourier/GeneratorRowOrderNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/GeneratorRowOrderNecessity.claim; result=D5/S3/Fourier/GeneratorRowOrderNecessity.result; claim=D5/S3/Fourier/GeneratorRowOrderNecessity.claim
   digest: Variable even-order folded characters force a quadratic generator coefficient floor. -/

import D5.S3.Fourier.FullBispectrumStability
import D5.S3.Fourier.GeneratorRowStability
import D5.S3.Fourier.FinitePoisson
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace D5.S3.Fourier.GeneratorRowOrderNecessity

open Finset
open scoped BigOperators ComplexConjugate Real
open FullBispectrumStability (cyclic_parseval dft_translation unit_mul_conj)
open D5.S3.Fourier.FinitePoisson

noncomputable section

abbrev Parameter := {M : ℕ // 32 ≤ M}
abbrev order (p : Parameter) : ℕ := 2 * p.1

private instance order_neZero (p : Parameter) : NeZero (order p) := ⟨by
  dsimp [order]
  omega⟩

private instance order_gt_one (p : Parameter) : Fact (1 < order p) := ⟨by
  dsimp [order]
  omega⟩

def sourceSpectrum (p : Parameter) : ZMod (order p) → ℂ := fun _ => 1

def foldedSpectrum (p : Parameter) (k : ZMod (order p)) : ℂ :=
  @ite ℂ (k.val ≤ p.1) (Classical.propDecidable _)
    (ZMod.stdAddChar k) (ZMod.stdAddChar (-k))

def sourceSignal (p : Parameter) : ZMod (order p) → ℂ :=
  ZMod.dft.symm (sourceSpectrum p)

def targetSignal (p : Parameter) : ZMod (order p) → ℂ :=
  ZMod.dft.symm (foldedSpectrum p)

private def bispectrum {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (k l : ZMod N) : ℂ :=
  F k * F l * conj (F (k + l))

private def countingError {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (t : ZMod N) : ℝ :=
  ∑ x, ‖g x - f (x - t)‖ ^ 2

private def observationTolerance (p : Parameter) : ℝ := 4 * Real.pi / (order p : ℝ)


private lemma sum_stdAddChar_mul (p : Parameter) (a : ZMod (order p)) :
    ∑ k : ZMod (order p), ZMod.stdAddChar (a * k) =
      if a = 0 then (order p : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, card_univ]
  · rw [if_neg ha]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar (order p) ha)

private lemma stdAddChar_unit (p : Parameter) (k : ZMod (order p)) :
    ‖ZMod.stdAddChar k‖ = 1 := by
  exact (ZMod.stdAddChar (N := order p)).norm_apply k

private lemma folded_real_part (p : Parameter) (k : ZMod (order p)) :
    foldedSpectrum p k + conj (foldedSpectrum p k) =
      ZMod.stdAddChar k + conj (ZMod.stdAddChar k) := by
  unfold foldedSpectrum
  by_cases hk : k.val ≤ p.1
  · simp [hk]
  · rw [if_neg hk, AddChar.map_neg_eq_conj]
    simp only [Complex.conj_conj]
    ring



private lemma folded_even (p : Parameter) (k : ZMod (order p)) :
    foldedSpectrum p (-k) = foldedSpectrum p k := by
  unfold foldedSpectrum
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hk : k.val ≤ p.1
  · have hnegval : (-k).val = order p - k.val := by
      simp [ZMod.neg_val, hk0]
    by_cases hmid : k.val = p.1
    · have hkeq : (-k) = k := by
        apply ZMod.val_injective (order p)
        rw [hnegval, hmid]
        dsimp [order]
        omega
      simp [hkeq, hmid]
    · have hneg : ¬ (-k).val ≤ p.1 := by
        rw [hnegval]
        dsimp [order]
        omega
      simp [hk, hneg]
  · have hnegval : (-k).val = order p - k.val := by
      simp [ZMod.neg_val, hk0]
    have hneg : (-k).val ≤ p.1 := by
      rw [hnegval]
      dsimp [order]
      omega
    simp [hk, hneg]

private lemma folded_zero (p : Parameter) : foldedSpectrum p 0 = 1 := by
  simp [foldedSpectrum]

private lemma source_dft (p : Parameter) : ZMod.dft (sourceSignal p) = sourceSpectrum p := by
  exact (ZMod.dft (N := order p) (E := ℂ)).apply_symm_apply _

private lemma target_dft (p : Parameter) : ZMod.dft (targetSignal p) = foldedSpectrum p := by
  exact (ZMod.dft (N := order p) (E := ℂ)).apply_symm_apply _

private lemma correlation (p : Parameter) (t : ZMod (order p)) :
    (∑ k : ZMod (order p), foldedSpectrum p k *
      conj (ZMod.stdAddChar (-(k * t)))).re =
      if t = 1 ∨ t = -1 then (order p : ℝ) / 2 else 0 := by
  classical
  have hsum1 (a : ZMod (order p)) :
      ∑ k : ZMod (order p), ZMod.stdAddChar (a * k) =
      if a = 0 then (order p : ℂ) else 0 := sum_stdAddChar_mul p a
  have hconj_sum :
      conj (∑ k : ZMod (order p), foldedSpectrum p k *
        conj (ZMod.stdAddChar (-(k * t)))) =
      ∑ k : ZMod (order p), conj (foldedSpectrum p k) *
        conj (ZMod.stdAddChar (-(k * t))) := by
    rw [map_sum]
    apply Fintype.sum_equiv (Equiv.neg (ZMod (order p)))
    intro k
    simp only [Equiv.neg_apply, map_mul, Complex.conj_conj]
    rw [folded_even]
    have hci (a : ZMod (order p)) :
        conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
      exact (AddChar.map_neg_eq_conj _ _).symm
    rw [hci]
    congr 1
    simp only [neg_mul, neg_neg]
  have hsplit :
      (∑ k : ZMod (order p), foldedSpectrum p k *
        conj (ZMod.stdAddChar (-(k * t)))) +
      conj (∑ k : ZMod (order p), foldedSpectrum p k *
        conj (ZMod.stdAddChar (-(k * t)))) =
      ∑ k : ZMod (order p),
        (foldedSpectrum p k + conj (foldedSpectrum p k)) *
          conj (ZMod.stdAddChar (-(k * t))) := by
    rw [hconj_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hrow :
      (∑ k : ZMod (order p), (foldedSpectrum p k + conj (foldedSpectrum p k)) *
        conj (ZMod.stdAddChar (-(k * t)))) =
      ∑ k : ZMod (order p),
        (ZMod.stdAddChar k + conj (ZMod.stdAddChar k)) *
          conj (ZMod.stdAddChar (-(k * t))) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [folded_real_part]
  have hcorr :
      (∑ k : ZMod (order p), foldedSpectrum p k *
        conj (ZMod.stdAddChar (-(k * t)))) +
      conj (∑ k : ZMod (order p), foldedSpectrum p k *
        conj (ZMod.stdAddChar (-(k * t)))) =
      (if t = 1 then (order p : ℂ) else 0) +
        (if t = -1 then (order p : ℂ) else 0) := by
    rw [hsplit, hrow]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    -- The two summands are primitive character sums.
    have hconj (a : ZMod (order p)) :
        conj (ZMod.stdAddChar a) = (ZMod.stdAddChar a)⁻¹ := by
      rw [← AddChar.map_neg_eq_conj, AddChar.map_neg_eq_inv]
    have hA : ∑ k : ZMod (order p), ZMod.stdAddChar k *
        conj (ZMod.stdAddChar (-(k * t))) =
        if t = -1 then (order p : ℂ) else 0 := by
      have he : ∀ k : ZMod (order p),
          ZMod.stdAddChar k * conj (ZMod.stdAddChar (-(k * t))) =
            ZMod.stdAddChar ((1 + t) * k) := by
        intro k
        rw [hconj, ← AddChar.map_neg_eq_inv]
        rw [← AddChar.map_add_eq_mul]
        congr 1
        rw [add_mul]
        simp [mul_comm]
      simp_rw [he]
      have hz := hsum1 (1 + t)
      by_cases h : t = -1
      · have hzero : (1 + t : ZMod (order p)) = 0 := by simp [h]
        have hz' := hz
        rw [if_pos hzero] at hz'
        simpa [h] using hz'
      · have hzero : (1 + t : ZMod (order p)) ≠ 0 := by
          intro hzero
          apply h
          exact eq_neg_of_add_eq_zero_right hzero
        have hz' := hz
        rw [if_neg hzero] at hz'
        simpa [h] using hz'
    have hB : ∑ k : ZMod (order p), conj (ZMod.stdAddChar k) *
        conj (ZMod.stdAddChar (-(k * t))) =
        if t = 1 then (order p : ℂ) else 0 := by
      have he : ∀ k : ZMod (order p),
          conj (ZMod.stdAddChar k) * conj (ZMod.stdAddChar (-(k * t))) =
            ZMod.stdAddChar ((-1 + t) * k) := by
        intro k
        rw [hconj, hconj, ← AddChar.map_neg_eq_inv, ← AddChar.map_neg_eq_inv]
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      simp_rw [he]
      have hz := hsum1 (-1 + t)
      by_cases h : t = 1
      · have hzero : (-1 + t : ZMod (order p)) = 0 := by simp [h]
        have hz' := hz
        rw [if_pos hzero] at hz'
        simpa [h] using hz'
      · have hzero : (-1 + t : ZMod (order p)) ≠ 0 := by
          intro hzero
          apply h
          have ht : t = -(-1 : ZMod (order p)) :=
            eq_neg_of_add_eq_zero_right hzero
          simpa using ht
        have hz' := hz
        rw [if_neg hzero] at hz'
        simpa [h] using hz'
    rw [hA, hB]
    ring
  let z := ∑ k : ZMod (order p), foldedSpectrum p k *
      conj (ZMod.stdAddChar (-(k * t)))
  have hr : 2 * z.re =
      ((if t = 1 then (order p : ℂ) else 0) +
        (if t = -1 then (order p : ℂ) else 0)).re := by
    calc
      2 * z.re = (z + conj z).re := by simp [Complex.add_re]; ring
      _ = ((if t = 1 then (order p : ℂ) else 0) +
        (if t = -1 then (order p : ℂ) else 0)).re := by
          exact congrArg Complex.re hcorr
  change z.re = if t = 1 ∨ t = -1 then (order p : ℝ) / 2 else 0
  have hpm : (1 : ZMod (order p)) ≠ -1 := by
    intro hh
    have hv := congrArg ZMod.val hh
    have hv' : (1 : ℕ) = order p - 1 := by
      simpa [ZMod.neg_val, ZMod.val_one] using hv
    dsimp [order] at hv'
    have hlt := (show (1 : ℕ) < order p by
      dsimp [order]
      omega)
    omega
  by_cases h : t = 1 ∨ t = -1
  · rcases h with rfl | rfl
    · have hne : (1 : ZMod (order p)) ≠ -1 := hpm
      simp [hne] at hr ⊢
      nlinarith [hr]
    · have hne : (-1 : ZMod (order p)) ≠ 1 := fun hh => hpm hh.symm
      simp [hne] at hr ⊢
      nlinarith [hr]
  · have h1 : t ≠ 1 := by
      intro ht
      exact h (Or.inl ht)
    have h2 : t ≠ -1 := by
      intro ht
      exact h (Or.inr ht)
    simp [h1, h2] at hr ⊢
    nlinarith [hr]

private lemma stdAddChar_conj (p : Parameter) (a : ZMod (order p)) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  exact (AddChar.map_neg_eq_conj _ _).symm

private lemma folded_low (p : Parameter) (k : ZMod (order p))
    (hk : k.val < p.1) : foldedSpectrum p k = ZMod.stdAddChar k := by
  simp [foldedSpectrum, Nat.le_of_lt hk]

private lemma folded_high (p : Parameter) (k : ZMod (order p))
    (hk : p.1 ≤ k.val) : foldedSpectrum p k = ZMod.stdAddChar (-k) := by
  by_cases hmid : k.val = p.1
  · have hk0 : k ≠ 0 := by
      intro h
      have hh : p.1 = 0 := by simpa [h] using hmid.symm
      have hp := p.property
      omega
    have he : -k = k := by
      apply ZMod.val_injective (order p)
      simp only [ZMod.neg_val, if_neg hk0, hmid]
      dsimp [order]
      omega
    simp [foldedSpectrum, hmid, he]
  · simp [foldedSpectrum, show ¬ k.val ≤ p.1 by omega]

private lemma folded_succ_low (p : Parameter) (k : ZMod (order p))
    (hk : k.val < p.1) :
    foldedSpectrum p (k + 1) = ZMod.stdAddChar (k + 1) := by
  have hlt : k.val + (1 : ℕ) < order p := by
    dsimp [order]
    omega
  have hv := ZMod.val_add_of_lt (a := k) (b := 1) (by simpa only [ZMod.val_one] using hlt)
  simp only [ZMod.val_one] at hv
  have hle : (k + 1).val ≤ p.1 := by omega
  simp [foldedSpectrum, hle]

private lemma folded_succ_high (p : Parameter) (k : ZMod (order p))
    (hk : p.1 ≤ k.val) :
    foldedSpectrum p (k + 1) = ZMod.stdAddChar (-(k + 1)) := by
  by_cases hnext : (k + 1).val ≤ p.1
  · have hlt_or_wrap : k.val + 1 < order p ∨ order p ≤ k.val + 1 := by omega
    rcases hlt_or_wrap with hlt | hwrap
    · have hv := ZMod.val_add_of_lt (a := k) (b := 1) (by simpa only [ZMod.val_one] using hlt)
      simp only [ZMod.val_one] at hv
      omega
    · have hv := ZMod.val_add_of_le (a := k) (b := 1) (by simpa only [ZMod.val_one] using hwrap)
      simp only [ZMod.val_one] at hv
      have hkmax : k.val = order p - 1 := by
        have hklt := k.val_lt
        omega
      have hz : k + 1 = 0 := by
        apply ZMod.val_injective (order p)
        simp only [ZMod.val_zero]
        omega
      simp [hz, folded_zero]
  · simp [foldedSpectrum, hnext]

private lemma generator_row (p : Parameter) (k : ZMod (order p)) :
    bispectrum (foldedSpectrum p) k 1 - bispectrum (sourceSpectrum p) k 1 =
      if k.val < p.1 then 0 else ZMod.stdAddChar (2 : ZMod (order p)) - 1 := by
  have h1 : foldedSpectrum p 1 = ZMod.stdAddChar (1 : ZMod (order p)) := by
    apply folded_low
    simp only [ZMod.val_one]
    omega
  simp only [bispectrum, sourceSpectrum, map_one, one_mul]
  rw [h1]
  by_cases hk : k.val < p.1
  · rw [folded_low p k hk, folded_succ_low p k hk]
    rw [stdAddChar_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    simp [hk]
  · have hk' : p.1 ≤ k.val := by omega
    rw [folded_high p k hk', folded_succ_high p k hk']
    rw [stdAddChar_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    simp [hk]
    congr 2
    abel
    simp [nsmul_eq_mul]

private lemma source_energy_exact (p : Parameter) :
    GeneratorRowStability.sourceEnergy (sourceSignal p) = ((order p : ℝ) - 1) / (order p : ℝ) := by
  unfold GeneratorRowStability.sourceEnergy
  rw [source_dft p]
  simp only [sourceSpectrum, norm_one, one_pow]
  have hcard : ((univ : Finset (ZMod (order p))).erase 0).card = order p - 1 := by
    rw [card_erase_of_mem (mem_univ 0), card_univ, ZMod.card]
  rw [sum_const, hcard]
  have hN1 : 1 ≤ order p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  simp only [nsmul_eq_mul, Nat.cast_sub hN1, Nat.cast_one]
  ring

private lemma observation_tolerance_bounds (p : Parameter) :
    0 < observationTolerance p ∧ observationTolerance p ≤ 1 / 4 := by
  have hN : (0 : ℝ) < order p := by
    exact_mod_cast (NeZero.pos (order p))
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_four
  dsimp [observationTolerance]
  constructor
  · positivity
  · have hpM : (64 : ℝ) ≤ order p := by
      dsimp [order]
      exact_mod_cast (show 64 ≤ 2 * p.1 by omega)
    apply (div_le_iff₀ hN).2
    nlinarith

private lemma folded_row_bound (p : Parameter) :
    ‖ZMod.stdAddChar (2 : ZMod (order p)) - 1‖ ≤ observationTolerance p := by
  have hchar : ZMod.stdAddChar (2 : ZMod (order p)) =
      Complex.exp (((4 * Real.pi / (order p : ℝ) : ℝ) : ℂ) * Complex.I) := by
    have h := ZMod.stdAddChar_coe (N := order p) (2 : ℤ)
    norm_num only [Int.cast_ofNat] at h
    rw [h]
    push_cast
    congr 1
    ring
  rw [hchar]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 4 * Real.pi / (order p : ℝ))
  have he := (observation_tolerance_bounds p).1
  have hx : 0 < 4 * Real.pi / (order p : ℝ) := he
  rw [Real.norm_eq_abs, abs_of_pos hx] at hh
  simpa only [observationTolerance, mul_comm] using hh

private lemma translation_error (p : Parameter) (t : ZMod (order p)) :
    countingError (sourceSignal p) (targetSignal p) t =
      if t = 1 ∨ t = -1 then 1 else 2 := by
  rw [show countingError (sourceSignal p) (targetSignal p) t =
      ∑ x, ‖targetSignal p x - sourceSignal p (x - t)‖ ^ 2 by rfl]
  rw [cyclic_parseval]
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hcoef (k : ZMod (order p)) :
      ZMod.dft (fun x => targetSignal p x - sourceSignal p (x - t)) k =
        foldedSpectrum p k - ZMod.stdAddChar (-(k * t)) := by
    have hh := congr_fun ((ZMod.dft (N := order p) (E := ℂ)).map_sub
      (targetSignal p) (fun x => sourceSignal p (x - t))) k
    change ZMod.dft (fun x => targetSignal p x - sourceSignal p (x - t)) k =
      ZMod.dft (targetSignal p) k -
        ZMod.dft (fun x => sourceSignal p (x - t)) k at hh
    rw [dft_translation] at hh
    simpa [target_dft p, source_dft p, sourceSpectrum] using hh
  simp_rw [hcoef]
  have hnormJ (k : ZMod (order p)) : ‖foldedSpectrum p k‖ = 1 := by
    unfold foldedSpectrum
    split_ifs <;> exact stdAddChar_unit p _
  have hnormC (k : ZMod (order p)) :
      ‖ZMod.stdAddChar (-(k * t))‖ = 1 := by
    exact stdAddChar_unit p _
  have hsum :
      (∑ k : ZMod (order p),
        ‖foldedSpectrum p k - ZMod.stdAddChar (-(k * t))‖ ^ 2) =
      2 * (order p : ℝ) - 2 *
        (∑ k : ZMod (order p), foldedSpectrum p k *
          conj (ZMod.stdAddChar (-(k * t)))).re := by
    simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, hnormJ, hnormC]
    simp only [one_pow]
    rw [sum_sub_distrib, ← mul_sum, ← Complex.re_sum]
    simp [ZMod.card]
    ring
  rw [hsum, correlation p t]
  have hN : (order p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne (order p))
  by_cases h : t = 1 ∨ t = -1
  · rw [if_pos h, if_pos h]
    field_simp [hN]
    <;> ring
  · rw [if_neg h, if_neg h]
    field_simp [hN]
    <;> ring


private lemma coefficient_floor (p : Parameter) :
    (order p : ℝ) ^ 3 / (16 * Real.pi ^ 2 * ((order p : ℝ) - 1)) >
      (order p : ℝ) ^ 2 / (16 * Real.pi ^ 2) := by
  have hN : (1 : ℝ) < order p := by
    exact_mod_cast (show 1 < order p by dsimp [order]; have hp := p.property; omega)
  have hpi : 0 < Real.pi := Real.pi_pos
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  have hpos : 0 < (order p : ℝ) ^ 2 * (16 * Real.pi ^ 2) := by positivity
  nlinarith only [hpos]

private lemma coefficient_necessary (p : Parameter) (K : ℝ)
    (hbound : ∃ t : ZMod (order p),
      countingError (sourceSignal p) (targetSignal p) t ≤
        K * observationTolerance p ^ 2 * GeneratorRowStability.sourceEnergy (sourceSignal p)) :
    (order p : ℝ) ^ 3 / (16 * Real.pi ^ 2 * ((order p : ℝ) - 1)) ≤ K := by
  obtain ⟨t, ht⟩ := hbound
  have hlow : 1 ≤ countingError (sourceSignal p) (targetSignal p) t := by
    rw [translation_error]
    split_ifs <;> norm_num
  have hN : (1 : ℝ) < order p := by
    exact_mod_cast (show 1 < order p by dsimp [order]; have hp := p.property; omega)
  have hp := Real.pi_pos
  let A := observationTolerance p ^ 2 *
    GeneratorRowStability.sourceEnergy (sourceSignal p)
  have hA : 0 < A := by
    dsimp [A]
    rw [source_energy_exact]
    exact mul_pos (sq_pos_of_pos (observation_tolerance_bounds p).1)
      (div_pos (by linarith) (by linarith))
  have hKA : 1 ≤ K * A := by
    dsimp [A]
    nlinarith [hlow.trans ht]
  have hK : 1 / A ≤ K := (div_le_iff₀ hA).2 hKA
  have hid : 1 / A =
      (order p : ℝ) ^ 3 / (16 * Real.pi ^ 2 * ((order p : ℝ) - 1)) := by
    dsimp [A, observationTolerance]
    rw [source_energy_exact]
    field_simp
    ring
  rwa [hid] at hK

/-- Actual inverse complex signals at every even order have complete calibrated rows,
exact counting distances, and a quadratic coefficient obstruction. -/
theorem parameter_family (p : Parameter) :
    ZMod.dft (sourceSignal p) = sourceSpectrum p ∧
    ZMod.dft (targetSignal p) = foldedSpectrum p ∧
    ZMod.dft (sourceSignal p) 0 = (1 : ℂ) ∧
    ZMod.dft (targetSignal p) 0 = (1 : ℂ) ∧
    (∀ k, ‖ZMod.dft (sourceSignal p) k‖ = 1 ∧
      ‖ZMod.dft (targetSignal p) k‖ = 1) ∧
    (∀ k, bispectrum (ZMod.dft (targetSignal p)) 0 k =
      bispectrum (ZMod.dft (sourceSignal p)) 0 k) ∧
    (∀ k, bispectrum (ZMod.dft (targetSignal p)) k 1 =
      if k.val < p.1 then 1 else ZMod.stdAddChar (2 : ZMod (order p))) ∧
    (∀ k, ‖bispectrum (ZMod.dft (targetSignal p)) k 1 -
      bispectrum (ZMod.dft (sourceSignal p)) k 1‖ ≤ observationTolerance p) ∧
    0 < observationTolerance p ∧ observationTolerance p ≤ 1 / 4 ∧
    GeneratorRowStability.sourceEnergy (sourceSignal p) = ((order p : ℝ) - 1) / (order p : ℝ) ∧
    (∀ t, countingError (sourceSignal p) (targetSignal p) t =
      if t = 1 ∨ t = -1 then 1 else 2) ∧
    (∀ K : ℝ, (∃ t : ZMod (order p),
      countingError (sourceSignal p) (targetSignal p) t ≤
        K * observationTolerance p ^ 2 * GeneratorRowStability.sourceEnergy (sourceSignal p)) →
      (order p : ℝ) ^ 3 / (16 * Real.pi ^ 2 * ((order p : ℝ) - 1)) ≤ K ∧
        (order p : ℝ) ^ 2 / (16 * Real.pi ^ 2) <
          (order p : ℝ) ^ 3 / (16 * Real.pi ^ 2 * ((order p : ℝ) - 1))) := by
  have hn (k : ZMod (order p)) : ‖foldedSpectrum p k‖ = 1 := by
    unfold foldedSpectrum
    split_ifs <;> exact stdAddChar_unit p _
  refine ⟨source_dft p, target_dft p, ?_, ?_, ?_, ?_, ?_, ?_,
    (observation_tolerance_bounds p).1, (observation_tolerance_bounds p).2,
    source_energy_exact p, translation_error p, ?_⟩
  · simp [source_dft p, sourceSpectrum]
  · simp [target_dft p, folded_zero p]
  · intro k
    simp [source_dft p, target_dft p, sourceSpectrum, hn k]
  · intro k
    rw [source_dft p, target_dft p]
    simp only [bispectrum, sourceSpectrum, folded_zero, zero_add, one_mul, map_one]
    exact unit_mul_conj _ (hn k)
  · intro k
    have h := generator_row p k
    rw [target_dft p]
    have he : bispectrum (foldedSpectrum p) k 1 - 1 =
        (if k.val < p.1 then 1 else ZMod.stdAddChar (2 : ZMod (order p))) - 1 := by
      by_cases hk : k.val < p.1 <;>
        simpa [bispectrum, sourceSpectrum, hk] using h
    have hh := congrArg (fun z : ℂ => z + 1) he
    simpa only [sub_add_cancel] using hh
  · intro k
    rw [source_dft p, target_dft p, generator_row]
    split_ifs
    · simpa using (observation_tolerance_bounds p).1.le
    · exact folded_row_bound p
  · intro K h
    exact ⟨coefficient_necessary p K h, coefficient_floor p⟩

/-- One coefficient for the original actual-signal observation contract at every even order. -/
def claim : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Parameter)
    (f g : ZMod (order p) → ℂ) (ε : ℝ),
  0 ≤ ε → ε ≤ 1 / 4 →
  ZMod.dft f 0 = (1 : ℂ) → ZMod.dft g 0 = (1 : ℂ) →
  (∀ k, ‖ZMod.dft f k‖ = 1 ∧ ‖ZMod.dft g k‖ = 1) →
  (∀ k, bispectrum (ZMod.dft g) 0 k = bispectrum (ZMod.dft f) 0 k) →
  (∀ k, ‖bispectrum (ZMod.dft g) k 1 - bispectrum (ZMod.dft f) k 1‖ ≤ ε) →
  ∃ t : ZMod (order p), countingError f g t ≤
    C * ε ^ 2 * GeneratorRowStability.sourceEnergy f

/-- The calibrated observed-input contract admits no single finite uniform coefficient. -/
theorem result : ¬ claim := by
  rintro ⟨C, hC, hb⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (max (32 : ℝ) (8 * (C + 1)))
  have hM32 : 32 ≤ M := by
    have hh := (le_max_left (32 : ℝ) (8 * (C + 1))).trans_lt hM
    exact_mod_cast hh.le
  let p : Parameter := ⟨M, hM32⟩
  obtain ⟨hF, hJ, hF0, hJ0, hn, hzero, hrow, hgen, he, hes, henergy,
    herr, hcoef⟩ := parameter_family p
  have hactual := hb p (sourceSignal p) (targetSignal p) (observationTolerance p)
    he.le hes hF0 hJ0 hn hzero hgen
  have hfloor := (hcoef C hactual).1
  have hstrict := (hcoef C hactual).2
  have hMlarge : 8 * (C + 1) < (M : ℝ) :=
    (le_max_right (32 : ℝ) (8 * (C + 1))).trans_lt hM
  have hpi2 : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hquad : C < (order p : ℝ) ^ 2 / (16 * Real.pi ^ 2) := by
    apply (lt_div_iff₀ (by positivity : 0 < 16 * Real.pi ^ 2)).2
    have hCC : C < (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
    have hMM : 64 * (C + 1) ^ 2 < (M : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((M : ℝ) - 8 * (C + 1))]
    have hCpi := mul_le_mul_of_nonneg_left hpi2.le hC
    dsimp [order, p]
    push_cast
    nlinarith
  linarith


#print axioms parameter_family
#print axioms result

end
end D5.S3.Fourier.GeneratorRowOrderNecessity

/- GID: D5/S3/Weil/SpectralHilbert
   generality: I
   mirror-B: D5/B/S3/Weil/SpectralHilbert
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize the labeled zeta vector in l2 and identify its zeta reproducing kernel. -/

import D5.S1.Digit.PrimeAxisEncoding
import D5.S3.Midline.UniversalHeatTrace
import D5.S3.Weil.Convention
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace D5.S3.Weil.SpectralHilbert

open D5.S1.Digit
open D5.S3.Midline.UniversalHeatTrace
open D5.S3.Weil.Convention
open scoped ComplexConjugate

/-- The Hilbert completion of complex coefficient families on prime-axis addresses. -/
noncomputable abbrev ZetaHilbertSpace := lp (fun _ : PrimeAxisTable => ℂ) 2

/-- The source convention is linear in the first entry, opposite to mathlib's convention. -/
noncomputable def sourcePairing (x y : ZetaHilbertSpace) : ℂ :=
  inner ℂ y x

/-- In source order, the Hilbert pairing is the sum of coordinate products. -/
theorem source_pairing_eq_tsum (x y : ZetaHilbertSpace) :
    sourcePairing x y = ∑' a, x a * conj (y a) := by
  rw [sourcePairing, lp.inner_eq_tsum]
  congr 1

/-- The labeled zeta coefficient at a prime-axis address. -/
noncomputable def labeledZetaCoefficient (s : ℂ) (a : PrimeAxisTable) : ℂ :=
  1 / (((primeAxisEncoding a : ℕ+) : ℕ) : ℂ) ^ s

private noncomputable def addressEquivNat : ℕ ≃ PrimeAxisTable :=
  (primeAxisEncoding.trans Equiv.pnatEquivNat).symm

private theorem addressEquivNat_encode (n : ℕ) :
    ((primeAxisEncoding (addressEquivNat n) : ℕ+) : ℕ) = n + 1 := by
  have h :=
    Equiv.apply_symm_apply (primeAxisEncoding.trans Equiv.pnatEquivNat) n
  change (primeAxisEncoding (addressEquivNat n)).natPred = n at h
  calc
    ((primeAxisEncoding (addressEquivNat n) : ℕ+) : ℕ) =
        (primeAxisEncoding (addressEquivNat n)).natPred + 1 :=
      (PNat.natPred_add_one _).symm
    _ = n + 1 := by rw [h]

private theorem labeledZetaCoefficient_norm_sq (s : ℂ) (n : ℕ) :
    ‖labeledZetaCoefficient s (addressEquivNat n)‖ ^ (2 : ℝ) =
      1 / ((n + 1 : ℕ) : ℝ) ^ (2 * s.re) := by
  rw [labeledZetaCoefficient, addressEquivNat_encode, Real.rpow_two, norm_div,
    norm_one, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1),
    one_div_pow]
  congr 1
  rw [← Real.rpow_mul_natCast (by positivity) s.re 2]
  congr 1
  ring

/-- The logarithmic length on the existing prime-axis carrier. -/
noncomputable def primeAxisLogLength (a : PrimeAxisTable) : ℝ :=
  Real.log (((primeAxisEncoding a : ℕ+) : ℕ) : ℝ)

private theorem primeAxisLogLength_addressEquivNat (n : ℕ) :
    primeAxisLogLength (addressEquivNat n) = Real.log (n + 1 : ℝ) := by
  rw [primeAxisLogLength, addressEquivNat_encode]
  norm_num

private theorem primeAxisHeatTerm_addressEquivNat (σ : ℝ) (n : ℕ) :
    Real.exp (-σ * primeAxisLogLength (addressEquivNat n)) =
      1 / ((n + 1 : ℕ) : ℝ) ^ σ := by
  rw [primeAxisLogLength_addressEquivNat, Real.rpow_def_of_pos (by positivity)]
  rw [one_div, ← Real.exp_neg]
  congr 1
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- The prime-axis logarithmic length has genuine abscissa one, with no boundary
claim folded into the definition. -/
theorem prime_axis_log_length_is_heat_abscissa :
    IsHeatAbscissa primeAxisLogLength 1 := by
  constructor
  · intro σ hσ
    rw [← addressEquivNat.summable_iff]
    refine (summable_congr (primeAxisHeatTerm_addressEquivNat σ)).2 ?_
    have hp := (Real.summable_one_div_nat_add_rpow 1 σ).2 hσ
    have hshift (n : ℕ) : |(n : ℝ) + 1| = ((n + 1 : ℕ) : ℝ) := by
      rw [abs_of_pos (by positivity), Nat.cast_add, Nat.cast_one]
    simpa only [hshift] using hp
  · intro σ hσ hsum
    have hnat : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ σ) := by
      rw [← addressEquivNat.summable_iff] at hsum
      exact (summable_congr (primeAxisHeatTerm_addressEquivNat σ)).mp hsum
    have hp : 1 < σ := by
      apply (Real.summable_one_div_nat_add_rpow 1 σ).mp
      have hshift (n : ℕ) : |(n : ℝ) + 1| = ((n + 1 : ℕ) : ℝ) := by
        rw [abs_of_pos (by positivity), Nat.cast_add, Nat.cast_one]
      simpa only [hshift] using hnat
    linarith

private theorem heatCoefficient_primeAxisLogLength (s : ℂ) (a : PrimeAxisTable) :
    heatCoefficient primeAxisLogLength s a = labeledZetaCoefficient s a := by
  have hN : 0 < (((primeAxisEncoding a : ℕ+) : ℕ) : ℝ) := by
    exact_mod_cast PNat.pos (primeAxisEncoding a)
  rw [heatCoefficient, primeAxisLogLength, labeledZetaCoefficient,
    Complex.cpow_def]
  simp only [Nat.cast_eq_zero]
  rw [if_neg (Nat.ne_of_gt (PNat.pos (primeAxisEncoding a)))]
  rw [Complex.ofReal_log hN.le]
  rw [one_div, ← Complex.exp_neg]
  congr 1
  norm_num
  ring

/-- The labeled zeta vector is square-summable exactly right of the critical line. -/
theorem labeled_zeta_mem_iff (s : ℂ) :
    Memℓp (labeledZetaCoefficient s) 2 ↔ criticalAbscissa < s.re := by
  have hcoeff : labeledZetaCoefficient s = heatCoefficient primeAxisLogLength s := by
    funext a
    exact (heatCoefficient_primeAxisLogLength s a).symm
  rw [hcoeff, criticalAbscissa]
  constructor
  · intro hmem
    rw [heat_coefficient_mem_iff primeAxisLogLength 1 s] at hmem
    by_contra hnot
    have hle : s.re ≤ 1 / 2 := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (prime_axis_log_length_is_heat_abscissa.2 (2 * s.re) (by linarith)) hmem
    · have hboundary : ¬Summable (fun a =>
          Real.exp (-1 * primeAxisLogLength a)) := by
        intro hb
        have hcomp := (addressEquivNat.summable_iff).2 hb
        have hnat : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
          simpa using (summable_congr (primeAxisHeatTerm_addressEquivNat 1)).mp hcomp
        have hp : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 : ℝ)) := by
          have hshift (n : ℕ) : |(n : ℝ) + 1| = ((n + 1 : ℕ) : ℝ) := by
            rw [abs_of_pos (by positivity), Nat.cast_add, Nat.cast_one]
          simpa only [hshift, Real.rpow_one] using hnat
        have hn : ¬Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 : ℝ)) := by
          rw [Real.summable_one_div_nat_add_rpow]
          norm_num
        exact hn hp
      apply hboundary
      have hfun : (fun a => Real.exp (-1 * primeAxisLogLength a)) =
          (fun a => Real.exp (-(2 * s.re) * primeAxisLogLength a)) := by
        funext a
        congr 1
        rw [heq]
        ring
      rw [hfun]
      exact hmem
  · intro hs
    exact heat_coefficient_mem_of_abscissa primeAxisLogLength 1
      prime_axis_log_length_is_heat_abscissa s hs

/-- Explicit specialization bridge: the universal heat-abscissa theorem on
`PrimeAxisTable`, with logarithmic length and `α = 1`, recovers the established
labeled-zeta membership statement. -/
theorem labeled_zeta_mem_iff_via_universal_heat_trace (s : ℂ) :
    Memℓp (labeledZetaCoefficient s) 2 ↔ criticalAbscissa < s.re :=
  labeled_zeta_mem_iff s

/-- The labeled zeta coefficient family as an actual Hilbert vector. -/
noncomputable def labeledZetaVector (s : ℂ) (hs : criticalAbscissa < s.re) :
    ZetaHilbertSpace :=
  ⟨labeledZetaCoefficient s, (labeled_zeta_mem_iff s).2 hs⟩

@[simp]
theorem labeledZetaVector_apply (s : ℂ) (hs : criticalAbscissa < s.re)
    (a : PrimeAxisTable) : labeledZetaVector s hs a = labeledZetaCoefficient s a :=
  rfl

/-- The labeled-vector norm square is zeta at twice the real abscissa. -/
theorem labeled_zeta_norm_sq (s : ℂ) (hs : criticalAbscissa < s.re) :
    ((‖labeledZetaVector s hs‖ ^ 2 : ℝ) : ℂ) =
      classicalZeta ((2 * s.re : ℝ) : ℂ) := by
  have hz : 1 < 2 * s.re := by
    rw [criticalAbscissa] at hs
    linarith
  have hnorm : ‖labeledZetaVector s hs‖ ^ 2 =
      ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * s.re) := by
    have hlp : ‖labeledZetaVector s hs‖ ^ (2 : ℝ) =
        ∑' a : PrimeAxisTable,
          ‖labeledZetaVector s hs a‖ ^ (2 : ℝ) := by
      simpa using (lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num)
        (labeledZetaVector s hs))
    calc
      ‖labeledZetaVector s hs‖ ^ 2 =
          ‖labeledZetaVector s hs‖ ^ (2 : ℝ) :=
        (Real.rpow_two _).symm
      _ = ∑' a : PrimeAxisTable,
          ‖labeledZetaVector s hs a‖ ^ (2 : ℝ) := hlp
      _ = ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * s.re) := by
        rw [← addressEquivNat.tsum_eq]
        congr 1
        funext n
        exact labeledZetaCoefficient_norm_sq s n
  rw [hnorm]
  have hsum : Summable (fun n : ℕ =>
      1 / ((n + 1 : ℕ) : ℝ) ^ (2 * s.re)) := by
    have hshift (n : ℕ) : |(n : ℝ) + 1| = ((n + 1 : ℕ) : ℝ) := by
      rw [abs_of_pos (by positivity), Nat.cast_add, Nat.cast_one]
    simpa only [hshift] using
      (Real.summable_one_div_nat_add_rpow 1 (2 * s.re)).2 hz
  change Complex.ofRealCLM (∑' n : ℕ,
    1 / ((n + 1 : ℕ) : ℝ) ^ (2 * s.re)) = _
  rw [Complex.ofRealCLM.map_tsum hsum]
  have hcast (n : ℕ) :
      Complex.ofRealCLM (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * s.re)) =
        1 / ((n + 1 : ℕ) : ℂ) ^ ((2 * s.re : ℝ) : ℂ) := by
    change ((1 / ((n + 1 : ℕ) : ℝ) ^ (2 * s.re) : ℝ) : ℂ) = _
    push_cast
    rw [Complex.ofReal_cpow (by positivity)]
    norm_num
  calc
    (∑' n : ℕ, Complex.ofRealCLM
        (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * s.re))) =
        ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ ((2 * s.re : ℝ) : ℂ) := by
      congr 1
      funext n
      exact hcast n
    _ = classicalZeta ((2 * s.re : ℝ) : ℂ) := by
      rw [classicalZeta,
        zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hz)]
      congr 1
      funext n
      norm_num

/-- The raw coefficient pairing is the zeta kernel in its convergence half-plane. -/
theorem labeled_zeta_kernel (s w : ℂ) (h : 1 < (s + conj w).re) :
    (∑' a : PrimeAxisTable,
      labeledZetaCoefficient s a * conj (labeledZetaCoefficient w a)) =
      classicalZeta (s + conj w) := by
  rw [classicalZeta, zeta_eq_tsum_one_div_nat_add_one_cpow h,
    ← addressEquivNat.tsum_eq]
  congr 1
  funext n
  simp only [labeledZetaCoefficient]
  rw [addressEquivNat_encode]
  norm_num
  have harg : (((n : ℂ) + 1).arg) ≠ Real.pi := by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact ne_of_lt Real.pi_pos
  have hconj :
      conj (((n : ℂ) + 1) ^ w) = ((n : ℂ) + 1) ^ conj w := by
    symm
    simpa using Complex.cpow_conj ((n : ℂ) + 1) w harg
  rw [hconj]
  rw [← mul_inv_rev, mul_comm,
    ← Complex.cpow_add s (conj w) (Nat.cast_add_one_ne_zero n)]

/-- In the l2 domain, the source-ordered inner product is the zeta kernel. -/
theorem labeled_zeta_inner (s w : ℂ)
    (hs : criticalAbscissa < s.re) (hw : criticalAbscissa < w.re) :
    sourcePairing (labeledZetaVector s hs) (labeledZetaVector w hw) =
      classicalZeta (s + conj w) := by
  rw [source_pairing_eq_tsum]
  simp_rw [labeledZetaVector_apply]
  apply labeled_zeta_kernel
  rw [criticalAbscissa] at hs hw
  simpa using (show 1 < s.re + w.re by linarith)

/-- Kernel resonance has the unique mirror partner and self-resonates on the critical line. -/
theorem resonance_partner_spec (s w : ℂ) :
    (s + conj w = 1 ↔ w = 1 - conj s) ∧
    (s + conj s = 1 ↔ s.re = criticalAbscissa) ∧
    (criticalAbscissa < s.re → (1 - conj s).re < criticalAbscissa) := by
  constructor
  · constructor
    · intro h
      have hc : conj s + w = 1 := by
        simpa using congrArg conj h
      linear_combination hc
    · intro h
      rw [h]
      simp
  · constructor
    · constructor
      · intro h
        have hre := congrArg Complex.re h
        rw [criticalAbscissa]
        simp at hre
        linarith
      · intro h
        apply Complex.ext
        · rw [criticalAbscissa] at h
          simp
          linarith
        · simp
    · intro hs
      rw [criticalAbscissa] at hs ⊢
      simp
      linarith

end D5.S3.Weil.SpectralHilbert

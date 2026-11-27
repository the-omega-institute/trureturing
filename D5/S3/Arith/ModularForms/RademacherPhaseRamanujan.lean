/- GID: D5/S3/Arith/ModularForms/RademacherPhaseRamanujan
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/RademacherPhaseRamanujan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The inverse-residue phase sum and the arithmetic constant of the rectangular linear term. -/

import D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
import D5.S3.Arith.ModularForms.RademacherLinearConstant
import D5.S3.Arith.ModularForms.RademacherLinearCutoff
import D5.S3.Arith.ModularForms.RademacherVacuum
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.RamanujanSums
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

open Filter
open scoped BigOperators ComplexConjugate LSeries.notation ArithmeticFunction.Moebius Topology UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherPhaseRamanujan

open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity (ramanujanSum sum_ramanujanSum_divisors)
open D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.RamanujanSums (ramanujan_one)
open D5.S3.Arith.ModularForms.RademacherVacuum (cutoffPairs denominator inverseResidue inverseResidue_spec linearCutoff linearSummand
    mem_cutoffPairs rademacherCutoff rademacherCutoff_eq remainderCutoff remainderLimit
    tendstoUniformlyOn_remainderCutoff vacuumArgument vacuumPhase)
open D5.S3.Arith.ModularForms.RademacherLinearCutoff
  (inverseMod inverseMod_spec linearPhase linearPrincipalValueCutoff linearRectangularCutoff
    linearRectangularCutoff_sub_tendstoUniformlyOn linearWeight
    reducedResidues shiftedArgument strictDenominators)
open D5.S3.Arith.ModularForms.RademacherLinearConstant (moebius_linear_constant)

set_option autoImplicit false

noncomputable section

/-- The positive exponential of an integer numerator modulo the modulus. -/
def residuePhase (c a : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / (c : ℂ)))

theorem residuePhase_modEq {c a b : ℤ} (hc : c ≠ 0) (hab : a ≡ b [ZMOD c]) :
    residuePhase c a = residuePhase c b := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp hab
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * ((b : ℂ) / (c : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / (c : ℂ)) +
          (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hk, Int.cast_add, Int.cast_mul]
    field_simp [hcC]
  unfold residuePhase
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem eq_of_inverse_congruences {c a x y : ℤ}
    (hx₀ : 0 ≤ x) (hxc : x < c) (hy₀ : 0 ≤ y) (hyc : y < c)
    (hx : a * x ≡ 1 [ZMOD c]) (hy : a * y ≡ 1 [ZMOD c]) : x = y := by
  have h₁ : x ≡ x * (a * y) [ZMOD c] := by
    simpa only [mul_one] using hy.symm.mul_left x
  have h₂ : x * (a * y) ≡ y [ZMOD c] := by
    rw [show x * (a * y) = y * (a * x) by ring]
    simpa only [mul_one] using hx.mul_left y
  simpa only [Int.emod_eq_of_lt hx₀ hxc, Int.emod_eq_of_lt hy₀ hyc] using (h₁.trans h₂).eq

private theorem gcd_eq_one_of_inverse_congruence {c a x : ℤ}
    (h : a * x ≡ 1 [ZMOD c]) : a.gcd c = 1 := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp h
  refine Int.isCoprime_iff_gcd_eq_one.mp ⟨x, k, ?_⟩
  rw [hk]
  ring

/-- Negate the vacuum Bézout inverse and choose its representative in `[0,c)`. -/
def negatedInverseResidue (c d : ℤ) : ℤ :=
  (-inverseResidue c d) % c

private theorem negatedInverseResidue_spec {c d : ℤ} (hc : 0 < c) (hd : d.gcd c = 1) :
    0 ≤ negatedInverseResidue c d ∧ negatedInverseResidue c d < c ∧
      d * negatedInverseResidue c d ≡ -1 [ZMOD c] := by
  have hg : c.gcd d = 1 := (Int.gcd_comm c d).trans hd
  refine ⟨Int.emod_nonneg _ hc.ne', Int.emod_lt_of_pos _ hc, ?_⟩
  refine ((Int.mod_modEq (-inverseResidue c d) c).mul_left d).trans ?_
  rw [mul_neg]
  exact (inverseResidue_spec hc hg).2.2.neg

theorem negatedInverseResidue_mem {c d : ℤ} (hc : 0 < c) (hd : d ∈ reducedResidues c) :
    negatedInverseResidue c d ∈ reducedResidues c := by
  obtain ⟨h₀, hlt, h⟩ := negatedInverseResidue_spec hc (Finset.mem_filter.mp hd).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h₀, hlt⟩, ?_⟩
  apply gcd_eq_one_of_inverse_congruence (x := -d)
  rw [mul_neg, mul_comm (negatedInverseResidue c d) d]
  simpa only [neg_neg] using h.neg

theorem negatedInverseResidue_involutive {c d : ℤ} (hc : 0 < c)
    (hd : d ∈ reducedResidues c) :
    negatedInverseResidue c (negatedInverseResidue c d) = d := by
  obtain ⟨hdI, hdg⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd₀, hdc⟩ := Finset.mem_Ico.mp hdI
  have hd' := negatedInverseResidue_mem hc hd
  obtain ⟨h₀, hlt, h⟩ := negatedInverseResidue_spec hc (Finset.mem_filter.mp hd').2
  apply eq_of_inverse_congruences h₀ hlt hd₀ hdc (a := -negatedInverseResidue c d)
  · rw [neg_mul]
    simpa only [neg_neg] using h.neg
  · rw [neg_mul, mul_comm (negatedInverseResidue c d) d]
    simpa only [neg_neg] using (negatedInverseResidue_spec hc hdg).2.2.neg

theorem negatedInverseResidue_bijOn {c : ℤ} (hc : 0 < c) :
    Set.BijOn (negatedInverseResidue c) (↑(reducedResidues c) : Set ℤ)
      (↑(reducedResidues c) : Set ℤ) := by
  refine ⟨fun _ hd => negatedInverseResidue_mem hc hd, ?_, ?_⟩
  · intro x hx y hy hxy
    calc
      x = negatedInverseResidue c (negatedInverseResidue c x) :=
        (negatedInverseResidue_involutive hc hx).symm
      _ = negatedInverseResidue c (negatedInverseResidue c y) :=
        congrArg (negatedInverseResidue c) hxy
      _ = y := negatedInverseResidue_involutive hc hy
  · intro d hd
    exact ⟨negatedInverseResidue c d, negatedInverseResidue_mem hc hd,
      negatedInverseResidue_involutive hc hd⟩

theorem vacuumPhase_eq_residuePhase_negatedInverse {c : ℤ} (hc : c ≠ 0) (d : ℤ) :
    vacuumPhase c d = residuePhase c (negatedInverseResidue c d) := by
  calc
    vacuumPhase c d = residuePhase c (-inverseResidue c d) := by
      unfold vacuumPhase residuePhase
      congr 1
      simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
        Complex.ofReal_ofNat, Complex.ofReal_intCast, Int.cast_neg]
      ring
    _ = _ := (residuePhase_modEq hc (Int.mod_modEq (-inverseResidue c d) c)).symm

private theorem sum_reducedResidues_natCast (c : ℕ) (f : ℤ → ℂ) :
    (∑ d ∈ reducedResidues (c : ℤ), f d) =
      ∑ d ∈ (Finset.range c).filter (fun d => d.Coprime c), f (d : ℤ) := by
  refine Finset.sum_nbij' Int.toNat (fun d : ℕ => (d : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdI, hdg⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd₀, hdc⟩ := Finset.mem_Ico.mp hdI
    have hcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd₀
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact Int.ofNat_lt.mp (by simpa only [hcast] using hdc)
    · rw [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_natCast_natCast, hcast]
      exact hdg
  · intro d hd
    obtain ⟨hdc, hdg⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨by exact_mod_cast (Nat.zero_le d), by exact_mod_cast (Finset.mem_range.mp hdc)⟩, ?_⟩
    simpa only [Int.gcd_natCast_natCast] using (Nat.coprime_iff_gcd_eq_one.mp hdg)
  · intro d hd
    exact Int.toNat_of_nonneg (Finset.mem_Ico.mp (Finset.mem_filter.mp hd).1).1
  · intro d _
    exact Int.toNat_natCast d
  · intro d hd
    rw [Int.toNat_of_nonneg (Finset.mem_Ico.mp (Finset.mem_filter.mp hd).1).1]

theorem sum_vacuumPhase_eq_ramanujanSum (c : ℕ) (hc : 0 < c) :
    (∑ d ∈ reducedResidues (c : ℤ), vacuumPhase (c : ℤ) d) = ramanujanSum c 1 := by
  have hcZ : 0 < (c : ℤ) := by exact_mod_cast hc
  calc
    (∑ d ∈ reducedResidues (c : ℤ), vacuumPhase (c : ℤ) d) =
        ∑ d ∈ reducedResidues (c : ℤ), residuePhase (c : ℤ) d := by
      refine Finset.sum_nbij' (negatedInverseResidue (c : ℤ)) (negatedInverseResidue (c : ℤ))
        (fun _ hd => negatedInverseResidue_mem hcZ hd)
        (fun _ hd => negatedInverseResidue_mem hcZ hd)
        (fun _ hd => negatedInverseResidue_involutive hcZ hd)
        (fun _ hd => negatedInverseResidue_involutive hcZ hd) ?_
      exact fun d _ => vacuumPhase_eq_residuePhase_negatedInverse hcZ.ne' d
    _ = ramanujanSum c 1 := by
      rw [sum_reducedResidues_natCast, ramanujanSum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [residuePhase, Int.cast_natCast, Nat.cast_one, mul_one]

/-- The Ramanujan sum at frequency `-1`, in the same natural representatives as D5. -/
def negativeRamanujanSum (c : ℕ) : ℂ :=
  ∑ d ∈ (Finset.range c).filter (fun d => d.Coprime c),
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(d : ℂ) / (c : ℂ)))

theorem negativeRamanujanSum_eq_conj (c : ℕ) :
    negativeRamanujanSum c = conj (ramanujanSum c 1) := by
  rw [negativeRamanujanSum, ramanujanSum, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Complex.exp_conj]
  congr 1
  simp only [Nat.cast_one, mul_one, map_mul, map_div₀, map_ofNat, map_natCast,
    Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The frequency-one specialization of the D5 divisor identity by Möbius inversion. -/
theorem ramanujanSum_one_eq_moebius (c : ℕ) (hc : 0 < c) :
    ramanujanSum c 1 = (μ c : ℂ) := by
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun n hn => sum_ramanujanSum_divisors n 1 hn)
  have hmem : (c, 1) ∈ c.divisorsAntidiagonal := by
    simp [hc.ne']
  calc
    ramanujanSum c 1 = ∑ x ∈ c.divisorsAntidiagonal,
        (μ x.1 : ℂ) * (if x.2 ∣ (1 : ℕ) then (x.2 : ℂ) else 0) := (h c hc).symm
    _ = (μ c : ℂ) := by
      rw [Finset.sum_eq_single_of_mem (c, 1) hmem]
      · simp
      · intro x hx hneq
        have hx₁ : x.1 * x.2 = c := (Nat.mem_divisorsAntidiagonal.mp hx).1
        have hx₂ : x.2 ≠ 1 := by
          intro hx₂
          apply hneq
          exact Prod.ext (by simpa [hx₂] using hx₁) hx₂
        simp [Nat.dvd_one, hx₂]

theorem negativeRamanujanSum_eq_moebius (c : ℕ) (hc : 0 < c) :
    negativeRamanujanSum c = (μ c : ℂ) := by
  rw [negativeRamanujanSum_eq_conj, ramanujanSum_one_eq_moebius c hc, map_intCast]

theorem sum_vacuumPhase_eq_negativeRamanujanSum (c : ℕ) (hc : 0 < c) :
    (∑ d ∈ reducedResidues (c : ℤ), vacuumPhase (c : ℤ) d) = negativeRamanujanSum c := by
  rw [sum_vacuumPhase_eq_ramanujanSum c hc, ramanujanSum_one_eq_moebius c hc,
    negativeRamanujanSum_eq_moebius c hc]

theorem sum_vacuumPhase_eq_moebius (c : ℕ) (hc : 0 < c) :
    (∑ d ∈ reducedResidues (c : ℤ), vacuumPhase (c : ℤ) d) = (μ c : ℂ) := by
  rw [sum_vacuumPhase_eq_negativeRamanujanSum c hc, negativeRamanujanSum_eq_moebius c hc]

theorem sum_vacuumPhase_nat_eq_negativeRamanujanSum (c : ℕ) (hc : 0 < c) :
    (∑ d ∈ (Finset.range c).filter (fun d => d.Coprime c), vacuumPhase (c : ℤ) (d : ℤ)) =
      negativeRamanujanSum c := by
  rw [← sum_reducedResidues_natCast c (vacuumPhase (c : ℤ)),
    sum_vacuumPhase_eq_negativeRamanujanSum c hc]

theorem sum_vacuumPhase_one :
    (∑ d ∈ reducedResidues (1 : ℤ), vacuumPhase 1 d) = 1 := by
  simpa only [Nat.cast_one, ramanujan_one] using
    sum_vacuumPhase_eq_ramanujanSum 1 Nat.zero_lt_one

/-- The two suppliers choose the same inverse representative by uniqueness. -/
theorem linearPhase_eq_vacuumPhase {c d : ℤ} (hc : 0 < c) (hd : d.gcd c = 1) :
    linearPhase c d = vacuumPhase c d := by
  obtain ⟨hl₀, hlc, hl⟩ := inverseMod_spec hc hd
  obtain ⟨hv₀, hvc, hv⟩ := inverseResidue_spec hc ((Int.gcd_comm c d).trans hd)
  have hinv := eq_of_inverse_congruences hl₀ hlc hv₀ hvc hl hv
  have harg : -(2 * Real.pi * (inverseResidue c d : ℝ) / (c : ℝ)) =
      -2 * Real.pi * (inverseResidue c d : ℝ) / (c : ℝ) := by ring
  rw [linearPhase, vacuumPhase, hinv, harg]

private theorem vacuumPhase_eq_of_modEq {c d e : ℤ} (hc : 0 < c)
    (hd : Int.gcd c d = 1) (he : Int.gcd c e = 1) (hde : d ≡ e [ZMOD c]) :
    vacuumPhase c d = vacuumPhase c e := by
  obtain ⟨hd₀, hdc, hdInv⟩ := inverseResidue_spec hc hd
  obtain ⟨he₀, hec, heInv⟩ := inverseResidue_spec hc he
  have hdInv' : e * inverseResidue c d ≡ 1 [ZMOD c] :=
    (hde.symm.mul_right _).trans hdInv
  have hinv := eq_of_inverse_congruences hd₀ hdc he₀ hec hdInv' heInv
  simp only [vacuumPhase, hinv]

private theorem linearPhase_mod_eq_vacuumPhase {c d : ℤ} (hc : 0 < c) (hd : d.gcd c = 1) :
    linearPhase c (d % c) = vacuumPhase c d := by
  have hmod : (d % c).gcd c = 1 := (Int.gcd_emod d c).trans hd
  exact (linearPhase_eq_vacuumPhase hc hmod).trans
    (vacuumPhase_eq_of_modEq hc ((Int.gcd_comm _ _).trans hmod)
      ((Int.gcd_comm _ _).trans hd) (Int.mod_modEq d c))

private theorem mem_strictDenominators {M c d : ℤ} :
    d ∈ strictDenominators M c ↔ |d| < M ∧ Int.gcd c d = 1 := by
  simp only [strictDenominators, Finset.mem_filter, Finset.mem_Ioo, abs_lt, Int.gcd_comm d c]

/-- The two finite linear sums use the same strict rectangle and the same complex phase. -/
theorem linearCutoff_eq_linearRectangularCutoff (N : ℕ) (τ : ℍ) :
    linearCutoff N τ = linearRectangularCutoff N (τ : ℂ) := by
  unfold linearCutoff linearRectangularCutoff
  rw [Finset.sum_sigma']
  let toSigma (p : ℤ × ℤ) : Σ _ : ℕ, ℤ := ⟨p.1.toNat, p.2⟩
  let toRow (p : Σ _ : ℕ, ℤ) : ℤ × ℤ := ((p.1 : ℤ), p.2)
  refine Finset.sum_nbij' toSigma toRow ?_ ?_ ?_ ?_ ?_
  · rintro ⟨c, d⟩ hp
    obtain ⟨hc, hcN, hd, hprim⟩ := mem_cutoffPairs.mp hp
    have hcCast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc.le
    apply Finset.mem_sigma.mpr
    change c.toNat ∈ (Finset.range N).erase 0 ∧
      d ∈ strictDenominators ((N : ℤ) ^ 2) (c.toNat : ℤ)
    rw [hcCast, mem_strictDenominators, Finset.mem_erase, Finset.mem_range]
    have hcNat : 0 < c.toNat := by omega
    exact ⟨⟨hcNat.ne', by omega⟩, hd, hprim⟩
  · rintro ⟨c, d⟩ hp
    obtain ⟨hc, hd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hc₀, hcN⟩ := Finset.mem_erase.mp hc
    obtain ⟨hd, hprim⟩ := mem_strictDenominators.mp hd
    change ((c : ℤ), d) ∈ cutoffPairs N
    exact mem_cutoffPairs.mpr
      ⟨by exact_mod_cast Nat.pos_of_ne_zero hc₀, by exact_mod_cast Finset.mem_range.mp hcN,
        hd, hprim⟩
  · rintro ⟨c, d⟩ hp
    change ((c.toNat : ℤ), d) = (c, d)
    rw [Int.toNat_of_nonneg (mem_cutoffPairs.mp hp).1.le]
  · rintro ⟨c, d⟩ _
    change (⟨(c : ℤ).toNat, d⟩ : Σ _ : ℕ, ℤ) = ⟨c, d⟩
    rw [Int.toNat_natCast]
  · rintro ⟨c, d⟩ hp
    obtain ⟨hc, _, _, hprim⟩ := mem_cutoffPairs.mp hp
    change linearSummand c d τ = linearPhase (c.toNat : ℤ) (d % (c.toNat : ℤ)) *
      (2 * (Real.pi : ℂ) * Complex.I /
        ((c.toNat : ℂ) * ((c.toNat : ℂ) * (τ : ℂ) + (d : ℂ))))
    have hcCast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc.le
    have hcC : (c.toNat : ℂ) = (c : ℂ) := by exact_mod_cast hcCast
    rw [hcCast, hcC,
      linearPhase_mod_eq_vacuumPhase hc ((Int.gcd_comm _ _).trans hprim)]
    simp only [linearSummand, vacuumArgument, denominator, Complex.ofReal_mul,
      Complex.ofReal_ofNat]

/-- The arithmetic weight before multiplication by `2π²`. -/
def vacuumPhaseWeight (c : ℕ) : ℂ :=
  (∑ d ∈ reducedResidues (c : ℤ), vacuumPhase (c : ℤ) d) / (c : ℂ) ^ 2

theorem vacuumPhaseWeight_eq_LSeries_term (c : ℕ) :
    vacuumPhaseWeight c = LSeries.term ↗μ (2 : ℂ) c := by
  cases c with
  | zero => simp [vacuumPhaseWeight]
  | succ c =>
    rw [vacuumPhaseWeight, sum_vacuumPhase_eq_moebius _ (Nat.succ_pos c),
      LSeries.term_of_ne_zero (Nat.succ_ne_zero c), Complex.cpow_two]

theorem hasSum_vacuumPhaseWeight :
    HasSum vacuumPhaseWeight (LSeries ↗μ (2 : ℂ)) := by
  have h : LSeriesSummable ↗μ (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num)
  rw [funext vacuumPhaseWeight_eq_LSeries_term]
  exact h.LSeriesHasSum

theorem summable_norm_vacuumPhaseWeight :
    Summable (fun c : ℕ => ‖vacuumPhaseWeight c‖) :=
  hasSum_vacuumPhaseWeight.summable.norm

theorem hasSum_linearPhaseConstant :
    HasSum (fun c : ℕ => 2 * (Real.pi : ℂ) ^ 2 * vacuumPhaseWeight c) (12 : ℂ) := by
  rw [← moebius_linear_constant]
  exact hasSum_vacuumPhaseWeight.mul_left (2 * (Real.pi : ℂ) ^ 2)

/-- The strict positive outer cutoff of the arithmetic part. -/
def linearConstantCutoff (N : ℕ) : ℂ :=
  ∑ c ∈ (Finset.range N).erase 0, 2 * (Real.pi : ℂ) ^ 2 * vacuumPhaseWeight c

theorem tendsto_linearConstantCutoff :
    Tendsto linearConstantCutoff atTop (𝓝 (12 : ℂ)) := by
  refine hasSum_linearPhaseConstant.tendsto_sum_nat.congr ?_
  intro N
  unfold linearConstantCutoff
  symm
  apply Finset.sum_erase
  rw [vacuumPhaseWeight_eq_LSeries_term, LSeries.term_zero, mul_zero]

private theorem linearWeight_mul_cot_constant (c : ℕ) (hc : 0 < c)
    (d : ℤ) (hd : d ∈ reducedResidues (c : ℤ)) :
    linearWeight (c : ℤ) d * (-(Real.pi : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) ^ 2 * (vacuumPhase (c : ℤ) d / (c : ℂ) ^ 2) := by
  have hcZ : 0 < (c : ℤ) := by exact_mod_cast hc
  rw [linearWeight, linearPhase_eq_vacuumPhase hcZ (Finset.mem_filter.mp hd).2,
    Int.cast_natCast]
  calc
    _ = -(2 * (Real.pi : ℂ) ^ 2 * (vacuumPhase (c : ℤ) d / (c : ℂ) ^ 2)) *
        (Complex.I * Complex.I) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [Complex.I_mul_I]
      ring

private theorem linearConstantCutoff_eq_sum (N : ℕ) :
    linearConstantCutoff N = ∑ c ∈ (Finset.range N).erase 0,
      ∑ d ∈ reducedResidues (c : ℤ), linearWeight (c : ℤ) d * (-(Real.pi : ℂ) * Complex.I) := by
  unfold linearConstantCutoff
  apply Finset.sum_congr rfl
  intro c hc
  have hcpos := Nat.pos_of_ne_zero (Finset.mem_erase.mp hc).1
  unfold vacuumPhaseWeight
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simpa only [div_eq_mul_inv] using (linearWeight_mul_cot_constant c hcpos d hd).symm

private theorem cotangent_positive_powers (z : ℍ) :
    (Real.pi : ℂ) * Complex.cot (Real.pi * (z : ℂ)) =
      -(Real.pi : ℂ) * Complex.I +
        (-2 * (Real.pi : ℂ) * Complex.I) *
          ∑' n : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ)) ^ (n + 1) := by
  rw [pi_mul_cot_pi_q_exp,
    (summable_geometric_of_norm_lt_one (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).tsum_eq_zero_add,
    pow_zero]
  ring

/-- The positive powers in the cotangent expansions at the strict outer cutoff. -/
def linearPrincipalValueQTail (N : ℕ) (τ : ℍ) : ℂ :=
  ∑ c ∈ (Finset.range N).erase 0, ∑ d ∈ reducedResidues (c : ℤ),
    linearWeight (c : ℤ) d * ((-2 * (Real.pi : ℂ) * Complex.I) *
      ∑' n : ℕ, Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * shiftedArgument (τ : ℂ) (c : ℤ) d) ^ (n + 1))

/-- The arithmetic cutoff is the constant part of the finite sum of cotangent expansions. -/
theorem linearPrincipalValueCutoff_eq_constant_add_qTail (N : ℕ) (τ : ℍ) :
    linearPrincipalValueCutoff N (τ : ℂ) =
      linearConstantCutoff N + linearPrincipalValueQTail N τ := by
  rw [linearPrincipalValueCutoff, linearConstantCutoff_eq_sum, linearPrincipalValueQTail,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hshift : (d : ℂ) / ((c : ℤ) : ℂ) = Complex.ofReal ((d : ℝ) / ((c : ℤ) : ℝ)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_intCast]
  have him : 0 < (shiftedArgument (τ : ℂ) (c : ℤ) d).im := by
    simpa only [shiftedArgument, hshift, Complex.add_im, Complex.ofReal_im, add_zero,
      UpperHalfPlane.coe_im] using τ.im_pos
  let z : ℍ := ⟨shiftedArgument (τ : ℂ) (c : ℤ) d, him⟩
  have hq := cotangent_positive_powers z
  change (Real.pi : ℂ) * Complex.cot (Real.pi * shiftedArgument (τ : ℂ) (c : ℤ) d) =
    -(Real.pi : ℂ) * Complex.I + (-2 * (Real.pi : ℂ) * Complex.I) *
      ∑' n : ℕ, Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * shiftedArgument (τ : ℂ) (c : ℤ) d) ^ (n + 1) at hq
  rw [hq, mul_add]

/-- Removing the positive-power cutoff from the rectangular linear term leaves the limit 12. -/
theorem tendsto_linearRectangularCutoff_sub_qTail (τ : ℍ) :
    Tendsto (fun N : ℕ => linearRectangularCutoff N (τ : ℂ) - linearPrincipalValueQTail N τ)
      atTop (𝓝 (12 : ℂ)) := by
  have herror := (linearRectangularCutoff_sub_tendstoUniformlyOn ‖(τ : ℂ)‖).tendsto_at
    (show (τ : ℂ) ∈ {z : ℂ | ‖z‖ ≤ ‖(τ : ℂ)‖ ∧ 0 < z.im} from ⟨le_rfl, τ.im_pos⟩)
  have h := herror.add tendsto_linearConstantCutoff
  rw [zero_add] at h
  refine h.congr fun N => ?_
  rw [linearPrincipalValueCutoff_eq_constant_add_qTail N τ]
  abel

/-- The linear part of the vacuum cutoff, after removing the positive powers, converges
uniformly to its Möbius constant on bounded parts of the upper half-plane. -/
theorem tendstoUniformlyOn_linearCutoff_sub_qTail (B : ℝ) :
    TendstoUniformlyOn (fun N τ => linearCutoff N τ - linearPrincipalValueQTail N τ)
      (fun _ => (12 : ℂ)) atTop {τ : ℍ | ‖(τ : ℂ)‖ ≤ B} := by
  let K : Set ℍ := {τ : ℍ | ‖(τ : ℂ)‖ ≤ B}
  have herror := ((linearRectangularCutoff_sub_tendstoUniformlyOn B).comp
    (fun τ : ℍ => (τ : ℂ))).mono
      (show K ⊆ (fun τ : ℍ => (τ : ℂ)) ⁻¹' {z : ℂ | ‖z‖ ≤ B ∧ 0 < z.im} from
        fun τ hτ => ⟨hτ, τ.im_pos⟩)
  have h := herror.add (tendsto_linearConstantCutoff.tendstoUniformlyOn_const K)
  refine (h.congr (Eventually.of_forall (fun N τ _ => ?_))).congr_right (fun _ _ => zero_add _)
  change linearRectangularCutoff N (τ : ℂ) - linearPrincipalValueCutoff N (τ : ℂ) +
    linearConstantCutoff N = linearCutoff N τ - linearPrincipalValueQTail N τ
  rw [linearCutoff_eq_linearRectangularCutoff, linearPrincipalValueCutoff_eq_constant_add_qTail]
  abel

/-- Removing the pole and the positive-power cutoff leaves the arithmetic constant and
the normally convergent quadratic remainder. -/
theorem tendstoUniformlyOn_rademacherCutoff_sub_pole_sub_qTail {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N τ => rademacherCutoff N τ -
      Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I * (τ : ℂ)) -
      linearPrincipalValueQTail N τ) (fun τ => 12 + remainderLimit τ) atTop K := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (continuous_norm.comp UpperHalfPlane.continuous_coe).continuousOn
  have hlinear := (tendstoUniformlyOn_linearCutoff_sub_qTail B).mono
    (show K ⊆ {τ : ℍ | ‖(τ : ℂ)‖ ≤ B} from fun τ hτ => hB (Set.mem_image_of_mem _ hτ))
  refine (hlinear.add (tendstoUniformlyOn_remainderCutoff hK)).congr
    (Eventually.of_forall (fun N τ _ => ?_))
  change linearCutoff N τ - linearPrincipalValueQTail N τ + remainderCutoff N τ =
    rademacherCutoff N τ - Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I * (τ : ℂ)) -
      linearPrincipalValueQTail N τ
  rw [rademacherCutoff_eq]
  abel

end

end D5.S3.Arith.ModularForms.RademacherPhaseRamanujan

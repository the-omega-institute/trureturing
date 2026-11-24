/- GID: D5/S3/Arith/ModularForms/RademacherLinearTailConvergence
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Locally uniform convergence of the actual linear principal-value Rademacher tail. -/

import D5.S3.Arith.ModularForms.RademacherKloostermanCoefficient
import D5.S3.CharacterSums.KloostermanSummability
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter
open scoped BigOperators Topology UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherLinearTailConvergence

open D5.S3.Arith.ModularForms.RademacherLinearCutoff
  (linearWeight reducedResidues shiftedArgument)
open D5.S3.Arith.ModularForms.RademacherPhaseRamanujan (linearPrincipalValueQTail)
open D5.S3.Arith.ModularForms.RademacherKloostermanCoefficient
  (sum_linearQTail_power_eq_kloosterman)
open D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase (kloosterman)
open D5.S3.CharacterSums.KloostermanSummability (norm_kloosterman_div_sq_le)

set_option autoImplicit false

noncomputable section

local notation "𝕢" => Function.Periodic.qParam 1

/-- The contribution of modulus `c` to the Fourier coefficient of `q^m`.
The zero term allows the positive moduli to be summed over a natural range. -/
def linearQTailCoefficient (c m : ℕ) : ℂ :=
  if hc : c = 0 then 0 else
    (4 * (Real.pi : ℂ) ^ 2 / (c : ℂ) ^ 2) *
      @kloosterman c ⟨hc⟩ ((m : ℤ) : ZMod c) (-1)

/-- The positive-power Fourier series with the full modulus sum in each coefficient. -/
def linearPrincipalValueQTailLimit (τ : ℍ) : ℂ :=
  ∑' n : ℕ, (∑' c : ℕ, linearQTailCoefficient c (n + 1)) * 𝕢 (τ : ℂ) ^ (n + 1)

private def linearQTailTerm (c n : ℕ) (τ : ℍ) : ℂ :=
  linearQTailCoefficient c (n + 1) * 𝕢 (τ : ℂ) ^ (n + 1)

private theorem hasSum_nativeLinearQTail (N : ℕ) (τ : ℍ) :
    HasSum (fun n : ℕ => ∑ c ∈ (Finset.range N).erase 0, ∑ d ∈ reducedResidues (c : ℤ),
      linearWeight (c : ℤ) d * ((-2 * (Real.pi : ℂ) * Complex.I) *
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * shiftedArgument (τ : ℂ) (c : ℤ) d) ^ (n + 1)))
      (linearPrincipalValueQTail N τ) := by
  unfold linearPrincipalValueQTail
  refine hasSum_sum (s := (Finset.range N).erase 0) (fun c _ => ?_)
  refine hasSum_sum (s := reducedResidues (c : ℤ)) (fun d _ => ?_)
  let z := shiftedArgument (τ : ℂ) (c : ℤ) d
  have him : 0 < z.im := by
    simpa [z, shiftedArgument, Complex.add_im, Complex.div_im] using τ.im_pos
  let qz := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)
  have hq : ‖qz‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨z, him⟩ : ℍ)
  have hgeom : Summable (fun n : ℕ => qz ^ (n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => qz ^ n) 1).2
      (summable_geometric_of_norm_lt_one hq)
  exact (hgeom.hasSum.mul_left (-2 * (Real.pi : ℂ) * Complex.I)).mul_left
    (linearWeight (c : ℤ) d)

private def modulusMajorant (c : ℕ) : ℝ :=
  (4 * Real.pi ^ 2 * (4 : ℝ) ^ (4 ^ 8 : ℕ)) * (c : ℝ) ^ (-(9 / 8) : ℝ)

private theorem modulusMajorant_nonneg (c : ℕ) : 0 ≤ modulusMajorant c := by
  unfold modulusMajorant
  positivity

private theorem summable_modulusMajorant : Summable modulusMajorant := by
  have h : Summable (fun c : ℕ => (c : ℝ) ^ (-(9 / 8) : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact h.mul_left (4 * Real.pi ^ 2 * (4 : ℝ) ^ (4 ^ 8 : ℕ))

private theorem norm_linearQTailCoefficient_le (c m : ℕ) :
    ‖linearQTailCoefficient c m‖ ≤ modulusMajorant c := by
  by_cases hc : c = 0
  · subst c
    rw [linearQTailCoefficient, dite_eq_left (rfl : (0 : ℕ) = 0), norm_zero]
    exact modulusMajorant_nonneg 0
  · let : NeZero c := ⟨hc⟩
    have hfour : ‖(4 : ℂ)‖ = (4 : ℝ) := by
      simpa only [Nat.cast_ofNat] using Complex.norm_natCast 4
    calc
      ‖linearQTailCoefficient c m‖ = (4 * Real.pi ^ 2) *
          (‖kloosterman ((m : ℤ) : ZMod c) (-1)‖ / (c : ℝ) ^ 2) := by
        simp only [linearQTailCoefficient, dite_eq_right hc, Complex.norm_mul, Complex.norm_div,
          Complex.norm_pow, Complex.norm_natCast, hfour, Complex.norm_of_nonneg Real.pi_pos.le]
        rw [div_mul_eq_mul_div₀, mul_div_assoc]
      _ ≤ modulusMajorant c := by
        -- The all-moduli bound uses the native `kloosterman_modulus_one` at `c = 1`.
        simpa only [modulusMajorant, mul_assoc] using
          mul_le_mul_of_nonneg_left (norm_kloosterman_div_sq_le ((m : ℤ) : ZMod c) (-1))
            (show 0 ≤ (4 : ℝ) * Real.pi ^ 2 by positivity)

private def qRadius (δ : ℝ) : ℝ := Real.exp (-2 * Real.pi * δ)

private def geometricMass (δ : ℝ) : ℝ := qRadius δ * (1 - qRadius δ)⁻¹

private theorem hasSum_qRadius_pow_succ {δ : ℝ} (hδ : 0 < δ) :
    HasSum (fun n : ℕ => qRadius δ ^ (n + 1)) (geometricMass δ) := by
  have hlt : qRadius δ < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) hδ)
  have hnonneg : 0 ≤ qRadius δ := (Real.exp_pos _).le
  simpa only [geometricMass, pow_succ'] using
    (hasSum_geometric_of_lt_one hnonneg hlt).mul_left (qRadius δ)

private theorem norm_linearQTailTerm_le {δ : ℝ} {τ : ℍ} (hτ : δ ≤ τ.im) (c n : ℕ) :
    ‖linearQTailTerm c n τ‖ ≤ modulusMajorant c * qRadius δ ^ (n + 1) := by
  have hq : ‖𝕢 (τ : ℂ)‖ ≤ qRadius δ := by
    rw [Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im, qRadius, Real.exp_le_exp]
    exact mul_le_mul_of_nonpos_left hτ (mul_nonpos_of_nonpos_of_nonneg (by norm_num) Real.pi_pos.le)
  rw [linearQTailTerm, Complex.norm_mul, Complex.norm_pow]
  exact mul_le_mul (norm_linearQTailCoefficient_le c (n + 1))
    (pow_le_pow_left₀ (norm_nonneg _) hq _) (pow_nonneg (norm_nonneg _) _)
    (modulusMajorant_nonneg c)

/-- Each coefficient is an absolutely convergent sum of the normalized Kloosterman terms. -/
theorem summable_norm_linearQTailCoefficient (m : ℕ) :
    Summable (fun c : ℕ => ‖linearQTailCoefficient c m‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun c => norm_linearQTailCoefficient_le c m) summable_modulusMajorant

/-- The actual positive-power cutoff is the strict finite modulus sum of the Fourier terms. -/
theorem linearPrincipalValueQTail_eq_sum_tsum (N : ℕ) (τ : ℍ) :
    linearPrincipalValueQTail N τ = ∑ c ∈ Finset.range N,
      ∑' n : ℕ, linearQTailCoefficient c (n + 1) * 𝕢 (τ : ℂ) ^ (n + 1) := by
  calc
    linearPrincipalValueQTail N τ =
        ∑' n : ℕ, ∑ c ∈ (Finset.range N).erase 0, ∑ d ∈ reducedResidues (c : ℤ),
          linearWeight (c : ℤ) d * ((-2 * (Real.pi : ℂ) * Complex.I) *
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * shiftedArgument (τ : ℂ) (c : ℤ) d) ^
                (n + 1)) := (hasSum_nativeLinearQTail N τ).tsum_eq.symm
    _ = ∑' n : ℕ, ∑ c ∈ (Finset.range N).erase 0, linearQTailTerm c n τ := by
      apply tsum_congr
      intro n
      rw [sum_linearQTail_power_eq_kloosterman N n τ, Finset.sum_mul,
        ← Finset.sum_coe_sort ((Finset.range N).erase 0)]
      apply Finset.sum_congr rfl
      intro c _
      simp only [linearQTailTerm, linearQTailCoefficient, dite_eq_right (Finset.mem_erase.mp c.2).1,
        Function.Periodic.qParam, Complex.ofReal_one, div_one]
    _ = ∑ c ∈ (Finset.range N).erase 0, ∑' n : ℕ, linearQTailTerm c n τ := by
      refine Summable.tsum_finsetSum (fun c _ => ?_)
      have hgeom := (hasSum_qRadius_pow_succ τ.im_pos).mul_left (modulusMajorant c)
      exact hgeom.summable.of_norm_bounded (norm_linearQTailTerm_le (δ := τ.im) le_rfl c)
    _ = ∑ c ∈ Finset.range N, ∑' n : ℕ, linearQTailTerm c n τ := by
      apply Finset.sum_erase
      simp [linearQTailTerm, linearQTailCoefficient]

private theorem tsum_moduli_eq_linearPrincipalValueQTailLimit (τ : ℍ) :
    (∑' c : ℕ, ∑' n : ℕ, linearQTailTerm c n τ) = linearPrincipalValueQTailLimit τ := by
  have hgeom := hasSum_qRadius_pow_succ τ.im_pos
  have hnonneg : 0 ≤ qRadius τ.im := (Real.exp_pos _).le
  have hmajorant : Summable (fun p : ℕ × ℕ =>
      modulusMajorant p.1 * qRadius τ.im ^ (p.2 + 1)) := by
    have hnonnegProd : 0 ≤ (fun p : ℕ × ℕ =>
        modulusMajorant p.1 * qRadius τ.im ^ (p.2 + 1)) :=
      fun p => mul_nonneg (modulusMajorant_nonneg p.1) (pow_nonneg hnonneg _)
    refine (summable_prod_of_nonneg hnonnegProd).2 ?_
    refine ⟨fun c => (hgeom.mul_left (modulusMajorant c)).summable, ?_⟩
    have hrow (c : ℕ) :
        (∑' n : ℕ, modulusMajorant c * qRadius τ.im ^ (n + 1)) =
          modulusMajorant c * geometricMass τ.im :=
      (hgeom.mul_left (modulusMajorant c)).tsum_eq
    simp_rw [hrow]
    exact summable_modulusMajorant.mul_right (geometricMass τ.im)
  have h : Summable (Function.uncurry (fun c n => linearQTailTerm c n τ)) :=
    hmajorant.of_norm_bounded (fun p => norm_linearQTailTerm_le (δ := τ.im) le_rfl p.1 p.2)
  calc
    (∑' c : ℕ, ∑' n : ℕ, linearQTailTerm c n τ) =
        ∑' n : ℕ, ∑' c : ℕ, linearQTailTerm c n τ := (Summable.tsum_comm h).symm
    _ = linearPrincipalValueQTailLimit τ := by
      unfold linearPrincipalValueQTailLimit
      apply tsum_congr
      intro n
      exact (summable_norm_linearQTailCoefficient (n + 1)).of_norm.tsum_mul_right _

/-- The linear principal-value Fourier tail converges uniformly above every positive height. -/
theorem tendstoUniformlyOn_linearPrincipalValueQTail {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn linearPrincipalValueQTail linearPrincipalValueQTailLimit atTop
      {τ : ℍ | δ ≤ τ.im} := by
  have hgeom := hasSum_qRadius_pow_succ hδ
  have hM := tendstoUniformlyOn_tsum_nat
    (f := fun c τ => ∑' n : ℕ, linearQTailTerm c n τ)
    (s := {τ : ℍ | δ ≤ τ.im})
    (summable_modulusMajorant.mul_right (geometricMass δ))
    (fun c τ hτ => tsum_of_norm_bounded (hgeom.mul_left (modulusMajorant c))
      (norm_linearQTailTerm_le hτ c))
  refine (hM.congr (F' := linearPrincipalValueQTail) ?_).congr_right ?_
  · exact Eventually.of_forall (fun N τ _ => (linearPrincipalValueQTail_eq_sum_tsum N τ).symm)
  · exact fun τ _ => tsum_moduli_eq_linearPrincipalValueQTailLimit τ

/-- Local uniform convergence in the upper half-plane with the same Fourier-series limit. -/
theorem tendstoLocallyUniformly_linearPrincipalValueQTail :
    TendstoLocallyUniformly linearPrincipalValueQTail linearPrincipalValueQTailLimit atTop := by
  refine Metric.tendstoLocallyUniformly_iff.2 (fun ε hε τ => ?_)
  let δ := τ.im / 2
  have hδ : 0 < δ := half_pos τ.im_pos
  have hτ : δ < τ.im := half_lt_self τ.im_pos
  have hopen : IsOpen {z : ℍ | δ < z.im} := isOpen_lt continuous_const UpperHalfPlane.continuous_im
  refine ⟨{z : ℍ | δ < z.im}, hopen.mem_nhds hτ, ?_⟩
  exact ((Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_linearPrincipalValueQTail hδ))
    ε hε).mono (fun N hN z hz => hN z (show δ ≤ z.im from le_of_lt (show δ < z.im from hz)))

end

end D5.S3.Arith.ModularForms.RademacherLinearTailConvergence

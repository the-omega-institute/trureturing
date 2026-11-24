import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperCuspGerms
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial

/-! The formal energy expansion of the normalized HHBB iterate at the cusp one. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Topology NNReal ENNReal TensorProduct
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalIterateExpansion

open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd)

private theorem hasFPowerSeriesAt_of_energy_sum {A : ℂ → ℂ} {c : ℕ → ℂ}
    (hSum : ∀ s ∈ ball (0 : ℂ) 1, HasSum (fun E => c E * s ^ E) (A s)) :
    HasFPowerSeriesAt A (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
  have hHalf : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, norm_one]
    norm_num
  have hRadius : ((1 / 2 : ℝ≥0) : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    have h := (hSum _ hHalf).summable.tendsto_atTop_zero.norm
    simpa [norm_mul, norm_pow, norm_div, FormalMultilinearSeries.ofScalars_norm] using h
  refine ⟨((1 / 2 : ℝ≥0) : ℝ≥0∞), hRadius, by norm_num, ?_⟩
  intro s hs
  have hs' : s ∈ ball (0 : ℂ) 1 := by
    apply mem_ball_zero_iff.mpr
    have h := mem_eball_zero_iff.mp hs
    rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at h
    exact (show ‖s‖ < 1 / 2 from by exact_mod_cast h).trans (by norm_num)
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using hSum s hs'

private theorem finite_binomial_hasFPowerSeriesAt
    (S : Finset ℕ) (c e : ℕ → ℂ) :
    HasFPowerSeriesAt (fun s : ℂ => ∑ j ∈ S, c j * (1 + s) ^ e j)
      (FormalMultilinearSeries.ofScalars ℂ (fun E => ∑ j ∈ S, c j * Ring.choose (e j) E)) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change HasFPowerSeriesAt (fun _ : ℂ => (0 : ℂ))
      (FormalMultilinearSeries.ofScalars ℂ (0 : ℕ → ℂ)) 0
    simpa using (hasFPowerSeriesAt_const (𝕜 := ℂ) (e := (0 : ℂ)) (c := (0 : ℂ)))
  | @insert j S hj ih =>
    have h := (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := e j)).const_smul
      (c := c j)
    simpa only [Finset.sum_insert hj, ← FormalMultilinearSeries.ofScalars_add,
      ← FormalMultilinearSeries.ofScalars_smul, binomialSeries, Pi.add_def, Pi.smul_apply,
      smul_eq_mul] using h.add ih

private theorem numerator_hasFPowerSeriesAt (P : Polynomial ℂ) (α : ℂ) :
    HasFPowerSeriesAt (fun s : ℂ => (1 + s) ^ α * P.eval (1 + s)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun E => ∑ j ∈ P.support, P.coeff j * Ring.choose (α - j) E)) 0 := by
  refine (finite_binomial_hasFPowerSeriesAt P.support P.coeff (fun j => α - j)).congr ?_
  filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with s hs
  have hx := (Complex.mem_slitPlane_iff_arg.mp
    (Complex.mem_slitPlane_of_norm_lt_one (mem_ball_zero_iff.mp hs)))
  rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.cpow_sub _ _ hx.2, Complex.cpow_natCast, inv_pow, div_eq_mul_inv]
  ring

/-- Cancellation of the pole at one and the inverse energy coordinate give the
principal-power germ of the iterate at zero. -/
theorem hhbb_iterate_germ_at_zero {H A : ℂ → ℂ} (P : Polynomial ℂ) (a b L N : ℕ)
    (hA : ContinuousAt A 0)
    (hRational : ∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ),
      H y = P.eval y / (y ^ a * (1 - y) ^ b))
    (hChart : ∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ),
      H y = (1 - y) ^ (-(b : ℤ)) * (Complex.sqrt y) ^ ((N : ℤ) - L + 1) *
        A ((1 - y) / y)) :
    A =ᶠ[𝓝 (0 : ℂ)] fun s : ℂ => (1 + s) ^ ((a : ℂ) + ((N : ℂ) - L + 1) / 2) *
      P.eval (1 + s)⁻¹ := by
  let α : ℂ := (a : ℂ) + ((N : ℂ) - L + 1) / 2
  apply (hA.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (numerator_hasFPowerSeriesAt P α).analyticAt.continuousAt).mp
  have hCoord : Tendsto (fun s : ℂ => (1 + s)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : ContinuousAt (fun s : ℂ => (1 + s)⁻¹) 0 := by
        apply ContinuousAt.inv₀ (by fun_prop)
        simp
      simpa using h.continuousWithinAt.tendsto
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      simpa using hs
  filter_upwards [hCoord.eventually hRational, hCoord.eventually hChart,
    eventually_mem_nhdsWithin (s := ({0} : Set ℂ)ᶜ),
    eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds (0 : ℂ) zero_lt_one)]
    with s hR hC hs₀ hs
  let y : ℂ := (1 + s)⁻¹
  have hx := Complex.mem_slitPlane_iff_arg.mp
    (Complex.mem_slitPlane_of_norm_lt_one (mem_ball_zero_iff.mp hs))
  have hy : y ≠ 0 := inv_ne_zero hx.2
  have hy₁ : 1 - y ≠ 0 := by
    have hs' : s ≠ 0 := by simpa using hs₀
    simpa [y, sub_ne_zero] using hs'
  have hRatio : (1 - y) / y = s := by
    dsimp only [y]
    field_simp [hx.2]
    ring
  change H y = P.eval y / (y ^ a * (1 - y) ^ b) at hR
  change H y = (1 - y) ^ (-(b : ℤ)) * (Complex.sqrt y) ^ ((N : ℤ) - L + 1) *
    A ((1 - y) / y) at hC
  rw [hRatio, zpow_neg, zpow_natCast] at hC
  have hyb : (1 - y) ^ b ≠ 0 := pow_ne_zero _ hy₁
  have hP := (div_eq_iff (mul_ne_zero (pow_ne_zero a hy) hyb)).mp (hR.symm.trans hC)
  have hP' : P.eval y = A s * (y ^ a * (Complex.sqrt y) ^ ((N : ℤ) - L + 1)) := by
    rw [hP]
    field_simp [hyb]
  have hPower : y ^ a * (Complex.sqrt y) ^ ((N : ℤ) - L + 1) = ((1 + s) ^ α)⁻¹ := by
    rw [← Complex.cpow_natCast, Complex.sqrt, ← Complex.cpow_int_mul, ← Complex.cpow_add _ _ hy]
    have hExp : (a : ℂ) + (↑((N : ℤ) - L + 1) : ℂ) * (2 : ℂ)⁻¹ = α := by
      dsimp [α]
      push_cast
      ring
    rw [hExp]
    exact Complex.inv_cpow (1 + s) α hx.1
  rw [hPower] at hP'
  have hNonzero : (1 + s) ^ α ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hx.2)
  exact ((mul_inv_eq_iff_eq_mul₀ hNonzero).mp hP'.symm).trans (mul_comm _ _)

/-- The actual HHBB iterate energy series and its coefficients at the collision
(y=1), expressed through the common rational numerator. -/
theorem hhbb_iterate_powerSeries_and_coeff
    {H A : ℂ → ℂ} (P : Polynomial ℂ) (a b M K L N : ℕ)
    (u v : TwistedEven) (w bState : TwistedOdd)
    (hRational : ∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ),
      H y = P.eval y / (y ^ a * (1 - y) ^ b))
    (hChart : ∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ),
      H y = (1 - y) ^ (-(b : ℤ)) * (Complex.sqrt y) ^ ((N : ℤ) - L + 1) *
        A ((1 - y) / y))
    (hSum : ∀ s ∈ ball (0 : ℂ) 1, HasSum
      (fun E : ℕ => fixedAIterateCoeff false M K L N (fixedAExponent M K E)
        u v w.val bState.val * s ^ E) (A s)) :
    let α : ℂ := (a : ℂ) + ((N : ℂ) - L + 1) / 2
    PowerSeries.mk (fun E => fixedAIterateCoeff false M K L N (fixedAExponent M K E)
      u v w.val bState.val) =
      (∑ j ∈ P.support, PowerSeries.C (P.coeff j) * PowerSeries.binomialSeries ℂ (α - j)) ∧
    ∀ E : ℕ, fixedAIterateCoeff false M K L N (fixedAExponent M K E) u v w.val bState.val =
      ∑ j ∈ P.support, P.coeff j * Ring.choose (α - j) E := by
  intro α
  have hActual := hasFPowerSeriesAt_of_energy_sum hSum
  have hGerm := hhbb_iterate_germ_at_zero P a b L N hActual.analyticAt.continuousAt
    hRational hChart
  have hSeries := hActual.eq_formalMultilinearSeries
    ((numerator_hasFPowerSeriesAt P α).congr hGerm.symm)
  have hCoeff (E : ℕ) : fixedAIterateCoeff false M K L N (fixedAExponent M K E)
      u v w.val bState.val = ∑ j ∈ P.support, P.coeff j * Ring.choose (α - j) E := by
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg (fun f => FormalMultilinearSeries.coeff f E) hSeries
  refine ⟨?_, hCoeff⟩
  ext E
  simpa only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul,
    PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one] using hCoeff E

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeFixedPairAIterate (fixedASlitSewn)
open NativeHHBBUpperCuspGerms (hhbb_marked_upper_cusp_germs)

/-- For the marked states, the actual sewn A sum supplies the energy coefficients.
The normalized half-plane chart supplies the germ used to read the same coefficients
from the common numerator. -/
theorem hhbb_marked_iterate_energy_expansion {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w bState : TwistedOdd) (p q r d : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : bState.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] d)
    (H : ℂ → ℂ) (P : Polynomial ℂ) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let A (s : ℂ) := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-s)
    let α : ℂ := (a : ℂ) + ((N : ℂ) - L + 1) / 2
    let c (E : ℕ) := fixedAIterateCoeff false M K L N (fixedAExponent M K E)
      u v w.val bState.val
    (∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ), H y = P.eval y / (y ^ a * (1 - y) ^ b)) →
    (∀ y : ℂ, (1 / 2 : ℝ) < y.re → y ≠ 1 →
      H y = (1 - y) ^ (-((6 + (M : ℤ) + K) / 2)) *
        (Complex.sqrt y * (Complex.sqrt y ^ ((N : ℤ) - L) * A ((1 - y) / y)))) →
    PowerSeries.mk c =
      (∑ j ∈ P.support, PowerSeries.C (P.coeff j) * PowerSeries.binomialSeries ℂ (α - j)) ∧
    ∀ E : ℕ, c E = ∑ j ∈ P.support, P.coeff j * Ring.choose (α - j) E := by
  intro grade V M K L N a b A α c hRational hNormalized
  obtain ⟨_, _, ⟨_, _, hSum, _⟩, _⟩ :=
    hhbb_marked_upper_cusp_germs slot colour n l hl hpar u v w bState p q r d hu hv hw hb
  have hbCast : (b : ℤ) = (6 + (M : ℤ) + K) / 2 := by
    simp only [b, Int.natCast_div, Nat.cast_add, Nat.cast_ofNat]
  have hHalf : ∀ᶠ y : ℂ in 𝓝 (1 : ℂ), (1 / 2 : ℝ) < y.re :=
    (Complex.continuous_re.continuousAt (x := 1)).eventually (lt_mem_nhds (by norm_num))
  have hChart : ∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ),
      H y = (1 - y) ^ (-(b : ℤ)) * (Complex.sqrt y) ^ ((N : ℤ) - L + 1) *
        A ((1 - y) / y) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hHalf,
      eventually_mem_nhdsWithin (s := ({1} : Set ℂ)ᶜ)] with y hy hyOne
    have hy₀ : y ≠ 0 := by
      rintro rfl
      norm_num at hy
    have hZ : Complex.sqrt y ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hy₀)
    rw [hNormalized y hy (by simpa using hyOne), hbCast, zpow_add₀ hZ, zpow_one]
    ring
  exact hhbb_iterate_powerSeries_and_coeff P a b M K L N u v w bState hRational hChart hSum

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalIterateExpansion

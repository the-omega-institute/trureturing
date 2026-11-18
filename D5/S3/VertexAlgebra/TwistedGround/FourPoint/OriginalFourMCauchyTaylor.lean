/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCauchyTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCauchyTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor coefficients of the actual same-puncture free subtraction. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAnalyticPullback
import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

/-! Bivariate Taylor extraction for the ordinary regular Cauchy correction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Filter PowerSeries
open scoped Topology BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCauchyTaylor

open OriginalGaussianSewnAnalytic (coefficient)
open private cpow_affine_coefficient from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAnalyticPullback
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport (unitPower contractionScalar)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy (regularSeries)
open private inner outer liftOuter e b c bi ci half sumRootInverse sumRootInverse_mul from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy
open private analyticAt_local_cpow from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap

private theorem coefficient_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coefficient n (fun z => f z + g z) = coefficient n f + coefficient n g := by
  simp only [coefficient, iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

private theorem coefficient_mul_univariate {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coefficient n (fun z => f z * g z) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, coefficient ij.1 f * coefficient ij.2 g := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coefficient i f * coefficient j g)]
  simp only [coefficient, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have h : i ≤ n := by simpa using hi
  have hc : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((n-i).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have hn (k : ℕ) : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hn]
  linear_combination iteratedDeriv i f 0 * iteratedDeriv (n-i) g 0 * hc

private theorem coefficient_const (a : ℂ) (n : ℕ) :
    coefficient n (fun _ => a) = if n = 0 then a else 0 := by
  cases n with
  | zero => simp [coefficient]
  | succ n => simp [coefficient, iteratedDeriv_const]

private def slice (f : ℂ × ℂ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  coefficient n (fun u => f (u, v))

private theorem slice_analytic {f : ℂ × ℂ → ℂ} (hf : AnalyticAt ℂ f (0, 0)) (n : ℕ) :
    AnalyticAt ℂ (slice f n) 0 := by
  let L : ℂ →L[ℂ] ℂ × ℂ := (ContinuousLinearMap.id ℂ ℂ).prod 0
  let M := ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ℂ × ℂ) ℂ
    (fun _ => (1, 0))
  let g : ℂ → ℂ := fun v => M (iteratedFDeriv ℂ n f (0, v)) / (n.factorial : ℂ)
  have hD : AnalyticAt ℂ (iteratedFDeriv ℂ n f) (0, 0) := by
    exact (AnalyticOnNhd.iteratedFDeriv (s := {x | AnalyticAt ℂ f x})
      (fun _ hx => hx) n) _ hf
  have hg : AnalyticAt ℂ g 0 := by
    have ha := hD.curry_right
    have hm : AnalyticAt ℂ (fun v => M (iteratedFDeriv ℂ n f (0, v))) 0 :=
      AnalyticAt.comp (f := fun v : ℂ => iteratedFDeriv ℂ n f (0, v)) (M.analyticAt _) ha
    exact hm.div_const
  apply hg.congr
  have ha : ∀ᶠ v : ℂ in 𝓝 0, AnalyticAt ℂ f (0, v) := by
    exact (continuousAt_const.prodMk continuousAt_id).tendsto hf.eventually_analyticAt
  filter_upwards [ha] with v hv
  let F : ℂ × ℂ → ℂ := fun y => f (y + (0, v))
  have hF : AnalyticAt ℂ F 0 :=
    hv.comp_of_eq (analyticAt_id.add analyticAt_const) (by simp)
  have hd : ContDiffAt ℂ n F 0 := hF.contDiffAt
  have he : iteratedFDeriv ℂ n (F ∘ L) 0 =
      (iteratedFDeriv ℂ n F 0).compContinuousLinearMap (fun _ => L) := by
    obtain ⟨s, hsOpen, hs, hFs⟩ := hd.contDiffWithinAt.contDiffOn' (s := Set.univ)
      (m := n) le_rfl (by simp)
    simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hFs
    have hL : L 0 ∈ s := by simpa using hs
    have h := L.iteratedFDerivWithin_comp_right hFs hsOpen.uniqueDiffOn
      (hsOpen.preimage L.continuous).uniqueDiffOn hL le_rfl
    have hs' := (hsOpen.preimage L.continuous).uniqueDiffOn (𝕜 := ℂ)
    have hd' : ContDiffAt ℂ n (F ∘ L) 0 :=
      ContDiffAt.comp 0 (by simpa using hd) L.contDiff.contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs' hd' hL] at h
    rw [map_zero, iteratedFDerivWithin_eq_iteratedFDeriv hsOpen.uniqueDiffOn hd hs] at h
    exact h
  have hcomp : F ∘ L = fun u => f (u, v) := by ext u; simp [F, L]
  have hh := congrArg (fun m : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ =>
    m (fun _ => 1)) he
  rw [hcomp, ← iteratedDeriv_eq_iteratedFDeriv] at hh
  change _ = iteratedFDeriv ℂ n F 0 (fun _ => L 1) at hh
  have htrans : iteratedFDeriv ℂ n F 0 = iteratedFDeriv ℂ n f (0, v) := by
    simpa [F] using (iteratedFDeriv_comp_add_right (𝕜 := ℂ) (f := f) n (0, v) 0)
  rw [htrans] at hh
  simpa [g, M, slice, coefficient, L] using
    congrArg (fun a : ℂ => a / (n.factorial : ℂ)) hh.symm

private def taylor (f : ℂ → ℂ) : PowerSeries ℂ := mk fun n => coefficient n f

private def taylorPair (f : ℂ × ℂ → ℂ) : PowerSeries (LaurentSeries ℂ) :=
  mk fun n => HahnSeries.ofPowerSeries ℤ ℂ (taylor (slice (fun uv => f (uv.2, uv.1)) n))

private theorem taylor_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) : taylor f = taylor g := by
  apply PowerSeries.ext
  intro n
  simp only [taylor, coeff_mk, coefficient, h.iteratedDeriv_eq]

private theorem taylor_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) : taylor (fun z => f z + g z) = taylor f + taylor g := by
  apply PowerSeries.ext
  intro n
  simp only [taylor, coeff_mk, map_add, coefficient_add hf hg]

private theorem taylor_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) : taylor (fun z => f z * g z) = taylor f * taylor g := by
  apply PowerSeries.ext
  intro n
  simp only [taylor, coeff_mk, coeff_mul, coefficient_mul_univariate hf hg]

private theorem taylor_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    taylor (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, taylor (f i) := by
  apply PowerSeries.ext
  intro n
  simp only [taylor, coeff_mk, map_sum, coefficient,
    iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt), Finset.sum_div]

private theorem taylor_const (a : ℂ) : taylor (fun _ => a) = C a := by
  apply PowerSeries.ext
  intro n
  simp [taylor, coefficient_const, coeff_C]

private theorem taylorPair_const (a : ℂ) :
    taylorPair (fun _ => a) = C (HahnSeries.C a) := by
  apply PowerSeries.ext
  intro n
  have hs : slice (fun _ => a) n = fun _ => if n = 0 then a else 0 := by
    funext u
    exact coefficient_const a n
  simp only [taylorPair, coeff_mk, hs, taylor_const, HahnSeries.ofPowerSeries_C, coeff_C]
  split_ifs <;> simp

private theorem taylorPair_fst (f : ℂ → ℂ) :
    taylorPair (fun uv => f uv.1) = outer (taylor f) := by
  apply PowerSeries.ext
  intro n
  have hs : slice (fun uv => f uv.2) n = fun u => if n = 0 then f u else 0 := by
    funext u
    exact coefficient_const (f u) n
  simp only [taylorPair, coeff_mk, hs, outer, RingHom.comp_apply, coeff_C, liftOuter]
  split_ifs
  · rfl
  · simp [taylor_const]

private theorem taylorPair_snd (f : ℂ → ℂ) :
    taylorPair (fun uv => f uv.2) = inner (taylor f) := by
  apply PowerSeries.ext
  intro n
  change coeff n (taylorPair (fun uv => f uv.2)) =
    coeff n (PowerSeries.map HahnSeries.C (taylor f))
  rw [coeff_map, taylorPair, coeff_mk]
  change HahnSeries.ofPowerSeries ℤ ℂ (taylor (fun _ => coefficient n f)) =
    HahnSeries.C (coeff n (taylor f))
  rw [taylor_const, HahnSeries.ofPowerSeries_C, taylor, coeff_mk]

private theorem taylorPair_congr {f g : ℂ × ℂ → ℂ}
    (h : f =ᶠ[𝓝 (0, 0)] g) : taylorPair f = taylorPair g := by
  rw [nhds_prod_eq] at h
  obtain ⟨p, hp, q, hq, h⟩ := eventually_prod_iff.mp h
  apply PowerSeries.ext
  intro n
  simp only [taylorPair, coeff_mk]
  apply congrArg (HahnSeries.ofPowerSeries ℤ ℂ)
  apply taylor_congr
  filter_upwards [hp] with u hu
  have he : (fun v => f (u, v)) =ᶠ[𝓝 0] (fun v => g (u, v)) := hq.mono fun v hv => h hu hv
  simp only [slice, coefficient, he.iteratedDeriv_eq]

private theorem slice_swap_analytic {f : ℂ × ℂ → ℂ} (hf : AnalyticAt ℂ f (0, 0))
    (n : ℕ) : AnalyticAt ℂ (slice (fun uv => f (uv.2, uv.1)) n) 0 := by
  apply slice_analytic
  exact hf.comp_of_eq (analyticAt_snd.prod analyticAt_fst) rfl

private theorem taylorPair_add {f g : ℂ × ℂ → ℂ} (hf : AnalyticAt ℂ f (0, 0))
    (hg : AnalyticAt ℂ g (0, 0)) :
    taylorPair (fun uv => f uv + g uv) = taylorPair f + taylorPair g := by
  apply PowerSeries.ext
  intro n
  simp only [taylorPair, coeff_mk, map_add]
  rw [← map_add, ← taylor_add (slice_swap_analytic hf n) (slice_swap_analytic hg n)]
  apply congrArg (HahnSeries.ofPowerSeries ℤ ℂ)
  apply taylor_congr
  have ht : Tendsto (fun u : ℂ => (u, (0 : ℂ))) (𝓝 0) (𝓝 (0, 0)) :=
    (continuousAt_id.prodMk (continuousAt_const (y := (0 : ℂ)))).tendsto
  filter_upwards [ht hf.eventually_analyticAt, ht hg.eventually_analyticAt] with u hfu hgu
  exact coefficient_add hfu.curry_right hgu.curry_right n

private theorem taylorPair_mul {f g : ℂ × ℂ → ℂ} (hf : AnalyticAt ℂ f (0, 0))
    (hg : AnalyticAt ℂ g (0, 0)) :
    taylorPair (fun uv => f uv * g uv) = taylorPair f * taylorPair g := by
  apply PowerSeries.ext
  intro n
  let sf := slice (fun uv => f (uv.2, uv.1))
  let sg := slice (fun uv => g (uv.2, uv.1))
  simp only [taylorPair, coeff_mk, coeff_mul]
  change _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
    HahnSeries.ofPowerSeries ℤ ℂ (taylor (sf ij.1)) *
      HahnSeries.ofPowerSeries ℤ ℂ (taylor (sg ij.2))
  let terms : ℕ × ℕ → ℂ → ℂ := fun ij u => sf ij.1 u * sg ij.2 u
  have hterms (ij : ℕ × ℕ) : AnalyticAt ℂ (terms ij) 0 :=
    (slice_swap_analytic hf ij.1).mul (slice_swap_analytic hg ij.2)
  have hsum : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      HahnSeries.ofPowerSeries ℤ ℂ (taylor (terms ij))) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        HahnSeries.ofPowerSeries ℤ ℂ (taylor (sf ij.1)) *
          HahnSeries.ofPowerSeries ℤ ℂ (taylor (sg ij.2)) := by
    apply Finset.sum_congr rfl
    intro ij _
    rw [show taylor (terms ij) = taylor (sf ij.1) * taylor (sg ij.2) from
      taylor_mul (slice_swap_analytic hf ij.1) (slice_swap_analytic hg ij.2), map_mul]
  rw [← hsum, ← map_sum, ← taylor_sum _ (fun ij _ => hterms ij)]
  apply congrArg (HahnSeries.ofPowerSeries ℤ ℂ)
  apply taylor_congr
  have ht : Tendsto (fun u : ℂ => (u, (0 : ℂ))) (𝓝 0) (𝓝 (0, 0)) :=
    (continuousAt_id.prodMk (continuousAt_const (y := (0 : ℂ)))).tendsto
  filter_upwards [ht hf.eventually_analyticAt, ht hg.eventually_analyticAt] with u hfu hgu
  exact coefficient_mul_univariate hfu.curry_right hgu.curry_right n

private theorem taylor_binomial (eta a : ℂ) :
    taylor (fun z => (1-eta*z)^a) = unitPower eta a := by
  apply PowerSeries.ext
  intro n
  rw [taylor, coeff_mk, cpow_affine_coefficient, unitPower, coeff_rescale, binomialSeries_coeff]
  simp

private def rootPower (eta a : ℂ) (z : ℂ) : ℂ := (1-eta*z)^a

private theorem rootPower_analytic (eta a : ℂ) : AnalyticAt ℂ (rootPower eta a) 0 :=
  analyticAt_local_cpow (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp)

private theorem rootPower_zero (eta a : ℂ) : rootPower eta a 0 = 1 := by simp [rootPower]

private theorem taylorPair_regularSeries (eta : ℂ) :
    taylorPair (fun uv => eta * (1 + rootPower eta (1/2) uv.1 * rootPower eta (1/2) uv.2) /
      (2 * rootPower eta (1/2) uv.1 * rootPower eta (1/2) uv.2 *
        (rootPower eta (1/2) uv.1 + rootPower eta (1/2) uv.2)^2)) = regularSeries eta := by
  let B : ℂ × ℂ → ℂ := fun uv => rootPower eta (1/2) uv.1
  let C₀ : ℂ × ℂ → ℂ := fun uv => rootPower eta (1/2) uv.2
  let Bi : ℂ × ℂ → ℂ := fun uv => rootPower eta (-1/2) uv.1
  let Ci : ℂ × ℂ → ℂ := fun uv => rootPower eta (-1/2) uv.2
  let S := fun uv => B uv + C₀ uv
  let Si := fun uv => (S uv)⁻¹
  have hB : AnalyticAt ℂ B (0, 0) := (rootPower_analytic eta _).comp_of_eq analyticAt_fst rfl
  have hC : AnalyticAt ℂ C₀ (0, 0) := (rootPower_analytic eta _).comp_of_eq analyticAt_snd rfl
  have hBi : AnalyticAt ℂ Bi (0, 0) := (rootPower_analytic eta _).comp_of_eq analyticAt_fst rfl
  have hCi : AnalyticAt ℂ Ci (0, 0) := (rootPower_analytic eta _).comp_of_eq analyticAt_snd rfl
  have hS : AnalyticAt ℂ S (0, 0) := hB.add hC
  have hS₀ : S (0, 0) ≠ 0 := by norm_num [S, B, C₀, rootPower_zero]
  have hSi : AnalyticAt ℂ Si (0, 0) := hS.inv hS₀
  have hbt : taylorPair B = b eta := by
    dsimp only [B]
    rw [taylorPair_fst,
      show taylor (rootPower eta _) = unitPower eta _ from taylor_binomial _ _, b]
  have hct : taylorPair C₀ = c eta := by
    dsimp only [C₀]
    rw [taylorPair_snd,
      show taylor (rootPower eta _) = unitPower eta _ from taylor_binomial _ _, c]
  have hbit : taylorPair Bi = bi eta := by
    dsimp only [Bi]
    rw [taylorPair_fst,
      show taylor (rootPower eta _) = unitPower eta _ from taylor_binomial _ _, bi]
  have hcit : taylorPair Ci = ci eta := by
    dsimp only [Ci]
    rw [taylorPair_snd,
      show taylor (rootPower eta _) = unitPower eta _ from taylor_binomial _ _, ci]
  have hst : taylorPair S = b eta + c eta := by
    dsimp only [S]
    rw [taylorPair_add hB hC, hbt, hct]
  have hsit : taylorPair Si = sumRootInverse eta := by
    have hprod : (b eta + c eta) * taylorPair Si = 1 := by
      rw [← hst, ← taylorPair_mul hS hSi]
      trans taylorPair (fun _ => 1)
      · apply taylorPair_congr
        filter_upwards [hS.continuousAt.eventually_ne hS₀] with uv huv
        exact mul_inv_cancel₀ huv
      · simp [taylorPair_const]
    calc
      taylorPair Si = taylorPair Si * ((b eta+c eta)*sumRootInverse eta) := by
        rw [sumRootInverse_mul, mul_one]
      _ = ((b eta+c eta) * taylorPair Si) * sumRootInverse eta := by ring
      _ = sumRootInverse eta := by rw [hprod, one_mul]
  trans taylorPair (fun uv => eta * (2:ℂ)⁻¹ * (1+B uv*C₀ uv) * Bi uv * Ci uv * (Si uv*Si uv))
  · apply taylorPair_congr
    apply Eventually.of_forall
    intro uv
    have hb : Bi uv = (B uv)⁻¹ := by
      change (1-eta*uv.1)^(-1/2:ℂ) = ((1-eta*uv.1)^(1/2:ℂ))⁻¹
      rw [show (-1/2:ℂ) = -(1/2) by ring, Complex.cpow_neg]
    have hc : Ci uv = (C₀ uv)⁻¹ := by
      change (1-eta*uv.2)^(-1/2:ℂ) = ((1-eta*uv.2)^(1/2:ℂ))⁻¹
      rw [show (-1/2:ℂ) = -(1/2) by ring, Complex.cpow_neg]
    change eta * (1 + B uv * C₀ uv) / (2 * B uv * C₀ uv * S uv ^ 2) = _
    change _ = eta * (2:ℂ)⁻¹ * (1+B uv*C₀ uv) * Bi uv * Ci uv * (Si uv*Si uv)
    rw [hb, hc]
    dsimp only [Si]
    rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv, ← inv_pow, pow_two]
    ring
  · let N : ℂ × ℂ → ℂ := fun uv => 1 + B uv * C₀ uv
    let K : ℂ × ℂ → ℂ := fun _ => eta * (2:ℂ)⁻¹
    have hK : AnalyticAt ℂ K (0, 0) := analyticAt_const
    have hN : AnalyticAt ℂ N (0, 0) := analyticAt_const.add (hB.mul hC)
    have hNt : taylorPair N = 1 + b eta * c eta := by
      change taylorPair (fun uv => 1+B uv*C₀ uv) = _
      rw [taylorPair_add (f := fun _ => 1) (g := fun uv => B uv * C₀ uv)
        analyticAt_const (hB.mul hC), taylorPair_mul hB hC, hbt, hct, taylorPair_const]
      simp
    change taylorPair (fun uv => K uv * N uv * Bi uv * Ci uv * (Si uv*Si uv)) = _
    rw [taylorPair_mul (f := fun uv => K uv * N uv * Bi uv * Ci uv) (g := fun uv => Si uv*Si uv)
      (((hK.mul hN).mul hBi).mul hCi) (hSi.mul hSi),
      taylorPair_mul hSi hSi, hsit,
      taylorPair_mul (f := fun uv => K uv * N uv * Bi uv) ((hK.mul hN).mul hBi) hCi, hcit,
      taylorPair_mul (f := fun uv => K uv * N uv) (hK.mul hN) hBi, hbit,
      taylorPair_mul hK hN, hNt]
    rw [show taylorPair K = C (HahnSeries.C (eta * (2:ℂ)⁻¹)) from taylorPair_const _]
    rw [regularSeries, e, half, map_mul, map_inv₀, map_ofNat, map_mul]
    ring

open OriginalFourMActualChart (Chart Puncture loweringParameter)
open private freeCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct

private def regularCorrection (eta : ℂ) (u v : ℂ) : ℂ :=
  let B := rootPower eta (1/2) u
  let C₀ := rootPower eta (1/2) v
  eta * (1+B*C₀) / (2*B*C₀*(B+C₀)^2)

private theorem regular_correction_coefficient (eta : ℂ) (p q : ℕ) :
    coefficient p (fun u => coefficient q (fun v => regularCorrection eta u v)) =
      eta^(p+q+1) * contractionScalar p q := by
  have h := taylorPair_regularSeries eta
  change taylorPair (fun uv => regularCorrection eta uv.1 uv.2) = regularSeries eta at h
  have hc := congrArg (fun A : PowerSeries (LaurentSeries ℂ) =>
    (coeff q A).coeff (p:ℤ)) h
  simp only [taylorPair, coeff_mk] at hc
  rw [LaurentSeries.coeff_coe_powerSeries, taylor, coeff_mk,
    D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy.regular_series_coefficient] at hc
  exact hc

/-- The chart subtraction uses the literal finite lowering contraction at
every pair of ordinary Taylor indices, including equal indices. -/
theorem chart_free_correction_coefficient (c : Chart) (i : Puncture) (p q : ℕ) :
    coefficient p (fun u => coefficient q (fun v => freeCorrection c i
      ((1-loweringParameter c i*u)^(1/2:ℂ)) ((1-loweringParameter c i*v)^(1/2:ℂ)))) =
      loweringParameter c i^(p+q+1) * contractionScalar p q := by
  exact regular_correction_coefficient (loweringParameter c i) p q

open LatticeGeneratingFieldLocality (LatticeData Index Oscillator)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
  (creationPart contraction normalOrder lowering_normal_order_word)
open private vacuum vacuumProjection vacuumProjection_apply from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

private theorem pair_top_coefficient (D : LatticeData) (x y : Index D) :
    coeff (x.2+y.2+1) (normalOrder D [x, y]) (1 : Oscillator D) =
      ((D.G x.1 y.1 : ℂ) * contractionScalar x.2 y.2) • (1 : Oscillator D) := by
  have hword : normalOrder D [x, y] =
      (creationPart D x * creationPart D y + contraction D x y) * vacuum D := by
    simp [normalOrder, mul_assoc, add_mul]
  rw [hword, vacuum, coeff_mul_C, map_add]
  have hzero : coeff (x.2+y.2+1) (creationPart D x * creationPart D y) = 0 := by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have hsum : ij.1 + ij.2 = x.2+y.2+1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    simp only [creationPart, coeff_mk]
    split_ifs <;> first | omega | simp
  rw [hzero, zero_add, contraction, coeff_monomial, ite_eq_left rfl]
  simp [vacuumProjection_apply]

private theorem weighted_pair_symmetry (D : LatticeData) (hu : IsUnit D.G.det) (x y : Index D) :
    (D.G x.1 y.1 : ℂ) * contractionScalar x.2 y.2 =
      (D.G y.1 x.1 : ℂ) * contractionScalar y.2 x.2 := by
  let n := x.2+y.2+1
  have hxy := lowering_normal_order_word D hu [x, y] n
  have hyx := lowering_normal_order_word D hu [y, x] n
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hxy hyx
  rw [mul_comm (MvPolynomial.X y : Oscillator D)] at hyx
  have he := hxy.symm.trans hyx
  rw [show n = x.2+y.2+1 by rfl, pair_top_coefficient D x y,
    show x.2+y.2+1 = y.2+x.2+1 by omega, pair_top_coefficient D y x] at he
  simpa [MvPolynomial.constantCoeff_smul] using
    congrArg (fun f : Oscillator D => f.constantCoeff) he

private theorem native_regular_correction_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (eta : ℂ) (x y : Index D) :
    (D.G x.1 y.1 : ℂ) *
      coefficient y.2 (fun v => coefficient x.2 (fun u => regularCorrection eta u v)) =
      (D.G x.1 y.1 : ℂ) * (eta^(x.2+y.2+1) * contractionScalar x.2 y.2) := by
  have hswap (u v : ℂ) : regularCorrection eta u v = regularCorrection eta v u := by
    unfold regularCorrection
    ring
  have hsel : (fun v => coefficient x.2 (fun u => regularCorrection eta u v)) =
      (fun v => coefficient x.2 (fun u => regularCorrection eta v u)) := by
    funext v
    congr 1
    funext u
    exact hswap u v
  rw [hsel, regular_correction_coefficient, show y.2+x.2+1 = x.2+y.2+1 by omega]
  calc
    _ = eta^(x.2+y.2+1) * ((D.G y.1 x.1 : ℂ) * contractionScalar y.2 x.2) := by
      rw [D.symmetric x.1 y.1]
      ring
    _ = _ := by rw [weighted_pair_symmetry D hu y x]; ring

/-- In the native order of the two Taylor selectors, the regular subtraction
is the Gram-weighted pair obtained by normally ordering the original currents. -/
theorem native_free_correction_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (c : Chart) (i : Puncture) (x y : Index D) :
    (D.G x.1 y.1 : ℂ) * coefficient y.2 (fun v => coefficient x.2 (fun u => freeCorrection c i
      ((1-loweringParameter c i*u)^(1/2:ℂ)) ((1-loweringParameter c i*v)^(1/2:ℂ)))) =
      (D.G x.1 y.1 : ℂ) * (loweringParameter c i^(x.2+y.2+1) * contractionScalar x.2 y.2) :=
  native_regular_correction_coefficient D hu (loweringParameter c i) x y

open OriginalFourMActualChart (scale scaleRoot chosen_roots)
open OriginalFourMOccupationTransport (inverseRoot)
open private rawLocal halfJacobian from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private scale_ne from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart
open private root_ne from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport

private theorem pair_coefficient_congr {F G : ℂ × ℂ → ℂ} (h : F =ᶠ[𝓝 (0, 0)] G)
    (p q : ℕ) :
    coefficient q (fun v => coefficient p (fun u => F (u, v))) =
      coefficient q (fun v => coefficient p (fun u => G (u, v))) := by
  rw [nhds_prod_eq] at h
  obtain ⟨P, hP, Q, hQ, h⟩ := eventually_prod_iff.mp h
  have he : (fun v => coefficient p (fun u => F (u, v))) =ᶠ[𝓝 0]
      (fun v => coefficient p (fun u => G (u, v))) := by
    filter_upwards [hQ] with v hv
    have he : (fun u => F (u, v)) =ᶠ[𝓝 0] (fun u => G (u, v)) :=
      hP.mono fun u hu => h hu hv
    simp only [coefficient, he.iteratedDeriv_eq]
  exact congrArg (fun z : ℂ => z / (q.factorial : ℂ)) (he.iteratedDeriv_eq (n := q))

private theorem inverse_correction_germ {a : ℝ} (ha : 0 < a) (ha₁ : a < 1)
    (c : Chart) (i : Puncture) :
    (fun uv : ℂ × ℂ => -freeCorrection c i (inverseRoot c a i uv.1) (inverseRoot c a i uv.2) /
      (halfJacobian c a i (inverseRoot c a i uv.1) *
        halfJacobian c a i (inverseRoot c a i uv.2))) =ᶠ[𝓝 (0, 0)]
      (fun uv => regularCorrection (-loweringParameter c i / scale c a i) uv.1 uv.2) := by
  let lam := scale c a i
  let eta := loweringParameter c i
  let s := scaleRoot c a i
  let t := -eta / lam
  let B := fun u : ℂ => 1 - t*u
  let R := rootPower t (1/2)
  have hl : lam ≠ 0 := scale_ne ha ha₁ c i
  have hS : s ≠ 0 := root_ne ha ha₁ c i
  have hs : s^2 = lam := (chosen_roots ha ha₁ c i).1
  have hB : ContinuousAt B 0 := continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hb : ∀ᶠ u in 𝓝 0, B u ∈ Complex.slitPlane :=
    hB.eventually (Complex.isOpen_slitPlane.mem_nhds (by simp [B]))
  have hsum : ∀ᶠ uv : ℂ × ℂ in 𝓝 (0, 0), R uv.1 + R uv.2 ≠ 0 := by
    have hR : AnalyticAt ℂ R 0 := rootPower_analytic t (1/2)
    have h₁ : AnalyticAt ℂ (fun uv : ℂ × ℂ => R uv.1) (0, 0) :=
      hR.comp_of_eq analyticAt_fst rfl
    have h₂ : AnalyticAt ℂ (fun uv : ℂ × ℂ => R uv.2) (0, 0) :=
      hR.comp_of_eq analyticAt_snd rfl
    have hh := (h₁.add h₂).continuousAt
    exact hh.eventually_ne (by norm_num [R, rootPower_zero])
  have ht₁ : Tendsto (Prod.fst : ℂ × ℂ → ℂ) (𝓝 (0, 0)) (𝓝 0) := continuous_fst.continuousAt
  have ht₂ : Tendsto (Prod.snd : ℂ × ℂ → ℂ) (𝓝 (0, 0)) (𝓝 0) := continuous_snd.continuousAt
  have hroot (u : ℂ) (hu : B u ∈ Complex.slitPlane) : inverseRoot c a i u = (R u)⁻¹ := by
    have hu₀ := Complex.slitPlane_ne_zero hu
    have hd : lam+eta*u = lam*B u := by
      dsimp [B,t]
      field_simp
      ring
    have he : 1-eta*rawLocal c a i u = (B u)⁻¹ := by
      change 1-eta*(u/(lam+eta*u)) = _
      rw [hd]
      field_simp [hu₀]
      dsimp [B,t]
      field_simp
      ring
    unfold inverseRoot
    change (1-eta*rawLocal c a i u)^(1/2:ℂ) = _
    rw [he, Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi hu)]
    rfl
  filter_upwards [ht₁ hb, ht₂ hb, hsum] with uv h₁ h₂ h₃
  have hp : R uv.1 ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero h₁))
  have hq : R uv.2 ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero h₂))
  rw [hroot _ h₁, hroot _ h₂]
  change -(eta * (1+(R uv.1)⁻¹*(R uv.2)⁻¹) /
    (2*(R uv.1)⁻¹*(R uv.2)⁻¹*((R uv.1)⁻¹+(R uv.2)⁻¹)^2)) /
      ((s/((R uv.1)⁻¹)^3)*(s/((R uv.2)⁻¹)^3)) =
       (-eta/lam)*(1+R uv.1*R uv.2)/(2*R uv.1*R uv.2*(R uv.1+R uv.2)^2)
  rw [← hs]
  have hi : (R uv.1)⁻¹ + (R uv.2)⁻¹ = (R uv.1 + R uv.2)/(R uv.1*R uv.2) := by
    field_simp
    ring
  rw [hi]
  field_simp
  ring

/-- The correction added to the inverse half-current pullback has exactly
the same coefficient as a contracted pair in the original lowering action.
The two inverse scale powers are taken at the incoming modes. -/
theorem inverse_physical_free_correction_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) (c : Chart) (i : Puncture) (x y : Index D) :
    (D.G x.1 y.1 : ℂ) * coefficient y.2 (fun v => coefficient x.2 (fun u =>
      -freeCorrection c i (inverseRoot c a i u) (inverseRoot c a i v) /
        (halfJacobian c a i (inverseRoot c a i u) * halfJacobian c a i (inverseRoot c a i v)))) =
      ((scaleRoot c a i)⁻¹)^(2*x.2+1) * ((scaleRoot c a i)⁻¹)^(2*y.2+1) *
        ((D.G x.1 y.1 : ℂ) * ((-loweringParameter c i)^(x.2+y.2+1) *
          contractionScalar x.2 y.2)) := by
  rw [pair_coefficient_congr (inverse_correction_germ ha ha₁ c i) x.2 y.2,
    native_regular_correction_coefficient D hu, div_pow, ← (chosen_roots ha ha₁ c i).1]
  rw [← pow_add, show 2*x.2+1+(2*y.2+1) = 2*(x.2+y.2+1) by omega, pow_mul,
    div_eq_mul_inv, ← inv_pow, ← inv_pow]
  ring

open OriginalFourMAnalyticPullback (inverse_physical_source_coefficient)
open private rawLocal_analytic inverseRoot_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport

private def inverseJac (c : Chart) (a : ℝ) (i : Puncture) (u : ℂ) : ℂ :=
  (halfJacobian c a i (inverseRoot c a i u))⁻¹

private def creatorEntry (c : Chart) (a : ℝ) (i : Puncture) (n k : ℕ) : ℂ :=
  (scaleRoot c a i)⁻¹ ^ (2*n+1) *
    (-loweringParameter c i)^(n-k) * Ring.choose ((n:ℂ)+1/2) (n-k)

private theorem inverseJac_analytic {a : ℝ} (ha : 0 < a) (ha₁ : a < 1)
    (c : Chart) (i : Puncture) : AnalyticAt ℂ (inverseJac c a i) 0 := by
  change AnalyticAt ℂ (fun u => (scaleRoot c a i / (inverseRoot c a i u)^3)⁻¹) 0
  simp only [inv_div]
  exact ((inverseRoot_analytic ha ha₁ c i).pow 3).div_const

private theorem inverse_pullback_entry {a : ℝ} (ha : 0 < a) (ha₁ : a < 1)
    (c : Chart) (i : Puncture) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    coefficient n (fun u => inverseJac c a i u * f (rawLocal c a i u)) =
      ∑ k ∈ Finset.range (n+1), creatorEntry c a i n k * coefficient k f := by
  unfold inverseJac
  rw [inverse_physical_source_coefficient ha ha₁ c i hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold creatorEntry
  ring

private theorem coefficient_mul_scalar (z : ℂ) (n : ℕ) (f : ℂ → ℂ) :
    coefficient n (fun u => z*f u) = z*coefficient n f := by
  simp only [coefficient, iteratedDeriv_const_mul_field, mul_div_assoc]

/-- Each leg of a regular covariance carries its own finite creator
transform, with the chosen local lift and the native order of selectors. -/
theorem inverse_physical_two_leg_coefficient {a : ℝ} (ha : 0 < a) (ha₁ : a < 1)
    (c : Chart) (i j : Puncture) {F : ℂ × ℂ → ℂ} (hF : AnalyticAt ℂ F (0, 0))
    (m n : ℕ) :
    coefficient n (fun v => coefficient m (fun u =>
      inverseJac c a i u * inverseJac c a j v * F (rawLocal c a i u, rawLocal c a j v))) =
      ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (n+1),
        creatorEntry c a i m k * creatorEntry c a j n l *
          coefficient l (fun v => coefficient k (fun u => F (u, v))) := by
  let g := rawLocal c a j
  have hg : AnalyticAt ℂ g 0 := rawLocal_analytic ha ha₁ c j
  have hg₀ : g 0 = 0 := by simp [g, rawLocal]
  have ht : Tendsto (fun v => ((0:ℂ), g v)) (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [hg₀] using (continuousAt_const.prodMk hg.continuousAt).tendsto
  have he : (fun v => coefficient m (fun u =>
      inverseJac c a i u * inverseJac c a j v * F (rawLocal c a i u, rawLocal c a j v))) =ᶠ[𝓝 0]
      (fun v => ∑ k ∈ Finset.range (m+1),
        creatorEntry c a i m k * (inverseJac c a j v * slice F k (g v))) := by
    filter_upwards [ht hF.eventually_analyticAt] with v hv
    have hv' : AnalyticAt ℂ (fun u => F (u, g v)) 0 := hv.curry_left
    rw [show (fun u => inverseJac c a i u * inverseJac c a j v *
        F (rawLocal c a i u, rawLocal c a j v)) =
      (fun u => inverseJac c a j v * (inverseJac c a i u *
        F (rawLocal c a i u, g v))) from by funext u; dsimp [g]; ring,
      coefficient_mul_scalar, inverse_pullback_entry ha ha₁ c i hv', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold slice
    ring
  have hterms (k : ℕ) : AnalyticAt ℂ
      (fun v => creatorEntry c a i m k * (inverseJac c a j v * slice F k (g v))) 0 :=
    analyticAt_const.mul ((inverseJac_analytic ha ha₁ c j).mul
      ((slice_analytic hF k).comp_of_eq hg hg₀))
  have hjet := he.iteratedDeriv_eq (n := n)
  unfold coefficient at hjet ⊢
  rw [hjet, iteratedDeriv_fun_sum (fun k _ => (hterms k).contDiffAt), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]
  change creatorEntry c a i m k * coefficient n
    (fun v => inverseJac c a j v * (slice F k) (rawLocal c a j v)) = _
  rw [inverse_pullback_entry ha ha₁ c j (slice_analytic hF k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  unfold slice coefficient
  ring

open OriginalFourMOccupationTransport (flags)
open OriginalFourMSignedOverlap (chartCovariance chart_covariance_analytic)
open OriginalFourMPhysicalCovariance (physicalCovariance)
open private jac slotCorrection same_flags physicalCovariance_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

private theorem pair_coefficient_add {F G : ℂ × ℂ → ℂ}
    (hF : AnalyticAt ℂ F (0, 0)) (hG : AnalyticAt ℂ G (0, 0)) (m n : ℕ) :
    coefficient n (slice (fun uv => F uv + G uv) m) =
      coefficient n (slice F m) + coefficient n (slice G m) := by
  have ht : Tendsto (fun v : ℂ => ((0 : ℂ), v)) (𝓝 0) (𝓝 (0, 0)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have he : slice (fun uv => F uv + G uv) m =ᶠ[𝓝 0]
      (fun v => slice F m v + slice G m v) := by
    filter_upwards [ht hF.eventually_analyticAt, ht hG.eventually_analyticAt] with v hfv hgv
    exact coefficient_add hfv.curry_left hgv.curry_left m
  have hh : coefficient n (slice (fun uv => F uv + G uv) m) =
      coefficient n (fun v => slice F m v + slice G m v) :=
    congrArg (fun z : ℂ => z / (n.factorial : ℂ)) (he.iteratedDeriv_eq (n := n))
  rw [hh, coefficient_add (slice_analytic hF m) (slice_analytic hG m)]

/-- All native chart blocks use the two finite creator transforms in
physical coordinates. The actual same-puncture block adds precisely the
original Gram-weighted contraction with the inverse lowering parameter. -/
theorem selected_physical_covariance (D : LatticeData) (hu : IsUnit D.G.det)
    {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) (upperA : Bool)
    (c : Chart) (i j : Puncture) (x y : Index D) :
    let K := fun u v => chartCovariance upperA c a
      (flags c i).1 (flags c j).1 (flags c i).2 (flags c j).2 u v
    (D.G x.1 y.1 : ℂ) * coefficient y.2 (fun v => coefficient x.2 (fun u =>
      physicalCovariance upperA c a i j u v)) =
    (D.G x.1 y.1 : ℂ) *
      (∑ k ∈ Finset.range (x.2+1), ∑ l ∈ Finset.range (y.2+1),
        creatorEntry c a i x.2 k * creatorEntry c a j y.2 l *
          coefficient l (fun v => coefficient k (fun u => K u v))) +
    (if (flags c i).1 = (flags c j).1 ∧ (flags c i).2 = (flags c j).2 then
      ((scaleRoot c a i)⁻¹)^(2*x.2+1) * ((scaleRoot c a i)⁻¹)^(2*y.2+1) *
        ((D.G x.1 y.1 : ℂ) * ((-loweringParameter c i)^(x.2+y.2+1) *
          contractionScalar x.2 y.2))
    else 0) := by
  dsimp only
  let K : ℂ × ℂ → ℂ := fun uv => chartCovariance upperA c a
    (flags c i).1 (flags c j).1 (flags c i).2 (flags c j).2 uv.1 uv.2
  have hK : AnalyticAt ℂ K (0, 0) := chart_covariance_analytic ha ha₁ upperA c _ _ _ _
  let F : ℂ × ℂ → ℂ := fun uv => inverseJac c a i uv.1 * inverseJac c a j uv.2 *
    K (rawLocal c a i uv.1, rawLocal c a j uv.2)
  let G : ℂ × ℂ → ℂ := fun uv => -slotCorrection c a i j uv.1 uv.2 /
    (jac c a i uv.1 * jac c a j uv.2)
  have hF : AnalyticAt ℂ F (0, 0) := by
    have h₁ := (inverseJac_analytic ha ha₁ c i).comp_of_eq
      (analyticAt_fst (𝕜 := ℂ) (p := ((0, 0) : ℂ × ℂ))) rfl
    have h₂ := (inverseJac_analytic ha ha₁ c j).comp_of_eq
      (analyticAt_snd (𝕜 := ℂ) (p := ((0, 0) : ℂ × ℂ))) rfl
    have hp := ((rawLocal_analytic ha ha₁ c i).comp_of_eq
      (analyticAt_fst (𝕜 := ℂ) (p := ((0, 0) : ℂ × ℂ))) rfl).prod
      ((rawLocal_analytic ha ha₁ c j).comp_of_eq
      (analyticAt_snd (𝕜 := ℂ) (p := ((0, 0) : ℂ × ℂ))) rfl)
    exact (h₁.mul h₂).mul (hK.comp_of_eq hp (by simp [rawLocal]))
  have hp : (fun uv : ℂ × ℂ => physicalCovariance upperA c a i j uv.1 uv.2) =
      fun uv => F uv + G uv := by
    funext uv
    simp only [F, G, K, physicalCovariance]
    change (_ - slotCorrection c a i j uv.1 uv.2) / (jac c a i uv.1 * jac c a j uv.2) =
      (jac c a i uv.1)⁻¹ * (jac c a j uv.2)⁻¹ * _ +
        -slotCorrection c a i j uv.1 uv.2 / (jac c a i uv.1 * jac c a j uv.2)
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hF' := inverse_physical_two_leg_coefficient ha ha₁ c i j hK x.2 y.2
  change coefficient y.2 (slice F x.2) = _ at hF'
  have hleft : (fun v => coefficient x.2 (fun u => physicalCovariance upperA c a i j u v)) =
      slice (fun uv => F uv + G uv) x.2 := by
    exact congrArg (fun W => slice W x.2) hp
  have hG : AnalyticAt ℂ G (0, 0) := by
    have hP := physicalCovariance_analytic upperA ha ha₁ c i j
    rw [hp] at hP
    have hdiff := hP.sub hF
    exact hdiff.congr (Eventually.of_forall (fun uv => by
      change F uv + G uv - F uv = G uv
      ring))
  rw [hleft, pair_coefficient_add hF hG x.2 y.2, hF', mul_add]
  congr 1
  by_cases hij : i = j
  · subst j
    simp only [G, slotCorrection, and_self, ite_true, jac]
    exact inverse_physical_free_correction_coefficient D hu ha ha₁ c i x y
  · have hf : ¬ ((flags c i).1 = (flags c j).1 ∧ (flags c i).2 = (flags c j).2) :=
      fun h => hij (same_flags c h)
    rw [ite_eq_right hf]
    have hG₀ : G = 0 := by
      funext uv
      simp [G, slotCorrection, hf]
    have hz : slice G x.2 = fun _ => 0 := by
      rw [hG₀]
      funext v
      change coefficient x.2 (fun _ => 0) = 0
      rw [coefficient_const]
      split_ifs <;> rfl
    rw [hz, coefficient_const]
    split_ifs <;> simp

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCauchyTaylor

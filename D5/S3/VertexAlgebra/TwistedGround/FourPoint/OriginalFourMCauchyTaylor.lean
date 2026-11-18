/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCauchyTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCauchyTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor coefficients of the actual same-puncture free subtraction. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAnalyticPullback
import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy

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
    rw [taylorPair_fst, show taylor (rootPower eta _) = unitPower eta _ from taylor_binomial _ _, b]
  have hct : taylorPair C₀ = c eta := by
    dsimp only [C₀]
    rw [taylorPair_snd, show taylor (rootPower eta _) = unitPower eta _ from taylor_binomial _ _, c]
  have hbit : taylorPair Bi = bi eta := by
    dsimp only [Bi]
    rw [taylorPair_fst, show taylor (rootPower eta _) = unitPower eta _ from taylor_binomial _ _, bi]
  have hcit : taylorPair Ci = ci eta := by
    dsimp only [Ci]
    rw [taylorPair_snd, show taylor (rootPower eta _) = unitPower eta _ from taylor_binomial _ _, ci]
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

/-- The chart subtraction uses the literal finite lowering contraction at
every pair of ordinary Taylor indices, including equal indices. -/
theorem chart_free_correction_coefficient (c : Chart) (i : Puncture) (p q : ℕ) :
    coefficient p (fun u => coefficient q (fun v => freeCorrection c i
      ((1-loweringParameter c i*u)^(1/2:ℂ)) ((1-loweringParameter c i*v)^(1/2:ℂ)))) =
      loweringParameter c i^(p+q+1) * contractionScalar p q := by
  let eta := loweringParameter c i
  let R : ℂ × ℂ → ℂ := fun uv => freeCorrection c i (rootPower eta (1/2) uv.1)
    (rootPower eta (1/2) uv.2)
  have h := taylorPair_regularSeries eta
  change taylorPair R = regularSeries eta at h
  have hc := congrArg (fun A : PowerSeries (LaurentSeries ℂ) =>
    (coeff q A).coeff (p:ℤ)) h
  simp only [taylorPair, coeff_mk] at hc
  rw [LaurentSeries.coeff_coe_powerSeries, taylor, coeff_mk,
    D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy.regular_series_coefficient] at hc
  exact hc

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCauchyTaylor

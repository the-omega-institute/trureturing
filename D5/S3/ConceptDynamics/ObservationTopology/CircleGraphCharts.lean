/- GID: D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts
   mirror-E: none(waiver:pure-existential-chart-construction)
   anchors: []
   utility: none
   digest: Analytic intrinsic Circle maps with injective differentials have fixed-complement graph charts. -/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Int.GCD
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open WithLp

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function Set Topology
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

namespace D5.S3.ConceptDynamics.ObservationTopology.CircleGraphCharts

/-- For the actual intrinsic Circle, an injective differential gives actual
normal-form charts, with one fixed Euclidean complement at every point. The
nonlinear thickening and its local inverse are constructed inside the proof. -/
theorem isImmersionOfComplement_of_contMDiff_injective_mvfderiv
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (f : Circle → V) (hf : ContMDiff (𝓡 1) 𝓘(ℝ, V) ⊤ f)
    (hdf : ∀ z, Function.Injective (mvfderiv (𝓡 1) f z)) :
    Manifold.IsImmersionOfComplement
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ V - 1)))
      (𝓡 1) 𝓘(ℝ, V) ⊤ f := by
  classical
  let E := EuclideanSpace ℝ (Fin 1)
  let W := EuclideanSpace ℝ (Fin (Module.finrank ℝ V - 1))
  have hLocal (z : Circle) (L : (E × W) ≃L[ℝ] V)
      (hL : ∀ u : E, L (u, 0) =
        fderiv ℝ (f ∘ (chartAt E z).symm) (chartAt E z z) u) :
      Manifold.IsImmersionAtOfComplement W (𝓡 1) 𝓘(ℝ, V) ⊤ f z := by
    classical
    let c : OpenPartialHomeomorph Circle E := chartAt E z
    let q : E := c z
    let g : E → V := f ∘ c.symm
    have hcz : z ∈ c.source := mem_chart_source E z
    have hc : c ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ Circle :=
      IsManifold.chart_mem_maximalAtlas z
    have hq : q ∈ c.target := c.map_source hcz
    have hg : ContDiffAt ℝ ⊤ g q := by
      exact ((hf (c.symm q)).comp q
        (contMDiffAt_symm_of_mem_maximalAtlas hc hq)).contDiffAt
    let D : E →L[ℝ] V := fderiv ℝ g q
    have hD : HasFDerivAt g D q := (hg.differentiableAt (by simp)).hasFDerivAt
    have hLu (u : E) : L (u, 0) = D u := hL u
    let P : V →L[ℝ] E :=
      (ContinuousLinearMap.fst ℝ E W).comp L.symm.toContinuousLinearMap
    let N : V →L[ℝ] V := L.toContinuousLinearMap.comp
      ((0 : V →L[ℝ] E).prod
        ((ContinuousLinearMap.snd ℝ E W).comp L.symm.toContinuousLinearMap))
    let b : V := L (q, 0)
    let H : V → V := fun y => g (P y) + N y
    have hPb : P b = q := by simp [P, b]
    have hHaxis (u : E) : H (L (u, 0)) = g u := by simp [H, P, N]
    have hHb : H b = f z := by
      rw [hHaxis]
      exact congrArg f (c.left_inv hcz)
    have hH : ContDiffAt ℝ ⊤ H b := by
      apply ContDiffAt.add
      · exact (hPb.symm ▸ hg).comp b P.contDiff.contDiffAt
      · exact N.contDiff.contDiffAt
    have hHder : HasFDerivAt H
        (ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V) b := by
      have hd : HasFDerivAt H (D.comp P + N) b :=
        ((hPb.symm ▸ hD).comp b P.hasFDerivAt).add N.hasFDerivAt
      convert hd using 1
      ext y
      change y = D (L.symm y).1 + L (0, (L.symm y).2)
      calc
        y = L (L.symm y) := (L.apply_symm_apply y).symm
        _ = L ((L.symm y).1, 0) + L (0, (L.symm y).2) := by
          rw [← map_add]
          congr 1
          ext <;> simp
        _ = _ := by rw [hLu]
    let e : OpenPartialHomeomorph V V :=
      hH.toOpenPartialHomeomorph H hHder (by simp)
    have hb : b ∈ e.source := hH.mem_toOpenPartialHomeomorph_source hHder (by simp)
    have hinv : ContDiffAt ℝ ⊤ e.symm (f z) := by
      rw [← hHb]
      exact hH.to_localInverse hHder (by simp)
    obtain ⟨s, hs, hHs⟩ := hH.contDiffOn (m := ⊤) le_rfl (by simp)
    obtain ⟨s₀, hs₀s, hs₀, hbs₀⟩ := mem_nhds_iff.mp hs
    obtain ⟨t, ht, hIt⟩ := hinv.contDiffOn (m := ⊤) le_rfl (by simp)
    obtain ⟨t₀, ht₀t, ht₀, hft₀⟩ := mem_nhds_iff.mp ht
    let cod : OpenPartialHomeomorph V V :=
      (e.restrOpen s₀ hs₀).symm.restrOpen t₀ ht₀
    have hcodinv : (cod.symm : V → V) = H := rfl
    have hbCod : b ∈ cod.target := by
      change b ∈ (e.source ∩ s₀) ∩ e ⁻¹' t₀
      exact ⟨⟨hb, hbs₀⟩, by change H b ∈ t₀; rwa [hHb]⟩
    have hcodz : f z ∈ cod.source := by
      have h := cod.map_target hbCod
      rwa [hcodinv, hHb] at h
    have hcodAtlas : cod ∈ IsManifold.maximalAtlas 𝓘(ℝ, V) ⊤ V := by
      apply cod.mem_maximalAtlas_of_contMDiffOn
      · change ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) ⊤ e.symm cod.source
        apply ContDiffOn.contMDiffOn
        apply hIt.mono
        intro y hy
        change y ∈ (e.target ∩ e.symm ⁻¹' s₀) ∩ t₀ at hy
        exact ht₀t hy.2
      · change ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) ⊤ H cod.target
        apply ContDiffOn.contMDiffOn
        apply hHs.mono
        intro y hy
        change y ∈ (e.source ∩ s₀) ∩ e ⁻¹' t₀ at hy
        exact hs₀s hy.1.2
    let A : E → V := fun u => L (u, 0)
    have hA : Continuous A := L.continuous.comp (continuous_id.prodMk continuous_const)
    let U : Set E := A ⁻¹' cod.target
    have hU : IsOpen U := cod.open_target.preimage hA
    let dom : OpenPartialHomeomorph Circle E := c.trans (OpenPartialHomeomorph.ofSet U hU)
    have hdomz : z ∈ dom.source := by
      change z ∈ c.source ∩ c ⁻¹' U
      exact ⟨hcz, hbCod⟩
    have hdomAtlas : dom ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ Circle := by
      apply dom.mem_maximalAtlas_of_contMDiffOn
      · change ContMDiffOn (𝓡 1) (𝓡 1) ⊤ c dom.source
        exact (contMDiffOn_of_mem_maximalAtlas hc).mono (by
          intro x hx
          change x ∈ c.source ∩ c ⁻¹' U at hx
          exact hx.1)
      · change ContMDiffOn (𝓡 1) (𝓡 1) ⊤ c.symm dom.target
        exact (contMDiffOn_symm_of_mem_maximalAtlas hc).mono (by
          intro u hu
          change u ∈ U ∩ c.target at hu
          exact hu.2)
    have hsource : dom.source ⊆ f ⁻¹' cod.source := by
      intro x hx
      change x ∈ c.source ∩ c ⁻¹' U at hx
      have htarg : L (c x, 0) ∈ cod.target := hx.2
      have h := cod.map_target htarg
      rw [hcodinv, hHaxis] at h
      change f (c.symm (c x)) ∈ cod.source at h
      rwa [c.left_inv hx.1] at h
    apply Manifold.IsImmersionAtOfComplement.mk_of_charts L dom cod
      hdomz hcodz hdomAtlas hcodAtlas hsource
    intro u hu
    have hut : u ∈ dom.target := by rw [dom.extend_target] at hu; exact hu.1
    change cod (f (dom.symm u)) = L (u, 0)
    change u ∈ U ∩ c.target at hut
    change cod (f (c.symm u)) = L (u, 0)
    calc
      cod (f (c.symm u)) = cod (H (L (u, 0))) := by rw [hHaxis]; rfl
      _ = L (u, 0) := by
        rw [← hcodinv]
        exact cod.right_inv hut.1
  change Manifold.IsImmersionOfComplement W (𝓡 1) 𝓘(ℝ, V) ⊤ f
  intro z
  let D : E →L[ℝ] V :=
    fderiv ℝ (f ∘ (chartAt E z).symm) (chartAt E z z)
  have hDinj : Function.Injective D := by
    have h := (hf z).mdifferentiableAt (by simp)
    have hd := h.mvfderiv
    simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ] at hd
    have hi := hdf z
    rw [hd] at hi
    exact hi
  let B : Submodule ℝ V := D.rangeᗮ
  have hrank : Module.finrank ℝ D.range = 1 := by
    rw [LinearMap.finrank_range_of_inj hDinj]
    exact finrank_euclideanSpace_fin
  have hdim := Submodule.finrank_add_finrank_orthogonal D.range
  have hWB : Module.finrank ℝ W = Module.finrank ℝ B := by
    simp only [W, finrank_euclideanSpace_fin, B]
    rw [hrank] at hdim
    omega
  let C : W ≃L[ℝ] B := ContinuousLinearEquiv.ofFinrankEq hWB
  have hker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hDinj
  let T : (E × B) ≃L[ℝ] V :=
    D.coprodSubtypeLEquivOfIsCompl D.range.isCompl_orthogonal hker
  let L : (E × W) ≃L[ℝ] V :=
    ((ContinuousLinearEquiv.refl ℝ E).prodCongr C).trans T
  apply hLocal z L
  intro u
  simp only [L, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply, map_zero]
  simpa [T, ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl] using (show D u = fderiv ℝ (f ∘ (chartAt E z).symm) (chartAt E z z) u from rfl)

end D5.S3.ConceptDynamics.ObservationTopology.CircleGraphCharts

end

/-! ## Phase kernels, frequency gcd, and Circle chords

Planar chord dot products and squared Circle chord norms have explicit
trigonometric formulas. For nonempty finite paired sensors with positive
frequencies and amplitudes, equal outputs correspond exactly to phase differences
in integer multiples of `2 * Real.pi / Finset.univ.gcd k`. Every nonempty family
of common delays preserves this kernel. A frequency gcd greater than one gives
distinct Circle states with equal outputs at every delay; the sensors distinguish
Circle states exactly when the frequency gcd is one.
-/

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.PairedDelayGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

def circleState (φ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  toLp 2 ![Real.cos φ, Real.sin φ]

def pairedSensor (k : ι → ℕ) (a : ι → ℝ) (φ : ℝ) :
    EuclideanSpace ℝ (ι × Fin 2) :=
  toLp 2 (fun p => a p.1 *
    if p.2 = 0 then Real.cos ((k p.1 : ℝ) * φ)
    else Real.sin ((k p.1 : ℝ) * φ))

theorem planar_chord_dot (u v t : ℝ) :
    (Real.cos u - Real.cos v) * (Real.cos (u - t) - Real.cos (v - t)) +
      (Real.sin u - Real.sin v) * (Real.sin (u - t) - Real.sin (v - t)) =
    4 * Real.sin ((u - v) / 2) ^ 2 * Real.cos t := by
  rw [Real.cos_sub_cos, Real.cos_sub_cos, Real.sin_sub_sin, Real.sin_sub_sin]
  have hd : ((u - t) - (v - t)) / 2 = (u - v) / 2 := by ring
  have hm : ((u - t) + (v - t)) / 2 = (u + v) / 2 - t := by ring
  rw [hd, hm, Real.sin_sub, Real.cos_sub]
  linear_combination
    (4 * Real.sin ((u - v) / 2) ^ 2 * Real.cos t) *
      (Real.sin_sq_add_cos_sq ((u + v) / 2))

theorem circle_chord_norm_sq (φ ψ : ℝ) :
    ‖circleState φ - circleState ψ‖ ^ 2 =
      4 * Real.sin ((φ - ψ) / 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa [circleState, Fin.sum_univ_two, pow_two] using planar_chord_dot φ ψ 0

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.PairedDelayGeometry

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.FinitePairedKernel

open PairedDelayGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

private theorem exp_eq_iff_coordinates (u v : ℝ) :
    Circle.exp u = Circle.exp v ↔
      Real.cos u = Real.cos v ∧ Real.sin u = Real.sin v := by
  constructor
  · intro h
    have hc := congrArg (fun z : Circle => (z : ℂ).re) h
    have hs := congrArg (fun z : Circle => (z : ℂ).im) h
    exact ⟨by simpa [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] using hc,
      by simpa [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] using hs⟩
  · rintro ⟨hc, hs⟩
    apply Circle.ext
    apply Complex.ext <;> simpa [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]

private theorem circle_state_eq_iff_exp (φ ψ : ℝ) :
    circleState φ = circleState ψ ↔ Circle.exp φ = Circle.exp ψ := by
  constructor
  · intro h
    apply (exp_eq_iff_coordinates φ ψ).mpr
    exact ⟨by simpa [circleState] using congrArg (fun x => x 0) h,
      by simpa [circleState] using congrArg (fun x => x 1) h⟩
  · intro h
    obtain ⟨hc, hs⟩ := (exp_eq_iff_coordinates φ ψ).mp h
    ext j
    fin_cases j <;> simp [circleState, hc, hs]

private theorem paired_eq_iff_powers (k : ι → ℕ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (φ ψ : ℝ) :
    pairedSensor k a φ = pairedSensor k a ψ ↔
      ∀ i, Circle.exp (φ - ψ) ^ k i = 1 := by
  constructor
  · intro h i
    have hc : Real.cos ((k i : ℝ) * φ) = Real.cos ((k i : ℝ) * ψ) := by
      apply mul_left_cancel₀ (ne_of_gt (ha i))
      simpa [pairedSensor] using congrArg (fun x => x (i, 0)) h
    have hs : Real.sin ((k i : ℝ) * φ) = Real.sin ((k i : ℝ) * ψ) := by
      apply mul_left_cancel₀ (ne_of_gt (ha i))
      simpa [pairedSensor] using congrArg (fun x => x (i, 1)) h
    have he := (exp_eq_iff_coordinates _ _).mpr ⟨hc, hs⟩
    have hd : (k i : ℝ) * (φ - ψ) = (k i : ℝ) * φ - (k i : ℝ) * ψ := by ring
    rw [← div_eq_one, ← Circle.exp_sub, ← hd, Circle.exp_natCast_mul] at he
    exact he
  · intro h
    have hcoords (i : ι) :
        Real.cos ((k i : ℝ) * φ) = Real.cos ((k i : ℝ) * ψ) ∧
        Real.sin ((k i : ℝ) * φ) = Real.sin ((k i : ℝ) * ψ) := by
      apply (exp_eq_iff_coordinates _ _).mp
      apply div_eq_one.mp
      rw [← Circle.exp_sub, ← mul_sub, Circle.exp_natCast_mul]
      exact h i
    ext p
    rcases p with ⟨i, j⟩
    fin_cases j <;> simp [pairedSensor, (hcoords i).1, (hcoords i).2]

private theorem powers_iff_finset_gcd (s : Finset ι) (k : ι → ℕ) (z : Circle) :
    (∀ i ∈ s, z ^ k i = 1) ↔ z ^ s.gcd k = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.gcd_insert]
    change (∀ j ∈ insert i s, z ^ k j = 1) ↔ z ^ Nat.gcd (k i) (s.gcd k) = 1
    rw [pow_gcd_eq_one, ← ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]

private theorem frequency_gcd_pos [Nonempty ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) : 0 < Finset.univ.gcd k := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hd : Finset.univ.gcd k ∣ k i := Finset.gcd_dvd (Finset.mem_univ i)
  by_contra h
  have hz : Finset.univ.gcd k = 0 := Nat.eq_zero_of_not_pos h
  rw [hz, zero_dvd_iff] at hd
  exact (ne_of_gt (hk i)) hd

theorem finite_paired_kernel [Nonempty ι] (k : ι → ℕ) (a : ι → ℝ)
    (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i) (φ ψ : ℝ) :
    pairedSensor k a φ = pairedSensor k a ψ ↔
      ∃ n : ℤ, φ - ψ = (2 * Real.pi / (↑(Finset.univ.gcd k : ℕ) : ℝ)) * n := by
  classical
  have hg : (↑(Finset.univ.gcd k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (frequency_gcd_pos k hk))
  rw [paired_eq_iff_powers k a ha φ ψ]
  have hfold := powers_iff_finset_gcd Finset.univ k (Circle.exp (φ - ψ))
  simp only [Finset.mem_univ, forall_const] at hfold
  rw [hfold, ← Circle.exp_natCast_mul, Circle.exp_eq_one]
  apply exists_congr
  intro n
  constructor <;> intro h
  · calc
      φ - ψ = ((n : ℝ) * (2 * Real.pi)) / (↑(Finset.univ.gcd k : ℕ) : ℝ) :=
        (eq_div_iff hg).mpr (by simpa [mul_comm] using h)
      _ = (2 * Real.pi / (↑(Finset.univ.gcd k : ℕ) : ℝ)) * n := by ring
  · calc
      (↑(Finset.univ.gcd k : ℕ) : ℝ) * (φ - ψ) =
          (↑(Finset.univ.gcd k : ℕ) : ℝ) * ((2 * Real.pi / (↑(Finset.univ.gcd k : ℕ) : ℝ)) * n) :=
        congrArg ((↑(Finset.univ.gcd k : ℕ) : ℝ) * ·) h
      _ = (n : ℝ) * (2 * Real.pi) := by field_simp

private theorem common_shift_kernel (k : ι → ℕ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (t φ ψ : ℝ) :
    pairedSensor k a (φ - t) = pairedSensor k a (ψ - t) ↔
      pairedSensor k a φ = pairedSensor k a ψ := by
  have hd : (φ - t) - (ψ - t) = φ - ψ := by ring
  rw [paired_eq_iff_powers k a ha (φ - t) (ψ - t), hd,
    paired_eq_iff_powers k a ha φ ψ]

theorem delay_family_kernel {J : Type*} [Nonempty J] (k : ι → ℕ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (t : J → ℝ) (φ ψ : ℝ) :
    (∀ j, pairedSensor k a (φ - t j) = pairedSensor k a (ψ - t j)) ↔
      pairedSensor k a φ = pairedSensor k a ψ := by
  constructor
  · intro h
    obtain ⟨j⟩ := ‹Nonempty J›
    exact (common_shift_kernel k a ha (t j) φ ψ).mp (h j)
  · intro h j
    exact (common_shift_kernel k a ha (t j) φ ψ).mpr h

theorem gcd_alias [Nonempty ι] (k : ι → ℕ) (a : ι → ℝ)
    (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i)
    (hg : 1 < Finset.univ.gcd k) :
    ∃ d : ℝ, 0 < d ∧ d < 2 * Real.pi ∧ circleState d ≠ circleState 0 ∧
      ∀ t : ℝ, pairedSensor k a (d - t) = pairedSensor k a (0 - t) := by
  classical
  let d := 2 * Real.pi / (↑(Finset.univ.gcd k : ℕ) : ℝ)
  have hgR : (1 : ℝ) < (↑(Finset.univ.gcd k : ℕ) : ℝ) := by exact_mod_cast hg
  have hd : 0 < d := div_pos (by positivity) (by linarith)
  have hdlt : d < 2 * Real.pi := by
    dsimp [d]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (↑(Finset.univ.gcd k : ℕ) : ℝ))).mpr
    have hm : 0 < (2 * Real.pi) * ((↑(Finset.univ.gcd k : ℕ) : ℝ) - 1) :=
      mul_pos (by positivity) (sub_pos.mpr hgR)
    nlinarith
  have hsep : circleState d ≠ circleState 0 := by
    intro h
    have hnorm := circle_chord_norm_sq d 0
    rw [h, sub_self, norm_zero, zero_pow (by norm_num)] at hnorm
    have hs : 0 < Real.sin (d / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    simp only [sub_zero] at hnorm
    nlinarith [sq_pos_of_pos hs]
  have heq : pairedSensor k a d = pairedSensor k a 0 := by
    apply (finite_paired_kernel k a hk ha d 0).mpr
    exact ⟨1, by simp [d]⟩
  have hall := (delay_family_kernel k a ha (fun t : ℝ => t) d 0).mpr heq
  exact ⟨d, hd, hdlt, hsep, hall⟩

theorem finite_paired_injective_iff_gcd_one [Nonempty ι] (k : ι → ℕ) (a : ι → ℝ)
    (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i) :
    (∀ φ ψ, pairedSensor k a φ = pairedSensor k a ψ → circleState φ = circleState ψ) ↔
      Finset.univ.gcd k = 1 := by
  classical
  constructor
  · intro hinj
    have hgpos := frequency_gcd_pos k hk
    by_contra hg
    have hgt : 1 < Finset.univ.gcd k := by omega
    obtain ⟨d, _, _, hsep, hall⟩ := gcd_alias k a hk ha hgt
    exact hsep (hinj d 0 (by simpa using hall 0))
  · intro hg φ ψ heq
    apply (circle_state_eq_iff_exp φ ψ).mpr
    have hfold := powers_iff_finset_gcd Finset.univ k (Circle.exp (φ - ψ))
    have he : Circle.exp (φ - ψ) = 1 := by
      simpa [hg] using hfold.mp (by
        simpa using (paired_eq_iff_powers k a ha φ ψ).mp heq)
    rw [Circle.exp_sub, div_eq_one] at he
    exact he

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.FinitePairedKernel

/-! ## Actual finite paired sensors on the intrinsic Circle

The map below has the original real Euclidean output, not a phase quotient.
All helper declarations are consumed by `finite_paired_intrinsic_circle`.
The CircleGraph theorem above supplies the actual fixed-complement normal form.
-/

namespace D5.S3.ConceptDynamics.ObservationTopology.CircleGraphCharts

open D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors
open PairedDelayGeometry FinitePairedKernel

noncomputable section

variable {ι : Type*} [Fintype ι]

private def ambientSensor (k : ι → ℕ) (a : ι → ℝ) (z : ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) :=
  toLp 2 (fun p => a p.1 *
    if p.2 = 0 then (z ^ k p.1).re else (z ^ k p.1).im)

/-- The original finite paired harmonics evaluated on the actual intrinsic Circle. -/
def intrinsicSensor (k : ι → ℕ) (a : ι → ℝ) (z : Circle) :
    EuclideanSpace ℝ (ι × Fin 2) := ambientSensor k a (z : ℂ)

private def stateOfCircle (z : Circle) : EuclideanSpace ℝ (Fin 2) :=
  toLp 2 ![(z : ℂ).re, (z : ℂ).im]

private theorem stateOfCircle_injective : Function.Injective stateOfCircle := by
  intro z w h
  apply Circle.ext
  apply Complex.ext
  · simpa [stateOfCircle] using congrArg (fun v => v 0) h
  · simpa [stateOfCircle] using congrArg (fun v => v 1) h

private theorem stateOfCircle_exp (φ : ℝ) :
    stateOfCircle (Circle.exp φ) = circleState φ := by
  ext j
  fin_cases j <;>
    simp [stateOfCircle, circleState, Circle.coe_exp, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem intrinsicSensor_exp (k : ι → ℕ) (a : ι → ℝ) (φ : ℝ) :
    intrinsicSensor k a (Circle.exp φ) = pairedSensor k a φ := by
  have hpow (i : ι) : ((Circle.exp φ : Circle) : ℂ) ^ k i =
      (Circle.exp ((k i : ℝ) * φ) : ℂ) := by
    rw [Circle.exp_natCast_mul, Circle.coe_pow]
  have hcoords (i : ι) :
      (((Circle.exp φ : Circle) : ℂ) ^ k i).re = Real.cos ((k i : ℝ) * φ) ∧
      (((Circle.exp φ : Circle) : ℂ) ^ k i).im = Real.sin ((k i : ℝ) * φ) := by
    rw [hpow, Circle.coe_exp]
    exact ⟨Complex.exp_ofReal_mul_I_re ((k i : ℝ) * φ),
      Complex.exp_ofReal_mul_I_im ((k i : ℝ) * φ)⟩
  ext p
  rcases p with ⟨i, j⟩
  fin_cases j
  · change a i * (((Circle.exp φ : Circle) : ℂ) ^ k i).re =
      a i * Real.cos ((k i : ℝ) * φ)
    exact congrArg (fun x : ℝ => a i * x) (hcoords i).1
  · change a i * (((Circle.exp φ : Circle) : ℂ) ^ k i).im =
      a i * Real.sin ((k i : ℝ) * φ)
    exact congrArg (fun x : ℝ => a i * x) (hcoords i).2

private theorem ambientSensor_contDiff (k : ι → ℕ) (a : ι → ℝ) :
    ContDiff ℝ ⊤ (ambientSensor k a) := by
  apply (contDiff_piLp 2).mpr
  rintro ⟨i, j⟩
  fin_cases j
  · simpa [ambientSensor] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℂ => a i)).mul
        (Complex.reCLM.contDiff.comp (contDiff_id.pow (k i)))
  · simpa [ambientSensor] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℂ => a i)).mul
        (Complex.imCLM.contDiff.comp (contDiff_id.pow (k i)))

private theorem intrinsicSensor_contMDiff (k : ι → ℕ) (a : ι → ℝ) :
    ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (ι × Fin 2)) ⊤
      (intrinsicSensor k a) := by
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  exact (ambientSensor_contDiff k a).contMDiff.comp contMDiff_coe_sphere

/-- A single positive harmonic detects every ambient infinitesimal displacement
away from the origin. The pair of real coordinates is essential here. -/
private theorem ambientSensor_fderiv_injective [Nonempty ι]
    (k : ι → ℕ) (a : ι → ℝ) (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i)
    (z : ℂ) (hz : z ≠ 0) :
    Function.Injective (fderiv ℝ (ambientSensor k a) z) := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  let Q : EuclideanSpace ℝ (ι × Fin 2) → ℂ :=
    fun v => (v (i, 0) : ℂ) + (v (i, 1) : ℂ) * Complex.I
  have hQ : ContDiff ℝ ⊤ Q := by
    have hcoord (j : Fin 2) :
        ContDiff ℝ ⊤ (fun v : EuclideanSpace ℝ (ι × Fin 2) => (v (i, j) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        ((contDiff_apply ℝ ℝ (i, j)).comp PiLp.contDiff_ofLp)
    exact (hcoord 0).add ((hcoord 1).mul contDiff_const)
  have hQP : Q ∘ ambientSensor k a = fun w : ℂ => (a i : ℂ) * w ^ k i := by
    funext w
    apply Complex.ext <;> simp [Q, ambientSensor, Complex.mul_re, Complex.mul_im]
  let c : ℂ := (a i : ℂ) * ((k i : ℂ) * z ^ (k i - 1))
  have hc : c ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (ha i).ne'
    · exact mul_ne_zero (by exact_mod_cast (hk i).ne') (pow_ne_zero _ hz)
  have hd : HasDerivAt (fun w : ℂ => (a i : ℂ) * w ^ k i) c z :=
    (hasDerivAt_pow (k i) z).const_mul (a i : ℂ)
  have hscalar (v : ℂ) :
      fderiv ℝ (fun w : ℂ => (a i : ℂ) * w ^ k i) z v = v * c := by
    rw [(hd.hasFDerivAt.restrictScalars ℝ).fderiv]
    change v • c = v * c
    rfl
  have hchain := fderiv_comp z
    (hQ.differentiable (by simp) (ambientSensor k a z))
    ((ambientSensor_contDiff k a).differentiable (by simp) z)
  rw [hQP] at hchain
  intro u v huv
  apply mul_right_cancel₀ hc
  rw [← hscalar u, ← hscalar v, hchain]
  exact congrArg (fderiv ℝ Q (ambientSensor k a z)) huv

private theorem intrinsicSensor_mvfderiv_injective [Nonempty ι]
    (k : ι → ℕ) (a : ι → ℝ) (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i)
    (z : Circle) : Function.Injective (mvfderiv (𝓡 1) (intrinsicSensor k a) z) := by
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  let c : OpenPartialHomeomorph Circle (EuclideanSpace ℝ (Fin 1)) :=
    chartAt (EuclideanSpace ℝ (Fin 1)) z
  let q : EuclideanSpace ℝ (Fin 1) := c z
  let g : EuclideanSpace ℝ (Fin 1) → ℂ := fun u => (c.symm u : ℂ)
  have hcz : z ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin 1)) z
  have hq : q ∈ c.target := c.map_source hcz
  have hc : c ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ Circle :=
    IsManifold.chart_mem_maximalAtlas z
  have hco : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ⊤ (fun w : Circle => (w : ℂ)) :=
    contMDiff_coe_sphere
  have hg : ContDiffAt ℝ ⊤ g q :=
    ((hco (c.symm q)).comp q
      (contMDiffAt_symm_of_mem_maximalAtlas hc hq)).contDiffAt
  have hgz : g q = (z : ℂ) := congrArg (fun w : Circle => (w : ℂ)) (c.left_inv hcz)
  have hi : Function.Injective (fderiv ℝ g q) := by
    have hinj := injective_mvfderiv_subtypeVal_sphere (E := ℂ) (n := 1) z
    rw [((contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ⊤) z).mdifferentiableAt
      (by simp)).mvfderiv] at hinj
    simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ] at hinj
    rw [chartAt_self_eq (H := ℂ)] at hinj
    change Function.Injective (fderiv ℝ g q) at hinj
    exact hinj
  have h := ((intrinsicSensor_contMDiff k a) z).mdifferentiableAt (by simp)
  have hd := h.mvfderiv
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ] at hd
  rw [hd]
  change Function.Injective (fderiv ℝ (ambientSensor k a ∘ g) q)
  rw [fderiv_comp q ((ambientSensor_contDiff k a).differentiable (by simp) (g q))
    (hg.differentiableAt (by simp))]
  have hout : Function.Injective (fderiv ℝ (ambientSensor k a) (g q)) := by
    rw [hgz]
    exact ambientSensor_fderiv_injective k a hk ha (z : ℂ) z.coe_ne_zero
  exact hout.comp hi

private theorem intrinsicSensor_injective_iff [Nonempty ι]
    (k : ι → ℕ) (a : ι → ℝ) (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i) :
    Function.Injective (intrinsicSensor k a) ↔ Finset.univ.gcd k = 1 := by
  rw [← finite_paired_injective_iff_gcd_one k a hk ha]
  constructor
  · intro h φ ψ he
    have hz : Circle.exp φ = Circle.exp ψ := h (by
      simpa only [intrinsicSensor_exp] using he)
    simpa only [stateOfCircle_exp] using congrArg stateOfCircle hz
  · intro h z w he
    obtain ⟨φ, rfl⟩ := Circle.exp_surjective z
    obtain ⟨ψ, rfl⟩ := Circle.exp_surjective w
    apply stateOfCircle_injective
    simpa only [stateOfCircle_exp] using
      h φ ψ (by simpa only [intrinsicSensor_exp] using he)

/-- Every positive nonempty finite paired family is an analytic immersion of the
intrinsic Circle. Its actual map is an embedding, equivalently gives a
homeomorphism onto its range, exactly when the full frequency gcd is one.
No distinctness assumption is needed; the original distinct family is included.
The displayed complement is fixed over the whole Circle. -/
theorem finite_paired_intrinsic_circle [Nonempty ι]
    (k : ι → ℕ) (a : ι → ℝ) (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i) :
    (∀ φ : ℝ, intrinsicSensor k a (Circle.exp φ) = pairedSensor k a φ) ∧
    ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (ι × Fin 2)) ⊤
      (intrinsicSensor k a) ∧
    (∀ z, Function.Injective (mvfderiv (𝓡 1) (intrinsicSensor k a) z)) ∧
    Manifold.IsImmersionOfComplement
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (ι × Fin 2)) - 1)))
      (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (ι × Fin 2)) ⊤ (intrinsicSensor k a) ∧
    (Topology.IsEmbedding (intrinsicSensor k a) ↔ Finset.univ.gcd k = 1) ∧
    ((∃ e : Circle ≃ₜ Set.range (intrinsicSensor k a),
      ∀ z, (e z : EuclideanSpace ℝ (ι × Fin 2)) = intrinsicSensor k a z) ↔
      Finset.univ.gcd k = 1) := by
  classical
  have hs := intrinsicSensor_contMDiff k a
  have hd := intrinsicSensor_mvfderiv_injective k a hk ha
  have he : Topology.IsEmbedding (intrinsicSensor k a) ↔ Finset.univ.gcd k = 1 := by
    constructor
    · intro h
      exact (intrinsicSensor_injective_iff k a hk ha).mp h.injective
    · intro h
      exact (hs.continuous.isClosedEmbedding
        ((intrinsicSensor_injective_iff k a hk ha).mpr h)).isEmbedding
  refine ⟨intrinsicSensor_exp k a, hs, hd,
    isImmersionOfComplement_of_contMDiff_injective_mvfderiv _ hs hd, he, ?_⟩
  constructor
  · rintro ⟨e, heq⟩
    apply (intrinsicSensor_injective_iff k a hk ha).mp
    intro z w hzw
    apply e.injective
    apply Subtype.ext
    simpa only [heq] using hzw
  · intro hg
    exact ⟨(he.mpr hg).toHomeomorph, fun _ => rfl⟩

end
end D5.S3.ConceptDynamics.ObservationTopology.CircleGraphCharts

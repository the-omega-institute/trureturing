/- GID: D5/S3/Geometry/ProbabilityTransport/SmoothDensityWeakTransport
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/SmoothDensityWeakTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual smooth periodic density and characteristic transport -/
import D5.S3.Geometry.ProbabilityTransport.PeriodicDensityCalculus

/-!
# SmoothDensityWeakTransport

Actual smooth periodic density transport on the closed time slab.
-/

set_option maxHeartbeats 2000000


noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SmoothDensityTransport

local instance (d : ℕ) : IsProbabilityMeasure (haar d) := by
  unfold haar
  infer_instance

/-- Compact-cell parameter integration with the exact product Haar of the root.
This consumed helper applies the accepted convex integral supplier. -/
theorem haar_integral_C1On {d : ℕ} {T : ℝ} {F : ℝ → Torus d → ℝ}
    (hT : 0 < T)
    (hF : ContDiffOn ℝ 1 (fun p : ℝ × Euclid d => F p.1 (quotient d p.2))
      (Icc 0 T ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun t => ∫ x, F t x ∂haar d) (Icc 0 T) := by
  let P := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let C : ℝ × (Fin d → ℝ) → ℝ := fun p => F p.1 (quotient d (P p.2))
  have hM : ContDiff ℝ 1 (fun p : ℝ × (Fin d → ℝ) => (p.1, P p.2)) :=
    contDiff_fst.prodMk (P.contDiff.comp contDiff_snd)
  have hC : ContDiffOn ℝ 1 C (Icc 0 T ×ˢ univ) :=
    hF.comp hM.contDiffOn (fun p hp => ⟨hp.1, mem_univ _⟩)
  have H := (convex_Icc 0 T).contDiffOn_integral_smul_of_contDiffOn
    (μ := cellMeasure d) (g := fun _ : closedCell d => (1 : ℝ))
    (ι := fun z : closedCell d => z.1) (F := C) (n := (1 : ℕ∞))
    (integrable_const 1) continuous_subtype_val (uniqueDiffOn_Icc hT)
    ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ)
    (hC.of_le (by norm_num)) (fun s hs z => ⟨hs, mem_univ z.1⟩)
  apply H.congr
  intro s hs
  simp only [one_smul]
  rw [haar_integral_closedCell]
  rfl

/-- Differentiate a Haar integral from closed-slab C1 regularity and an actual
pointwise time derivative. No discontinuous representative is differentiated. -/
private theorem haar_integral_hasDerivAt {d : ℕ} {T t : ℝ}
    {F : ℝ → Torus d → ℝ} {g : Torus d → ℝ}
    (hF : ContDiffOn ℝ 1 (fun p : ℝ × Euclid d => F p.1 (quotient d p.2))
      (Icc 0 T ×ˢ univ)) (ht : t ∈ Ioo 0 T)
    (hg : ∀ x, HasDerivAt (fun s => F s x) (g x) t) :
    HasDerivAt (fun s => ∫ x, F s x ∂haar d) (∫ x, g x ∂haar d) t := by
  have hT : 0 < T := ht.1.trans ht.2
  have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  let P := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let C : ℝ × (Fin d → ℝ) → ℝ := fun p => F p.1 (quotient d (P p.2))
  let W : Set (ℝ × (Fin d → ℝ)) := Icc 0 T ×ˢ univ
  have hM : ContDiff ℝ 1 (fun p : ℝ × (Fin d → ℝ) => (p.1, P p.2)) :=
    contDiff_fst.prodMk (P.contDiff.comp contDiff_snd)
  have hC : ContDiffOn ℝ 1 C W :=
    hF.comp hM.contDiffOn (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hW : UniqueDiffOn ℝ W := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hu : UniqueDiffWithinAt ℝ (Icc 0 T) t := (uniqueDiffOn_Icc hT) t htc
  let D : (ℝ × (Fin d → ℝ)) → (ℝ →L[ℝ] ℝ) := fun p =>
    (fderivWithin ℝ C W p).comp (ContinuousLinearMap.inl ℝ ℝ (Fin d → ℝ))
  have hD : ContinuousOn D W :=
    (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.inl ℝ ℝ (Fin d → ℝ))).continuous.comp_continuousOn
      (hC.continuousOn_fderivWithin hW (by norm_num))
  have hpart (z : closedCell d) : HasFDerivWithinAt
      (fun s => C (s, z.1)) (D (t, z.1)) (Icc 0 T) t := by
    have hjoint : HasFDerivWithinAt C (fderivWithin ℝ C W (t, z.1)) W (t, z.1) :=
      (hC.differentiableOn (by norm_num) (t, z.1) ⟨htc, mem_univ z.1⟩).hasFDerivWithinAt
    exact hjoint.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t z.1).hasFDerivWithinAt
      (s := Icc 0 T) (t := W) (fun s hs => ⟨hs, mem_univ z.1⟩)
  have hDc : Continuous (fun z : closedCell d => D (t, z.1)) :=
    hD.comp_continuous (f := fun z : closedCell d => (t, z.1))
      (continuous_const.prodMk continuous_subtype_val)
      (fun z => show (t, z.1) ∈ W from ⟨htc, mem_univ z.1⟩)
  have hDi : Integrable (fun z : closedCell d => D (t, z.1)) (cellMeasure d) := by
    simpa only [integrableOn_univ] using
      hDc.continuousOn.integrableOn_compact (K := univ) isCompact_univ
  have hslice : (fun z : closedCell d =>
      fderivWithin ℝ (fun s => C (s, z.1)) (Icc 0 T) t) =
        fun z : closedCell d => D (t, z.1) :=
    funext (fun z => (hpart z).fderivWithin hu)
  have hvalue (z : closedCell d) : D (t, z.1) 1 = g (quotient d (P z.1)) :=
    ((hpart z).hasDerivWithinAt.derivWithin hu).symm.trans
      ((hg (quotient d (P z.1))).hasDerivWithinAt.derivWithin hu)
  have heval : (∫ z : closedCell d,
      fderivWithin ℝ (fun s => C (s, z.1)) (Icc 0 T) t ∂cellMeasure d) 1 =
        ∫ x, g x ∂haar d := by
    rw [hslice, ContinuousLinearMap.integral_apply hDi]
    simp_rw [hvalue]
    rw [haar_integral_closedCell]
    rfl
  have H : HasFDerivWithinAt
      (fun s => ∫ z : closedCell d, C (s, z.1) ∂cellMeasure d)
      (∫ z : closedCell d,
        fderivWithin ℝ (fun s => C (s, z.1)) (Icc 0 T) t ∂cellMeasure d)
      (Icc 0 T) t := by
    simpa only [one_smul] using
      (convex_Icc 0 T).hasFDerivWithinAt_integral_smul_of_contDiffOn
        (μ := cellMeasure d) (g := fun _ : closedCell d => (1 : ℝ))
        (ι := fun z : closedCell d => z.1) (F := C)
        (integrable_const 1) continuous_subtype_val hW hC
        (fun s hs z => ⟨hs, mem_univ z.1⟩) htc hu
  have H' := H.hasDerivWithinAt
  rw [heval] at H'
  have HF := H'.congr_of_mem (f₁ := fun s => ∫ x, F s x ∂haar d)
    (fun s hs => by rw [haar_integral_closedCell]; rfl) htc
  exact HF.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Continuity of the root's actual divergence; coordinates are scalar
gradients, so the existing C1 gradient descent supplies the proof. -/
private theorem continuous_divergence_of_C1_lift {d : ℕ} {V : Torus d → Euclid d}
    (hV : ContDiff ℝ 1 (fun a : Euclid d => V (quotient d a))) :
    Continuous (divergence V) := by
  have hVi (i : Fin d) : ContDiff ℝ 1 (fun a : Euclid d => V (quotient d a) i) :=
    contDiff_pi.mp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff.comp hV) i
  have hsum : divergence V = fun x => ∑ i : Fin d, gradient (fun y => V y i) x i := by
    funext x
    simp [divergence, gradient, liftedGradient]
  rw [hsum]
  exact continuous_finsetSum _ (fun i _ =>
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp (continuous_gradient_C1 (hVi i)))

/-- The accepted flux identity and Haar IBP imply the exact weak spatial
transport identity for the original velocity. This is not an assumed PDE. -/
private theorem fpRHS_test_integral {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (φ : Torus d → ℝ)
    (hφ : ContDiff ℝ 1 (fun a : Euclid d => φ (quotient d a))) :
    (∫ x, φ x * fpRHS U τ ρ t x ∂haar d) =
      ∫ x, ρ t x * inner ℝ (gradient φ x) (velocity U τ ρ t x) ∂haar d := by
  have hμ := chemicalPotential_smooth h ht
  have hV : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d =>
      ρ t (quotient d a) • gradient (chemicalPotential U τ ρ t) (quotient d a)) :=
    (h.spatial_smooth t ht).smul (smooth_gradient_lift hμ)
  have H := periodic_haar_ibp φ
    (fun x => ρ t x • gradient (chemicalPotential U τ ρ t) x) hφ (hV.of_le (by simp))
  simp_rw [flux_divergence h ht] at H
  rw [H, ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp [velocity, real_inner_smul_right])

/-- Moving-test weak continuity equation, derived from the ORIGINAL SmoothFP
PDE. The only additional data are a C1 test and its time derivative at t. -/
theorem weak_transport_hasDerivAt {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ)
    {φ : ℝ → Torus d → ℝ} {φdot : Torus d → ℝ}
    (hφ : ContDiffOn ℝ 1 (fun p : ℝ × Euclid d => φ p.1 (quotient d p.2))
      (Icc 0 T ×ˢ univ)) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hφdot : Continuous φdot)
    (hdt : ∀ x, HasDerivAt (fun s => φ s x) (φdot x) t) :
    HasDerivAt (fun s => ∫ x, φ s x * ρ s x ∂haar d)
      (∫ x, ρ t x * (φdot x +
        inner ℝ (gradient (φ t) x) (velocity U τ ρ t x)) ∂haar d) t := by
  have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  have hφs : ContDiff ℝ 1 (fun a : Euclid d => φ t (quotient d a)) := by
    apply contDiffOn_univ.mp
    exact hφ.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun a _ => ⟨htc, mem_univ a⟩)
  have hφc : Continuous (φ t) := continuous_of_lift hφs.continuous
  have hρc : Continuous (ρ t) := continuous_of_lift (h.spatial_smooth t htc).continuous
  have hμ := chemicalPotential_smooth h htc
  have hvc : Continuous (velocity U τ ρ t) := (continuous_gradient hμ).neg
  have hV : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d =>
      ρ t (quotient d a) • gradient (chemicalPotential U τ ρ t) (quotient d a)) :=
    (h.spatial_smooth t htc).smul (smooth_gradient_lift hμ)
  have hfc : Continuous (fpRHS U τ ρ t) :=
    (continuous_divergence_of_C1_lift (hV.of_le (by simp))).congr
      (fun x => flux_divergence h htc x)
  have hic : Continuous (fun x => inner ℝ (gradient (φ t) x) (velocity U τ ρ t x)) :=
    (continuous_gradient_C1 hφs).inner hvc
  have hA : Integrable (fun x => φdot x * ρ t x) (haar d) :=
    compact_integrable (hφdot.mul hρc)
  have hB : Integrable (fun x => φ t x * fpRHS U τ ρ t x) (haar d) :=
    compact_integrable (hφc.mul hfc)
  have hC : Integrable (fun x => ρ t x * φdot x) (haar d) :=
    compact_integrable (hρc.mul hφdot)
  have hD : Integrable (fun x =>
      ρ t x * inner ℝ (gradient (φ t) x) (velocity U τ ρ t x)) (haar d) :=
    compact_integrable (hρc.mul hic)
  have HF : ContDiffOn ℝ 1
      (fun p : ℝ × Euclid d => φ p.1 (quotient d p.2) * ρ p.1 (quotient d p.2))
      (Icc 0 T ×ˢ univ) := hφ.mul (h.density_smooth.of_le (by simp))
  have H := haar_integral_hasDerivAt HF ht
    (fun x => (hdt x).mul (h.pde t ht x))
  have heq : (∫ x, φdot x * ρ t x + φ t x * fpRHS U τ ρ t x ∂haar d) =
      ∫ x, ρ t x * (φdot x +
        inner ℝ (gradient (φ t) x) (velocity U τ ρ t x)) ∂haar d := by
    rw [integral_add hA hB, fpRHS_test_integral h htc (φ t) hφs]
    calc
      (∫ x, φdot x * ρ t x ∂haar d) +
          (∫ x, ρ t x * inner ℝ (gradient (φ t) x) (velocity U τ ρ t x) ∂haar d)
          = (∫ x, ρ t x * φdot x ∂haar d) +
            (∫ x, ρ t x * inner ℝ (gradient (φ t) x) (velocity U τ ρ t x) ∂haar d) := by
              congr 1
              exact integral_congr_ae (ae_of_all _ (fun x => mul_comm _ _))
      _ = ∫ x, ρ t x * φdot x +
          ρ t x * inner ℝ (gradient (φ t) x) (velocity U τ ρ t x) ∂haar d :=
        (integral_add hC hD).symm
      _ = _ := integral_congr_ae (ae_of_all _ (fun x => (mul_add _ _ _).symm))
  change HasDerivAt (fun s => ∫ x, φ s x * ρ s x ∂haar d)
    (∫ x, φdot x * ρ t x + φ t x * fpRHS U τ ρ t x ∂haar d) t at H
  rw [heq] at H
  exact H

/-- Direct application to the actual withDensity law. This consumed helper
uses the pinned Bochner withDensity identity, including its finiteness premise. -/
theorem densityMeasure_test_integral {d : ℕ} {r : Torus d → ℝ}
    (hr : Continuous r) (hp : ∀ x, 0 ≤ r x) (f : Torus d → ℝ) :
    (∫ x, f x ∂densityMeasure r) = ∫ x, f x * r x ∂haar d := by
  unfold densityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hr.measurable.ennreal_ofReal
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change (ENNReal.ofReal (r x)).toReal • f x = f x * r x
    rw [ENNReal.toReal_ofReal (hp x), smul_eq_mul, mul_comm])

end SmoothDensityTransport



noncomputable section
open Set MeasureTheory
namespace SmoothDensityTransport

private theorem eulerBackwardTest_materialDerivative {d : ℕ}
    (b : ℝ → Euclid d → Euclid d) (g : Euclid d → ℝ)
    (u v s : ℝ) (x : Euclid d)
    (hb : ContDiff ℝ 1 (b u)) (hg : ContDiff ℝ 1 g) :
    fderiv ℝ
      (fun p : ℝ × Euclid d => g (p.2 + (v - p.1) • b u p.2))
      (s, x) (1, b s x) =
    fderiv ℝ g (x + (v - s) • b u x)
      (b s x - b u x + (v - s) • (fderiv ℝ (b u) x (b s x))) := by
  have hbu := ((hb.differentiable (by norm_num) x).hasFDerivAt.comp
    (s, x) (hasFDerivAt_snd (𝕜 := ℝ) (p := (s, x))))
  have ht := (hasFDerivAt_const v (s, x)).sub
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (s, x)))
  have hi := (hasFDerivAt_snd (𝕜 := ℝ) (p := (s, x))).add (ht.smul hbu)
  have H := ((hg.differentiable (by norm_num)
    (x + (v - s) • b u x)).hasFDerivAt.comp (s, x) hi)
  change HasFDerivAt
    (fun p : ℝ × Euclid d => g (p.2 + (v - p.1) • b u p.2)) _ (s, x) at H
  rw [H.fderiv]
  change fderiv ℝ g (x + (v - s) • b u x)
    (b s x + ((v - s) • (fderiv ℝ (b u) x (b s x)) +
      (0 - (1 : ℝ)) • b u x)) = _
  congr 1
  simp only [zero_sub, neg_smul, one_smul]
  abel

/-- One-cell residual bound, using only first derivatives. The actual density
integral consumes this estimate after discharging its hypotheses from the
original smooth slab. -/
theorem eulerBackwardTest_residual_bound {d : ℕ}
    (b : ℝ → Euclid d → Euclid d) (g : Euclid d → ℝ)
    (u v s δ A K L B : ℝ) (x : Euclid d)
    (hb : ContDiff ℝ 1 (b u)) (hg : ContDiff ℝ 1 g)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hs : 0 ≤ v - s) (hδ : v - s ≤ δ)
    (hgt : ‖fderiv ℝ g (x + (v - s) • b u x)‖ ≤ A)
    (hbt : ‖b s x - b u x‖ ≤ K * δ)
    (hbx : ‖fderiv ℝ (b u) x‖ ≤ L) (hbv : ‖b s x‖ ≤ B) :
    |fderiv ℝ
      (fun p : ℝ × Euclid d => g (p.2 + (v - p.1) • b u p.2))
      (s, x) (1, b s x)| ≤ A * (K + L * B) * δ := by
  rw [eulerBackwardTest_materialDerivative b g u v s x hb hg, ← Real.norm_eq_abs]
  have hDb : ‖fderiv ℝ (b u) x (b s x)‖ ≤ L * B :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hbx hbv (norm_nonneg _) hL)
  have hr : ‖b s x - b u x + (v - s) • (fderiv ℝ (b u) x (b s x))‖ ≤
      (K + L * B) * δ := by
    calc
      _ ≤ ‖b s x - b u x‖ + ‖(v - s) • (fderiv ℝ (b u) x (b s x))‖ := norm_add_le _ _
      _ = ‖b s x - b u x‖ + (v - s) * ‖fderiv ℝ (b u) x (b s x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
      _ ≤ K * δ + δ * (L * B) := by
        exact add_le_add hbt (mul_le_mul hδ hDb (norm_nonneg _) (hs.trans hδ))
      _ = _ := by ring
  calc
    _ ≤ ‖fderiv ℝ g (x + (v - s) • b u x)‖ *
        ‖b s x - b u x + (v - s) • (fderiv ℝ (b u) x (b s x))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ A * ((K + L * B) * δ) := mul_le_mul hgt hr (norm_nonneg _) hA
    _ = _ := by ring

end SmoothDensityTransport

namespace SmoothDensityTransport
open Finset Real
/-- Finite-grid Grönwall. Beyond the terminal index the error stays constant,
while both coefficients are zero. This avoids assuming estimates off-grid. -/
theorem finiteGrid_gronwall (N : ℕ) (e : ℕ → ℝ) (a b : ℝ)
    (he0 : 0 ≤ e 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : ∀ n < N, e (n + 1) ≤ (1 + a) * e n + b) :
    e N ≤ (e 0 + (N : ℝ) * b) * Real.exp ((N : ℝ) * a) := by
  let u : ℕ → ℝ := fun n => e (min n N)
  let c : ℕ → ℝ := fun n => if n < N then a else 0
  let z : ℕ → ℝ := fun n => if n < N then b else 0
  have hu : ∀ n ≥ 0, u (n + 1) ≤ (1 + c n) * u n + z n := by
    intro n _
    by_cases hn : n < N
    · simpa [u, c, z, hn, Nat.min_eq_left (Nat.le_of_lt hn),
        Nat.min_eq_left (Nat.succ_le_of_lt hn)] using he n hn
    · have hN : N ≤ n := Nat.le_of_not_gt hn
      simp [u, c, z, hn, Nat.min_eq_right hN,
        Nat.min_eq_right (hN.trans (Nat.le_succ n))]
  have hc : ∀ n ≥ 0, 0 ≤ c n := by intro n _;dsimp [c];split_ifs <;> positivity
  have hz : ∀ n ≥ 0, 0 ≤ z n := by intro n _;dsimp [z];split_ifs <;> positivity
  have H := discrete_gronwall (u := u) (c := c) (b := z)
    (n₀ := 0) (by simpa [u] using he0) hu hc hz (n := N) (Nat.zero_le N)
  have hcSum : ∑ i ∈ Ico 0 N, c i = (N : ℝ) * a := by
    calc
      _ = ∑ i ∈ Ico 0 N, a := by
        apply sum_congr rfl
        intro i hi
        simp [c, (mem_Ico.mp hi).2]
      _ = _ := by simp
  have hzSum : ∑ i ∈ Ico 0 N, z i = (N : ℝ) * b := by
    calc
      _ = ∑ i ∈ Ico 0 N, b := by
        apply sum_congr rfl
        intro i hi
        simp [z, (mem_Ico.mp hi).2]
      _ = _ := by simp
  rw [hcSum, hzSum] at H
  simpa [u] using H

end SmoothDensityTransport

namespace SmoothDensityTransport
/-- Exact moment equality from a uniform C/N bound. The coefficient is fixed
before N varies; it cannot hide an N-dependent test or error constant. -/
theorem moment_eq_of_uniform_inverse_nat_bound (a b M : ℝ)
    (h : ∀ N : ℕ, 1 ≤ N → |a - b| ≤ M / (N : ℝ)) : a = b := by
  by_contra hab
  have hp : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (M / |a - b|))
  have hNp : 0 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNn : 1 ≤ N := by exact_mod_cast hNp
  have H := (le_div_iff₀ hNp).mp (h N hNn)
  have H' := (div_lt_iff₀ hp).mp ((le_max_right _ _).trans_lt hN)
  nlinarith

end SmoothDensityTransport

namespace SmoothDensityTransport
/-- The explicit Euler C(T)/N rate from a finite-grid local error recurrence.
This retained finite-grid helper is consumed by
`actual_characteristic_euler_grid_error`, which supplies the actual
characteristic/Euler recurrence hypotheses. -/
theorem finiteGrid_euler_error_bound (N : ℕ) (hN : 1 ≤ N)
    (r L D : ℝ) (hr : 0 ≤ r) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (e : ℕ → ℝ) (he0 : e 0 = 0)
    (he : ∀ n < N,
      e (n + 1) ≤ (1 + L * (r / (N : ℝ))) * e n + D * (r / (N : ℝ)) ^ 2) :
    e N ≤ Real.exp (L * r) * D * r ^ 2 / (N : ℝ) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have H := finiteGrid_gronwall N e (L * (r / (N : ℝ)))
    (D * (r / (N : ℝ)) ^ 2) (by simp [he0])
    (mul_nonneg hL (div_nonneg hr hNp.le))
    (mul_nonneg hD (sq_nonneg _)) he
  have harg : (N : ℝ) * (L * (r / (N : ℝ))) = L * r := by
    field_simp [ne_of_gt hNp]
  rw [he0, zero_add, harg] at H
  convert H using 1 <;> field_simp [ne_of_gt hNp] <;> ring

end SmoothDensityTransport

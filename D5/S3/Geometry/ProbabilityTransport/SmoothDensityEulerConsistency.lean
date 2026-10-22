/- GID: D5/S3/Geometry/ProbabilityTransport/SmoothDensityEulerConsistency
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/SmoothDensityEulerConsistency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual smooth periodic density and characteristic transport -/
import D5.S3.Geometry.ProbabilityTransport.SmoothDensityWeakTransport
import D5.S3.Geometry.ProbabilityTransport.SmoothDensityCharacteristics

/-!
# SmoothDensityEulerConsistency

Actual smooth periodic density transport on the closed time slab.
-/

set_option maxHeartbeats 2000000

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SmoothDensityTransport

/-- Derivatives of a globally C1 joint lift agree along spatial quotient fibres.
The fundamental-domain representative is never differentiated. -/
private theorem joint_fderiv_fibre {d : ℕ} (φ : ℝ → Torus d → ℝ)
    (t : ℝ) {a b : Euclid d} (hab : quotient d a = quotient d b) :
    fderiv ℝ (fun p : ℝ × Euclid d => φ p.1 (quotient d p.2)) (t,a) =
      fderiv ℝ (fun p : ℝ × Euclid d => φ p.1 (quotient d p.2)) (t,b) := by
  let F : ℝ × Euclid d → ℝ := fun p => φ p.1 (quotient d p.2)
  have hshift : (fun p => F (p + (0,b-a))) = F := by
    funext p
    simp [F, quotient_add, quotient_sub, hab]
  have H := congrArg (fun G : ℝ × Euclid d → ℝ => fderiv ℝ G (t,a)) hshift
  rw [fderiv_comp_add_right] at H
  have hp : (t,a) + (0,b-a) = (t,b) := by ext <;> simp <;> abel
  rw [hp] at H
  exact H.symm

/-- Exact duality with the representative-defined gradient in all dimensions,
including the empty coordinate type. -/
private theorem gradient_inner_eq_fderiv {d : ℕ} (f : Torus d → ℝ)
    (a v : Euclid d) :
    inner ℝ (liftedGradient f a) v =
      fderiv ℝ (fun z : Euclid d => f (quotient d z)) a v := by
  classical
  have hv : (∑ i : Fin d, v i • basisVector d i) = v := by
    simpa [basisVector, EuclideanSpace.basisFun_apply, EuclideanSpace.single] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  conv_rhs => rw [← hv]
  simp [liftedGradient, PiLp.inner_apply, map_sum, mul_comm]

/-- The PDE derivative is the integral of the actual material derivative for
any globally C1 periodic moving test. This is used by the Euler cell below. -/
private theorem density_pairing_material_derivative {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) {φ : ℝ → Torus d → ℝ}
    (hφ : ContDiff ℝ 1 (fun p : ℝ × Euclid d => φ p.1 (quotient d p.2)))
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => ∫ x, φ s x * ρ s x ∂haar d)
      (∫ x, ρ t x *
        fderiv ℝ (fun p : ℝ × Euclid d => φ p.1 (quotient d p.2))
          (t,representative d x) (1,velocity U τ ρ t x) ∂haar d) t := by
  let F : ℝ × Euclid d → ℝ := fun p => φ p.1 (quotient d p.2)
  let D : Torus d → ℝ := fun x => fderiv ℝ F (t,representative d x) (1,0)
  have hDq (a : Euclid d) : D (quotient d a) = fderiv ℝ F (t,a) (1,0) := by
    dsimp [D]
    rw [joint_fderiv_fibre φ t (quotient_representative d (quotient d a))]
  have hDc : Continuous D := by
    apply continuous_of_lift
    simp_rw [hDq]
    exact ((hφ.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have hdt (x : Torus d) : HasDerivAt (fun s => φ s x) (D x) t := by
    have H := (hφ.differentiable (by simp) (t,representative d x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (representative d x)))
    convert H using 1 <;> simp [F,D,Function.comp_def,quotient_representative]
  have H := weak_transport_hasDerivAt h hφ.contDiffOn ht hDc hdt
  convert H using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    congr 1
    have hs := (hφ.differentiable (by simp) (t,representative d x)).hasFDerivAt.comp
      (representative d x) (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (representative d x))
    change HasFDerivAt (fun a : Euclid d => φ t (quotient d a)) _ _ at hs
    have hsum : ((1:ℝ),velocity U τ ρ t x) =
        (1,0) + (0,velocity U τ ρ t x) := by ext <;> simp
    rw [hsum, map_add]
    congr 1
    change fderiv ℝ F (t,representative d x) (0,velocity U τ ρ t x) = _
    rw [gradient, gradient_inner_eq_fderiv]
    have hd := congrArg (fun L : Euclid d →L[ℝ] ℝ => L (velocity U τ ρ t x)) hs.fderiv
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,F] using hd.symm)

/-- The actual finite Euler backward test on the original torus. -/
def actualEulerTest {d : ℕ} (U : Torus d → ℝ) (τ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (u v : ℝ) (g : Torus d → ℝ)
    (s : ℝ) (x : Torus d) : ℝ :=
  g (quotient d (representative d x + (v-s) • velocity U τ ρ u x))

private theorem actualEulerTest_lift {d : ℕ} (U : Torus d → ℝ) (τ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (u v s : ℝ) (g : Torus d → ℝ) (a : Euclid d) :
    actualEulerTest U τ ρ u v g s (quotient d a) =
      g (quotient d (a+(v-s) • velocity U τ ρ u (quotient d a))) := by
  simp only [actualEulerTest, quotient_add, quotient_representative]

private theorem actualEulerTest_contDiff {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) {u : ℝ} (hu : u ∈ Icc 0 T)
    (v : ℝ) (g : Torus d → ℝ)
    (hg : ContDiff ℝ 1 (fun a : Euclid d => g (quotient d a))) :
    ContDiff ℝ 1 (fun p : ℝ × Euclid d =>
      actualEulerTest U τ ρ u v g p.1 (quotient d p.2)) := by
  simp_rw [actualEulerTest_lift]
  have hb : ContDiff ℝ 1 (fun a : Euclid d => velocity U τ ρ u (quotient d a)) :=
    ((smooth_gradient_lift (chemicalPotential_smooth h hu)).neg).of_le (by simp)
  exact hg.comp (contDiff_snd.add ((contDiff_const.sub contDiff_fst).smul
    (hb.comp contDiff_snd)))

/-- Quantitative one-cell PDE-to-Euler estimate for the actual density laws.
The test has one derivative; the Euler step need not be invertible. -/
private theorem actual_density_euler_cell_bound {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    {u v A B L K : ℝ} (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T) (huv : u ≤ v)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hBv : ∀ s ∈ Icc 0 T, ∀ a : Euclid d, ‖velocity U τ ρ s (quotient d a)‖ ≤ B)
    (hLv : ∀ a : Euclid d,
      ‖fderiv ℝ (fun z => velocity U τ ρ u (quotient d z)) a‖ ≤ L)
    (hKt : ∀ s ∈ Icc u v, ∀ a : Euclid d,
      ‖velocity U τ ρ s (quotient d a) - velocity U τ ρ u (quotient d a)‖ ≤ K * (v-u))
    (g : Torus d → ℝ)
    (hg : ContDiff ℝ 1 (fun a : Euclid d => g (quotient d a)))
    (hgA : ∀ a : Euclid d, ‖fderiv ℝ (fun z => g (quotient d z)) a‖ ≤ A) :
    |(∫ x, g x ∂densityMeasure (ρ v)) -
      (∫ x, actualEulerTest U τ ρ u v g u x ∂densityMeasure (ρ u))| ≤
        A * (K+L*B) * (v-u)^2 := by
  let φ := actualEulerTest U τ ρ u v g
  let M : ℝ → ℝ := fun s => ∫ x, φ s x * ρ s x ∂haar d
  let F : ℝ × Euclid d → ℝ := fun p => φ p.1 (quotient d p.2)
  let R : ℝ := A*(K+L*B)*(v-u)
  have hφ : ContDiff ℝ 1 F := actualEulerTest_contDiff h hu v g hg
  have hM : ContinuousOn M (Icc u v) :=
    (haar_integral_C1On hT (hφ.contDiffOn.mul
      (h.density_smooth.of_le (by simp)))).continuousOn.mono
        (Icc_subset_Icc hu.1 hv.2)
  have hder (s : ℝ) (hs : s ∈ Ioo u v) :
      HasDerivAt M (∫ x, ρ s x * fderiv ℝ F (s,representative d x)
        (1,velocity U τ ρ s x) ∂haar d) s :=
    density_pairing_material_derivative h hφ ⟨hu.1.trans_lt hs.1, hs.2.trans_le hv.2⟩
  have hres (s : ℝ) (hs : s ∈ Ioo u v) (x : Torus d) :
      |fderiv ℝ F (s,representative d x) (1,velocity U τ ρ s x)| ≤ R := by
    let b : ℝ → Euclid d → Euclid d := fun t a => velocity U τ ρ t (quotient d a)
    have hF : F = fun p : ℝ × Euclid d =>
        (fun z : Euclid d => g (quotient d z)) (p.2+(v-p.1) • b u p.2) := by
      funext p
      exact actualEulerTest_lift U τ ρ u v p.1 g p.2
    rw [hF]
    have H := eulerBackwardTest_residual_bound b (fun a => g (quotient d a))
      u v s (v-u) A K L B (representative d x)
      (((smooth_gradient_lift (chemicalPotential_smooth h hu)).neg).of_le (by simp)) hg
      hA hL hB (by linarith [hs.2]) (by linarith [hs.1])
      (hgA _) (hKt s ⟨hs.1.le,hs.2.le⟩ _) (hLv _)
      (hBv s ⟨hu.1.trans hs.1.le, hs.2.le.trans hv.2⟩ _)
    simpa only [b,quotient_representative] using H
  have hbound (s : ℝ) (hs : s ∈ Ioo u v) :
      |∫ x, ρ s x * fderiv ℝ F (s,representative d x)
        (1,velocity U τ ρ s x) ∂haar d| ≤ R := by
    have hsc : s ∈ Icc 0 T := ⟨hu.1.trans hs.1.le, hs.2.le.trans hv.2⟩
    letI : IsProbabilityMeasure (densityMeasure (ρ s)) :=
      (gibbs_kl_from_smoothFP h).2.2 s hsc |>.1
    have Heq : (∫ x, ρ s x * fderiv ℝ F (s,representative d x)
        (1,velocity U τ ρ s x) ∂haar d) =
        ∫ x, fderiv ℝ F (s,representative d x) (1,velocity U τ ρ s x) ∂densityMeasure (ρ s) := by
      rw [densityMeasure_test_integral
        (continuous_of_lift (h.spatial_smooth s hsc).continuous)
        (fun x => (h.positive s hsc x).le)]
      exact integral_congr_ae (ae_of_all _ (fun x => mul_comm _ _))
    rw [Heq, ← Real.norm_eq_abs]
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all (densityMeasure (ρ s))
        (fun x => by simpa only [Real.norm_eq_abs] using hres s hs x))
  have hpair : |M v-M u| ≤ A*(K+L*B)*(v-u)^2 := by
    by_cases huv' : u = v
    · subst v; simp
    have huvl : u < v := lt_of_le_of_ne huv huv'
    obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope M
      (fun s => ∫ x, ρ s x * fderiv ℝ F (s,representative d x)
        (1,velocity U τ ρ s x) ∂haar d) huvl hM hder
    have H := hbound c hc
    rw [he, abs_div, abs_of_pos (sub_pos.mpr huvl)] at H
    have H' := (div_le_iff₀ (sub_pos.mpr huvl)).mp H
    dsimp [R] at H'
    nlinarith
  have hvφ : φ v = g := by
    funext x
    simp [φ,actualEulerTest,quotient_representative]
  rw [densityMeasure_test_integral
    (continuous_of_lift (h.spatial_smooth v hv).continuous)
    (fun x => (h.positive v hv x).le),
    densityMeasure_test_integral
    (continuous_of_lift (h.spatial_smooth u hu).continuous)
    (fun x => (h.positive u hu x).le)]
  simpa only [M,hvφ] using hpair

end SmoothDensityTransport

noncomputable section
open Set Metric
namespace SmoothDensityTransport

/-- Actual characteristics have a uniform speed bound through both endpoints. -/
private theorem actual_characteristic_speed_bound {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) {B : ℝ}
    (hB : ∀ t ∈ Icc 0 T, ∀ a : Euclid d, ‖velocity U τ ρ t (quotient d a)‖ ≤ B)
    (r : Icc 0 T) (a : Euclid d) {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖characteristic h hT r a t - characteristic h hT r a s‖ ≤ B * |t-s| := by
  have H := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (characteristic_ode h hT r a) (fun z hz => hB z hz _) hs ht
  simpa only [Real.norm_eq_abs] using H

/-- The actual ODE gives the local Euler truncation error, with no transport,
flow derivative, ambient time extension or inverse-step premise. -/
private theorem actual_characteristic_euler_local_error {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    {B L K u v : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hB : ∀ t ∈ Icc 0 T, ∀ a : Euclid d, ‖velocity U τ ρ t (quotient d a)‖ ≤ B)
    (hL : ∀ t ∈ Icc 0 T, ∀ a b : Euclid d,
      ‖velocity U τ ρ t (quotient d a)-velocity U τ ρ t (quotient d b)‖ ≤ L*‖a-b‖)
    (hK : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
      ‖velocity U τ ρ t (quotient d a)-velocity U τ ρ s (quotient d a)‖ ≤ K*|t-s|)
    (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T) (huv : u ≤ v)
    (r : Icc 0 T) (a : Euclid d) :
    ‖characteristic h hT r a v - characteristic h hT r a u -
      (v-u) • velocity U τ ρ u (quotient d (characteristic h hT r a u))‖ ≤
        (K+L*B)*(v-u)^2 := by
  let X := characteristic h hT r a
  let b : ℝ → Euclid d → Euclid d := fun t x => velocity U τ ρ t (quotient d x)
  let Y : ℝ → Euclid d := fun t => X t-X u-(t-u) • b u (X u)
  have hY (t : ℝ) (ht : t ∈ Icc u v) :
      HasDerivWithinAt Y (b t (X t)-b u (X u)) (Icc u v) t := by
    have H := ((characteristic_ode h hT r a t
      ⟨hu.1.trans ht.1,ht.2.trans hv.2⟩).mono (Icc_subset_Icc hu.1 hv.2)).sub_const (X u)
    convert H.sub (((hasDerivAt_id t).sub_const u).smul_const (b u (X u))).hasDerivWithinAt using 1 <;>
      simp [Y,X,b,Pi.sub_apply]
    rfl
  have hbound (t : ℝ) (ht : t ∈ Icc u v) :
      ‖b t (X t)-b u (X u)‖ ≤ (K+L*B)*(v-u) := by
    have htc : t ∈ Icc 0 T := ⟨hu.1.trans ht.1,ht.2.trans hv.2⟩
    have hx := actual_characteristic_speed_bound h hT hB r a hu htc
    have hlt := hL t htc (X t) (X u)
    have hkt := hK u hu t htc (X u)
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at hx hkt
    calc
      _ ≤ ‖b t (X t)-b t (X u)‖+‖b t (X u)-b u (X u)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L*(B*(t-u))+K*(t-u) := add_le_add
        (hlt.trans (mul_le_mul_of_nonneg_left hx hL0)) hkt
      _ = (K+L*B)*(t-u) := by ring
      _ ≤ (K+L*B)*(v-u) := mul_le_mul_of_nonneg_left (by linarith [ht.2])
        (add_nonneg hK0 (mul_nonneg hL0 hB0))
  have H := norm_image_sub_le_of_norm_deriv_le_segment' hY
    (fun t ht => hbound t ⟨ht.1,ht.2.le⟩) v ⟨huv,le_rfl⟩
  simpa only [Y,X,b,sub_self,zero_smul,sub_zero,pow_two,mul_assoc] using H

/-- The actual explicit Euler trajectory; the finite grid approximates the
same characteristic, rather than replacing it by a finite model. -/
def actualEulerPath {d : ℕ} (U : Torus d → ℝ) (τ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (δ : ℝ) (a : Euclid d) : ℕ → Euclid d
  | 0 => a
  | n+1 => actualEulerPath U τ ρ δ a n + δ •
      velocity U τ ρ ((n : ℝ)*δ) (quotient d (actualEulerPath U τ ρ δ a n))

/-- Finite-N comparison with the original characteristicOperator. All field
bounds are supplied by the original smooth-slab constants in its consumer. -/
private theorem actual_characteristic_euler_grid_error {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    {B L K r : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hB : ∀ t ∈ Icc 0 T, ∀ a : Euclid d, ‖velocity U τ ρ t (quotient d a)‖ ≤ B)
    (hL : ∀ t ∈ Icc 0 T, ∀ a b : Euclid d,
      ‖velocity U τ ρ t (quotient d a)-velocity U τ ρ t (quotient d b)‖ ≤ L*‖a-b‖)
    (hK : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
      ‖velocity U τ ρ t (quotient d a)-velocity U τ ρ s (quotient d a)‖ ≤ K*|t-s|)
    (hr : r ∈ Icc 0 T) (N : ℕ) (hN : 1 ≤ N) (a : Euclid d) :
    ‖characteristicOperator h hT 0 r a - actualEulerPath U τ ρ (r/(N:ℝ)) a N‖ ≤
      Real.exp (L*r)*(K+L*B)*r^2/(N:ℝ) := by
  let δ : ℝ := r/(N:ℝ)
  let X := characteristic h hT (⟨0,⟨le_rfl,hT.le⟩⟩ : Icc 0 T) a
  let P := actualEulerPath U τ ρ δ a
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hδ : 0 ≤ δ := div_nonneg hr.1 hNp.le
  have htime (n : ℕ) (hn : n ≤ N) : (n:ℝ)*δ ∈ Icc 0 T := by
    have hnR : (n:ℝ) ≤ N := by exact_mod_cast hn
    constructor
    · positivity
    · calc
        (n:ℝ)*δ ≤ (N:ℝ)*δ := mul_le_mul_of_nonneg_right hnR hδ
        _ = r := by dsimp [δ];field_simp
        _ ≤ T := hr.2
  have he0 : ‖X ((↑(0:ℕ):ℝ)*δ)-P 0‖ = 0 := by
    have hx : X 0 = a := characteristic_initial h hT ⟨0,⟨le_rfl,hT.le⟩⟩ a
    simp only [Nat.cast_zero,zero_mul,P,actualEulerPath,hx,sub_self,norm_zero]
  have hstep (n : ℕ) (hn : n < N) :
      ‖X ((n+1:ℕ)*δ)-P (n+1)‖ ≤
        (1+L*δ)*‖X ((n:ℝ)*δ)-P n‖+(K+L*B)*δ^2 := by
    let t : ℝ := (n:ℝ)*δ
    let v : ℝ := ((n+1:ℕ):ℝ)*δ
    have hdiff : v-t = δ := by dsimp [v,t];push_cast;ring
    have ht := htime n hn.le
    have hv := htime (n+1) hn
    have huv : t ≤ v := sub_nonneg.mp (by rw [hdiff];exact hδ)
    have H := actual_characteristic_euler_local_error h hT hB0 hL0 hK0 hB hL hK
      ht hv huv (⟨0,⟨le_rfl,hT.le⟩⟩ : Icc 0 T) a
    change ‖X v-X t-(v-t) • velocity U τ ρ t (quotient d (X t))‖ ≤ _ at H
    rw [hdiff] at H
    have HL := hL t ht (X t) (P n)
    have heq : X v-P (n+1) =
        (X v-X t-δ • velocity U τ ρ t (quotient d (X t))) +
        ((X t-P n)+δ • (velocity U τ ρ t (quotient d (X t))-
          velocity U τ ρ t (quotient d (P n)))) := by
      dsimp [P,actualEulerPath,t]
      module
    rw [heq]
    calc
      _ ≤ ‖X v-X t-δ • velocity U τ ρ t (quotient d (X t))‖+
          (‖X t-P n‖+‖δ • (velocity U τ ρ t (quotient d (X t))-
          velocity U τ ρ t (quotient d (P n)))‖) :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ (K+L*B)*δ^2+(‖X t-P n‖+δ*(L*‖X t-P n‖)) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ]
        exact add_le_add H (add_le_add_right (mul_le_mul_of_nonneg_left HL hδ) _)
      _ = _ := by ring
  have H := finiteGrid_euler_error_bound N hN r L (K+L*B) hr.1 hL0
    (add_nonneg hK0 (mul_nonneg hL0 hB0))
    (fun n => ‖X ((n:ℝ)*δ)-P n‖) he0 hstep
  have hterminal : (N:ℝ)*δ = r := by dsimp [δ];field_simp
  rw [hterminal] at H
  rw [characteristicOperator_of_mem h hT 0 ⟨le_rfl,hT.le⟩]
  exact H

end SmoothDensityTransport

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SmoothDensityTransport

/-- Derivative propagation through an actual Euler pullback. -/
private theorem actualEulerTest_derivative_bound {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) {u v A L : ℝ}
    (hu : u ∈ Icc 0 T) (huv : u ≤ v) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hLv : ∀ a : Euclid d, ‖fderiv ℝ (fun z => velocity U τ ρ u (quotient d z)) a‖ ≤ L)
    (g : Torus d → ℝ)
    (hg : ContDiff ℝ 1 (fun a : Euclid d => g (quotient d a)))
    (hgA : ∀ a : Euclid d, ‖fderiv ℝ (fun z => g (quotient d z)) a‖ ≤ A)
    (a : Euclid d) :
    ‖fderiv ℝ (fun z => actualEulerTest U τ ρ u v g u (quotient d z)) a‖ ≤
      A*(1+L*(v-u)) := by
  let b : Euclid d → Euclid d := fun z => velocity U τ ρ u (quotient d z)
  have hb : ContDiff ℝ 1 b := ((smooth_gradient_lift (chemicalPotential_smooth h hu)).neg).of_le (by simp)
  have hd := (hasFDerivAt_id a).add
    ((hb.differentiable (by simp) a).hasFDerivAt.const_smul (v-u))
  have H := (hg.differentiable (by simp) (a+(v-u) • b a)).hasFDerivAt.comp a hd
  have heq : (fun z => actualEulerTest U τ ρ u v g u (quotient d z)) =
      fun z => g (quotient d (z+(v-u) • b z)) := by
    funext z;exact actualEulerTest_lift U τ ρ u v u g z
  rw [heq]
  have Heq : fderiv ℝ (fun z => g (quotient d (z+(v-u) • b z))) a =
      (fderiv ℝ (fun z => g (quotient d z)) (a+(v-u) • b a)).comp
        (ContinuousLinearMap.id ℝ (Euclid d)+(v-u) • fderiv ℝ b a) := H.fderiv
  rw [Heq]
  have hnorm : ‖ContinuousLinearMap.id ℝ (Euclid d)+(v-u) • fderiv ℝ b a‖ ≤
      1+L*(v-u) := by
    calc
      _ ≤ ‖ContinuousLinearMap.id ℝ (Euclid d)‖+‖(v-u) • fderiv ℝ b a‖ := norm_add_le _ _
      _ ≤ 1+(v-u)*L := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr huv)]
        exact add_le_add (ContinuousLinearMap.norm_id_le) (mul_le_mul_of_nonneg_left (hLv a) (sub_nonneg.mpr huv))
      _ = _ := by ring
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hgA _) hnorm (norm_nonneg _) hA)

/-- Exact backward Euler tests on the actual torus, indexed by starting step
and number of remaining steps. -/
def actualEulerBackward {d : ℕ} (U : Torus d → ℝ) (τ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (δ : ℝ) (f : Torus d → ℝ) :
    ℕ → ℕ → Torus d → ℝ
  | _,0 => f
  | m,k+1 => actualEulerTest U τ ρ ((m:ℝ)*δ) (((m+1:ℕ):ℝ)*δ)
      (actualEulerBackward U τ ρ δ f (m+1) k) ((m:ℝ)*δ)

/-- The recursively constructed tests evaluate the same actual Euler path. -/
private theorem actualEulerBackward_path {d : ℕ} (U : Torus d → ℝ) (τ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (δ : ℝ) (f : Torus d → ℝ) (a : Euclid d)
    (m k : ℕ) :
    actualEulerBackward U τ ρ δ f m k
      (quotient d (actualEulerPath U τ ρ δ a m)) =
      f (quotient d (actualEulerPath U τ ρ δ a (m+k))) := by
  induction k generalizing m with
  | zero => simp [actualEulerBackward]
  | succ k ih =>
    rw [actualEulerBackward,actualEulerTest_lift]
    have hd : (((m+1:ℕ):ℝ)*δ)-(m:ℝ)*δ = δ := by push_cast;ring
    rw [hd]
    change actualEulerBackward U τ ρ δ f (m+1) k
      (quotient d (actualEulerPath U τ ρ δ a (m+1))) = _
    rw [ih]
    congr 3
    omega

/-- Regularity and uniform first-derivative growth for the actual backward
tests, derived only at grid points lying on the original closed slab. -/
private theorem actualEulerBackward_regular_bound {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) {δ C L : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hLv : ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
      ‖fderiv ℝ (fun z => velocity U τ ρ t (quotient d z)) a‖ ≤ L)
    (f : Torus d → ℝ) (hf : ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a)))
    (hfC : ∀ a : Euclid d, ‖fderiv ℝ (fun z => f (quotient d z)) a‖ ≤ C)
    (m k : ℕ) (hslab : ((m+k:ℕ):ℝ)*δ ≤ T) :
    ContDiff ℝ 1 (fun a : Euclid d => actualEulerBackward U τ ρ δ f m k (quotient d a)) ∧
      ∀ a : Euclid d,
        ‖fderiv ℝ (fun z => actualEulerBackward U τ ρ δ f m k (quotient d z)) a‖ ≤
          C*(1+L*δ)^k := by
  induction k generalizing m with
  | zero => simpa [actualEulerBackward] using And.intro hf hfC
  | succ k ih =>
    have hnext : (((m+1+k:ℕ):ℝ)*δ) ≤ T := by
      have heq : m+1+k = m+(k+1) := by omega
      simpa only [heq] using hslab
    obtain ⟨hg,hgA⟩ := ih (m+1) hnext
    have hum : (m:ℝ)*δ ∈ Icc 0 T := by
      constructor
      · positivity
      · have hm : (m:ℝ) ≤ ((m+(k+1):ℕ):ℝ) := by exact_mod_cast (Nat.le_add_right m (k+1))
        exact (mul_le_mul_of_nonneg_right hm hδ).trans hslab
    have huv : (m:ℝ)*δ ≤ ((m+1:ℕ):ℝ)*δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ m) hδ
    have hd : (((m+1:ℕ):ℝ)*δ)-(m:ℝ)*δ = δ := by push_cast;ring
    constructor
    · simpa only [actualEulerBackward,Function.comp_def,id_eq] using
        ((actualEulerTest_contDiff h hum (((m+1:ℕ):ℝ)*δ) _ hg).comp
          ((contDiff_const : ContDiff ℝ 1 (fun _ : Euclid d => (m:ℝ)*δ)).prodMk contDiff_id))
    · intro a
      have H := actualEulerTest_derivative_bound h hum huv
        (mul_nonneg hC (pow_nonneg (by positivity) k)) hL (hLv _ hum)
        _ hg hgA a
      rw [hd] at H
      simpa only [actualEulerBackward,pow_succ,mul_assoc] using H

/-- Finite-mesh transport consistency for the ORIGINAL density measures.
The recursively constructed backward tests are derived from f and the actual
velocity. The coefficient is independent of the mesh size. -/
theorem actual_density_euler_grid_error {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    {B L K C r : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hK0 : 0 ≤ K) (hC0 : 0 ≤ C)
    (hB : ∀ t ∈ Icc 0 T, ∀ a : Euclid d, ‖velocity U τ ρ t (quotient d a)‖ ≤ B)
    (hL : ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
      ‖fderiv ℝ (fun z => velocity U τ ρ t (quotient d z)) a‖ ≤ L)
    (hK : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
      ‖velocity U τ ρ t (quotient d a)-velocity U τ ρ s (quotient d a)‖ ≤ K*|t-s|)
    (f : Torus d → ℝ) (hf : ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a)))
    (hfC : ∀ a : Euclid d, ‖fderiv ℝ (fun z => f (quotient d z)) a‖ ≤ C)
    (hr : r ∈ Icc 0 T) (N : ℕ) (hN : 1 ≤ N) :
    |(∫ x, f x ∂densityMeasure (ρ r)) -
      (∫ x, f (quotient d (actualEulerPath U τ ρ (r/(N:ℝ)) (representative d x) N))
        ∂densityMeasure (ρ 0))| ≤ C*Real.exp (L*r)*(K+L*B)*r^2/(N:ℝ) := by
  let δ : ℝ := r/(N:ℝ)
  let A : ℝ := C*Real.exp (L*r)
  let ε : ℝ := A*(K+L*B)*δ^2
  let g : ℕ → Torus d → ℝ := fun i => actualEulerBackward U τ ρ δ f i (N-i)
  let M : ℕ → ℝ := fun i => ∫ x, g i x ∂densityMeasure (ρ ((i:ℝ)*δ))
  have hNp : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hδ : 0 ≤ δ := div_nonneg hr.1 hNp.le
  have hNδ : (N:ℝ)*δ = r := by dsimp [δ];field_simp
  have htime (i : ℕ) (hi : i ≤ N) : (i:ℝ)*δ ∈ Icc 0 T := by
    constructor
    · positivity
    · calc
        (i:ℝ)*δ ≤ (N:ℝ)*δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hδ
        _ = r := hNδ
        _ ≤ T := hr.2
  have hA : 0 ≤ A := mul_nonneg hC0 (Real.exp_pos _).le
  have hε : 0 ≤ ε := mul_nonneg (mul_nonneg hA (add_nonneg hK0 (mul_nonneg hL0 hB0))) (sq_nonneg _)
  have hpow (k : ℕ) (hk : k ≤ N) : C*(1+L*δ)^k ≤ A := by
    have H : (1+L*δ)^k ≤ Real.exp (L*r) := by
      calc
        _ ≤ (Real.exp (L*δ))^k := pow_le_pow_left₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp (L*δ)) k
        _ = Real.exp ((k:ℝ)*(L*δ)) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (L*r) := by
          apply Real.exp_le_exp.mpr
          have Hk := mul_le_mul_of_nonneg_right (show (k:ℝ) ≤ N by exact_mod_cast hk) hδ
          rw [hNδ] at Hk
          nlinarith [mul_le_mul_of_nonneg_left Hk hL0]
    exact mul_le_mul_of_nonneg_left H hC0
  have hcell (i : ℕ) (hi : i < N) : |M (i+1)-M i| ≤ ε := by
    have hni : i+1 ≤ N := hi
    have hidx : i+1+(N-(i+1)) = N := by omega
    have hslab : (((i+1+(N-(i+1)):ℕ):ℝ)*δ) ≤ T := by rw [hidx,hNδ];exact hr.2
    obtain ⟨hg,hgA⟩ := actualEulerBackward_regular_bound h hδ hC0 hL0 hL f hf hfC (i+1) (N-(i+1)) hslab
    have hgA' (a : Euclid d) :
        ‖fderiv ℝ (fun z => g (i+1) (quotient d z)) a‖ ≤ A :=
      (hgA a).trans (hpow _ (Nat.sub_le _ _))
    have hdiff : (((i+1:ℕ):ℝ)*δ)-(i:ℝ)*δ = δ := by push_cast;ring
    have huv : (i:ℝ)*δ ≤ ((i+1:ℕ):ℝ)*δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hδ
    have H := actual_density_euler_cell_bound h hT (htime i hi.le) (htime (i+1) hni) huv
      hA hB0 hL0 hK0 hB (hL _ (htime i hi.le)) (g := g (i+1)) hg hgA'
      (hKt := fun s hs a => by
        have hsc : s ∈ Icc 0 T := ⟨(htime i hi.le).1.trans hs.1,hs.2.trans (htime (i+1) hni).2⟩
        have H := hK _ (htime i hi.le) s hsc a
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)] at H
        exact H.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 _) hK0))
    have hgi : g i = actualEulerTest U τ ρ ((i:ℝ)*δ) (((i+1:ℕ):ℝ)*δ) (g (i+1)) ((i:ℝ)*δ) := by
      have hcount : N-i = (N-(i+1))+1 := by omega
      dsimp [g]
      rw [hcount,actualEulerBackward]
    rw [hdiff] at H
    simpa only [M,hgi,ε] using H
  have H := finiteGrid_gronwall N (fun i => |M i-M 0|) 0 ε (by simp) le_rfl hε
    (fun i hi => by
      have H := abs_sub_le (M (i+1)) (M i) (M 0)
      have Hc := hcell i hi
      simp only [add_zero,one_mul]
      linarith)
  simp only [sub_self,abs_zero,zero_add,mul_zero,Real.exp_zero,mul_one] at H
  have HMN : M N = ∫ x, f x ∂densityMeasure (ρ r) := by simp [M,g,actualEulerBackward,hNδ]
  have HM0 : M 0 = ∫ x, f (quotient d (actualEulerPath U τ ρ δ (representative d x) N)) ∂densityMeasure (ρ 0) := by
    simp only [M,g,Nat.sub_zero,Nat.cast_zero,zero_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      have H := actualEulerBackward_path U τ ρ δ f (representative d x) 0 N
      simpa [actualEulerPath,quotient_representative] using H)
  rw [HMN,HM0] at H
  convert H using 1
  dsimp [ε,A,δ]
  field_simp
  <;> ring

end SmoothDensityTransport

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SmoothDensityTransport

/-- The derivative bound supplied by the slab controls actual spatial velocity
differences, with no nonzero-dimension condition. -/
private theorem actual_velocity_spatial_bound {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) {L : ℝ}
    (hL : ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
      ‖fderiv ℝ (fun z => velocity U τ ρ t (quotient d z)) a‖ ≤ L) :
    ∀ t ∈ Icc 0 T, ∀ a b : Euclid d,
      ‖velocity U τ ρ t (quotient d a)-velocity U τ ρ t (quotient d b)‖ ≤ L*‖a-b‖ := by
  intro t ht a b
  exact (convex_univ : Convex ℝ (univ : Set (Euclid d))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ((smooth_gradient_lift (chemicalPotential_smooth h ht)).neg.differentiable (by simp)) z)
    (fun z _ => hL t ht z) (mem_univ b) (mem_univ a)

/-- Every finite Euler map is C1, as constructed from the actual smooth slices. -/
private theorem actualEulerPath_contDiff {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ) (hslab : (N:ℝ)*δ ≤ T) :
    ContDiff ℝ 1 (fun a : Euclid d => actualEulerPath U τ ρ δ a N) := by
  induction N with
  | zero =>
    change ContDiff ℝ 1 (id : Euclid d → Euclid d)
    exact contDiff_id
  | succ n ih =>
    have htime : (n:ℝ)*δ ∈ Icc 0 T := by
      constructor
      · positivity
      · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hδ).trans hslab
    have hP := ih htime.2
    have hb : ContDiff ℝ 1 (fun a : Euclid d => velocity U τ ρ ((n:ℝ)*δ) (quotient d a)) :=
      ((smooth_gradient_lift (chemicalPotential_smooth h htime)).neg).of_le (by simp)
    convert hP.add ((hb.comp hP).const_smul δ) using 1
    funext a
    rfl

/-- Forward slice continuity is derived from the actual Euler approximation.
No variational derivative of the flow is used. -/
private theorem actual_characteristic_slice_continuous {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) {r : ℝ} (hr : r ∈ Icc 0 T) :
    Continuous (characteristicOperator h hT 0 r) := by
  obtain ⟨B,L,K,C,hB0,hL0,hK0,hC0,hB,hL,hK,hC⟩ :=
    actual_smooth_slab_constants_including_zero h (fun _ => 0) contDiff_const
  have hLs := actual_velocity_spatial_bound h hL
  let D : ℝ := Real.exp (L*r)*(K+L*B)*r^2
  have hUnif : TendstoUniformly
      (fun n : ℕ => fun a : Euclid d => actualEulerPath U τ ρ (r/(n+1:ℕ)) a (n+1))
      (characteristicOperator h hT 0 r) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    obtain ⟨M,hM⟩ := exists_nat_gt (D/ε)
    filter_upwards [eventually_ge_atTop M] with n hn a
    have hnp : (0:ℝ) < (n+1:ℕ) := by positivity
    have HM : (M:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (hn.trans (Nat.le_succ n))
    rw [dist_eq_norm]
    calc
      _ ≤ D/(n+1:ℕ) := actual_characteristic_euler_grid_error h hT hB0 hL0 hK0 hB hLs hK hr (n+1) (by omega) a
      _ < ε := (div_lt_iff₀ hnp).mpr
        (by nlinarith [(div_lt_iff₀ hε).mp hM, mul_le_mul_of_nonneg_left HM hε.le])
  apply hUnif.continuous
  apply Filter.Eventually.frequently
  exact Filter.Eventually.of_forall (fun n => (actualEulerPath_contDiff h
    (div_nonneg hr.1 (by positivity)) (n+1) (by
      have hp : (n+1:ℝ) ≠ 0 := by positivity
      convert hr.2 using 1 <;> field_simp)).continuous)

def actualPhi {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) (r : ℝ) (x : Torus d) : Torus d :=
  quotient d (characteristicOperator h hT 0 r (representative d x))

private theorem actualPhi_continuous {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) {r : ℝ} (hr : r ∈ Icc 0 T) :
    Continuous (actualPhi h hT r) := by
  apply continuous_of_lift
  have heq (a : Euclid d) : actualPhi h hT r (quotient d a) =
      quotient d (characteristicOperator h hT 0 r a) :=
    characteristicOperator_quotient_representative h hT 0 r ⟨le_rfl,hT.le⟩ hr a
  simp_rw [heq]
  exact (quotient_isQuotientMap d).continuous.comp (actual_characteristic_slice_continuous h hT hr)

/-- Exact transport of every C1 periodic test by the ORIGINAL characteristic
operator, obtained by an arbitrarily fine finite Euler mesh. -/
theorem actual_density_characteristic_moment {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) {r : ℝ} (hr : r ∈ Icc 0 T)
    (f : Torus d → ℝ) (hf : ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a))) :
    (∫ x, f x ∂densityMeasure (ρ r)) = ∫ x, f (actualPhi h hT r x) ∂densityMeasure (ρ 0) := by
  obtain ⟨B,L,K,C,hB0,hL0,hK0,hC0,hB,hL,hK,hC⟩ := actual_smooth_slab_constants_including_zero h f hf
  have hLs := actual_velocity_spatial_bound h hL
  have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl,hT.le⟩
  letI : IsProbabilityMeasure (densityMeasure (ρ 0)) :=
    (gibbs_kl_from_smoothFP h).2.2 0 h0 |>.1
  have hfc : Continuous f := continuous_of_lift hf.continuous
  have hif : Integrable (fun x => f (actualPhi h hT r x)) (densityMeasure (ρ 0)) :=
    compact_integrable (hfc.comp (actualPhi_continuous h hT hr))
  apply moment_eq_of_uniform_inverse_nat_bound _ _ (2*C*Real.exp (L*r)*(K+L*B)*r^2)
  intro N hN
  have hNp : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  let δ : ℝ := r/(N:ℝ)
  let G : Torus d → ℝ := fun x => f (quotient d (actualEulerPath U τ ρ δ (representative d x) N))
  have hδ : 0 ≤ δ := div_nonneg hr.1 hNp.le
  have hNδ : (N:ℝ)*δ = r := by dsimp [δ];field_simp
  obtain ⟨hg,hgC⟩ := actualEulerBackward_regular_bound h hδ hC0 hL0 hL f hf hC 0 N (by simpa only [Nat.zero_add] using hNδ.le.trans hr.2)
  have hG : G = actualEulerBackward U τ ρ δ f 0 N := by
    funext x
    have H := actualEulerBackward_path U τ ρ δ f (representative d x) 0 N
    simpa [G,actualEulerPath,quotient_representative] using H.symm
  have hiG : Integrable G (densityMeasure (ρ 0)) := by
    rw [hG]
    exact compact_integrable (continuous_of_lift hg.continuous)
  have hcmp : |(∫ x, f (actualPhi h hT r x) ∂densityMeasure (ρ 0))-
      (∫ x, G x ∂densityMeasure (ρ 0))| ≤ C*Real.exp (L*r)*(K+L*B)*r^2/(N:ℝ) := by
    rw [← integral_sub hif hiG, ← Real.norm_eq_abs]
    have H := norm_integral_le_of_norm_le_const (μ := densityMeasure (ρ 0))
      (C := C*Real.exp (L*r)*(K+L*B)*r^2/(N:ℝ))
      (ae_of_all _ (fun x => by
        have HL := (convex_univ : Convex ℝ (univ : Set (Euclid d))).norm_image_sub_le_of_norm_fderiv_le
          (fun z _ => hf.differentiable (by simp) z) (fun z _ => hC z)
          (mem_univ (actualEulerPath U τ ρ δ (representative d x) N))
          (mem_univ (characteristicOperator h hT 0 r (representative d x)))
        have HX := actual_characteristic_euler_grid_error h hT hB0 hL0 hK0 hB hLs hK hr N hN (representative d x)
        have H := HL.trans (mul_le_mul_of_nonneg_left HX hC0)
        change ‖f (quotient d (characteristicOperator h hT 0 r (representative d x)))-
          f (quotient d (actualEulerPath U τ ρ δ (representative d x) N))‖ ≤ _
        convert H using 1 <;> ring))
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,actualPhi,G] using H
  have hden := actual_density_euler_grid_error h hT hB0 hL0 hK0 hC0 hB hL hK f hf hC hr N hN
  have H := abs_sub_le (∫ x, f x ∂densityMeasure (ρ r)) (∫ x, G x ∂densityMeasure (ρ 0))
    (∫ x, f (actualPhi h hT r x) ∂densityMeasure (ρ 0))
  rw [abs_sub_comm (∫ x, G x ∂densityMeasure (ρ 0))] at H
  change |(∫ x, f x ∂densityMeasure (ρ r)) - (∫ x, G x ∂densityMeasure (ρ 0))| ≤ _ at hden
  calc
    _ ≤ _ := H.trans (add_le_add hden hcmp)
    _ = _ := by ring

end SmoothDensityTransport

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SmoothDensityTransport

/-- The pinned torus Fourier characters have C1 Euclidean lifts in every finite
dimension. This uses their explicit exponential expression. -/
private theorem mFourier_lift_C1 (d : ℕ) (n : Fin d → ℤ) :
    ContDiff ℝ 1 (fun a : Euclid d => UnitAddTorus.mFourier n (quotient d a)) := by
  classical
  have hc (i : Fin d) : ContDiff ℝ 1 (fun a : Euclid d => (a i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_pi.mp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff i)
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,quotient,fourier_coe_apply,Complex.ofReal_one,div_one]
  exact contDiff_prod (fun i _ => Complex.contDiff_exp.comp (contDiff_const.mul (hc i)))

/-- The actual characteristic pushes the original initial density to the
original density at every closed-slab time. -/
theorem actual_density_characteristic_pushforward {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) {r : ℝ} (hr : r ∈ Icc 0 T) :
    Measure.map (actualPhi h hT r) (densityMeasure (ρ 0)) = densityMeasure (ρ r) := by
  have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl,hT.le⟩
  letI : IsProbabilityMeasure (densityMeasure (ρ 0)) :=
    (gibbs_kl_from_smoothFP h).2.2 0 h0 |>.1
  letI : IsProbabilityMeasure (densityMeasure (ρ r)) :=
    (gibbs_kl_from_smoothFP h).2.2 r hr |>.1
  have hΦ := actualPhi_continuous h hT hr
  letI : IsProbabilityMeasure (Measure.map (actualPhi h hT r) (densityMeasure (ρ 0))) :=
    inferInstance
  let μ := Measure.map (actualPhi h hT r) (densityMeasure (ρ 0))
  let ν := densityMeasure (ρ r)
  have hTests : ∀ f : Torus d → ℝ,
      ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a)) →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
    intro f hf
    dsimp [μ,ν]
    rw [integral_map hΦ.measurable.aemeasurable
      (continuous_of_lift hf.continuous).aestronglyMeasurable]
    exact (actual_density_characteristic_moment h hT hr f hf).symm
  have hi (σ : Measure (Torus d)) [IsFiniteMeasure σ] (f : C(Torus d,ℂ)) :
      Integrable f σ := by
    simpa only [integrableOn_univ] using
      f.continuous.continuousOn.integrableOn_compact (K := univ) isCompact_univ
  let J (σ : Measure (Torus d)) [IsFiniteMeasure σ] : C(Torus d,ℂ) →L[ℂ] ℂ :=
    LinearMap.mkContinuous
      { toFun := fun f => ∫ x, f x ∂σ
        map_add' := fun f g => by simpa using integral_add (hi σ f) (hi σ g)
        map_smul' := fun c f => by simpa only [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply] using integral_const_mul c (fun x => f x) }
      (σ.real univ) (fun f => by
        have H := norm_integral_le_of_norm_le_const (μ := σ)
          (ae_of_all _ (fun x => f.norm_coe_le_norm x))
        change ‖∫ x, f x ∂σ‖ ≤ σ.real univ * ‖f‖
        exact H.trans_eq (mul_comm _ _))
  have hd : Dense (Submodule.span ℂ (range (UnitAddTorus.mFourier (d := Fin d))) :
      Set C(Torus d,ℂ)) := by
    rw [dense_iff_closure_eq]
    change (↑((Submodule.span ℂ (range (UnitAddTorus.mFourier (d := Fin d)))).topologicalClosure) :
      Set C(Torus d,ℂ)) = univ
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    rfl
  have hJ : J μ = J ν := by
    apply ContinuousLinearMap.ext_on hd
    rintro f ⟨n,rfl⟩
    change (∫ x, UnitAddTorus.mFourier n x ∂μ) = ∫ x, UnitAddTorus.mFourier n x ∂ν
    apply Complex.ext
    · change RCLike.re (∫ x, UnitAddTorus.mFourier n x ∂μ) =
        RCLike.re (∫ x, UnitAddTorus.mFourier n x ∂ν)
      rw [← integral_re (hi μ _),← integral_re (hi ν _)]
      exact hTests (fun x => (UnitAddTorus.mFourier n x).re)
        (Complex.reCLM.contDiff.comp (mFourier_lift_C1 d n))
    · change RCLike.im (∫ x, UnitAddTorus.mFourier n x ∂μ) =
        RCLike.im (∫ x, UnitAddTorus.mFourier n x ∂ν)
      rw [← integral_im (hi μ _),← integral_im (hi ν _)]
      exact hTests (fun x => (UnitAddTorus.mFourier n x).im)
        (Complex.imCLM.contDiff.comp (mFourier_lift_C1 d n))
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : C(Torus d,ℂ) := ⟨fun x => (f x : ℂ),Complex.continuous_ofReal.comp f.continuous⟩
  have H := congrArg (fun L : C(Torus d,ℂ) →L[ℂ] ℂ => L g) hJ
  change (∫ x, (f x : ℂ) ∂μ) = ∫ x, (f x : ℂ) ∂ν at H
  simpa only [integral_complex_ofReal,Complex.ofReal_inj] using H

end SmoothDensityTransport

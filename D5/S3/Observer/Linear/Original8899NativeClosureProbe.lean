/- Exact full-source receiving candidate, original #8899 §§6.3/6.4.
   SOURCE ONLY / UNCOMPILED. No kernel, axiom, native or host-goal acceptance.
   Public repository 4d937d239686ac573662baad5ebfe84800a645aa;
   Lean 4.35.0; mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
   Original mathematical text 488e3fce13cd3f77e9051ae316dadc0da7f7a4fc.
   All local names organize this transient source and have actual consumers.
   No repository module, retention, admission or coverage claim is made. -/
import D5.S3.Observer.Linear.DerivativeLayerNormalizedObservation
import D5.S3.Observer.Linear.DerivativeLayerNativeGramian
import D5.S3.Observer.Linear.GradedCongruenceSpectrum
import D5.S3.Observer.Linear.ObservableTrajectoryCoordinates
import D5.S3.Observer.Linear.GaussianObservationLaw
import D5.S3.Observer.Linear.SpectralNoiseAsymptotics
import D5.S3.Observer.Linear.PhysicalFixedNoiseInformation
import D5.S3.Observer.Linear.HilbertMomentCoercivity
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Matrix.Spectrum

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ContinuousLinearMap MeasureTheory Module Filter Set
open scoped BigOperators Topology InnerProductSpace RealInnerProductSpace Matrix.Norms.L2Operator

namespace Original8899NativeAmbient

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

local instance {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] : CompleteSpace X := FiniteDimensional.complete ℝ X

def N (B : V →L[ℝ] V) (C : V →L[ℝ] W) (j : ℕ) : Submodule ℝ V :=
  ⨅ k : Fin j, LinearMap.ker (C.toLinearMap.comp (B.toLinearMap ^ (k : ℕ)))

def U (B : V →L[ℝ] V) (C : V →L[ℝ] W) : Submodule ℝ V :=
  (N B C (finrank ℝ V))ᗮ

def E (B : V →L[ℝ] V) (C : V →L[ℝ] W) (j : Fin (finrank ℝ V)) :
    Submodule ℝ V := N B C j ⊓ (N B C (j + 1))ᗮ

def Q (B : V →L[ℝ] V) (C : V →L[ℝ] W) (j : Fin (finrank ℝ V)) :
    U B C →L[ℝ] U B C :=
  (U B C).orthogonalProjectionOnto.comp ((E B C j).starProjection.comp (U B C).subtypeL)

def dU (B : V →L[ℝ] V) (C : V →L[ℝ] W) (T : ℝ) : U B C →L[ℝ] U B C :=
  ∑ j : Fin (finrank ℝ V), (Real.sqrt T * T ^ (j : ℕ)) • Q B C j

def eU (B : V →L[ℝ] V) (C : V →L[ℝ] W) (T : ℝ) : U B C →L[ℝ] U B C :=
  ∑ j : Fin (finrank ℝ V), (Real.sqrt T * T ^ (j : ℕ))⁻¹ • Q B C j

def A (B : V →L[ℝ] V) (C : V →L[ℝ] W) (t : ℝ) : V →L[ℝ] W :=
  C.comp (NormedSpace.exp (t • B))

def P (B : V →L[ℝ] V) (C : V →L[ℝ] W) (s : ℝ) : V →L[ℝ] W :=
  ∑ j : Fin (finrank ℝ V), (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) •
    C.comp ((B ^ (j : ℕ)).comp (E B C j).starProjection)

def GU (B : V →L[ℝ] V) (C : V →L[ℝ] W) (T : ℝ) : U B C →L[ℝ] U B C :=
  ∫ t in (0 : ℝ)..T,
    ((A B C t).comp (U B C).subtypeL).adjoint.comp
      ((A B C t).comp (U B C).subtypeL)

def PU (B : V →L[ℝ] V) (C : V →L[ℝ] W) (s : ℝ) : U B C →L[ℝ] W :=
  ∑ j : Fin (finrank ℝ V), (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) •
    C.comp ((B ^ (j : ℕ)).comp ((E B C j).starProjection.comp (U B C).subtypeL))

def HU (B : V →L[ℝ] V) (C : V →L[ℝ] W) : U B C →L[ℝ] U B C :=
  ∫ s in (0 : ℝ)..1, (PU B C s).adjoint.comp (PU B C s)

def G (B : V →L[ℝ] V) (C : V →L[ℝ] W) (T : ℝ) : V →L[ℝ] V :=
  ∫ t in (0 : ℝ)..T, (A B C t).adjoint.comp (A B C t)

def H (B : V →L[ℝ] V) (C : V →L[ℝ] W) : V →L[ℝ] V :=
  ∫ s in (0 : ℝ)..1, (P B C s).adjoint.comp (P B C s)

def dV (B : V →L[ℝ] V) (C : V →L[ℝ] W) (T : ℝ) : V →L[ℝ] V :=
  ∑ j : Fin (finrank ℝ V), (Real.sqrt T * T ^ (j : ℕ)) • (E B C j).starProjection

def eV (B : V →L[ℝ] V) (C : V →L[ℝ] W) (T : ℝ) : V →L[ℝ] V :=
  ∑ j : Fin (finrank ℝ V), (Real.sqrt T * T ^ (j : ℕ))⁻¹ • (E B C j).starProjection

def normalized (B : V →L[ℝ] V) (C : V →L[ℝ] W) (T : ℝ) : V →L[ℝ] V :=
  (eV B C T).comp ((G B C T).comp (eV B C T))

-- Operator conjugation is a continuous linear map; no comparison of incompatible
-- matrix and Hilbert norms is hidden in a simplifier call.
def transport {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (u : X ≃ₗᵢ[ℝ] Y) :
    (X →L[ℝ] X) →L[ℝ] (Y →L[ℝ] Y) :=
  ((ContinuousLinearMap.compL ℝ Y X Y) (u : X →L[ℝ] Y)).comp
    ((ContinuousLinearMap.compL ℝ Y X X).flip (u.symm : Y →L[ℝ] X))

theorem transport_apply {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (u : X ≃ₗᵢ[ℝ] Y)
    (K : X →L[ℝ] X) (x : Y) : transport u K x = u (K (u.symm x)) := rfl

theorem transport_comp {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (u : X ≃ₗᵢ[ℝ] Y)
    (K L : X →L[ℝ] X) :
    transport u (K.comp L) = (transport u K).comp (transport u L) := by
  ext x
  simp only [transport_apply, comp_apply, LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem transport_id {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (u : X ≃ₗᵢ[ℝ] Y) :
    transport u (.id ℝ X) = .id ℝ Y := by
  ext x
  exact u.apply_symm_apply x

theorem transport_gram {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (u : X ≃ₗᵢ[ℝ] Y) (f : Y →L[ℝ] Z) :
    transport u ((f.comp (u : X →L[ℝ] Y)).adjoint.comp
      (f.comp (u : X →L[ℝ] Y))) = f.adjoint.comp f := by
  simp only [adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]
  ext x
  change u (u.symm (f.adjoint (f (u (u.symm x)))) ) = f.adjoint (f x)
  rw [u.apply_symm_apply, u.apply_symm_apply]

theorem transport_integral_gram {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (u : X ≃ₗᵢ[ℝ] Y) (f : ℝ → Y →L[ℝ] Z) (hf : Continuous f) (a b : ℝ) :
    transport u (∫ t in a..b,
      ((f t).comp (u : X →L[ℝ] Y)).adjoint.comp ((f t).comp (u : X →L[ℝ] Y))) =
      ∫ t in a..b, (f t).adjoint.comp (f t) := by
  have hc : Continuous (fun t =>
      ((f t).comp (u : X →L[ℝ] Y)).adjoint.comp ((f t).comp (u : X →L[ℝ] Y))) :=
    (ContinuousLinearMap.adjoint.continuous.comp (hf.clm_comp continuous_const)).clm_comp
      (hf.clm_comp continuous_const)
  rw [← (transport u).intervalIntegral_comp_comm (hc.intervalIntegrable a b)]
  simp_rw [transport_gram]

theorem continuous_A (B : V →L[ℝ] V) (C : V →L[ℝ] W) : Continuous (A B C) := by
  have he : Continuous (NormedSpace.exp : (V →L[ℝ] V) → V →L[ℝ] V) := by
    apply continuous_iff_continuousAt.mpr
    intro K
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) K).continuousAt
  exact continuous_const.clm_comp (he.comp (continuous_id.smul continuous_const))

theorem continuous_P (B : V →L[ℝ] V) (C : V →L[ℝ] W) : Continuous (P B C) := by
  unfold P
  fun_prop

theorem right_limit_of_bound {X : Type*} [NormedAddCommGroup X] (K : ℝ → X) (K₀ : X)
    (B : V →L[ℝ] V) (R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ T : ℝ, 0 < T → T ≤ 1 → T * ‖B‖ < 1 → ‖K T - K₀‖ ≤ R * T) :
    Tendsto K (𝓝[>] (0 : ℝ)) (𝓝 K₀) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min 1 (min (1 / (1 + ‖B‖)) (ε / (R + 1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ∀ᶠ T : ℝ in 𝓝[>] (0 : ℝ), T < δ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hsmall] with T hT hTδ
  change 0 < T at hT
  have hT1 : T ≤ 1 := le_of_lt (hTδ.trans_le (min_le_left _ _))
  have hTb : T < 1 / (1 + ‖B‖) :=
    hTδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hTε : T < ε / (R + 1) :=
    hTδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbn : 0 < 1 + ‖B‖ := by positivity
  have hRn : 0 < R + 1 := by positivity
  have hbmul := (lt_div_iff₀ hbn).mp hTb
  have hRmul := (lt_div_iff₀ hRn).mp hTε
  have hTB : T * ‖B‖ < 1 := by nlinarith
  have hRT : R * T < ε := by nlinarith
  rw [dist_eq_norm]
  exact (hb T hT hT1 hTB).trans_lt hRT

-- The geometric premise is N(n)=0, already proved at both concrete consumers.
-- It is not a premise asserting any of the desired transport identities.
def inclusionIsometry (B : V →L[ℝ] V) (C : V →L[ℝ] W)
    (hN : N B C (finrank ℝ V) = ⊥) : U B C ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofTop V (U B C) (by simp only [U, hN, Submodule.bot_orthogonal_eq_top])

structure TransportFacts (B : V →L[ℝ] V) (C : V →L[ℝ] W)
    (hN : N B C (finrank ℝ V) = ⊥) : Prop where
  projection : ∀ j, transport (inclusionIsometry B C hN) (Q B C j) = (E B C j).starProjection
  forward : ∀ T, transport (inclusionIsometry B C hN) (dU B C T) = dV B C T
  inverse : ∀ T, transport (inclusionIsometry B C hN) (eU B C T) = eV B C T
  physical : ∀ T, transport (inclusionIsometry B C hN) (GU B C T) = G B C T
  polynomial : transport (inclusionIsometry B C hN) (HU B C) = H B C
  normalization : ∀ T,
    transport (inclusionIsometry B C hN)
      ((eU B C T).comp ((GU B C T).comp (eU B C T))) = normalized B C T
  inverse_left : ∀ T, 0 < T → (dV B C T).comp (eV B C T) = .id ℝ V
  inverse_right : ∀ T, 0 < T → (eV B C T).comp (dV B C T) = .id ℝ V
  restore : ∀ T, 0 < T →
    (dV B C T).comp ((normalized B C T).comp (dV B C T)) = G B C T
  positive : ∀ x : V, x ≠ 0 → 0 < ⟪x, H B C x⟫_ℝ
  bound : ∃ R : ℝ, 0 ≤ R ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T * ‖B‖ < 1 →
    ‖normalized B C T - H B C‖ ≤ R * T
  limit : Tendsto (normalized B C) (𝓝[>] (0 : ℝ)) (𝓝 (H B C))

theorem native_to_ambient (B : V →L[ℝ] V) (C : V →L[ℝ] W)
    (hN : N B C (finrank ℝ V) = ⊥) : TransportFacts B C hN := by
  classical
  let u := inclusionIsometry B C hN
  have hu : (u : U B C →L[ℝ] V) = (U B C).subtypeL := rfl
  have hU : U B C = ⊤ := by simp only [U, hN, Submodule.bot_orthogonal_eq_top]
  have hproj (x : V) : u ((U B C).orthogonalProjectionOnto x) = x := by
    change (U B C).starProjection x = x
    exact (U B C).starProjection_eq_self_iff.mpr (by rw [hU]; trivial)
  have hQ (j : Fin (finrank ℝ V)) : transport u (Q B C j) = (E B C j).starProjection := by
    ext x
    change u ((U B C).orthogonalProjectionOnto
      ((E B C j).starProjection (u (u.symm x)))) = _
    rw [u.apply_symm_apply, hproj]
  have hd (T : ℝ) : transport u (dU B C T) = dV B C T := by
    simp only [dU, dV, map_sum, map_smul, hQ]
  have he (T : ℝ) : transport u (eU B C T) = eV B C T := by
    simp only [eU, eV, map_sum, map_smul, hQ]
  have hG (T : ℝ) : transport u (GU B C T) = G B C T := by
    simpa only [GU, G, hu] using transport_integral_gram u (A B C) (continuous_A B C) 0 T
  have hF (s : ℝ) : PU B C s = (P B C s).comp (U B C).subtypeL := by
    ext x
    simp only [PU, P, comp_apply, sum_apply, smul_apply]
  have hH : transport u (HU B C) = H B C := by
    simpa only [HU, H, hF, hu] using transport_integral_gram u (P B C) (continuous_P B C) 0 1
  have hnorm (T : ℝ) :
      transport u ((eU B C T).comp ((GU B C T).comp (eU B C T))) = normalized B C T := by
    rw [transport_comp, transport_comp, he, hG]
    rfl
  have hn := D5.S3.Observer.Linear.DerivativeLayerNativeGramian.derivative_layer_native_gramian
    B.toLinearMap C.toLinearMap
  have hn' :
      (∀ T : ℝ, 0 < T →
        (dU B C T).comp (eU B C T) = .id ℝ (U B C) ∧
        (eU B C T).comp (dU B C T) = .id ℝ (U B C) ∧
        (eU B C T).comp ((GU B C T).comp (eU B C T)) =
          ∫ s in (0 : ℝ)..1,
            (Real.sqrt T • ((A B C (T*s)).comp (U B C).subtypeL).comp (eU B C T)).adjoint.comp
              (Real.sqrt T • ((A B C (T*s)).comp (U B C).subtypeL).comp (eU B C T))) ∧
      (∀ x : U B C, x ≠ 0 → 0 < ⟪x, HU B C x⟫_ℝ) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T * ‖B‖ < 1 →
        ‖(eU B C T).comp ((GU B C T).comp (eU B C T)) - HU B C‖ ≤ R * T := by
    simpa only [N, U, E, Q, dU, eU, GU, HU, PU, A, comp_assoc] using hn
  have hleft (T : ℝ) (hT : 0 < T) : (dV B C T).comp (eV B C T) = .id ℝ V := by
    have hh := congrArg (transport u) (hn'.1 T hT).1
    simpa only [transport_comp, hd, he, transport_id] using hh
  have hright (T : ℝ) (hT : 0 < T) : (eV B C T).comp (dV B C T) = .id ℝ V := by
    have hh := congrArg (transport u) (hn'.1 T hT).2.1
    simpa only [transport_comp, hd, he, transport_id] using hh
  have hrestore (T : ℝ) (hT : 0 < T) :
      (dV B C T).comp ((normalized B C T).comp (dV B C T)) = G B C T := by
    calc
      _ = ((dV B C T).comp (eV B C T)).comp
          ((G B C T).comp ((eV B C T).comp (dV B C T))) := by ext x; rfl
      _ = _ := by rw [hleft T hT, hright T hT, id_comp, comp_id]
  have hpos (x : V) (hx : x ≠ 0) : 0 < ⟪x, H B C x⟫_ℝ := by
    have hux : u.symm x ≠ 0 := by
      intro hz
      apply hx
      simpa only [u.apply_symm_apply, map_zero] using congrArg u hz
    have hp := hn'.2.1 (u.symm x) hux
    rw [← hH]
    simpa only [transport_apply, ← u.inner_map_map, u.apply_symm_apply] using hp
  obtain ⟨R, hR, herr⟩ := hn'.2.2
  let Rv := ‖transport u‖ * R
  have hRv : 0 ≤ Rv := mul_nonneg (norm_nonneg _) hR
  have hb (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hTB : T * ‖B‖ < 1) :
      ‖normalized B C T - H B C‖ ≤ Rv * T := by
    rw [← hnorm T, ← hH, ← map_sub]
    calc
      _ ≤ ‖transport u‖ * ‖(eU B C T).comp ((GU B C T).comp (eU B C T)) - HU B C‖ :=
        (transport u).le_opNorm _
      _ ≤ ‖transport u‖ * (R * T) := mul_le_mul_of_nonneg_left (herr T hT hT1 hTB) (norm_nonneg _)
      _ = Rv * T := by dsimp [Rv]; ring
  exact ⟨hQ, hd, he, hG, hH, hnorm, hleft, hright, hrestore, hpos,
    ⟨Rv, hRv, hb⟩, right_limit_of_bound _ _ B Rv hRv hb⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinates (b : OrthonormalBasis ι ℝ V) : (V →L[ℝ] V) →L[ℝ] Matrix ι ι ℝ :=
  (show (V →L[ℝ] V) →ₗ[ℝ] Matrix ι ι ℝ from
    { toFun := fun K => LinearMap.toMatrix b.toBasis b.toBasis K.toLinearMap
      map_add' := by intro K L; simp
      map_smul' := by intro c K; simp }).toContinuousLinearMap

theorem coordinates_comp (b : OrthonormalBasis ι ℝ V) (K L : V →L[ℝ] V) :
    coordinates b (K.comp L) = coordinates b K * coordinates b L := by
  exact LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis K.toLinearMap L.toLinearMap

theorem matrix_linear_error (b : OrthonormalBasis ι ℝ V)
    (B : V →L[ℝ] V) (C : V →L[ℝ] W) (hN : N B C (finrank ℝ V) = ⊥)
    (ht : TransportFacts B C hN) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T * ‖B‖ < 1 →
      ‖coordinates b (normalized B C T) - coordinates b (H B C)‖ ≤ R * T := by
  obtain ⟨R, hR, hb⟩ := ht.bound
  refine ⟨‖coordinates b‖ * R, mul_nonneg (norm_nonneg _) hR, ?_⟩
  intro T hT hT1 hTB
  rw [← map_sub]
  calc
    _ ≤ ‖coordinates b‖ * ‖normalized B C T - H B C‖ := (coordinates b).le_opNorm _
    _ ≤ ‖coordinates b‖ * (R * T) :=
      mul_le_mul_of_nonneg_left (hb T hT hT1 hTB) (norm_nonneg _)
    _ = (‖coordinates b‖ * R) * T := by ring

theorem matrix_integral_gram (b : OrthonormalBasis ι ℝ V)
    (f : ℝ → V →L[ℝ] W) (hf : Continuous f) (a c : ℝ) :
    coordinates b (∫ t in a..c, (f t).adjoint.comp (f t)) =
      fun i j => ∫ t in a..c, ⟪f t (b i), f t (b j)⟫_ℝ := by
  have hg : Continuous (fun t => (f t).adjoint.comp (f t)) :=
    (ContinuousLinearMap.adjoint.continuous.comp hf).clm_comp hf
  ext i j
  let L : (V →L[ℝ] V) →L[ℝ] ℝ :=
    (innerSL ℝ (b i)).comp (ContinuousLinearMap.apply ℝ V (b j))
  have hentry (K : V →L[ℝ] V) : coordinates b K i j = L K := by
    simp [coordinates, L, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]
  rw [hentry, ← L.intervalIntegral_comp_comm (hg.intervalIntegrable a c)]
  apply intervalIntegral.integral_congr
  intro t ht
  exact ContinuousLinearMap.adjoint_inner_right (f t) (b i) (f t (b j))

theorem action_gram {a c : Type} [Fintype a] [DecidableEq a]
    [Fintype c] [DecidableEq c] (M : Matrix a c ℝ) :
    D5.S3.Observer.Linear.GaussianObservationLaw.action (M.transpose * M) =
      (D5.S3.Observer.Linear.GaussianObservationLaw.action M).adjoint.comp
        (D5.S3.Observer.Linear.GaussianObservationLaw.action M) := by
  rw [D5.S3.Observer.Linear.GaussianObservationLaw.action_adjoint]
  ext x
  simp only [D5.S3.Observer.Linear.GaussianObservationLaw.action_apply,
    comp_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

theorem matrix_limit_posDef (b : OrthonormalBasis ι ℝ V)
    (B : V →L[ℝ] V) (C : V →L[ℝ] W) (hN : N B C (finrank ℝ V) = ⊥)
    (ht : TransportFacts B C hN) :
    (coordinates b (H B C)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [H, matrix_integral_gram b (P B C) (continuous_P B C)]
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, real_inner_comm]
  · intro x hx
    let v : V := b.repr.symm (WithLp.toLp 2 x)
    have hv : v ≠ 0 := by
      intro hz
      have hh := congrArg b.repr hz
      have hxx : x = 0 := by
        ext i
        simpa only [v, b.repr.apply_symm_apply, map_zero, PiLp.toLp_apply, WithLp.ofLp_zero, Pi.zero_apply] using
          congrArg (fun y : EuclideanSpace ℝ ι => y i) hh
      exact hx hxx
    have hrepr : (fun i => b.toBasis.repr v i) = x := by
      ext i
      simp [v, OrthonormalBasis.coe_toBasis_repr_apply]
    have hmul : (coordinates b (H B C)).mulVec x = fun i => b.repr (H B C v) i := by
      simpa only [coordinates, hrepr, OrthonormalBasis.coe_toBasis_repr_apply] using
        LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis (H B C).toLinearMap v
    have hq := b.repr.inner_map_map v (H B C v)
    have heq : x ⬝ᵥ (coordinates b (H B C)).mulVec x = ⟪v, H B C v⟫_ℝ := by
      rw [hmul]
      simpa only [v, b.repr.apply_symm_apply, EuclideanSpace.inner_eq_star_dotProduct,
        WithLp.ofLp_toLp, star_trivial] using hq
    simpa only [star_trivial, heq] using ht.positive v hv

-- The same isometry also transports the ONE chosen frame. This equality is
-- consumed at the determinant and exposes precisely which native matrix is used.
theorem frame_transport (B : V →L[ℝ] V) (C : V →L[ℝ] W)
    (hN : N B C (finrank ℝ V) = ⊥) (b : OrthonormalBasis ι ℝ V)
    (K : U B C →L[ℝ] U B C) :
    let u := inclusionIsometry B C hN
    let bU := b.map u.symm
    LinearMap.toMatrix bU.toBasis bU.toBasis K.toLinearMap =
      coordinates b (transport u K) := by
  intro u bU
  ext i j
  simp only [coordinates, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.map_apply, transport_apply]
  exact (u.inner_map_map (u.symm (b i)) (K (u.symm (b j)))).symm.trans
    (by rw [u.apply_symm_apply])

-- Exact physical determinant transport, with every native layer kept.
-- The premise N(n)=0 is supplied by actual jet injectivity at both sensors.
theorem physical_determinant_limit (B : V →L[ℝ] V) (C : V →L[ℝ] W)
    (hN : N B C (finrank ℝ V) = ⊥) (bstd : OrthonormalBasis ι ℝ V) :
    let q := ∑ j : Fin (finrank ℝ V), (2 * (j : ℕ) + 1) * finrank ℝ (E B C j)
    ∃ b : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V,
      let u := inclusionIsometry B C hN
      let bU := b.map u.symm
      let Hnative := fun T => LinearMap.toMatrix bU.toBasis bU.toBasis
        ((eU B C T).comp ((GU B C T).comp (eU B C T))).toLinearMap
      (∀ T : ℝ, 0 < T → (coordinates bstd (G B C T)).det / T ^ q = (Hnative T).det) ∧
      Tendsto Hnative (𝓝[>] (0 : ℝ)) (𝓝 (coordinates b (H B C))) ∧
      (∀ T : ℝ, (LinearMap.toMatrix bU.toBasis bU.toBasis (GU B C T).toLinearMap).det =
        (coordinates bstd (G B C T)).det) ∧
      (LinearMap.toMatrix bU.toBasis bU.toBasis (HU B C).toLinearMap).det =
        (coordinates bstd (H B C)).det ∧
      (coordinates b (H B C)).det = (coordinates bstd (H B C)).det ∧
      Tendsto (fun T => (coordinates bstd (G B C T)).det / T ^ q)
        (𝓝[>] (0 : ℝ)) (𝓝 (coordinates bstd (H B C)).det) := by
  classical
  intro q
  have ht := native_to_ambient B C hN
  have hf := D5.S3.Observer.Linear.DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation_facts B.toLinearMap C.toLinearMap
  have horth : OrthogonalFamily ℝ (fun j : Fin (finrank ℝ V) => E B C j)
      (fun j => (E B C j).subtypeₗᵢ) := by simpa only [E, N] using hf.2.2.1
  have hspan : (⨆ j : Fin (finrank ℝ V), E B C j) = ⊤ := by
    have hs : N B C (finrank ℝ V) ⊔ (⨆ j : Fin (finrank ℝ V), E B C j) = ⊤ :=
      hf.2.2.2.1
    simpa only [hN, bot_sup_eq] using hs
  have hint : DirectSum.IsInternal (fun j : Fin (finrank ℝ V) => E B C j) :=
    horth.isInternal_iff.mpr (by rw [hspan]; simp)
  let b := hint.subordinateOrthonormalBasis rfl horth
  let grade : Fin (finrank ℝ V) → Fin (finrank ℝ V) :=
    fun i => hint.subordinateOrthonormalBasisIndex rfl i horth
  let w : Fin (finrank ℝ V) → ℕ := fun i => (grade i : ℕ)
  have hbmem (i : Fin (finrank ℝ V)) : b i ∈ E B C (grade i) :=
    hint.subordinateOrthonormalBasis_subordinate rfl i horth
  have hcard (j : Fin (finrank ℝ V)) :
      (Finset.univ.filter (fun i => grade i = j)).card = finrank ℝ (E B C j) :=
    hint.card_filter_subordinateOrthonormalBasisIndex_eq rfl horth j
  have hpair : Pairwise (fun i j : Fin (finrank ℝ V) => E B C i ⟂ E B C j) := by
    exact orthogonalFamily_iff_pairwise.mp horth
  have hproject (j i : Fin (finrank ℝ V)) :
      (E B C j).starProjection (b i) = if j = grade i then b i else 0 := by
    by_cases hji : j = grade i
    · subst j
      simp only [ite_true]
      exact (E B C (grade i)).starProjection_eq_self_iff.mpr (hbmem i)
    · have ho : b i ∈ (E B C j)ᗮ :=
        (Submodule.isOrtho_iff_le.mp (hpair hji).symm) (hbmem i)
      simp only [hji, if_false, Submodule.starProjection_apply,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal ho, Submodule.coe_zero]
  have hdBasis (T : ℝ) (i : Fin (finrank ℝ V)) :
      dV B C T (b i) = (Real.sqrt T * T ^ w i) • b i := by
    simp only [dV, sum_apply, smul_apply, hproject]
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, w]
  let D (T : ℝ) : Matrix (Fin (finrank ℝ V)) (Fin (finrank ℝ V)) ℝ :=
    Matrix.diagonal (fun i => Real.sqrt T * T ^ w i)
  have hdM (T : ℝ) : coordinates b (dV B C T) = D T := by
    ext i j
    simp [coordinates, LinearMap.toMatrix_apply, hdBasis, D, Matrix.diagonal, eq_comm]
  have hq : (∑ i, (2 * w i + 1)) = q := by
    calc
      _ = ∑ i : Fin (finrank ℝ V), ∑ j : Fin (finrank ℝ V),
          if grade i = j then 2 * (j : ℕ) + 1 else 0 := by simp [w]
      _ = ∑ j : Fin (finrank ℝ V), ∑ i : Fin (finrank ℝ V),
          if grade i = j then 2 * (j : ℕ) + 1 else 0 := Finset.sum_comm
      _ = q := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_filter]
        simp [hcard, Nat.mul_comm, q]
  have hdetD (T : ℝ) (hT : 0 < T) : (D T).det * (D T).det = T ^ q := by
    simp only [D, Matrix.det_diagonal]
    rw [← Finset.prod_mul_distrib]
    calc
      _ = ∏ i : Fin (finrank ℝ V), T ^ (2 * w i + 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hp : T ^ (2 * w i + 1) = T ^ w i * T ^ w i * T := by
          rw [show 2 * w i + 1 = w i + w i + 1 by omega]
          simp only [pow_add, pow_one]
        rw [hp]
        calc
          _ = (Real.sqrt T * Real.sqrt T) * (T ^ w i * T ^ w i) := by ring
          _ = _ := by rw [Real.mul_self_sqrt hT.le]; ring
      _ = T ^ (∑ i, (2 * w i + 1)) := Finset.prod_pow_eq_pow_sum _ _ T
      _ = T ^ q := by rw [hq]
  let u := inclusionIsometry B C hN
  let bU := b.map u.symm
  let Hnative (T : ℝ) := LinearMap.toMatrix bU.toBasis bU.toBasis
    ((eU B C T).comp ((GU B C T).comp (eU B C T))).toLinearMap
  have hHM (T : ℝ) : Hnative T = coordinates b (normalized B C T) := by
    rw [Hnative, frame_transport, ht.normalization]
  have hlim : Tendsto Hnative (𝓝[>] (0 : ℝ)) (𝓝 (coordinates b (H B C))) := by
    simpa only [hHM] using ((coordinates b).continuous.tendsto (H B C)).comp ht.limit
  have hdetbasis (K : V →L[ℝ] V) : (coordinates b K).det = (coordinates bstd K).det := by
    simp only [coordinates, LinearMap.det_toMatrix]
  have hGUframe (T : ℝ) : LinearMap.toMatrix bU.toBasis bU.toBasis (GU B C T).toLinearMap =
      coordinates b (G B C T) := by
    rw [frame_transport, ht.physical]
  have hHUframe : LinearMap.toMatrix bU.toBasis bU.toBasis (HU B C).toLinearMap =
      coordinates b (H B C) := by
    rw [frame_transport, ht.polynomial]
  have hGdet (T : ℝ) :
      (LinearMap.toMatrix bU.toBasis bU.toBasis (GU B C T).toLinearMap).det =
        (coordinates bstd (G B C T)).det := by rw [hGUframe, hdetbasis]
  have hHdet : (LinearMap.toMatrix bU.toBasis bU.toBasis (HU B C).toLinearMap).det =
      (coordinates bstd (H B C)).det := by rw [hHUframe, hdetbasis]
  have hexact (T : ℝ) (hT : 0 < T) :
      (coordinates bstd (G B C T)).det / T ^ q = (Hnative T).det := by
    have hrestore := congrArg (coordinates b) (ht.restore T hT)
    have hm : coordinates b (G B C T) = D T * Hnative T * D T := by
      simpa only [coordinates_comp,
        ← hHM T, hdM, Matrix.mul_assoc] using hrestore.symm
    rw [← hGdet T, hGUframe T, hm, Matrix.det_mul, Matrix.det_mul]
    have hn : T ^ q ≠ 0 := pow_ne_zero _ hT.ne'
    calc
      (D T).det * (Hnative T).det * (D T).det / T ^ q =
          ((D T).det * (D T).det) * (Hnative T).det / T ^ q := by ring
      _ = (Hnative T).det := by rw [hdetD T hT]; field_simp
  have hdetlim : Tendsto (fun T => (Hnative T).det) (𝓝[>] (0 : ℝ))
      (𝓝 (coordinates bstd (H B C)).det) := by
    have hnativeLimit : Tendsto Hnative (𝓝[>] (0 : ℝ))
        (𝓝 (LinearMap.toMatrix bU.toBasis bU.toBasis (HU B C).toLinearMap)) := by
      rw [hHUframe]
      exact hlim
    rw [← hHdet]
    exact ((continuous_id.matrix_det).tendsto _).comp hnativeLimit
  refine ⟨b, hexact, hlim, hGdet, hHdet, hdetbasis _, ?_⟩
  apply hdetlim.congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (hexact T hT).symm

end Original8899NativeAmbient
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Filter Set Module ContinuousLinearMap
open scoped BigOperators ENNReal Topology InnerProductSpace RealInnerProductSpace
namespace Original63SourceOnly

open D5.S3.Observer.Linear

abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Window (p : ℕ) (T : ℝ) := Lp (V p) 2 (volume.restrict (Ioc 0 T))

variable {d p : ℕ}

def kernels (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p) (j : ℕ) : Submodule ℝ (V d) :=
  ⨅ k : Fin j, LinearMap.ker (C.toLinearMap.comp (B.toLinearMap ^ (k : ℕ)))

def layer (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p) (j : ℕ) : Submodule ℝ (V d) :=
  kernels B C j ⊓ (kernels B C (j + 1))ᗮ

def multiplicity (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p) (j : ℕ) : ℕ :=
  finrank ℝ (layer B C j)

def depthSpec (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p) (m : ℕ) : Prop :=
  kernels B C (m + 1) = ⊥ ∧ ∀ j < m, kernels B C (j + 1) ≠ ⊥

def physicalG (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p) (T : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  let b := Matrix.toEuclideanLin.symm B.toLinearMap
  let c := Matrix.toEuclideanLin.symm C.toLinearMap
  ∫ t in (0 : ℝ)..T, NormedSpace.exp (t • b.transpose) * c.transpose * c *
    NormedSpace.exp (t • b)

def observable (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p) : Prop :=
  ∀ x, (∀ k : Fin d, C ((B ^ (k : ℕ)) x) = 0) → x = 0

-- These choices use the actual trajectory supplier, never a Gramian square root.
def trajectoryF (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p)
    (hobs : observable B C) (T : ℝ) (hT : 0 < T) : V d →L[ℝ] Window p T :=
  Classical.choose (ObservableTrajectoryCoordinates.observable_trajectory_coordinates_all_bases d p B C T hT hobs)

def trajectoryM (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p)
    (hobs : observable B C) (T : ℝ) (hT : 0 < T)
    (b : OrthonormalBasis (Fin d) ℝ (trajectoryF B C hobs T hT).range) :
    Matrix (Fin d) (Fin d) ℝ :=
  Classical.choose (Classical.choose_spec
    ((Classical.choose_spec
      (ObservableTrajectoryCoordinates.observable_trajectory_coordinates_all_bases d p B C T hT hobs)).2.2.2 b))

def trajectoryFamily (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p)
    (hobs : observable B C)
    (basis : ∀ T (hT : 0 < T),
      OrthonormalBasis (Fin d) ℝ (trajectoryF B C hobs T hT).range) :
    ℝ → Matrix (Fin d) (Fin d) ℝ :=
  fun T => if hT : 0 < T then trajectoryM B C hobs T hT (basis T hT) else 0

-- Arbitrary supplied ON polynomial families, with no prescribed degrees or signs.
def polynomialON (m : ℕ) (ell : Fin (m + 1) → Polynomial ℝ) : Prop :=
  (∀ k, (ell k).degree ≤ (m : WithBot ℕ)) ∧
  ∀ k l, (∫ s in (0 : ℝ)..1, (ell k).eval s * (ell l).eval s) =
    if k = l then 1 else 0

abbrev MomentIndex (m p : ℕ) := Fin (m + 1) × Fin p

def momentM (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p)
    (m : ℕ) (ell : Fin (m + 1) → Polynomial ℝ) (T : ℝ) :
    Matrix (MomentIndex m p) (Fin d) ℝ :=
  fun kr j => (Real.sqrt T)⁻¹ * ∫ t in (0 : ℝ)..T,
    (ell kr.1).eval (t / T) *
      (C ((NormedSpace.exp (t • B)) (EuclideanSpace.basisFun (Fin d) ℝ j))) kr.2

def momentG (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p)
    (m : ℕ) (ell : Fin (m + 1) → Polynomial ℝ) (T : ℝ) :
    Matrix (Fin d) (Fin d) ℝ := (momentM B C m ell T).transpose * momentM B C m ell T

variable {a : Type} [Fintype a] [DecidableEq a]

def loss (x z : V d) : ℝ≥0∞ := ENNReal.ofReal (‖x - z‖ ^ 2 / 2)

def estimatorRisk (M : Matrix a (Fin d) ℝ) (β v : ℝ)
    (est : EuclideanSpace ℝ a → V d) : ℝ≥0∞ :=
  ∫⁻ z, loss z.2 (est z.1) ∂GaussianObservationLaw.jointLaw M β v⁻¹

def bayesRisk (M : Matrix a (Fin d) ℝ) (β v : ℝ) : ℝ≥0∞ :=
  ⨅ est : {f : EuclideanSpace ℝ a → V d // Measurable f}, estimatorRisk M β v est.1

def information (M : Matrix a (Fin d) ℝ) (β v : ℝ) : ℝ :=
  (GaussianObservationLaw.mutualInformation M β v⁻¹).toReal

def quadraticLaw (M : Matrix a (Fin d) ℝ) (β v : ℝ) : Prop :=
  let S := GaussianObservationLaw.covariance M β v⁻¹
  let A := GaussianObservationLaw.action (GaussianObservationLaw.gain M β v⁻¹)
  (∀ est : EuclideanSpace ℝ a → V d, Measurable est →
    estimatorRisk M β v est = ENNReal.ofReal (Matrix.trace S / 2) +
      ∫⁻ y, loss (A y) (est y) ∂GaussianObservationLaw.dataLaw M β v⁻¹) ∧
  estimatorRisk M β v A = ENNReal.ofReal (Matrix.trace S / 2) ∧
  bayesRisk M β v = ENNReal.ofReal (Matrix.trace S / 2)

-- This is an actual joint-law conclusion on any supplied probability space.
-- No covariance-only equality or assumed risk identity is a premise.
def independentRealization (M : Matrix a (Fin d) ℝ) (β σ : ℝ) : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → V d) (xi : Ω → EuclideanSpace ℝ a),
    Measurable X → Measurable xi → IndepFun X xi P →
    P.map X = multivariateGaussian 0 (β⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) →
    P.map xi = multivariateGaussian 0 (1 : Matrix a a ℝ) →
    P.map (fun w => (GaussianObservationLaw.action M (X w) + σ • xi w, X w)) =
      GaussianObservationLaw.jointLaw M β (σ ^ 2)⁻¹

-- The same all-measurable risk statement on the SUPPLIED probability space.
-- In particular, no finite-risk or L2 premise is imposed on the competitor.
def realizedQuadraticLaw (M : Matrix a (Fin d) ℝ) (β σ : ℝ) : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → V d) (xi : Ω → EuclideanSpace ℝ a),
    Measurable X → Measurable xi → IndepFun X xi P →
    P.map X = multivariateGaussian 0 (β⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) →
    P.map xi = multivariateGaussian 0 (1 : Matrix a a ℝ) →
    let Y := fun ω => GaussianObservationLaw.action M (X ω) + σ • xi ω
    let A := GaussianObservationLaw.action (GaussianObservationLaw.gain M β (σ ^ 2)⁻¹)
    let S := GaussianObservationLaw.covariance M β (σ ^ 2)⁻¹
    (∀ est : EuclideanSpace ℝ a → V d, Measurable est →
      (∫⁻ ω, loss (X ω) (est (Y ω)) ∂P) = ENNReal.ofReal (Matrix.trace S / 2) +
        ∫⁻ ω, loss (A (Y ω)) (est (Y ω)) ∂P) ∧
    (∫⁻ ω, loss (X ω) (A (Y ω)) ∂P) = ENNReal.ofReal (Matrix.trace S / 2) ∧
    (⨅ est : {f : EuclideanSpace ℝ a → V d // Measurable f},
      ∫⁻ ω, loss (X ω) (est.1 (Y ω)) ∂P) = ENNReal.ofReal (Matrix.trace S / 2)

def finiteExperiment (M : Matrix a (Fin d) ℝ) (β σ : ℝ) : Prop :=
  independentRealization M β σ ∧ quadraticLaw M β (σ ^ 2) ∧
  GaussianObservationLaw.mutualInformation M β (σ ^ 2)⁻¹ ≠ ∞ ∧
  information M β (σ ^ 2) =
    Real.log ((1 + ((β * σ ^ 2)⁻¹) • (M.transpose * M)).det) / 2 ∧
  GaussianObservationLaw.jointLaw M β (σ ^ 2)⁻¹ =
    GaussianObservationLaw.dataLaw M β (σ ^ 2)⁻¹ ⊗ₘ GaussianObservationLaw.posteriorKernel M β (σ ^ 2)⁻¹ ∧
  realizedQuadraticLaw M β σ

-- All FOUR clauses, simultaneously, for the actual matrix family in each branch.
def noiseConclusion (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p)
    (m : ℕ) (M : ℝ → Matrix a (Fin d) ℝ) (β : ℝ) : Prop :=
  (∀ α : ℝ,
    (fun T : ℝ => information (M T) β (T ^ α) -
      (1 / 2 : ℝ) * (∑ j : Fin (m + 1),
        (multiplicity B C j : ℝ) * max (α - (2 * (j : ℕ) + 1 : ℕ)) 0) *
          Real.log (1 / T)) =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
  (∀ α : ℝ,
    (∀ j : Fin (m + 1), 0 < multiplicity B C j → α ≠ (2 * (j : ℕ) + 1 : ℕ)) →
    Tendsto (fun T : ℝ => (bayesRisk (M T) β (T ^ α)).toReal)
      (𝓝[>] 0) (𝓝 ((1 / (2 * β)) * ∑ j : Fin (m + 1),
        if α < (2 * (j : ℕ) + 1 : ℕ) then (multiplicity B C j : ℝ) else 0))) ∧
  (∀ v : ℝ → ℝ, (∀ T, 0 < T → 0 < v T) →
    (Tendsto (fun T => (bayesRisk (M T) β (v T)).toReal) (𝓝[>] 0) (𝓝 0) ↔
      v =o[𝓝[>] 0] (fun T => T ^ (2 * m + 1)))) ∧
  (∀ η : ℝ, 0 < η →
    (fun T => information (M T) β η -
      T / (2 * β * η) * Matrix.trace
        ((Matrix.toEuclideanLin.symm C.toLinearMap).transpose *
          Matrix.toEuclideanLin.symm C.toLinearMap))
      =O[𝓝[>] 0] (fun T : ℝ => T ^ 2))

-- The L2 moment map and its integral representatives must be supplied as conclusions.
def actualMomentCoordinates (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p)
    (hobs : observable B C) (m : ℕ) (ell : Fin (m + 1) → Polynomial ℝ) : Prop :=
  ∀ T (hT : 0 < T), ∃ Q : Window p T →L[ℝ] EuclideanSpace ℝ (MomentIndex m p),
    (∀ g, ‖Q g‖ ≤ ‖g‖) ∧
    (∀ g kr, Q g kr = (Real.sqrt T)⁻¹ * ∫ t in (0 : ℝ)..T,
      (ell kr.1).eval (t / T) * (g t) kr.2) ∧
    (∀ (g : Window p T) (kr : MomentIndex m p), IntervalIntegrable (fun t : ℝ =>
      (ell kr.1).eval (t / T) * (g t) kr.2) volume 0 T) ∧
    Q.comp (trajectoryF B C hobs T hT) = GaussianObservationLaw.action (momentM B C m ell T) ∧
    (∀ x, GaussianObservationLaw.action (momentM B C m ell T) x =
      (Real.sqrt T)⁻¹ • ∫ t in (0 : ℝ)..T,
        (WithLp.toLp 2 (fun kr : MomentIndex m p =>
          (ell kr.1).eval (t / T) * (C ((NormedSpace.exp (t • B)) x)) kr.2)))

-- The actual 5.3 normalized operator estimate, with the SAME polynomial
-- limit as the trajectory. Finite-time equality Gmom=G is never asserted.
def normalizedMomentApproximation (B : V d →L[ℝ] V d) (C : V d →L[ℝ] V p)
    (m : ℕ) (ell : Fin (m + 1) → Polynomial ℝ) : Prop :=
  let e : ℝ → V d →L[ℝ] V d := fun T =>
    ∑ j : Fin d, (Real.sqrt T * T ^ (j : ℕ))⁻¹ • (layer B C j).starProjection
  let F0 : ℝ → V d →L[ℝ] V p := fun s =>
    ∑ j : Fin d, (s ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
      C.comp ((B ^ (j : ℕ)).comp (layer B C j).starProjection)
  (fun T => (e T).comp ((GaussianObservationLaw.action (momentG B C m ell T)).comp (e T)) -
    ∫ s in (0 : ℝ)..1, (F0 s).adjoint.comp (F0 s)) =O[𝓝[>] 0] (fun T : ℝ => T)


private theorem actualExperiment (n : ℕ) (β : ℝ) (hβ : 0 < β)
    {i : Type} [Fintype i] [DecidableEq i]
    (M : Matrix i (Fin (n + 1)) ℝ) (σ : ℝ) (hσ : 0 < σ ^ 2) :
    finiteExperiment M β σ := by
  classical
  have hgaussianSquared {i : Type} [Fintype i] [DecidableEq i]
      (S : Matrix i i ℝ) (hS : S.PosSemidef) (u z : EuclideanSpace ℝ i) :
      (∫⁻ x, ENNReal.ofReal (‖x - z‖ ^ 2 / 2) ∂multivariateGaussian u S) =
        ENNReal.ofReal (Matrix.trace S / 2 + ‖u - z‖ ^ 2 / 2) := by
    let ν := multivariateGaussian u S
    have hcoord (k : i) : MemLp (fun x : EuclideanSpace ℝ i => x k) 2 ν :=
      ((IsGaussian.hasGaussianLaw_id (μ := ν)).map_fun (EuclideanSpace.proj k)).memLp_two
    have hmean (k : i) : (∫ x : EuclideanSpace ℝ i, x k ∂ν) = u k := by
      calc
        (∫ x : EuclideanSpace ℝ i, x k ∂ν) =
            (EuclideanSpace.proj k) (∫ x : EuclideanSpace ℝ i, x ∂ν) :=
          (EuclideanSpace.proj k).integral_comp_comm IsGaussian.integrable_id
        _ = u k := by rw [integral_id_multivariateGaussian]; rfl
    have hsq (k : i) : (∫ x : EuclideanSpace ℝ i, (x k - z k) ^ 2 ∂ν) =
        S k k + (u k - z k) ^ 2 := by
      have hL2 : MemLp (fun x : EuclideanSpace ℝ i => x k - z k) 2 ν :=
        (hcoord k).sub (memLp_const _)
      have hv := variance_eq_sub hL2
      rw [variance_sub_const (hcoord k).aestronglyMeasurable,
        variance_eval_multivariateGaussian hS,
        integral_sub ((hcoord k).integrable (by norm_num)) (integrable_const _), hmean] at hv
      simpa only [integral_const, measureReal_univ_eq_one, one_smul] using
        (eq_add_of_sub_eq hv.symm)
    have hInt : Integrable (fun x : EuclideanSpace ℝ i => ‖x - z‖ ^ 2 / 2) ν := by
      simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, Pi.sub_apply] using
        (integrable_finsetSum Finset.univ (fun k _ =>
          ((hcoord k).sub (memLp_const (z k))).integrable_sq)).div_const 2
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (ae_of_all _ (fun x => div_nonneg (sq_nonneg _) (by norm_num)))]
    congr 1
    simp_rw [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
    rw [integral_div, integral_finsetSum _ (fun k _ =>
      ((hcoord k).sub (memLp_const (z k))).integrable_sq)]
    simp_rw [hsq]
    simp [Matrix.trace, Finset.sum_add_distrib, add_div]

  have hrisk {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (v : ℝ) (hv : 0 < v) : quadraticLaw M β v := by
    let σ := Real.sqrt v
    have hσ : σ ^ 2 = v := Real.sq_sqrt hv.le
    have hL := GaussianObservationLaw.gaussian_observation_law_complete M β σ hβ (by rwa [hσ])
    simp only [hσ] at hL
    let S := GaussianObservationLaw.covariance M β v⁻¹
    let A := GaussianObservationLaw.action (GaussianObservationLaw.gain M β v⁻¹)
    have hS : S.PosDef := (GaussianObservationLaw.precision_posDef M β v⁻¹ hβ (inv_pos.mpr hv).le).inv
    have htrace : 0 ≤ Matrix.trace S :=
      Finset.sum_nonneg (fun k _ => hS.posSemidef.diag_nonneg (i := k))
    have hdis : GaussianObservationLaw.jointLaw M β v⁻¹ =
        GaussianObservationLaw.dataLaw M β v⁻¹ ⊗ₘ GaussianObservationLaw.posteriorKernel M β v⁻¹ := hL.1.2.2.2.2.2.2.1
    have hcond (y : EuclideanSpace ℝ i) : GaussianObservationLaw.posteriorKernel M β v⁻¹ y =
        multivariateGaussian (A y) S := by
      rw [GaussianObservationLaw.posteriorKernel, GaussianObservationLaw.translatedKernel_apply, GaussianObservationLaw.translate_gaussian, add_zero]
    have hdecomp (est : EuclideanSpace ℝ i → V (n + 1)) (hest : Measurable est) :
        estimatorRisk M β v est = ENNReal.ofReal (Matrix.trace S / 2) +
          ∫⁻ y, loss (A y) (est y) ∂GaussianObservationLaw.dataLaw M β v⁻¹ := by
      unfold estimatorRisk
      rw [hdis, Measure.lintegral_compProd (by unfold loss; fun_prop)]
      simp_rw [hcond, loss, hgaussianSquared S hS.posSemidef]
      simp_rw [ENNReal.ofReal_add (div_nonneg htrace (by norm_num))
        (div_nonneg (sq_nonneg _) (by norm_num))]
      rw [lintegral_add_left measurable_const]
      simp
    have hattain : estimatorRisk M β v A = ENNReal.ofReal (Matrix.trace S / 2) := by
      rw [hdecomp A (by fun_prop)]
      simp [loss]
    refine ⟨hdecomp, hattain, le_antisymm ?_ ?_⟩
    · exact (iInf_le_of_le ⟨A, by fun_prop⟩ le_rfl).trans_eq hattain
    · apply le_iInf
      intro est
      rw [hdecomp est.1 est.2]
      exact le_self_add

  have hrealization {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (σ : ℝ) (hσ : 0 < σ ^ 2) :
      independentRealization M β σ := by
    intro Ω _ P _ X xi hX hxi hind hXlaw hxilaw
    let ν := P.map (fun ω => σ • xi ω)
    have hind' : IndepFun X (fun ω => σ • xi ω) P :=
      hind.comp measurable_id (by fun_prop)
    have hproduct := hind'.map_prod_eq_prod_map_map hX.aemeasurable (by fun_prop)
    have hcanon := GaussianObservationLaw.gaussian_observation_law_complete M β σ hβ hσ
    have hindcanon := hcanon.1.2.2.2.2.2.2.2.2.2
    have hcanonicalProduct := hindcanon.map_prod_eq_prod_map_map
      (by fun_prop) (by fun_prop)
    have hν : ν = multivariateGaussian 0 ((σ ^ 2) • (1 : Matrix i i ℝ)) := by
      dsimp [ν]
      rw [← Measure.map_map (by fun_prop) hxi, hxilaw]
      have hmap := GaussianObservationLaw.map_gaussian (0 : EuclideanSpace ℝ i) (1 : Matrix i i ℝ)
        Matrix.PosSemidef.one (σ • (1 : Matrix i i ℝ))
      simpa [GaussianObservationLaw.action, Matrix.smul_mul, Matrix.mul_smul, pow_two] using hmap
    have hinputProduct : (GaussianObservationLaw.inputLaw (n := Fin (n + 1)) (p := i) β (σ ^ 2)⁻¹).map
        (fun z => (GaussianObservationLaw.action GaussianObservationLaw.signal z, GaussianObservationLaw.action GaussianObservationLaw.noise z)) =
        (P.map X).prod ν := by
      rw [hcanonicalProduct, hcanon.1.2.2.2.2.2.2.2.1,
        hcanon.1.2.2.2.2.2.2.2.2.1, hXlaw, hν, inv_inv]
    have hpush := congrArg
      (fun μ : Measure (V (n + 1) × EuclideanSpace ℝ i) =>
        μ.map (fun z => (GaussianObservationLaw.action M z.1 + z.2, z.1)))
      (hproduct.trans hinputProduct.symm)
    simp only [Measure.map_map (by fun_prop) (by fun_prop)] at hpush
    simpa [GaussianObservationLaw.jointLaw, GaussianObservationLaw.action_apply, GaussianObservationLaw.observation, GaussianObservationLaw.signal, GaussianObservationLaw.noise,
      Matrix.fromCols_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec] using hpush

  have hexperiment {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (σ : ℝ) (hσ : 0 < σ ^ 2) : finiteExperiment M β σ := by
    have h := GaussianObservationLaw.gaussian_observation_law_complete M β σ hβ hσ
    have hq := hrisk M (σ ^ 2) hσ
    refine ⟨hrealization M σ hσ, hq, h.1.1, ?_, ?_, ?_⟩
    · simpa [information, mul_inv_rev, div_eq_mul_inv, mul_comm] using h.1.2.2.2.2.1
    · exact h.1.2.2.2.2.2.2.1
    · intro Ω _ P _ X xi hX hxi hind hXlaw hxilaw
      let Y : Ω → EuclideanSpace ℝ i := fun ω =>
        GaussianObservationLaw.action M (X ω) + σ • xi ω
      let A := GaussianObservationLaw.action (GaussianObservationLaw.gain M β (σ ^ 2)⁻¹)
      let S := GaussianObservationLaw.covariance M β (σ ^ 2)⁻¹
      have hY : Measurable Y := by fun_prop
      have hpair : Measurable (fun ω => (Y ω, X ω)) := hY.prodMk hX
      have hj : P.map (fun ω => (Y ω, X ω)) =
          GaussianObservationLaw.jointLaw M β (σ ^ 2)⁻¹ :=
        hrealization M σ hσ Ω P X xi hX hxi hind hXlaw hxilaw
      have hy : P.map Y = GaussianObservationLaw.dataLaw M β (σ ^ 2)⁻¹ := by
        calc
          P.map Y = (P.map (fun ω => (Y ω, X ω))).map Prod.fst :=
            (Measure.map_map measurable_fst hpair).symm
          _ = (GaussianObservationLaw.jointLaw M β (σ ^ 2)⁻¹).map Prod.fst := by rw [hj]
          _ = GaussianObservationLaw.dataLaw M β (σ ^ 2)⁻¹ := by
            simp only [GaussianObservationLaw.jointLaw, GaussianObservationLaw.dataLaw,
              Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      have hr (est : EuclideanSpace ℝ i → V (n + 1)) (he : Measurable est) :
          (∫⁻ ω, loss (X ω) (est (Y ω)) ∂P) = estimatorRisk M β (σ ^ 2) est := by
        change _ = ∫⁻ z, loss z.2 (est z.1) ∂GaussianObservationLaw.jointLaw M β (σ ^ 2)⁻¹
        rw [← hj, lintegral_map (by unfold loss; fun_prop) hpair]
      have he (est : EuclideanSpace ℝ i → V (n + 1)) (he : Measurable est) :
          (∫⁻ y, loss (A y) (est y) ∂GaussianObservationLaw.dataLaw M β (σ ^ 2)⁻¹) =
            ∫⁻ ω, loss (A (Y ω)) (est (Y ω)) ∂P := by
        rw [← hy, lintegral_map (by unfold loss; fun_prop) hY]
      refine ⟨?_, ?_, ?_⟩
      · intro est hest
        rw [hr est hest, hq.1 est hest, he est hest]
      · rw [hr A (by fun_prop)]
        exact hq.2.1
      · calc
          (⨅ est : {f : EuclideanSpace ℝ i → V (n + 1) // Measurable f},
              ∫⁻ ω, loss (X ω) (est.1 (Y ω)) ∂P) = bayesRisk M β (σ ^ 2) := by
            unfold bayesRisk
            congr 1
            funext est
            exact hr est.1 est.2
          _ = ENNReal.ofReal (Matrix.trace S / 2) := hq.2.2

  exact hexperiment M σ hσ

private theorem actualFrame (n r m : ℕ)
    (B : V (n + 1) →L[ℝ] V (n + 1)) (C : V (n + 1) →L[ℝ] V (r + 1))
    (hobs : observable B C) (hm : depthSpec B C m) :
    ∃ (b : OrthonormalBasis (Fin (n + 1)) ℝ (V (n + 1))) (w : Fin (n + 1) → ℕ),
      m ≤ n ∧ Monotone w ∧ (∀ i, w i ≤ m) ∧ w (Fin.last n) = m ∧
      (∀ j : Fin (n + 1), (Finset.univ.filter (fun i => w i = (j : ℕ))).card = multiplicity B C j) ∧
      (∀ j i : Fin (n + 1), (layer B C j).starProjection (b i) =
        if (j : ℕ) = w i then b i else 0) := by
  classical
  have hlayers := DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation_facts B.toLinearMap C.toLinearMap
  have hnative := DerivativeLayerNativeGramian.derivative_layer_native_gramian B.toLinearMap C.toLinearMap
  have hN : kernels B C (n + 1) = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply hobs x
      intro k
      have hk := (Submodule.mem_iInf _).mp hx k
      simpa [kernels, LinearMap.mem_ker, LinearMap.comp_apply] using hk
    · exact bot_le
  have hnest {j k : ℕ} (hjk : j ≤ k) : kernels B C k ≤ kernels B C j := by
    intro x hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    exact (Submodule.mem_iInf _).mp hx ⟨i, lt_of_lt_of_le i.isLt hjk⟩
  have horth : OrthogonalFamily ℝ (fun j : Fin (n + 1) => layer B C j)
      (fun j => (layer B C j).subtypeₗᵢ) := by
    simpa [kernels, layer] using hlayers.2.2.1
  have hspan : (⨆ j : Fin (n + 1), layer B C j) = ⊤ := by
    have hs := hlayers.2.2.2.1
    simpa [kernels, layer, hN] using hs
  have hinternal : DirectSum.IsInternal (fun j : Fin (n + 1) => layer B C j) :=
    horth.isInternal_iff.mpr (by rw [hspan]; simp)
  have hdim : finrank ℝ (V (n + 1)) = n + 1 := by simp [V]
  let b0 := hinternal.subordinateOrthonormalBasis hdim horth
  let w0 : Fin (n + 1) → ℕ := fun i =>
    (hinternal.subordinateOrthonormalBasisIndex hdim i horth : ℕ)
  let perm := Tuple.sort w0
  let w := w0 ∘ perm
  let b := b0.reindex perm.symm
  have hw : Monotone w := Tuple.monotone_sort w0
  have hcard (j : Fin (n + 1)) :
      (Finset.univ.filter (fun i => w i = (j : ℕ))).card = multiplicity B C j := by
    have hf := hinternal.card_filter_subordinateOrthonormalBasisIndex_eq hdim horth j
    have hf0 : (Finset.univ.filter (fun i => w0 i = (j : ℕ))).card =
        multiplicity B C j := by
      simpa only [w0, multiplicity, Fin.val_inj] using hf
    have hp := Fintype.card_congr
      (perm.subtypeEquiv (p := fun i => w i = (j : ℕ))
        (q := fun i => w0 i = (j : ℕ)) (fun i => Iff.rfl))
    have hc : (Finset.univ.filter (fun i => w i = (j : ℕ))).card =
        (Finset.univ.filter (fun i => w0 i = (j : ℕ))).card := by
      simpa only [Fintype.card_subtype, Finset.card_univ] using hp
    exact hc.trans hf0

  have hmn : m ≤ n := by
    by_contra h
    have hbad := hm.2 n (by omega)
    exact hbad hN
  have habove {j : ℕ} (hj : m < j) : layer B C j = ⊥ := by
    apply le_antisymm
    · exact inf_le_left.trans ((hnest (Nat.succ_le_of_lt hj)).trans_eq hm.1)
    · exact bot_le
  have hwm (i : Fin (n + 1)) : w0 i ≤ m := by
    by_contra h
    have hmem := hinternal.subordinateOrthonormalBasis_subordinate hdim i horth
    have hz := habove (Nat.lt_of_not_ge h)
    have hbzero : b0 i = 0 := by
      simpa only [b0, w0, hz, Submodule.mem_bot] using hmem
    have hbnonzero : b0 i ≠ 0 := b0.orthonormal.ne_zero i
    exact hbnonzero hbzero
  have hEm : layer B C m ≠ ⊥ := by
    have hNm : kernels B C m ≠ ⊥ := by
      by_cases hm0 : m = 0
      · subst m
        simp [kernels]
      · have hh := hm.2 (m - 1) (by omega)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hh
    simpa [layer, hm.1] using hNm
  have hlast : w (Fin.last n) = m := by
    have hupper : w (Fin.last n) ≤ m := hwm (perm (Fin.last n))
    rcases hinternal.exists_subordinateOrthonormalBasisIndex_eq hdim horth
      (i := (⟨m, by omega⟩ : Fin (n + 1))) hEm with ⟨i, hi⟩
    have hwi : w (perm.symm i) = m := by
      simp only [w, Function.comp_apply, Equiv.apply_symm_apply, w0, hi]
    exact le_antisymm hupper (hwi ▸ hw (Fin.le_last (perm.symm i)))

  have hpair : Pairwise (fun j k : Fin (n + 1) => layer B C j ⟂ layer B C k) := by
    intro j k hjk
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjk) with hlt | hlt
    · apply Submodule.isOrtho_iff_le.mpr
      exact (le_trans inf_le_right (Submodule.orthogonal_le
        (hnest (Nat.succ_le_of_lt hlt)))).trans
          (Submodule.orthogonal_le inf_le_left)
    · apply Submodule.isOrtho_comm.mpr
      apply Submodule.isOrtho_iff_le.mpr
      exact (le_trans inf_le_right (Submodule.orthogonal_le
        (hnest (Nat.succ_le_of_lt hlt)))).trans
          (Submodule.orthogonal_le inf_le_left)
  let grade : Fin (n + 1) → Fin (n + 1) := fun i =>
    hinternal.subordinateOrthonormalBasisIndex hdim (perm i) horth
  have hgrade (i : Fin (n + 1)) : (grade i : ℕ) = w i := rfl
  have hbmem (i : Fin (n + 1)) : b i ∈ layer B C (grade i) := by
    simpa only [b, b0, OrthonormalBasis.coe_reindex, Equiv.symm_symm] using
      hinternal.subordinateOrthonormalBasis_subordinate hdim (perm i) horth
  have hproject (j i : Fin (n + 1)) :
      (layer B C j).starProjection (b i) = if j = grade i then b i else 0 := by
    by_cases hji : j = grade i
    · subst j
      simpa using (layer B C (grade i)).starProjection_eq_self_iff.mpr (hbmem i)
    · have ho : b i ∈ (layer B C j)ᗮ :=
        (Submodule.isOrtho_iff_le.mp (hpair hji).symm) (hbmem i)
      simp only [hji, if_false, Submodule.starProjection_apply,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal ho, Submodule.coe_zero]
  refine ⟨b, w, hmn, hw, (fun i => hwm (perm i)), hlast, hcard, ?_⟩
  intro j i
  simpa only [← hgrade i, Fin.val_inj] using hproject j i

private theorem actualScalarStatistics (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ (V (n + 1)))
     {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ)
      (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : G.PosDef)
      (hcoordinates : G = LinearMap.toMatrix b.toBasis b.toBasis
        (GaussianObservationLaw.action (M.transpose * M)).toLinearMap)
      (v : ℝ) (hv : 0 < v) :
      let lam := fun j => hG.isHermitian.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin (n + 1))).symm j)
      information M β v = (1 / 2 : ℝ) * ∑ j, Real.log (1 + lam j / (β * v)) ∧
      (bayesRisk M β v).toReal = (1 / 2 : ℝ) * ∑ j, v / (β * v + lam j) := by
  classical
  have hexperiment {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (σ : ℝ) (hσ : 0 < σ ^ 2) : finiteExperiment M β σ :=
    actualExperiment n β hβ M σ hσ
  have hrisk {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (v : ℝ) (hv : 0 < v) : quadraticLaw M β v := by
    have hh := (hexperiment M (Real.sqrt v) (by rwa [Real.sq_sqrt hv.le])).2.1
    simpa only [Real.sq_sqrt hv.le] using hh
  intro lam
  let std := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let P := std.toBasis.toMatrix b
  have hPtP : P.transpose * P = 1 := by
    simpa only [P, Matrix.conjTranspose_eq_transpose_of_trivial] using
      std.toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hPPt : P * P.transpose = 1 := by
    simpa only [P, Matrix.conjTranspose_eq_transpose_of_trivial] using
      std.toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hcoord : G = P.transpose * (M.transpose * M) * P := by
    rw [hcoordinates]
    ext j k
    simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply,
      P, std, Basis.toMatrix_apply, GaussianObservationLaw.action_apply,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply, dotProduct,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hrestore : M.transpose * M = P * G * P.transpose := by
    rw [hcoord]
    symm
    calc
      P * (P.transpose * (M.transpose * M) * P) * P.transpose =
          (P * P.transpose) * (M.transpose * M) * (P * P.transpose) := by noncomm_ring
      _ = M.transpose * M := by rw [hPPt]; simp
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := hG.isHermitian.eigenvectorUnitary
  let R := P * U
  let ev := hG.isHermitian.eigenvalues
  have hUtU : U.transpose * U = 1 := by
    simpa only [U, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hG.isHermitian.eigenvectorUnitary
  have hUUt : U * U.transpose = 1 := mul_eq_one_comm.mp hUtU
  have hRtR : R.transpose * R = 1 := by
    simp only [R, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P.transpose, hPtP, Matrix.one_mul, hUtU]
  have hRRt : R * R.transpose = 1 := mul_eq_one_comm.mp hRtR
  have hdiag : M.transpose * M = R * Matrix.diagonal ev * R.transpose := by
    rw [hrestore, hG.isHermitian.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, R, U, ev, Matrix.transpose_mul,
      Matrix.mul_assoc]
  have hconj (a c : ℝ) :
      a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) + c • (M.transpose * M) =
        R * Matrix.diagonal (fun j => a + c * ev j) * R.transpose := by
    have hd : Matrix.diagonal (fun j => a + c * ev j) =
        a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) + c • Matrix.diagonal ev := by
      ext j k
      by_cases hjk : j = k <;> simp [Matrix.diagonal, hjk]
    rw [hd, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hRRt, ← hdiag]
  have hsum (f : ℝ → ℝ) : (∑ j, f (ev j)) = ∑ j, f (lam j) := by
    let ec : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
      (Fin.castOrderIso (Fintype.card_fin (n + 1))).toEquiv
    let ee : Fin (n + 1) ≃ Fin (n + 1) :=
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin (n + 1))))).symm.trans ec
    apply Fintype.sum_equiv ee
    intro j
    simp only [ev, lam, Matrix.IsHermitian.eigenvalues, ee, ec,
      Equiv.trans_apply, Equiv.apply_symm_apply]
  have hepos (j : Fin (n + 1)) : 0 < ev j := hG.eigenvalues_pos j
  have hdetR : R.det * R.transpose.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hRRt
  have hdet : (1 + ((β * v)⁻¹) • (M.transpose * M)).det =
      ∏ j, (1 + ev j / (β * v)) := by
    have hc := hconj 1 ((β * v)⁻¹)
    simp only [one_smul] at hc
    rw [hc, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    calc
      R.det * (∏ j, (1 + (β * v)⁻¹ * ev j)) * R.transpose.det =
          (∏ j, (1 + ev j / (β * v))) * (R.det * R.transpose.det) := by
            simp only [div_eq_mul_inv, mul_comm ((β * v)⁻¹)]
            ring
      _ = _ := by rw [hdetR, mul_one]
  have hprec : GaussianObservationLaw.precision M β v⁻¹ =
      R * Matrix.diagonal (fun j => β + v⁻¹ * ev j) * R.transpose := hconj β v⁻¹
  have hden (j : Fin (n + 1)) : β + v⁻¹ * ev j ≠ 0 :=
    (add_pos hβ (mul_pos (inv_pos.mpr hv) (hepos j))).ne'
  have hcov : GaussianObservationLaw.covariance M β v⁻¹ =
      R * Matrix.diagonal (fun j => (β + v⁻¹ * ev j)⁻¹) * R.transpose := by
    unfold GaussianObservationLaw.covariance
    apply Matrix.inv_eq_right_inv
    rw [hprec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R.transpose, hRtR, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    have hh : Matrix.diagonal (fun j => (β + v⁻¹ * ev j) * (β + v⁻¹ * ev j)⁻¹) = 1 := by
      ext j k
      simp [Matrix.diagonal, hden]
    rw [hh, Matrix.one_mul, hRRt]
  have htrace : Matrix.trace (GaussianObservationLaw.covariance M β v⁻¹) =
      ∑ j, v / (β * v + ev j) := by
    rw [hcov, Matrix.trace_mul_cycle, Matrix.mul_assoc, hRtR, Matrix.mul_one,
      Matrix.trace_diagonal]
    apply Finset.sum_congr rfl
    intro j _
    have hd : β * v + ev j ≠ 0 := (add_pos (mul_pos hβ hv) (hepos j)).ne'
    field_simp [hv.ne', hden j, hd]
    ring
  constructor
  · have hI := (hexperiment M (Real.sqrt v) (by rwa [Real.sq_sqrt hv.le])).2.2.2.1
    simp only [Real.sq_sqrt hv.le] at hI
    rw [hI, hdet, Real.log_prod (fun j _ =>
      (by positivity : (1 + ev j / (β * v)) ≠ 0)), hsum]
    ring
  · have hq := (hrisk M v hv).2.2
    have htr : 0 ≤ Matrix.trace (GaussianObservationLaw.covariance M β v⁻¹) := by
      rw [htrace]
      exact Finset.sum_nonneg (fun j _ => by positivity)
    rw [hq, ENNReal.toReal_ofReal (div_nonneg htr (by norm_num)), htrace, hsum]
    ring


def gramEigenvalues {n : ℕ} {k : Type} [Fintype k] [DecidableEq k]
    (M : Matrix k (Fin (n + 1)) ℝ) : Fin (n + 1) → ℝ :=
  (show (M.transpose * M).IsHermitian from
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian)).eigenvalues₀ ∘
        (Fin.castOrderIso (Fintype.card_fin (n + 1))).symm

private theorem actualCanonicalSpectrum (n : ℕ)
    {k : Type} [Fintype k] [DecidableEq k]
    (b : OrthonormalBasis (Fin (n + 1)) ℝ (V (n + 1)))
    (M : Matrix k (Fin (n + 1)) ℝ)
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : G.PosDef)
    (hcoord : G = LinearMap.toMatrix b.toBasis b.toBasis
      (GaussianObservationLaw.action (M.transpose * M)).toLinearMap) :
    (fun j => hG.isHermitian.eigenvalues₀
      ((Fin.castOrderIso (Fintype.card_fin (n + 1))).symm j)) = gramEigenvalues M := by
  classical
  let std := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let P := std.toBasis.toMatrix b
  have hPPt : P * P.transpose = 1 := by
    simpa only [P, Matrix.conjTranspose_eq_transpose_of_trivial] using
      std.toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hc : G = P.transpose * (M.transpose * M) * P := by
    rw [hcoord]
    ext j k
    simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply,
      P, std, Basis.toMatrix_apply, GaussianObservationLaw.action_apply,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply, dotProduct,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hchar : G.charpoly = (M.transpose * M).charpoly := by
    rw [hc, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hPPt, Matrix.one_mul]
  have hK : (M.transpose * M).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian
  have he : hG.isHermitian.eigenvalues₀ = hK.eigenvalues₀ := by
    apply List.ofFn_inj.mp
    rw [← hG.isHermitian.sort_roots_charpoly_eq_eigenvalues₀,
      ← hK.sort_roots_charpoly_eq_eigenvalues₀, hchar]
  funext j
  exact congrFun he _


-- One graded-congruence proof is consumed for each actual family. Its only
-- analytic input is convergence of that family's normalized actual Gramian.
private theorem actualSpectrum (n r : ℕ)
    (B : V (n + 1) →L[ℝ] V (n + 1)) (C : V (n + 1) →L[ℝ] V (r + 1))
    (hobs : observable B C)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ (V (n + 1)))
    (w : Fin (n + 1) → ℕ) (hw : Monotone w)
    (hproject : ∀ j i : Fin (n + 1), (layer B C j).starProjection (b i) =
      if (j : ℕ) = w i then b i else 0)
    (hwn : ∀ i, w i < n + 1)
    {k : Type} [Fintype k] [DecidableEq k]
    (M : ℝ → Matrix k (Fin (n + 1)) ℝ) (β : ℝ) (hβ : 0 < β)
    (hlimit :
      let e : ℝ → V (n + 1) →L[ℝ] V (n + 1) := fun T =>
        ∑ j : Fin (n + 1), (Real.sqrt T * T ^ (j : ℕ))⁻¹ • (layer B C j).starProjection
      let F0 : ℝ → V (n + 1) →L[ℝ] V (r + 1) := fun s =>
        ∑ j : Fin (n + 1), (s ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
          C.comp ((B ^ (j : ℕ)).comp (layer B C j).starProjection)
      Tendsto (fun T => (e T).comp
        ((GaussianObservationLaw.action ((M T).transpose * M T)).comp (e T)))
        (𝓝[>] 0) (𝓝 (∫ s in (0 : ℝ)..1, (F0 s).adjoint.comp (F0 s)))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ i,
        c * T ^ (2 * w i + 1) ≤ gramEigenvalues (M T) i ∧
        gramEigenvalues (M T) i ≤ C * T ^ (2 * w i + 1)) ∧
      (∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ v : ℝ, 0 < v →
        information (M T) β v = (1 / 2 : ℝ) *
          ∑ i, Real.log (1 + gramEigenvalues (M T) i / (β * v)) ∧
        (bayesRisk (M T) β v).toReal = (1 / 2 : ℝ) *
          ∑ i, v / (β * v + gramEigenvalues (M T) i)) := by
  classical
  let e : ℝ → V (n + 1) →L[ℝ] V (n + 1) := fun T =>
    ∑ j : Fin (n + 1), (Real.sqrt T * T ^ (j : ℕ))⁻¹ • (layer B C j).starProjection
  let F0 : ℝ → V (n + 1) →L[ℝ] V (r + 1) := fun s =>
    ∑ j : Fin (n + 1), (s ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
      C.comp ((B ^ (j : ℕ)).comp (layer B C j).starProjection)
  let H0 := LinearMap.toMatrix b.toBasis b.toBasis
    (∫ s in (0 : ℝ)..1, (F0 s).adjoint.comp (F0 s)).toLinearMap
  let HM : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun T =>
    LinearMap.toMatrix b.toBasis b.toBasis
      ((e T).comp ((GaussianObservationLaw.action ((M T).transpose * M T)).comp (e T))).toLinearMap
  let D (T : ℝ) := Matrix.diagonal (fun i => T ^ w i * Real.sqrt T)
  have heBasis (T : ℝ) (i : Fin (n + 1)) :
      e T (b i) = (Real.sqrt T * T ^ w i)⁻¹ • b i := by
    simp only [e, sum_apply, smul_apply, hproject]
    rw [Finset.sum_eq_single (⟨w i, hwn i⟩ : Fin (n + 1))]
    · simp
    · intro j _ hj
      simp only [if_neg (by simpa only [Fin.ext_iff] using hj), smul_zero]
    · simp
  have heMatrix (T : ℝ) : LinearMap.toMatrix b.toBasis b.toBasis (e T).toLinearMap =
      Matrix.diagonal (fun i => (Real.sqrt T * T ^ w i)⁻¹) := by
    ext i j
    simp [LinearMap.toMatrix_apply, heBasis, Matrix.diagonal, eq_comm]
  have hrestore (T : ℝ) (hT : 0 < T)
      (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
      D T * LinearMap.toMatrix b.toBasis b.toBasis
        ((e T).comp ((GaussianObservationLaw.action K).comp (e T))).toLinearMap * D T =
        LinearMap.toMatrix b.toBasis b.toBasis (GaussianObservationLaw.action K).toLinearMap := by
    let E := Matrix.diagonal (fun i => (Real.sqrt T * T ^ w i)⁻¹)
    have hDE : D T * E = 1 := by
      rw [D, E, Matrix.diagonal_mul_diagonal]
      ext i j
      have hn : Real.sqrt T * T ^ w i ≠ 0 :=
        mul_ne_zero (Real.sqrt_pos.mpr hT).ne' (pow_pos hT _).ne'
      simp [Matrix.diagonal, mul_comm (T ^ w i), hn]
    have hED : E * D T = 1 := mul_eq_one_comm.mp hDE
    simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.toMatrix_comp,
      heMatrix]
    change D T * (E * _ * E) * D T = _
    calc
      D T * (E * _ * E) * D T = (D T * E) * _ * (E * D T) := by noncomm_ring
      _ = _ := by rw [hDE, hED]; simp
  have hlimitM : Tendsto HM (𝓝[>] 0) (𝓝 H0) := by
    exact ((Original8899NativeAmbient.coordinates b).continuous.tendsto _).comp hlimit
  have hNativeZero : Original8899NativeAmbient.N B C (finrank ℝ (V (n + 1))) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    apply hobs x
    intro k
    simpa [Original8899NativeAmbient.N, V, LinearMap.mem_ker, LinearMap.comp_apply] using
      (Submodule.mem_iInf _).mp hx k
  have hTransport := Original8899NativeAmbient.native_to_ambient B C hNativeZero
  have hH0 : H0.PosDef := by
    have hp := Original8899NativeAmbient.matrix_limit_posDef b B C hNativeZero hTransport
    simpa [Original8899NativeAmbient.coordinates, Original8899NativeAmbient.H,
      Original8899NativeAmbient.P, Original8899NativeAmbient.E,
      Original8899NativeAmbient.N, kernels, layer, V, H0, F0] using hp
  have hHMspsd (T : ℝ) : (HM T).PosSemidef := by
    let L := (GaussianObservationLaw.action (M T)).comp (e T)
    let R := LinearMap.toMatrix b.toBasis (EuclideanSpace.basisFun (MomentIndex m (r + 1)) ℝ).toBasis L.toLinearMap
    have he (T : ℝ) : (e T).adjoint = e T := by
      apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      intro x y
      simp only [e, sum_apply, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro j _
      rw [(layer B C j).inner_starProjection_left_eq_right]
    have hfactor : HM T = R.transpose * R := by
      rw [HM, ← GaussianObservationLaw.action_adjoint]
      simp only [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_adjoint,
        ← ContinuousLinearMap.adjoint_toContinuousLinearMap, adjoint_comp, he]
      rfl
    rw [hfactor]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self R
  have hposM : ∀ᶠ T in 𝓝[>] (0 : ℝ), (HM T).PosDef := by
    have hd : Tendsto (fun T => (HM T).det) (𝓝[>] 0) (𝓝 H0.det) :=
      continuous_id.matrix_det.tendsto H0 |>.comp hlimitM
    filter_upwards [hd.eventually (Ioi_mem_nhds hH0.det_pos)] with T hT
    exact (hHMspsd T).posDef_iff_det_ne_zero.mpr hT.ne'
  let HMP : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun T => if (HM T).PosDef then HM T else H0
  have hpatch : HMP =ᶠ[𝓝[>] 0] HM := by
    filter_upwards [hposM] with T hT
    simp only [HMP, if_pos hT]
  have hlimitMP : Tendsto HMP (𝓝[>] 0) (𝓝 H0) := hlimitM.congr' hpatch.symm
  have hposMP (T : ℝ) : (HMP T).PosDef := by
    by_cases h : (HM T).PosDef
    · simpa only [HMP, if_pos h] using h
    · simpa only [HMP, if_neg h] using hH0
  have hcongMP (T : ℝ) (hT : 0 < T) :
      (Matrix.diagonal (fun i => T ^ w i * Real.sqrt T) * HMP T *
        Matrix.diagonal (fun i => T ^ w i * Real.sqrt T)).PosDef := by
    let D := Matrix.diagonal (fun i => T ^ w i * Real.sqrt T)
    have hD : IsUnit D := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
        mul_ne_zero (pow_pos hT _).ne' (Real.sqrt_pos.mpr hT).ne')
    simpa [D, Matrix.star_eq_conjTranspose] using hD.posDef_star_right_conjugate_iff.mpr (hposMP T)
  have hspec := D5.S3.Observer.Linear.graded_congruence_spectrum
    HMP H0 w hw hlimitMP hH0 hcongMP
  obtain ⟨c, C', δ, hc, hC, hδ, hb⟩ := hspec
  have hcoord : ∀ᶠ T in 𝓝[>] (0 : ℝ),
      D T * HMP T * D T = LinearMap.toMatrix b.toBasis b.toBasis
        (GaussianObservationLaw.action ((M T).transpose * M T)).toLinearMap := by
    filter_upwards [self_mem_nhdsWithin, hpatch] with T hT hp
    rw [hp]
    exact hrestore T hT ((M T).transpose * M T)
  have hcan : ∀ᶠ T in 𝓝[>] (0 : ℝ),
      ∀ hT : 0 < T, (fun i => (hcongMP T hT).isHermitian.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin (n + 1))).symm i)) = gramEigenvalues (M T) := by
    filter_upwards [self_mem_nhdsWithin, hcoord] with T hT hct
    intro hT
    exact actualCanonicalSpectrum n b (M T) _ (hcongMP T hT) hct
  refine ⟨c, C', hc, hC, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin, eventually_lt_nhdsWithin hδ, hcan] with T hT hsmall hSpectrum
    intro i
    have hh := hb T i hT hsmall
    simpa only [← congrFun (hSpectrum hT) i] using hh
  · filter_upwards [self_mem_nhdsWithin, hcoord, hcan] with T hT hct hSpectrum
    intro v hv
    have hh := actualScalarStatistics n β hβ b (M T) _ (hcongMP T hT) hct v hv
    simpa only [hSpectrum hT] using hh


private theorem actualNoiseConclusion (n r m : ℕ)
    (B : V (n + 1) →L[ℝ] V (n + 1)) (C : V (n + 1) →L[ℝ] V (r + 1))
    (hmn : m ≤ n) (w : Fin (n + 1) → ℕ) (hw : Monotone w)
    (hwm : ∀ i, w i ≤ m) (hlast : w (Fin.last n) = m)
    (hcard : ∀ j : Fin (n + 1),
      (Finset.univ.filter (fun i => w i = (j : ℕ))).card = multiplicity B C j)
    {k : Type} [Fintype k] [DecidableEq k]
    (MT : ℝ → Matrix k (Fin (n + 1)) ℝ) (β : ℝ) (hβ : 0 < β)
    (cT CT : ℝ) (hcT : 0 < cT) (hCT : 0 < CT)
    (hbT : ∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ i,
      cT * T ^ (2 * w i + 1) ≤ gramEigenvalues (MT T) i ∧
      gramEigenvalues (MT T) i ≤ CT * T ^ (2 * w i + 1))
    (hstat : ∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ v : ℝ, 0 < v →
      information (MT T) β v = (1 / 2 : ℝ) *
        ∑ i, Real.log (1 + gramEigenvalues (MT T) i / (β * v)) ∧
      (bayesRisk (MT T) β v).toReal = (1 / 2 : ℝ) *
        ∑ i, v / (β * v + gramEigenvalues (MT T) i))
    (hfixedTrajectory : ∀ η : ℝ, 0 < η →
      (fun T => information (MT T) β η - T / (2 * β * η) *
        Matrix.trace ((Matrix.toEuclideanLin.symm C.toLinearMap).transpose *
          Matrix.toEuclideanLin.symm C.toLinearMap)) =O[𝓝[>] 0] (fun T : ℝ => T ^ 2)) :
    noiseConclusion B C m MT β := by
  classical
  let lamT := fun T => gramEigenvalues (MT T)
  let q : Fin (n + 1) → ℕ := fun i => 2 * w i + 1
  have hq : ∀ i, q i ≤ q (Fin.last n) := by
    intro i
    dsimp [q]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw (Fin.le_last i))) 1
  have hsT := SpectralNoiseAsymptotics.spectral_noise_asymptotics n q hq lamT cT CT β hcT hCT hβ hbT
  have hgroup (f : ℕ → ℝ) : (∑ i : Fin (n + 1), f (w i)) =
      ∑ j : Fin (m + 1), (multiplicity B C j : ℝ) * f j := by
    let index : Fin (n + 1) → Fin (m + 1) := fun i =>
      ⟨w i, Nat.lt_succ_of_le (hwm i)⟩
    have hfib := Finset.sum_fiberwise_of_maps_to'
      (s := (Finset.univ : Finset (Fin (n + 1))))
      (t := (Finset.univ : Finset (Fin (m + 1))))
      (g := index) (fun i _ => Finset.mem_univ (index i)) (fun j => f (j : ℕ))
    rw [← hfib]
    apply Finset.sum_congr rfl
    intro j _
    have hcj : (Finset.univ.filter (fun i => index i = j)).card = multiplicity B C j := by
      have hfilter : (Finset.univ.filter (fun i => index i = j)) =
          Finset.univ.filter (fun i => w i = (j : ℕ)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Fin.ext_iff
      rw [hfilter]
      exact hcard ⟨j, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) (by omega)⟩
    simp only [Finset.sum_const, nsmul_eq_mul, hcj]

  have hthreshold (α : ℝ)
      (hα : ∀ j : Fin (m + 1), 0 < multiplicity B C j → α ≠ (2 * (j : ℕ) + 1 : ℕ)) :
      ∀ i, α ≠ (q i : ℝ) := by
    intro i
    have hi : w i ≤ m := by simpa [hlast] using hw (Fin.le_last i)
    have hocc : 0 < multiplicity B C (w i) := by
      have hc := hcard ⟨w i, lt_of_le_of_lt hi (Nat.lt_succ_of_le hmn)⟩
      rw [← hc]
      apply Finset.card_pos.mpr
      exact ⟨i, by simp⟩
    simpa [q] using hα ⟨w i, Nat.lt_succ_of_le hi⟩ hocc

  unfold noiseConclusion
  refine ⟨?_, ?_, ?_, hfixedTrajectory⟩
  · intro α
    have hs := hsT.1 α
    have hg := hgroup (fun j => max (α - (2 * j + 1 : ℕ)) 0)
    refine hs.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hstat, self_mem_nhdsWithin] with T hstatT hT
    rw [← (hstatT (T ^ α) (Real.rpow_pos_of_pos hT α)).1]
    simp only [q, hg]
  · intro α hα
    have hs := hsT.2.2 α (hthreshold α hα)
    have hg := hgroup (fun j => if α < (2 * j + 1 : ℕ) then β⁻¹ else 0)
    have heq := hs.congr' (show
        (fun T : ℝ => (1 / 2 : ℝ) * ∑ i, T ^ α / (β * T ^ α + lamT T i)) =ᶠ[𝓝[>] 0]
        (fun T : ℝ => (bayesRisk (MT T) β (T ^ α)).toReal) by
      filter_upwards [hstat, self_mem_nhdsWithin] with T hstatT hT
      exact (hstatT (T ^ α) (Real.rpow_pos_of_pos hT α)).2.symm)
    convert heq using 1
    simp only [q, hg, Finset.mul_sum, mul_ite, mul_zero, mul_inv_rev]
    congr 1
    field_simp
    ring
  · intro v hv
    have hs := hsT.2.1 v hv
    have heq : (fun T => (bayesRisk (MT T) β (v T)).toReal) =ᶠ[𝓝[>] 0]
        (fun T => (1 / 2 : ℝ) * ∑ i, v T / (β * v T + lamT T i)) := by
      filter_upwards [hstat, self_mem_nhdsWithin] with T hstatT hT
      exact (hstatT (v T) (hv T hT)).2
    rw [tendsto_congr' heq]
    simpa only [q, hlast] using hs

private theorem actualTrajectory (n r m : ℕ)
    (B : V (n + 1) →L[ℝ] V (n + 1)) (C : V (n + 1) →L[ℝ] V (r + 1))
    (hobs : observable B C) (hm : depthSpec B C m)
    (β : ℝ) (hβ : 0 < β)
    (basis : ∀ T (hT : 0 < T), OrthonormalBasis (Fin (n + 1)) ℝ
      (trajectoryF B C hobs T hT).range) :
    let MT := trajectoryFamily B C hobs basis
    (∀ T (hT : 0 < T), (MT T).transpose * MT T = physicalG B C T ∧
      (∀ σ : ℝ, 0 < σ ^ 2 → finiteExperiment (MT T) β σ)) ∧
    noiseConclusion B C m MT β ∧
    ∃ w : Fin (n + 1) → ℕ, ∃ c C' : ℝ,
      Monotone w ∧ (∀ i, w i ≤ m) ∧ w (Fin.last n) = m ∧
      (∀ j : Fin (n + 1),
        (Finset.univ.filter (fun i => w i = (j : ℕ))).card = multiplicity B C j) ∧
      0 < c ∧ 0 < C' ∧
      (∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ i,
        c * T ^ (2 * w i + 1) ≤ gramEigenvalues (MT T) i ∧
        gramEigenvalues (MT T) i ≤ C' * T ^ (2 * w i + 1)) ∧
      (∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ v : ℝ, 0 < v →
        information (MT T) β v = (1 / 2 : ℝ) *
          ∑ i, Real.log (1 + gramEigenvalues (MT T) i / (β * v)) ∧
        (bayesRisk (MT T) β v).toReal = (1 / 2 : ℝ) *
          ∑ i, v / (β * v + gramEigenvalues (MT T) i)) := by
  classical
  intro MT
  have hexperiment {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (σ : ℝ) (hσ : 0 < σ ^ 2) : finiteExperiment M β σ :=
    actualExperiment n β hβ M σ hσ
  have hrisk {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (v : ℝ) (hv : 0 < v) : quadraticLaw M β v := by
    have hh := (hexperiment M (Real.sqrt v) (by rwa [Real.sq_sqrt hv.le])).2.1
    simpa only [Real.sq_sqrt hv.le] using hh
  have htrajectory (T : ℝ) (hT : 0 < T) :
      (MT T).transpose * MT T = physicalG B C T := by
    have hf := Classical.choose_spec
      (ObservableTrajectoryCoordinates.observable_trajectory_coordinates_all_bases (n + 1) (r + 1) B C T hT hobs)
    have hu := Classical.choose_spec (hf.2.2.2 (basis T hT))
    have hM := Classical.choose_spec hu
    simpa only [MT, trajectoryFamily, dif_pos hT, trajectoryM, physicalG] using
      hM.2.2.2.2.2.2.2.2

  obtain ⟨b, w, hmn, hw, hwm, hlast, hcard, hproject⟩ := actualFrame n r m B C hobs hm
  have hNativeZero : Original8899NativeAmbient.N B C (finrank ℝ (V (n + 1))) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    apply hobs x
    intro k
    simpa [Original8899NativeAmbient.N, V, LinearMap.mem_ker, LinearMap.comp_apply] using
      (Submodule.mem_iInf _).mp hx k
  have hTransport := Original8899NativeAmbient.native_to_ambient B C hNativeZero
  have hPhysicalIntegral (T : ℝ) (hT : 0 < T) :
      GaussianObservationLaw.action (physicalG B C T) = Original8899NativeAmbient.G B C T := by
    have hf := Classical.choose_spec
      (ObservableTrajectoryCoordinates.observable_trajectory_coordinates_all_bases
        (n + 1) (r + 1) B C T hT hobs)
    have hu := Classical.choose_spec (hf.2.2.2 (basis T hT))
    have hM := Classical.choose_spec hu
    have hMT : MT T = trajectoryM B C hobs T hT (basis T hT) := by
      simp only [MT, trajectoryFamily, dif_pos hT]
    rw [← htrajectory T hT, Original8899NativeAmbient.action_gram, hMT,
      hM.2.2.2.2.2.1]
    exact (hM.2.2.2.2.2.2.1).trans hM.2.2.2.2.2.2.2.1
  have hlimit :
      let e : ℝ → V (n + 1) →L[ℝ] V (n + 1) := fun T =>
        ∑ j : Fin (n + 1), (Real.sqrt T * T ^ (j : ℕ))⁻¹ • (layer B C j).starProjection
      let F0 : ℝ → V (n + 1) →L[ℝ] V (r + 1) := fun s =>
        ∑ j : Fin (n + 1), (s ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
          C.comp ((B ^ (j : ℕ)).comp (layer B C j).starProjection)
      Tendsto (fun T => (e T).comp
        ((GaussianObservationLaw.action ((MT T).transpose * MT T)).comp (e T)))
        (𝓝[>] 0) (𝓝 (∫ s in (0 : ℝ)..1, (F0 s).adjoint.comp (F0 s))) := by
    have heq : Original8899NativeAmbient.normalized B C =ᶠ[𝓝[>] (0 : ℝ)]
        (fun T => (Original8899NativeAmbient.eV B C T).comp
          ((GaussianObservationLaw.action ((MT T).transpose * MT T)).comp
            (Original8899NativeAmbient.eV B C T))) := by
      filter_upwards [self_mem_nhdsWithin] with T hT
      rw [htrajectory T hT, hPhysicalIntegral T hT]
      rfl
    have hh := hTransport.limit.congr' heq
    simpa [Original8899NativeAmbient.normalized, Original8899NativeAmbient.eV,
      Original8899NativeAmbient.H, Original8899NativeAmbient.P,
      Original8899NativeAmbient.E, Original8899NativeAmbient.N, kernels, layer, V] using hh
  obtain ⟨c, C', hc, hC, hb, hstat⟩ := actualSpectrum n r B C hobs b w hw hproject
    (fun i => lt_of_le_of_lt (hwm i) (Nat.lt_succ_of_le hmn)) MT β hβ hlimit
  have hfixedTrajectory : ∀ η : ℝ, 0 < η →
      (fun T => information (MT T) β η - T / (2 * β * η) *
        Matrix.trace ((Matrix.toEuclideanLin.symm C.toLinearMap).transpose *
          Matrix.toEuclideanLin.symm C.toLinearMap)) =O[𝓝[>] 0] (fun T : ℝ => T ^ 2) := by
    intro η hη
    rcases PhysicalFixedNoiseInformation.physical_fixed_noise_information B C β η hβ hη with ⟨K, δ, hK, hδ, hb⟩
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [self_mem_nhdsWithin, eventually_lt_nhdsWithin hδ] with T hT hTδ
    have hM := htrajectory T hT
    have hI := (hexperiment (MT T) (Real.sqrt η) (by rwa [Real.sq_sqrt hη.le])).2.2.2.1
    simpa [hI, Real.sq_sqrt hη.le, hM, physicalG, GaussianObservationLaw.action, LinearMap.trace_toMatrix,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T)] using hb T hT hTδ.le

  have hn := actualNoiseConclusion n r m B C hmn w hw hwm hlast hcard MT β hβ
    c C' hc hC hb hstat hfixedTrajectory
  exact ⟨(fun T hT => ⟨htrajectory T hT, fun σ hσ => hexperiment (MT T) σ hσ⟩),
    hn, w, c, C', hw, hwm, hlast, hcard, hc, hC, hb, hstat⟩

private theorem actualOriginal63 (n r m cutoff : ℕ)
    (B : V (n + 1) →L[ℝ] V (n + 1))
    (C : V (n + 1) →L[ℝ] V (r + 1))
    (hobs : observable B C) (hm : depthSpec B C m) (hcut : m ≤ cutoff)
    (ell : Fin (cutoff + 1) → Polynomial ℝ) (hell : polynomialON cutoff ell)
    (β : ℝ) (hβ : 0 < β)
    (basis : ∀ T (hT : 0 < T), OrthonormalBasis (Fin (n + 1)) ℝ
      (trajectoryF B C hobs T hT).range) :
    let MT := trajectoryFamily B C hobs basis
    let MM := momentM B C cutoff ell
    (∀ T (hT : 0 < T),
      (MT T).transpose * MT T = physicalG B C T ∧
      (∀ σ : ℝ, 0 < σ ^ 2 → finiteExperiment (MT T) β σ)) ∧
    actualMomentCoordinates B C hobs cutoff ell ∧
    normalizedMomentApproximation B C cutoff ell ∧
    (∀ T, 0 < T → ∀ σ : ℝ, 0 < σ ^ 2 → finiteExperiment (MM T) β σ) ∧
    noiseConclusion B C m MT β ∧ noiseConclusion B C m MM β := by
  classical
  intro MT MM
  have hexperiment {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (σ : ℝ) (hσ : 0 < σ ^ 2) : finiteExperiment M β σ :=
    actualExperiment n β hβ M σ hσ
  have hrisk {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) (v : ℝ) (hv : 0 < v) : quadraticLaw M β v := by
    have hh := (hexperiment M (Real.sqrt v) (by rwa [Real.sq_sqrt hv.le])).2.1
    simpa only [Real.sq_sqrt hv.le] using hh
  -- A supplied (cutoff+1)-element ON family spans EVERY polynomial of degree ≤cutoff.
  -- This proves the reproduction premise; it is not assumed from the word ON.
  have hpolyReconstruct (q : Polynomial ℝ) (hq : q.degree ≤ (cutoff : WithBot ℕ)) (s : ℝ) :
      q.eval s = ∑ k : Fin (cutoff + 1),
        (∫ t in (0 : ℝ)..1, (ell k).eval t * q.eval t) * (ell k).eval s := by
    let P := Polynomial.degreeLT ℝ (cutoff + 1)
    let l : Fin (cutoff + 1) → P := fun k =>
      ⟨ell k, Polynomial.mem_degreeLT.mpr (lt_of_le_of_lt (hell.1 k) (by exact_mod_cast Nat.lt_succ_self cutoff))⟩
    have hli : LinearIndependent ℝ l := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      funext k
      have heval (t : ℝ) : ∑ j : Fin (cutoff + 1), c j * (ell j).eval t = 0 := by
        simpa [l, Polynomial.eval_finset_sum, Polynomial.eval_smul, smul_eq_mul] using
          congrArg (fun z : P => (z : Polynomial ℝ).eval t) hc
      have hInt : (∫ t in (0 : ℝ)..1,
          (ell k).eval t * ∑ j : Fin (cutoff + 1), c j * (ell j).eval t) = c k := by
        simp_rw [Finset.mul_sum, ← mul_assoc, mul_comm ((ell k).eval _) (c _), mul_assoc]
        rw [intervalIntegral.integral_finsetSum (fun j _ =>
          (by fun_prop : Continuous (fun t : ℝ => c j * ((ell k).eval t * (ell j).eval t))).intervalIntegrable _ _)]
        simp_rw [intervalIntegral.integral_const_mul, hell.2]
        simp
      simpa only [heval, mul_zero, intervalIntegral.integral_zero] using hInt.symm
    let equiv := Polynomial.degreeLTEquiv ℝ (cutoff + 1)
    letI : FiniteDimensional ℝ P := equiv.finiteDimensional
    have hdimP : finrank ℝ P = cutoff + 1 := by simpa using equiv.finrank_eq
    let lb : Basis (Fin (cutoff + 1)) ℝ P := Basis.mk hli
      (hli.span_eq_top_of_card_eq_finrank' (by simpa using hdimP.symm)).ge
    let qp : P := ⟨q, Polynomial.mem_degreeLT.mpr
      (lt_of_le_of_lt hq (by exact_mod_cast Nat.lt_succ_self cutoff))⟩
    have hexpand (t : ℝ) : q.eval t = ∑ k : Fin (cutoff + 1),
        lb.repr qp k * (ell k).eval t := by
      have h := congrArg (fun z : P => (z : Polynomial ℝ).eval t) (lb.sum_repr qp)
      simpa [lb, l, qp, Polynomial.eval_finset_sum, Polynomial.eval_smul, smul_eq_mul] using h.symm
    have hcoeff (k : Fin (cutoff + 1)) :
        (∫ t in (0 : ℝ)..1, (ell k).eval t * q.eval t) = lb.repr qp k := by
      simp_rw [hexpand, Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        (by fun_prop : Continuous (fun t : ℝ => (ell k).eval t *
          (lb.repr qp j * (ell j).eval t))).intervalIntegrable _ _)]
      simp_rw [mul_left_comm, intervalIntegral.integral_const_mul, hell.2]
      simp
    simpa only [hcoeff] using hexpand s

  -- B: actual rectangular moment rows; this is pointwise operator transport.
  have hmomentAction (T : ℝ) (x : V (n + 1)) :
      GaussianObservationLaw.action (MM T) x = (Real.sqrt T)⁻¹ • ∫ t in (0 : ℝ)..T,
        WithLp.toLp 2 (fun kr : MomentIndex cutoff (r + 1) =>
          (ell kr.1).eval (t / T) * (C ((NormedSpace.exp (t • B)) x)) kr.2) := by
    ext kr
    rw [GaussianObservationLaw.action_apply]
    simp only [WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, MM, momentM]
    have hint (j : Fin (n + 1)) : IntervalIntegrable (fun t : ℝ =>
        (ell kr.1).eval (t / T) *
          (C ((NormedSpace.exp (t • B)) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j))) kr.2)
        volume 0 T := (by fun_prop : Continuous _).intervalIntegrable _ _
    simp_rw [mul_assoc, ← intervalIntegral.integral_mul_const]
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun j _ =>
      (hint j).mul_const (x j))]
    rw [← (EuclideanSpace.proj kr).intervalIntegral_comp_comm]
    congr 2
    funext t
    have hx : (∑ j : Fin (n + 1), x j • EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) = x := by
      ext k
      simp
    rw [← hx]
    simp [map_sum, map_smul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

  have hTfull := actualTrajectory n r m B C hobs hm β hβ basis
  have htrajectory (T : ℝ) (hT : 0 < T) :
      (MT T).transpose * MT T = physicalG B C T := (hTfull.1 T hT).1
  have hlayers := DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation_facts B.toLinearMap C.toLinearMap
  have hnative := DerivativeLayerNativeGramian.derivative_layer_native_gramian B.toLinearMap C.toLinearMap
  have hN : kernels B C (n + 1) = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply hobs x
      intro k
      have hk := (Submodule.mem_iInf _).mp hx k
      simpa [kernels, LinearMap.mem_ker, LinearMap.comp_apply] using hk
    · exact bot_le
  have hnest {j k : ℕ} (hjk : j ≤ k) : kernels B C k ≤ kernels B C j := by
    intro x hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    exact (Submodule.mem_iInf _).mp hx ⟨i, lt_of_lt_of_le i.isLt hjk⟩
  obtain ⟨b, w, hmn, hw, hwm, hlast, hcard, hproject⟩ := actualFrame n r m B C hobs hm
  -- F: construct the polynomial projection on the actual L2 window.
  -- The integral-action proof above feeds this branch, as do hell's degree and ON facts.
  have hmomCoordinates : actualMomentCoordinates B C hobs cutoff ell := by
    intro T hT
    let μ : Measure ℝ := volume.restrict (Ioc 0 T)
    have hphiLp (kr : MomentIndex cutoff (r + 1)) : MemLp (fun t : ℝ =>
        ((Real.sqrt T)⁻¹ * (ell kr.1).eval (t / T)) •
          EuclideanSpace.basisFun (Fin (r + 1)) ℝ kr.2) 2 μ := by
      have hc : Continuous (fun t : ℝ =>
          ((Real.sqrt T)⁻¹ * (ell kr.1).eval (t / T)) •
            EuclideanSpace.basisFun (Fin (r + 1)) ℝ kr.2) := by fun_prop
      obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn hc.continuousOn
      apply MemLp.of_bound hc.aestronglyMeasurable K
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hK t (Ioc_subset_Icc_self ht)
    let phi : MomentIndex cutoff (r + 1) → Window (r + 1) T := fun kr =>
      (hphiLp kr).toLp _
    have hphi : Orthonormal ℝ phi := by
      rw [orthonormal_iff_ite]
      intro kr ls
      have hinner : ⟪phi kr, phi ls⟫_ℝ =
          (Real.sqrt T)⁻¹ ^ 2 *
            (∫ t in (0 : ℝ)..T, (ell kr.1).eval (t / T) * (ell ls.1).eval (t / T)) *
              (if kr.2 = ls.2 then 1 else 0) := by
        rw [Lp.inner_def, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_mul_const, intervalIntegral.integral_of_le hT.le]
        apply integral_congr_ae
        filter_upwards [(hphiLp kr).coeFn_toLp, (hphiLp ls).coeFn_toLp] with t hkr hls
        simp only [phi] at *
        rw [hkr, hls]
        simp [real_inner_smul_left, real_inner_smul_right,
          EuclideanSpace.basisFun_inner, pow_two, mul_assoc, mul_left_comm, mul_comm]
      have hchange : (∫ t in (0 : ℝ)..T,
          (ell kr.1).eval (t / T) * (ell ls.1).eval (t / T)) =
            T * (if kr.1 = ls.1 then 1 else 0) := by
        simpa only [zero_div, div_self hT.ne', smul_eq_mul, hell.2] using
          (intervalIntegral.integral_comp_div
            (fun s : ℝ => (ell kr.1).eval s * (ell ls.1).eval s)
            (a := 0) (b := T) hT.ne')
      rw [hinner, hchange]
      have hs : (Real.sqrt T)⁻¹ ^ 2 * T = 1 := by
        rw [← inv_pow, Real.sq_sqrt hT.le, inv_mul_cancel₀ hT.ne']
      by_cases hk : kr.1 = ls.1 <;> by_cases hl : kr.2 = ls.2
      · have hkl : kr = ls := Prod.ext hk hl
        simp [hk, hl, hkl, ← mul_assoc, hs]
      · have hkl : kr ≠ ls := fun h => hl (congrArg Prod.snd h)
        simp [hk, hl, hkl]
      · have hkl : kr ≠ ls := fun h => hk (congrArg Prod.fst h)
        simp [hk, hl, hkl]
      · have hkl : kr ≠ ls := fun h => hk (congrArg Prod.fst h)
        simp [hk, hl, hkl]
    let Q : Window (r + 1) T →L[ℝ] EuclideanSpace ℝ (MomentIndex cutoff (r + 1)) :=
      { toLinearMap :=
          { toFun := fun g => WithLp.toLp 2 (fun kr => ⟪phi kr, g⟫_ℝ)
            map_add' := by intro x y; ext kr; simp [inner_add_right]
            map_smul' := by intro c x; ext kr; simp }
        cont := by
          apply LinearMap.continuous_of_bound _ 1
          intro g
          have hb := hphi.sum_inner_products_le (x := g) (s := Finset.univ)
          have hsq : ‖WithLp.toLp 2 (fun kr => ⟪phi kr, g⟫_ℝ)‖ ^ 2 ≤ ‖g‖ ^ 2 := by
            simpa [EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs] using hb
          simpa using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg g)).mp hsq }
    have hQintegral (g : Window (r + 1) T) (kr : MomentIndex cutoff (r + 1)) :
        Q g kr = (Real.sqrt T)⁻¹ * ∫ t in (0 : ℝ)..T,
          (ell kr.1).eval (t / T) * (g t) kr.2 := by
      change ⟪phi kr, g⟫_ℝ = _
      rw [Lp.inner_def, ← intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le hT.le]
      apply integral_congr_ae
      filter_upwards [(hphiLp kr).coeFn_toLp] with t ht
      rw [show phi kr t = _ from ht]
      simp [real_inner_smul_left, EuclideanSpace.basisFun_inner, mul_assoc]
    have hQint (g : Window (r + 1) T) (kr : MomentIndex cutoff (r + 1)) :
        IntervalIntegrable (fun t : ℝ => (ell kr.1).eval (t / T) * (g t) kr.2)
          volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
      have hi := (L2.integrable_inner (𝕜 := ℝ) (phi kr) g).const_mul (Real.sqrt T)
      apply hi.congr
      filter_upwards [(hphiLp kr).coeFn_toLp] with t ht
      rw [show phi kr t = _ from ht]
      simp [real_inner_smul_left, EuclideanSpace.basisFun_inner,
        ← mul_assoc, (Real.sqrt_pos.mpr hT).ne']
    have hjoin : Q.comp (trajectoryF B C hobs T hT) =
        GaussianObservationLaw.action (MM T) := by
      ext x kr
      rw [comp_apply, hQintegral, hmomentAction T x]
      have hrep := (Classical.choose_spec
        (ObservableTrajectoryCoordinates.observable_trajectory_coordinates_all_bases
          (n + 1) (r + 1) B C T hT hobs)).1 x
      have hInt : (∫ t in (0 : ℝ)..T, (ell kr.1).eval (t / T) *
          (trajectoryF B C hobs T hT x t) kr.2) =
          ∫ t in (0 : ℝ)..T, (ell kr.1).eval (t / T) *
            (C ((NormedSpace.exp (t • B)) x)) kr.2 := by
        rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le]
        apply integral_congr_ae
        filter_upwards [hrep] with t ht
        rw [ht]
      rw [hInt]
      rw [← (EuclideanSpace.proj kr).intervalIntegral_comp_comm
        ((by fun_prop : Continuous (fun t : ℝ =>
          WithLp.toLp 2 (fun kr : MomentIndex cutoff (r + 1) =>
            (ell kr.1).eval (t / T) * (C ((NormedSpace.exp (t • B)) x)) kr.2))).intervalIntegrable 0 T)]
      rfl
    refine ⟨Q, ?_, hQintegral, hQint, hjoin, hmomentAction T⟩
    · intro g
      have hb := hphi.sum_inner_products_le (x := g) (s := Finset.univ)
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg g)).mp
      simpa [Q, EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs] using hb

  have habove {j : ℕ} (hj : cutoff < j) : layer B C j = ⊥ := by
    apply le_antisymm
    · exact inf_le_left.trans ((hnest (by omega : m + 1 ≤ j)).trans_eq hm.1)
    · exact bot_le
  -- MOMENT SOURCE ATTEMPT (not elaborated): all helpers in this section are
  -- local to the original root and are consumed by its two moment conclusions.
  let μ₁ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hlift (A : ℝ → V (n + 1) →L[ℝ] V (r + 1)) (hA : Continuous A) :
      ∃ L : V (n + 1) →L[ℝ] Window (r + 1) 1,
        ∀ x, (fun s => L x s) =ᵐ[μ₁] fun s => A s x := by
    have hmem (x : V (n + 1)) : MemLp (fun s => A s x) 2 μ₁ := by
      have hc : Continuous (fun s => A s x) :=
        (ContinuousLinearMap.apply ℝ (V (r + 1)) x).continuous.comp hA
      obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
      apply MemLp.of_bound hc.aestronglyMeasurable K
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hK s (Ioc_subset_Icc_self hs)
    let l : V (n + 1) →ₗ[ℝ] Window (r + 1) 1 :=
      { toFun := fun x => (hmem x).toLp (fun s => A s x)
        map_add' := by
          intro x y
          calc
            (hmem (x + y)).toLp _ = ((hmem x).add (hmem y)).toLp _ := by
              apply MemLp.toLp_congr
              exact ae_of_all _ (fun s => map_add (A s) x y)
            _ = _ := MemLp.toLp_add _ _
        map_smul' := by
          intro c x
          calc
            (hmem (c • x)).toLp _ = ((hmem x).const_smul c).toLp _ := by
              apply MemLp.toLp_congr
              exact ae_of_all _ (fun s => map_smul (A s) c x)
            _ = _ := MemLp.toLp_const_smul c _ }
    exact ⟨⟨l, l.continuous_of_finiteDimensional⟩, fun x => (hmem x).coeFn_toLp⟩
  have hL2diff (A A' : ℝ → V (n + 1) →L[ℝ] V (r + 1))
      (L L' : V (n + 1) →L[ℝ] Window (r + 1) 1)
      (hL : ∀ x, (fun s => L x s) =ᵐ[μ₁] fun s => A s x)
      (hL' : ∀ x, (fun s => L' x s) =ᵐ[μ₁] fun s => A' s x)
      (K : ℝ) (hK : 0 ≤ K)
      (hb : ∀ s ∈ Icc (0 : ℝ) 1, ‖A s - A' s‖ ≤ K) : ‖L - L'‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro x
    have hn : ‖(L - L') x‖ ≤ K * ‖x‖ := by
      have h := Lp.norm_le_of_ae_bound (f := (L - L') x)
        (mul_nonneg hK (norm_nonneg x)) (by
          filter_upwards [Lp.coeFn_sub (L x) (L' x), hL x, hL' x,
            ae_restrict_mem measurableSet_Ioc] with s hsub hs hs' hsi
          change ‖((L x - L' x) : Window (r + 1) 1) s‖ ≤ _
          rw [hsub, hs, hs']
          exact ((A s - A' s).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hb s (Ioc_subset_Icc_self hsi)) (norm_nonneg x)))
      simpa [μ₁, measureUnivNNReal] using h
    exact hn
  obtain ⟨Q₁, hQ₁, hQ₁int, _, _, _⟩ := hmomCoordinates 1 zero_lt_one
  have hQformula (g : Window (r + 1) 1) (kr : MomentIndex cutoff (r + 1)) :
      Q₁ g kr = ∫ s in (0 : ℝ)..1, (ell kr.1).eval s * (g s) kr.2 := by
    simpa only [Real.sqrt_one, inv_one, div_one, one_mul] using hQ₁int g kr
  have hQlift (A : ℝ → V (n + 1) →L[ℝ] V (r + 1))
      (L : V (n + 1) →L[ℝ] Window (r + 1) 1)
      (hL : ∀ x, (fun s => L x s) =ᵐ[μ₁] fun s => A s x)
      (x : V (n + 1)) (kr : MomentIndex cutoff (r + 1)) :
      Q₁ (L x) kr = ∫ s in (0 : ℝ)..1, (ell kr.1).eval s * (A s x) kr.2 := by
    rw [hQformula, intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_of_le (by norm_num)]
    apply integral_congr_ae
    filter_upwards [hL x] with s hs
    rw [hs]
  -- Parseval on the actual supplied polynomial space. This uses every degree
  -- and ON assumption through hpolyReconstruct, without choosing a new family.
  have hQpolyGram (A : ℝ → V (n + 1) →L[ℝ] V (r + 1)) (hA : Continuous A)
      (L : V (n + 1) →L[ℝ] Window (r + 1) 1)
      (hL : ∀ x, (fun s => L x s) =ᵐ[μ₁] fun s => A s x)
      (hpoly : ∀ x a, ∃ q : Polynomial ℝ, q.degree ≤ (cutoff : WithBot ℕ) ∧
        ∀ s, q.eval s = (A s x) a) :
      (Q₁.comp L).adjoint.comp (Q₁.comp L) =
        ∫ s in (0 : ℝ)..1, (A s).adjoint.comp (A s) := by
    have hrepro (x : V (n + 1)) (a : Fin (r + 1)) (s : ℝ) :
        (A s x) a = ∑ k : Fin (cutoff + 1), Q₁ (L x) (k, a) * (ell k).eval s := by
      obtain ⟨q, hq, he⟩ := hpoly x a
      simpa only [he, hQlift A L hL] using hpolyReconstruct q hq s
    have hparseval (x y : V (n + 1)) :
        ⟪Q₁ (L x), Q₁ (L y)⟫_ℝ =
          ∫ s in (0 : ℝ)..1, ⟪A s x, A s y⟫_ℝ := by
      simp only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply, star_trivial]
      rw [intervalIntegral.integral_finsetSum (fun a _ =>
        (by fun_prop : Continuous (fun s : ℝ => (A s x) a * (A s y) a)).intervalIntegrable _ _)]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [hrepro x a, Finset.sum_mul]
      rw [intervalIntegral.integral_finsetSum (fun k _ =>
        (by fun_prop : Continuous (fun s : ℝ =>
          (Q₁ (L x) (k, a) * (ell k).eval s) * (A s y) a)).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_assoc, intervalIntegral.integral_const_mul, ← hQlift A L hL y (k, a)]
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℝ
    intro x
    rw [comp_apply, adjoint_inner_right, comp_apply, comp_apply, hparseval]
    let ev : (V (n + 1) →L[ℝ] V (n + 1)) →L[ℝ] ℝ :=
      (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ (V (n + 1)) y)
    have hi := ev.intervalIntegral_comp_comm
      (((ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp hA).intervalIntegrable 0 1)
    simpa only [ev, comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply,
      adjoint_inner_right] using hi
  have hgramDiff (R S : V (n + 1) →L[ℝ] EuclideanSpace ℝ (MomentIndex cutoff (r + 1))) :
      ‖R.adjoint.comp R - S.adjoint.comp S‖ ≤ (‖R‖ + ‖S‖) * ‖R - S‖ := by
    have he : R.adjoint.comp R - S.adjoint.comp S =
        R.adjoint.comp (R - S) + (R - S).adjoint.comp S := by
      simp only [map_sub, comp_sub, sub_comp]
      abel
    rw [he]
    calc
      _ ≤ ‖R.adjoint.comp (R - S)‖ + ‖(R - S).adjoint.comp S‖ := norm_add_le _ _
      _ ≤ ‖R.adjoint‖ * ‖R - S‖ + ‖(R - S).adjoint‖ * ‖S‖ :=
        add_le_add (norm_comp_le _ _) (norm_comp_le _ _)
      _ = _ := by simp only [ContinuousLinearMap.adjoint.norm_map]; ring
  have hactionGram {i : Type} [Fintype i] [DecidableEq i]
      (M : Matrix i (Fin (n + 1)) ℝ) :
      GaussianObservationLaw.action (M.transpose * M) =
        (GaussianObservationLaw.action M).adjoint.comp (GaussianObservationLaw.action M) := by
    rw [GaussianObservationLaw.action_adjoint]
    ext x
    simp only [comp_apply, GaussianObservationLaw.action_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec]
  let A : ℝ → ℝ → V (n + 1) →L[ℝ] V (r + 1) :=
    fun T s => C.comp (NormedSpace.exp ((T * s) • B))
  have hAc (T : ℝ) : Continuous (A T) := by
    have he : Continuous (NormedSpace.exp : (V (n + 1) →L[ℝ] V (n + 1)) →
        V (n + 1) →L[ℝ] V (n + 1)) :=
      continuous_iff_continuousAt.mpr (fun z => (NormedSpace.exp_analytic (𝕂 := ℝ) z).continuousAt)
    exact continuous_const.clm_comp (he.comp ((continuous_const.mul continuous_id).smul continuous_const))
  choose L hL using (fun T : ℝ => hlift (A T) (hAc T))
  have hunitMoment (T : ℝ) (hT : 0 < T) (x : V (n + 1))
      (kr : MomentIndex cutoff (r + 1)) :
      GaussianObservationLaw.action (MM T) x kr = Real.sqrt T *
        ∫ s in (0 : ℝ)..1, (ell kr.1).eval s * (A T s x) kr.2 := by
    have hv := congrArg (fun z : EuclideanSpace ℝ (MomentIndex cutoff (r + 1)) => z kr)
      (hmomentAction T x)
    have hi : IntervalIntegrable (fun t : ℝ =>
        WithLp.toLp 2 (fun ka : MomentIndex cutoff (r + 1) =>
          (ell ka.1).eval (t / T) * (C ((NormedSpace.exp (t • B)) x)) ka.2)) volume 0 T :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have hp := (EuclideanSpace.proj kr).intervalIntegral_comp_comm hi
    change (∫ t in (0 : ℝ)..T, (ell kr.1).eval (t / T) *
      (C ((NormedSpace.exp (t • B)) x)) kr.2) = _ at hp
    have hscalar : GaussianObservationLaw.action (MM T) x kr = (Real.sqrt T)⁻¹ *
        ∫ t in (0 : ℝ)..T, (ell kr.1).eval (t / T) *
          (C ((NormedSpace.exp (t • B)) x)) kr.2 := by
      simpa only [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, ← hp] using hv
    have hc := intervalIntegral.smul_integral_comp_mul_left
      (fun t : ℝ => (ell kr.1).eval (t / T) *
        (C ((NormedSpace.exp (t • B)) x)) kr.2) T (a := 0) (b := 1)
    simp only [mul_zero, mul_one, smul_eq_mul,
      mul_div_cancel_left₀ _ hT.ne'] at hc
    rw [hscalar, ← hc]
    have hs : (Real.sqrt T)⁻¹ * T = Real.sqrt T := by
      rw [← Real.sq_sqrt hT.le, pow_two, ← mul_assoc,
        inv_mul_cancel₀ (Real.sqrt_pos.mpr hT).ne', one_mul]
    simp only [← mul_assoc, hs, A, comp_apply]
  have hmomentLift (T : ℝ) (hT : 0 < T) :
      GaussianObservationLaw.action (MM T) = Real.sqrt T • Q₁.comp (L T) := by
    ext x kr
    rw [hunitMoment T hT x kr]
    simp only [smul_apply, comp_apply, PiLp.smul_apply, smul_eq_mul,
      hQlift (A T) (L T) (hL T)]

  have hmomentApprox : normalizedMomentApproximation B C cutoff ell := by
    let e (T : ℝ) : V (n + 1) →L[ℝ] V (n + 1) :=
      ∑ j : Fin (n + 1), (Real.sqrt T * T ^ (j : ℕ))⁻¹ • (layer B C j).starProjection
    let F₀ (s : ℝ) : V (n + 1) →L[ℝ] V (r + 1) :=
      ∑ j : Fin (n + 1), (s ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
        C.comp ((B ^ (j : ℕ)).comp (layer B C j).starProjection)
    have hF₀ : Continuous F₀ := by dsimp [F₀]; fun_prop
    obtain ⟨L₀, hL₀⟩ := hlift F₀ hF₀
    let R₀ := Q₁.comp L₀
    let R (T : ℝ) := (GaussianObservationLaw.action (MM T)).comp (e T)
    have hpoly (x : V (n + 1)) (a : Fin (r + 1)) :
        ∃ q : Polynomial ℝ, q.degree ≤ (cutoff : WithBot ℕ) ∧ ∀ s, q.eval s = (F₀ s x) a := by
      let q : Polynomial ℝ := ∑ j : Fin (n + 1), if (j : ℕ) ≤ cutoff then
        Polynomial.monomial (j : ℕ)
          ((C ((B ^ (j : ℕ)) ((layer B C j).starProjection x))) a /
            ((j : ℕ).factorial : ℝ)) else 0
      refine ⟨q, ?_, ?_⟩
      · apply (Polynomial.degree_sum_le _ _).trans
        apply Finset.sup_le
        intro j _
        split_ifs with hj
        · exact (Polynomial.degree_monomial_le _ _).trans (by exact_mod_cast hj)
        · simp
      · intro s
        simp only [q, Polynomial.eval_finset_sum, F₀, sum_apply, smul_apply,
          WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, comp_apply]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : (j : ℕ) ≤ cutoff
        · simp only [if_pos hj, Polynomial.eval_monomial]
          ring
        · have hz := habove (Nat.lt_of_not_ge hj)
          simp [if_neg hj, hz]
    have hR₀Gram := hQpolyGram F₀ hF₀ L₀ hL₀ hpoly
    let U : Submodule ℝ (V (n + 1)) := (kernels B C (n + 1))ᗮ
    have hU : U = ⊤ := by simp only [U, hN, Submodule.orthogonal_bot]
    have hBpow (j : ℕ) : (B.toLinearMap ^ j).toContinuousLinearMap = B ^ j := by
      change (Module.End.toContinuousLinearMap (V (n + 1))) (B.toLinearMap ^ j) = _
      rw [map_pow]
      congr 1
      ext x
      rfl
    have hBc : B.toLinearMap.toContinuousLinearMap = B := by ext x; rfl
    have hCc : C.toLinearMap.toContinuousLinearMap = C := by ext x; rfl
    have hnativeError : ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 < T → T * ‖B‖ < 1 →
        ∀ s ∈ Icc (0 : ℝ) 1,
          ‖(∑ j : Fin (n + 1), (T ^ (j : ℕ))⁻¹ •
            (A T s).comp ((layer B C j).starProjection.comp U.subtypeL)) -
              (F₀ s).comp U.subtypeL‖ ≤ K * T := by
      simpa [V, kernels, layer, U, A, F₀, hBpow, hBc, hCc,
        ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_assoc] using hlayers.2.2.2.2.2
    obtain ⟨K, hK, herror⟩ := hnativeError
    have hpoint (T : ℝ) (hT : 0 < T) (hTB : T * ‖B‖ < 1)
        (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        ‖Real.sqrt T • (A T s).comp (e T) - F₀ s‖ ≤ K * T := by
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK hT.le)
      intro x
      let xu : U := ⟨x, by rw [hU]; trivial⟩
      have hval : (Real.sqrt T • (A T s).comp (e T) - F₀ s) x =
          ((∑ j : Fin (n + 1), (T ^ (j : ℕ))⁻¹ •
            (A T s).comp ((layer B C j).starProjection.comp U.subtypeL)) -
              (F₀ s).comp U.subtypeL) xu := by
        simp only [e, sub_apply, smul_apply, comp_apply, sum_apply, map_sum, map_smul,
          Submodule.subtypeL_apply, xu, Finset.smul_sum, smul_smul]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        field_simp [(Real.sqrt_pos.mpr hT).ne', (pow_pos hT (j : ℕ)).ne']
        <;> ring
      rw [hval]
      exact (ContinuousLinearMap.le_opNorm _ xu).trans
        (mul_le_mul_of_nonneg_right (herror T hT hTB s hs) (norm_nonneg xu))
    have hRerror (T : ℝ) (hT : 0 < T) (hTB : T * ‖B‖ < 1) : ‖R T - R₀‖ ≤ K * T := by
      let LN := Real.sqrt T • (L T).comp (e T)
      have hLN (x : V (n + 1)) : (fun s => LN x s) =ᵐ[μ₁]
          fun s => (Real.sqrt T • (A T s).comp (e T)) x := by
        exact (Lp.coeFn_smul (Real.sqrt T) (L T (e T x))).trans
          ((hL T (e T x)).const_smul (Real.sqrt T))
      have hn := hL2diff (fun s => Real.sqrt T • (A T s).comp (e T)) F₀
        LN L₀ hLN hL₀ (K * T) (mul_nonneg hK hT.le) (hpoint T hT hTB)
      have hR : R T - R₀ = Q₁.comp (LN - L₀) := by
        rw [R, hmomentLift T hT]
        ext x
        simp [R₀, LN]
      rw [hR]
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK hT.le)
      intro x
      exact (hQ₁ ((LN - L₀) x)).trans
        (((LN - L₀).le_opNorm x).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg x)))
    have hcongruence (T : ℝ) :
        (e T).comp ((GaussianObservationLaw.action (momentG B C cutoff ell T)).comp (e T)) =
          (R T).adjoint.comp (R T) := by
      have he : (e T).adjoint = e T := by
        symm
        apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
        intro x y
        simp only [e, sum_apply, smul_apply, sum_inner, inner_sum,
          real_inner_smul_left, real_inner_smul_right]
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun z : ℝ => (Real.sqrt T * T ^ (j : ℕ))⁻¹ * z)
          ((layer B C j).inner_starProjection_left_eq_right x y)
      rw [momentG, hactionGram]
      simp only [R, MM, adjoint_comp, he, ContinuousLinearMap.comp_assoc]
    change (fun T => (e T).comp ((GaussianObservationLaw.action (momentG B C cutoff ell T)).comp (e T)) -
      ∫ s in (0 : ℝ)..1, (F₀ s).adjoint.comp (F₀ s)) =O[𝓝[>] 0] (fun T : ℝ => T)
    apply Asymptotics.IsBigO.of_bound ((K + 2 * ‖R₀‖) * K)
    filter_upwards [self_mem_nhdsWithin,
      eventually_lt_nhdsWithin (by positivity : (0 : ℝ) < (‖B‖ + 1)⁻¹),
      eventually_lt_nhdsWithin zero_lt_one] with T hT hsmall hT1
    have hTB : T * ‖B‖ < 1 := by
      have hh := (lt_inv_iff₀ (by positivity : 0 < ‖B‖ + 1)).mp hsmall
      nlinarith [norm_nonneg B]
    have herr := hRerror T hT hTB
    have hRT : ‖R T‖ ≤ K + ‖R₀‖ := by
      calc
        _ ≤ ‖R T - R₀‖ + ‖R₀‖ := norm_le_norm_sub_add _ _
        _ ≤ K * T + ‖R₀‖ := add_le_add_right herr _
        _ ≤ _ := by nlinarith
    rw [hcongruence, ← hR₀Gram]
    simp only [Real.norm_eq_abs, abs_of_pos hT]
    calc
      _ ≤ (‖R T‖ + ‖R₀‖) * ‖R T - R₀‖ := hgramDiff (R T) R₀
      _ ≤ (K + 2 * ‖R₀‖) * (K * T) :=
        mul_le_mul (by linarith) herr (norm_nonneg _) (by positivity)
      _ = _ := by ring

  have hfixedMoment : ∀ η : ℝ, 0 < η →
      (fun T => information (MM T) β η - T / (2 * β * η) *
        Matrix.trace ((Matrix.toEuclideanLin.symm C.toLinearMap).transpose *
          Matrix.toEuclideanLin.symm C.toLinearMap)) =O[𝓝[>] 0] (fun T : ℝ => T ^ 2) := by
    -- Source attempt: prove the moment Gramian's own first-order expansion.
    -- Constants are fixed after B,C,ell,beta,eta; no schedule regularity is used.
    intro η hη
    let H := C.adjoint.comp C
    let R (T : ℝ) := Q₁.comp (L T)
    let G (T : ℝ) := GaussianObservationLaw.action (momentG B C cutoff ell T)
    have hA0 (s : ℝ) : A 0 s = C := by simp [A, NormedSpace.exp_zero]
    have hR0 : (R 0).adjoint.comp (R 0) = H := by
      have hp (x : V (n + 1)) (a : Fin (r + 1)) :
          ∃ q : Polynomial ℝ, q.degree ≤ (cutoff : WithBot ℕ) ∧
            ∀ s, q.eval s = (A 0 s x) a := by
        refine ⟨Polynomial.C (C x a), ?_, ?_⟩
        · exact Polynomial.degree_C_le.trans (by exact_mod_cast Nat.zero_le cutoff)
        · intro s
          simp only [Polynomial.eval_C, hA0]
      simpa only [R, hA0, intervalIntegral.integral_const, sub_zero, one_smul, H] using
        hQpolyGram (A 0) (hAc 0) (L 0) (hL 0) hp
    have hd : DifferentiableAt ℝ (fun t : ℝ => C.comp (NormedSpace.exp (t • B))) 0 := by
      exact differentiableAt_const.clm_comp
        ((NormedSpace.exp_analytic (𝕂 := ℝ) (0 • B)).differentiableAt.comp 0
          (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) B).differentiableAt)
    obtain ⟨c, hc⟩ := hd.isBigO_sub.bound
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hc
    let K := max c 0
    have hK : 0 ≤ K := le_max_right _ _
    have hpoint (T : ℝ) (hT : 0 < T) (hTs : T < ε)
        (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖A T s - A 0 s‖ ≤ K * T := by
      have ht0 : 0 ≤ T * s := mul_nonneg hT.le hs.1
      have htT : T * s ≤ T := mul_le_of_le_one_right hT.le hs.2
      have h := hb (show dist (T * s) 0 < ε by
        simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht0] using htT.trans_lt hTs)
      simp only [zero_smul, NormedSpace.exp_zero, sub_zero,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id,
        Real.norm_eq_abs, abs_of_nonneg ht0] at h
      rw [hA0]
      exact h.trans ((mul_le_mul_of_nonneg_right (le_max_left c 0) ht0).trans
        (mul_le_mul_of_nonneg_left htT hK))
    have hRerror (T : ℝ) (hT : 0 < T) (hTs : T < ε) : ‖R T - R 0‖ ≤ K * T := by
      have hn := hL2diff (A T) (A 0) (L T) (L 0) (hL T) (hL 0)
        (K * T) (mul_nonneg hK hT.le) (hpoint T hT hTs)
      have he : R T - R 0 = Q₁.comp (L T - L 0) := by
        ext x
        simp [R]
      rw [he]
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK hT.le)
      intro x
      exact (hQ₁ ((L T - L 0) x)).trans
        (((L T - L 0).le_opNorm x).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg x)))
    have hGfactor (T : ℝ) (hT : 0 < T) :
        G T = T • (R T).adjoint.comp (R T) := by
      rw [G, momentG, hactionGram, hmomentLift T hT]
      simp only [R, map_smulₛₗ, starRingEnd_apply, star_trivial,
        smul_comp, comp_smul, smul_smul, ← pow_two, Real.sq_sqrt hT.le]
    let F := (K + 2 * ‖R 0‖) * K
    have hGerror (T : ℝ) (hT : 0 < T) (hTs : T < ε) (hT1 : T ≤ 1) :
        ‖G T - T • H‖ ≤ F * T ^ 2 := by
      have herr := hRerror T hT hTs
      have hRT : ‖R T‖ ≤ K + ‖R 0‖ := by
        calc
          _ ≤ ‖R T - R 0‖ + ‖R 0‖ := norm_le_norm_sub_add _ _
          _ ≤ K * T + ‖R 0‖ := add_le_add_right herr _
          _ ≤ _ := by nlinarith
      rw [hGfactor T hT, ← hR0, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos hT]
      calc
        _ ≤ T * ((‖R T‖ + ‖R 0‖) * ‖R T - R 0‖) :=
          mul_le_mul_of_nonneg_left (hgramDiff (R T) (R 0)) hT.le
        _ ≤ T * ((K + 2 * ‖R 0‖) * (K * T)) := by gcongr
        _ = F * T ^ 2 := by dsimp [F]; ring
    have hGbigO : (fun T => G T - T • H) =O[𝓝[>] 0] (fun T : ℝ => T ^ 2) := by
      apply Asymptotics.IsBigO.of_bound F
      filter_upwards [self_mem_nhdsWithin, eventually_lt_nhdsWithin hε,
        eventually_lt_nhdsWithin zero_lt_one] with T hT hTs hT1
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T)] using
        hGerror T hT hTs hT1.le
    let s := (β * η)⁻¹
    let J (X : V (n + 1) →L[ℝ] V (n + 1)) :=
      (1 / 2 : ℝ) * Real.log ((ContinuousLinearMap.id ℝ (V (n + 1)) + s • X).det)
    let std := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
    let coordLin : (V (n + 1) →L[ℝ] V (n + 1)) →ₗ[ℝ]
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      { toFun := fun X => LinearMap.toMatrix std.toBasis std.toBasis X.toLinearMap
        map_add' := by intro X Y; simp
        map_smul' := by intro a X; simp }
    let coord : (V (n + 1) →L[ℝ] V (n + 1)) →L[ℝ]
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      ⟨coordLin, coordLin.continuous_of_finiteDimensional⟩
    have hdet (X : V (n + 1) →L[ℝ] V (n + 1)) : X.det = (coord X).det :=
      (LinearMap.det_toMatrix std.toBasis X.toLinearMap).symm
    have hcoordId : coord (ContinuousLinearMap.id ℝ (V (n + 1))) = 1 := by
      simp [coord, coordLin]
    have hcoordAction (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
        coord (GaussianObservationLaw.action X) = X := by
      ext i j
      simp [coord, coordLin, std, LinearMap.toMatrix_apply,
        GaussianObservationLaw.action_apply, OrthonormalBasis.repr_apply_apply,
        EuclideanSpace.basisFun_inner, Matrix.mulVec, dotProduct]
    have hJ : ContDiffAt ℝ 1 J 0 := by
      have hcoord : ContDiff ℝ 1 (fun X : V (n + 1) →L[ℝ] V (n + 1) =>
          coord (ContinuousLinearMap.id ℝ (V (n + 1)) + s • X)) := by
        exact coord.contDiff.comp (contDiff_const.add (contDiff_const.smul contDiff_id))
      have hd : ContDiff ℝ 1 (fun X : V (n + 1) →L[ℝ] V (n + 1) =>
          (coord (ContinuousLinearMap.id ℝ (V (n + 1)) + s • X)).det) := by
        simp only [Matrix.det_apply']
        apply ContDiff.sum
        intro σ _
        apply contDiff_const.mul
        apply contDiff_prod
        intro i _
        exact contDiff_pi.mp (contDiff_pi.mp hcoord (σ i)) i
      have hlog := hd.contDiffAt.log (by simp [hcoordId])
      simpa only [J, hdet] using (contDiffAt_const (c := (1 / 2 : ℝ))).mul hlog
    obtain ⟨D, S, hS, hLip⟩ := hJ.exists_lipschitzOnWith
    have ht : Tendsto (fun T : ℝ => T) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left inf_le_left
    have hbase : Tendsto (fun T : ℝ => T • H) (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_smul] using ht.smul (tendsto_const_nhds (x := H))
    have hGzero : Tendsto G (𝓝[>] 0) (𝓝 0) := by
      have he := hGbigO.trans_tendsto (by simpa using ht.pow 2)
      simpa only [sub_add_cancel, zero_add] using he.add hbase
    have hcompare : (fun T => J (G T) - J (T • H)) =O[𝓝[>] 0] (fun T : ℝ => T ^ 2) := by
      apply Asymptotics.IsBigO.of_bound ((D : ℝ) * F)
      filter_upwards [hGzero.eventually hS, hbase.eventually hS, self_mem_nhdsWithin,
        eventually_lt_nhdsWithin hε, eventually_lt_nhdsWithin zero_lt_one]
        with T hGS hHS hT hTs hT1
      have hh := hLip.dist_le_mul (G T) hGS (T • H) hHS
      simp only [dist_eq_norm] at hh
      have hh' := hh.trans (mul_le_mul_of_nonneg_left
        (hGerror T hT hTs hT1.le) D.coe_nonneg)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T), mul_assoc] using hh'
    have hinfo (T : ℝ) (hT : 0 < T) : information (MM T) β η = J (G T) := by
      have hi := (hexperiment (MM T) (Real.sqrt η) (by rwa [Real.sq_sqrt hη.le])).2.2.2.1
      simp only [Real.sq_sqrt hη.le] at hi
      rw [hi, J, hdet, map_add, map_smul, hcoordId, G, hcoordAction]
      dsimp only [s, momentG, MM]
      ring
    have htrace : LinearMap.trace ℝ (V (n + 1)) H.toLinearMap =
        Matrix.trace ((Matrix.toEuclideanLin.symm C.toLinearMap).transpose *
          Matrix.toEuclideanLin.symm C.toLinearMap) := by
      have hCaction : GaussianObservationLaw.action (Matrix.toEuclideanLin.symm C.toLinearMap) = C := by
        change (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm C.toLinearMap)).toContinuousLinearMap = C
        rw [LinearEquiv.apply_symm_apply]
        ext x
        rfl
      have he : H = GaussianObservationLaw.action
          ((Matrix.toEuclideanLin.symm C.toLinearMap).transpose *
            Matrix.toEuclideanLin.symm C.toLinearMap) := by
        rw [hactionGram, hCaction]
      rw [he, LinearMap.trace_eq_matrix_trace ℝ std.toBasis]
      exact congrArg Matrix.trace (hcoordAction _)
    have hideal : (fun T => J (T • H) - T / (2 * β * η) *
        Matrix.trace ((Matrix.toEuclideanLin.symm C.toLinearMap).transpose *
          Matrix.toEuclideanLin.symm C.toLinearMap)) =O[𝓝[>] 0] (fun T : ℝ => T ^ 2) := by
      rcases PhysicalFixedNoiseInformation.physical_fixed_noise_information
        (0 : V (n + 1) →L[ℝ] V (n + 1)) C β η hβ hη with ⟨K₀, δ, hK₀, hδ, hb₀⟩
      apply Asymptotics.IsBigO.of_bound K₀
      filter_upwards [self_mem_nhdsWithin, eventually_lt_nhdsWithin hδ] with T hT hTδ
      have hz : (∫ t in (0 : ℝ)..T,
          (C.comp (NormedSpace.exp (t • (0 : V (n + 1) →L[ℝ] V (n + 1))))).adjoint.comp
            (C.comp (NormedSpace.exp (t • (0 : V (n + 1) →L[ℝ] V (n + 1)))))) = T • H := by
        simp [H, NormedSpace.exp_zero, ContinuousLinearMap.one_def]
      have hbound := hb₀ T hT hTδ.le
      rw [hz, htrace] at hbound
      simpa only [J, s, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T)] using hbound
    have hsum := hcompare.add hideal
    refine hsum.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with T hT
    rw [hinfo T hT]
    ring

  have hlimitM :
      let e : ℝ → V (n + 1) →L[ℝ] V (n + 1) := fun T =>
        ∑ j : Fin (n + 1), (Real.sqrt T * T ^ (j : ℕ))⁻¹ • (layer B C j).starProjection
      let F0 : ℝ → V (n + 1) →L[ℝ] V (r + 1) := fun s =>
        ∑ j : Fin (n + 1), (s ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
          C.comp ((B ^ (j : ℕ)).comp (layer B C j).starProjection)
      Tendsto (fun T => (e T).comp
        ((GaussianObservationLaw.action ((MM T).transpose * MM T)).comp (e T)))
        (𝓝[>] 0) (𝓝 (∫ s in (0 : ℝ)..1, (F0 s).adjoint.comp (F0 s))) := by
    have ho := hmomentApprox
    have hz := ho.trans_tendsto
      (show Tendsto (fun T : ℝ => T) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left inf_le_left)
    have hh := hz.add_const
      (∫ s in (0 : ℝ)..1,
        ((∑ j : Fin (n + 1), (s ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
          C.comp ((B ^ (j : ℕ)).comp (layer B C j).starProjection))).adjoint.comp
        (∑ j : Fin (n + 1), (s ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
          C.comp ((B ^ (j : ℕ)).comp (layer B C j).starProjection)))
    simpa only [sub_add_cancel, zero_add, MM, momentG] using hh
  obtain ⟨cM, CM, hcM, hCM, hbM, hstatM⟩ := actualSpectrum n r B C hobs b w hw hproject
    (fun i => lt_of_le_of_lt (hwm i) (Nat.lt_succ_of_le hmn)) MM β hβ hlimitM
  have hNM := actualNoiseConclusion n r m B C hmn w hw hwm hlast hcard MM β hβ
    cM CM hcM hCM hbM hstatM hfixedMoment
  exact ⟨hTfull.1, hmomCoordinates, hmomentApprox,
    (fun T hT σ hσ => hexperiment (MM T) σ hσ), hTfull.2.1, hNM⟩

end Original63SourceOnly
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ContinuousLinearMap MeasureTheory ProbabilityTheory Module WithLp Set Filter
open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace Topology Matrix.Norms.L2Operator

namespace Original8899FixedTransport
-- Source segment: Original8899Theorem64Geometry.lean
/- Transient exact-application source, original PR 8899 Theorem 6.4.
   Base 4d937d239686ac573662baad5ebfe84800a645aa; Lean 4.35.0.
   SOURCE ONLY: no elaboration, kernel, axiom, or native acceptance claimed.
   No new D5 declaration or retention/admission claim is made.
   This section computes actual derivative layers and their polynomial limit.
   The physical exponential integral is retained in the native/statistical sections. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ContinuousLinearMap MeasureTheory Module WithLp Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Topology Matrix.Norms.L2Operator

-- Both readouts act on exactly this one energy-coordinate state space.
private theorem actualGeometry :
    let V := EuclideanSpace ℝ (Fin 4)
    let Bm : Matrix (Fin 4) (Fin 4) ℝ :=
      !![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0]
    let Cs : Matrix (Fin 1) (Fin 4) ℝ := !![1,0,1,0]
    let Cp : Matrix (Fin 2) (Fin 4) ℝ := !![1,0,0,0; 0,0,1,0]
    let b := Bm.toEuclideanLin.toContinuousLinearMap
    let cs := Cs.toEuclideanLin.toContinuousLinearMap
    let cp := Cp.toEuclideanLin.toContinuousLinearMap
    let Ns : ℕ → Submodule ℝ V := fun j =>
      ⨅ k : Fin j, LinearMap.ker (cs.toLinearMap.comp (b.toLinearMap ^ (k : ℕ)))
    let Np : ℕ → Submodule ℝ V := fun j =>
      ⨅ k : Fin j, LinearMap.ker (cp.toLinearMap.comp (b.toLinearMap ^ (k : ℕ)))
    let Es : ℕ → Submodule ℝ V := fun j => Ns j ⊓ (Ns (j+1))ᗮ
    let Ep : ℕ → Submodule ℝ V := fun j => Np j ⊓ (Np (j+1))ᗮ
    let vs : Fin 4 → V :=
      ![toLp 2 ![1,0,1,0], toLp 2 ![0,1,0,2],
        toLp 2 ![1,0,-1,0], toLp 2 ![0,2,0,-1]]
    let Ps : ℝ → V →L[ℝ] EuclideanSpace ℝ (Fin 1) := fun t =>
      ∑ j : Fin 4, (t^(j : ℕ)/(Nat.factorial (j : ℕ) : ℝ)) •
        cs.comp ((b^(j : ℕ)).comp ((Es j).starProjection))
    let Pp : ℝ → V →L[ℝ] EuclideanSpace ℝ (Fin 2) := fun t =>
      ∑ j : Fin 4, (t^(j : ℕ)/(Nat.factorial (j : ℕ) : ℝ)) •
        cp.comp ((b^(j : ℕ)).comp ((Ep j).starProjection))
    let e : Fin 4 → V := fun i => toLp 2 (Pi.single i (1 : ℝ))
    let Hs : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
      ∫ t in (0 : ℝ)..1, ⟪Ps t (e i),Ps t (e j)⟫_ℝ
    let Hp : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
      ∫ t in (0 : ℝ)..1, ⟪Pp t (e i),Pp t (e j)⟫_ℝ
    Bm.transpose = -Bm ∧ (Cs.transpose * Cs).trace = 2 ∧
    (Cp.transpose * Cp).trace = 2 ∧
    (∀ j : Fin 5, finrank ℝ (Ns j) = 4 - (j : ℕ)) ∧
    (∀ j : Fin 5, finrank ℝ (Np j) = if j = 0 then 4 else if j = 1 then 2 else 0) ∧
    (∀ j : Fin 4, finrank ℝ (Es j) = 1) ∧
    (∀ j : Fin 4, finrank ℝ (Ep j) = if (j : ℕ) < 2 then 2 else 0) ∧
    Ns 4 = ⊥ ∧ (∀ j < 4, Ns j ≠ ⊥) ∧
    Np 2 = ⊥ ∧ (∀ j < 2, Np j ≠ ⊥) ∧
    (∀ x : V, (∀ k : Fin 4, cs ((b ^ (k : ℕ)) x) = 0) → x = 0) ∧
    (∀ x : V, (∀ k : Fin 4, cp ((b ^ (k : ℕ)) x) = 0) → x = 0) ∧
    (∀ j : Fin 4, Es j = Submodule.span ℝ {vs j}) ∧
    (∀ j : Fin 4, ∀ x : V,
      (Es j).starProjection x = (⟪vs j,x⟫_ℝ/‖vs j‖^2) • vs j) ∧
    (∀ x : V,
      (Ep 0).starProjection x = toLp 2 ![x 0,0,x 2,0] ∧
      (Ep 1).starProjection x = toLp 2 ![0,x 1,0,x 3] ∧
      (Ep 2).starProjection x = 0 ∧ (Ep 3).starProjection x = 0) ∧
    (∀ t : ℝ, Ps t =
      (!![1+3*t^2/4,t+2*t^3/5,1-3*t^2/4,2*t-t^3/5] :
        Matrix (Fin 1) (Fin 4) ℝ).toEuclideanLin.toContinuousLinearMap) ∧
    (∀ t : ℝ, Pp t =
      (!![1,t,0,0; 0,0,1,2*t] : Matrix (Fin 2) (Fin 4) ℝ).toEuclideanLin.toContinuousLinearMap) ∧
    Hs = !![129/80,67/80,71/80,13/10;
      67/80,271/525,29/80,407/525;
      71/80,29/80,49/80,3/5; 13/10,407/525,3/5,619/525] ∧
    Hp = !![1,1/2,0,0; 1/2,1/3,0,0; 0,0,1,1; 0,0,1,4/3] ∧
    Hs.det = 1/2688000 ∧ Hp.det = 1/36 := by
  classical
  intro V Bm Cs Cp b cs cp Ns Np Es Ep vs Ps Pp e Hs Hp
  have actcomp {a d e : Type} [Fintype a] [DecidableEq a]
      [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
      (M : Matrix a e ℝ) (N : Matrix e d ℝ) :
      M.toEuclideanLin.comp N.toEuclideanLin = (M * N).toEuclideanLin := by
    ext x
    change toLp 2 (M.mulVec (ofLp (toLp 2 (N.mulVec (ofLp x))))) =
      toLp 2 ((M*N).mulVec (ofLp x))
    simp only [ofLp_toLp,Matrix.mulVec_mulVec]
  have actpow (k : ℕ) : b.toLinearMap ^ k = (Bm ^ k).toEuclideanLin := by
    induction k with
    | zero => ext x i; simp [b, Matrix.toEuclideanLin]
    | succ k hk =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, hk, actcomp]
  let J (j : ℕ) : Matrix (Fin j) (Fin 4) ℝ :=
    fun k i => (Cs * Bm ^ (k : ℕ)) 0 i
  have hNs (j : ℕ) : Ns j = LinearMap.ker (J j).toEuclideanLin := by
    ext x
    simp only [Ns, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro h
      apply (WithLp.ofLp_injective 2)
      funext k
      have hk := congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) (h k)
      simpa [cs, actpow, ← LinearMap.comp_apply, actcomp, J,
        Matrix.toEuclideanLin, Matrix.mulVec, dotProduct] using hk
    · intro h k
      apply (WithLp.ofLp_injective 2)
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      have hk := congrArg (fun y : EuclideanSpace ℝ (Fin j) => y k) h
      simpa [cs, actpow, ← LinearMap.comp_apply, actcomp, J,
        Matrix.toEuclideanLin, Matrix.mulVec, dotProduct] using hk
  -- Rank-nullity is used on the actual jet, with explicit right inverses.
  have hkerdim {k : ℕ} (M : Matrix (Fin k) (Fin 4) ℝ)
      (D : Matrix (Fin 4) (Fin k) ℝ) (hMD : M * D = 1) :
      finrank ℝ (LinearMap.ker M.toEuclideanLin) = 4-k := by
    have hsurj : Function.Surjective M.toEuclideanLin := by
      intro y
      refine ⟨D.toEuclideanLin y, ?_⟩
      have hh := congrArg (fun L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin k) => L y) (actcomp M D)
      simpa [hMD, Matrix.toEuclideanLin] using hh
    have hr := M.toEuclideanLin.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at hr
    simp only [Module.finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hr
    omega
  have hsdim : ∀ j : Fin 5, finrank ℝ (Ns j) = 4-(j : ℕ) := by
    intro j
    fin_cases j
    · simp [Ns]
    · rw [hNs]
      apply hkerdim _ (!![1; 0; 0; 0] : Matrix (Fin 4) (Fin 1) ℝ)
      ext i k; fin_cases i; fin_cases k
      norm_num [J, Cs, Bm, Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [hNs]
      apply hkerdim _ (!![1,0; 0,1; 0,0; 0,0] : Matrix (Fin 4) (Fin 2) ℝ)
      ext i k; fin_cases i; fin_cases k
      norm_num [J, Cs, Bm, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [hNs]
      apply hkerdim _ (!![4/3,0,1/3; 0,1,0; -1/3,0,-1/3; 0,0,0] :
        Matrix (Fin 4) (Fin 3) ℝ)
      ext i k; fin_cases i; fin_cases k
      norm_num [J, Cs, Bm, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [hNs]
      apply hkerdim _ (!![4/3,0,1/3,0; 0,4/3,0,1/3;
        -1/3,0,-1/3,0; 0,-1/6,0,-1/6] : Matrix (Fin 4) (Fin 4) ℝ)
      ext i k; fin_cases i; fin_cases k
      norm_num [J, Cs, Bm, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  have hnest (N : ℕ → Submodule ℝ V)
      (hN : ∃ p : ℕ, ∃ c : V →ₗ[ℝ] EuclideanSpace ℝ (Fin p),
        N = fun j => ⨅ k : Fin j, LinearMap.ker (c.comp (b.toLinearMap ^ (k : ℕ))))
      {j k : ℕ} (hjk : j ≤ k) : N k ≤ N j := by
    obtain ⟨p,c,rfl⟩ := hN
    intro x hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    exact ((Submodule.mem_iInf _).mp hx) ⟨i, lt_of_lt_of_le i.isLt hjk⟩
  have hsnest {j k : ℕ} (hjk : j ≤ k) : Ns k ≤ Ns j :=
    hnest Ns ⟨1,cs.toLinearMap,rfl⟩ hjk
  have hpnest {j k : ℕ} (hjk : j ≤ k) : Np k ≤ Np j :=
    hnest Np ⟨2,cp.toLinearMap,rfl⟩ hjk
  have hpker : Np 1 = LinearMap.ker Cp.toEuclideanLin := by
    ext x
    simp [Np, cp, Fin.forall_fin_one]
  have hpdim1 : finrank ℝ (Np 1) = 2 := by
    rw [hpker]
    apply hkerdim _ (!![1,0; 0,0; 0,1; 0,0] : Matrix (Fin 4) (Fin 2) ℝ)
    ext i k; fin_cases i; fin_cases k
    norm_num [Cp, Matrix.mul_apply, Fin.sum_univ_succ]
  have hpbot : Np 2 = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have h0 := ((Submodule.mem_iInf _).mp hx) (0 : Fin 2)
    have h1 := ((Submodule.mem_iInf _).mp hx) (1 : Fin 2)
    have h00 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) h0
    have h01 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1) h0
    have h10 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) h1
    have h11 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1) h1
    simp only [LinearMap.mem_ker, LinearMap.comp_apply] at h0 h1
    simp [cp, b, Cp, Bm, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h00 h01 h10 h11
    change x = 0
    apply (WithLp.ofLp_injective 2)
    funext i
    fin_cases i <;> simp only [Pi.zero_apply, WithLp.ofLp_zero] <;> linarith
  have hpbotge {j : ℕ} (hj : 2 ≤ j) : Np j = ⊥ :=
    bot_unique (hpbot ▸ hpnest hj)
  have hpdim : ∀ j : Fin 5, finrank ℝ (Np j) =
      if j = 0 then 4 else if j = 1 then 2 else 0 := by
    intro j; fin_cases j
    · simp [Np]
    · simpa using hpdim1
    · simp [hpbot]
    · simp [hpbotge (by omega : 2 ≤ 3)]
    · simp [hpbotge (by omega : 2 ≤ 4)]
  have hes : ∀ j : Fin 4, finrank ℝ (Es j) = 1 := by
    intro j
    have h := Submodule.finrank_add_inf_finrank_orthogonal (hsnest (Nat.le_succ (j : ℕ)))
    rw [inf_comm] at h
    have h0 := hsdim (⟨j, by omega⟩ : Fin 5)
    have h1 := hsdim (⟨j+1, by omega⟩ : Fin 5)
    change finrank ℝ (Ns (j+1)) + finrank ℝ (Es j) = finrank ℝ (Ns j) at h
    omega
  have hep : ∀ j : Fin 4, finrank ℝ (Ep j) =
      if (j : ℕ) < 2 then 2 else 0 := by
    intro j
    have h := Submodule.finrank_add_inf_finrank_orthogonal (hpnest (Nat.le_succ (j : ℕ)))
    rw [inf_comm] at h
    change finrank ℝ (Np (j+1)) + finrank ℝ (Ep j) = finrank ℝ (Np j) at h
    fin_cases j <;> simp_all [Np]
  have hsbot : Ns 4 = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    simpa using hsdim (4 : Fin 5)
  have hsnon : ∀ j < 4, Ns j ≠ ⊥ := by
    intro j hj hz
    have h := hsdim (⟨j, by omega⟩ : Fin 5)
    rw [hz, Submodule.finrank_bot] at h
    omega
  have hpnon : ∀ j < 2, Np j ≠ ⊥ := by
    intro j hj hz
    interval_cases j
    · have h := hpdim (0 : Fin 5); norm_num [hz] at h
    · have h := hpdim1; norm_num [hz] at h
  have hsobs (x : V) (hx : ∀ k : Fin 4, cs ((b ^ (k : ℕ)) x) = 0) : x = 0 := by
    have hm : x ∈ Ns 4 := (Submodule.mem_iInf _).mpr hx
    simpa [hsbot] using hm
  have hpobs (x : V) (hx : ∀ k : Fin 4, cp ((b ^ (k : ℕ)) x) = 0) : x = 0 := by
    have hm : x ∈ Np 4 := (Submodule.mem_iInf _).mpr hx
    simpa [hpbotge (by omega : 2 ≤ 4)] using hm
  -- Identify the actual layers, rather than inferring their projections from dimensions.
  have hvne (j : Fin 4) : vs j ≠ 0 := by
    intro hz
    fin_cases j
    · have hh := congrArg (fun x : V => x 0) hz
      norm_num [vs] at hh
    · have hh := congrArg (fun x : V => x 1) hz
      norm_num [vs] at hh
    · have hh := congrArg (fun x : V => x 0) hz
      norm_num [vs] at hh
    · have hh := congrArg (fun x : V => x 1) hz
      norm_num [vs] at hh
  have hvmem (j : Fin 4) : vs j ∈ Es j := by
    constructor
    · apply (Submodule.mem_iInf _).mpr
      intro k
      fin_cases j <;> fin_cases k <;>
        apply (WithLp.ofLp_injective 2) <;> funext i <;> fin_cases i <;>
        norm_num [vs,cs,b,Cs,Bm,pow_succ,LinearMap.comp_apply,
          LinearMap.mul_apply,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,
          Fin.sum_univ_succ]
    · apply (Submodule.mem_orthogonal _ _).mpr
      intro y hy
      fin_cases j
      · have hy0 : cs ((b^0) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (0 : Fin 1)
        have he0 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy0
        simp [cs,b,Cs,Bm,pow_succ,ContinuousLinearMap.mul_apply,
          Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at he0
        simp [vs,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
          Fin.sum_univ_succ]
        linarith
      · have hy0 : cs ((b^0) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (0 : Fin 2)
        have he0 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy0
        have hy1 : cs ((b^1) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (1 : Fin 2)
        have he1 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy1
        simp [cs,b,Cs,Bm,pow_succ,ContinuousLinearMap.mul_apply,
          Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at he0 he1
        simp [vs,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
          Fin.sum_univ_succ]
        linarith
      · have hy0 : cs ((b^0) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (0 : Fin 3)
        have he0 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy0
        have hy1 : cs ((b^1) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (1 : Fin 3)
        have he1 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy1
        have hy2 : cs ((b^2) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (2 : Fin 3)
        have he2 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy2
        simp [cs,b,Cs,Bm,pow_succ,ContinuousLinearMap.mul_apply,
          Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at he0 he1 he2
        simp [vs,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
          Fin.sum_univ_succ]
        linarith
      · have hy0 : cs ((b^0) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (0 : Fin 4)
        have he0 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy0
        have hy1 : cs ((b^1) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (1 : Fin 4)
        have he1 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy1
        have hy2 : cs ((b^2) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (2 : Fin 4)
        have he2 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy2
        have hy3 : cs ((b^3) y) = 0 :=
          ((Submodule.mem_iInf _).mp hy) (3 : Fin 4)
        have he3 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hy3
        simp [cs,b,Cs,Bm,pow_succ,ContinuousLinearMap.mul_apply,
          Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at he0 he1 he2 he3
        simp [vs,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
          Fin.sum_univ_succ]
        linarith
  have hspan (j : Fin 4) : Es j = Submodule.span ℝ {vs j} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_singleton_le_iff_mem.mpr (hvmem j))
    rw [finrank_span_singleton (hvne j),hes j]
  have hprojS (j : Fin 4) (x : V) :
      (Es j).starProjection x = (⟪vs j,x⟫_ℝ/‖vs j‖^2) • vs j := by
    rw [hspan]
    exact Submodule.starProjection_singleton ℝ x
  have hprojN (x : V) : (Np 1).starProjection x = toLp 2 ![0,x 1,0,x 3] := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hpker]
      apply (WithLp.ofLp_injective 2)
      funext i
      fin_cases i <;>
        simp [Cp,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    · intro y hy
      rw [hpker] at hy
      have hy0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hy
      have hy1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hy
      simp [Cp,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hy0 hy1
      simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ,
        PiLp.sub_apply,hy0,hy1]
  have hprojP (x : V) :
      (Ep 0).starProjection x = toLp 2 ![x 0,0,x 2,0] ∧
      (Ep 1).starProjection x = toLp 2 ![0,x 1,0,x 3] ∧
      (Ep 2).starProjection x = 0 ∧ (Ep 3).starProjection x = 0 := by
    have he0 : Ep 0 = (Np 1)ᗮ := by simp [Ep,Np]
    have he1 : Ep 1 = Np 1 := by simp [Ep,hpbot]
    have he2 : Ep 2 = ⊥ := by simp [Ep,hpbot]
    have he3 : Ep 3 = ⊥ := by simp [Ep,hpbotge (by omega : 2 ≤ 3)]
    refine ⟨?_,?_,?_,?_⟩
    · rw [he0,Submodule.starProjection_orthogonal_val,hprojN]
      apply (WithLp.ofLp_injective 2)
      funext i
      fin_cases i <;> simp [PiLp.sub_apply]
    · simpa only [he1] using hprojN x
    · simp [he2]
    · simp [he3]
  have hPs (t : ℝ) : Ps t =
      (!![1+3*t^2/4,t+2*t^3/5,1-3*t^2/4,2*t-t^3/5] :
        Matrix (Fin 1) (Fin 4) ℝ).toEuclideanLin.toContinuousLinearMap := by
    ext x i
    fin_cases i
    simp [Ps,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply,hprojS,vs,EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.inner_eq_star_dotProduct,cs,b,Cs,Bm,pow_succ,
      ContinuousLinearMap.mul_apply,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ]
    ring
  have hPp (t : ℝ) : Pp t =
      (!![1,t,0,0; 0,0,1,2*t] : Matrix (Fin 2) (Fin 4) ℝ).toEuclideanLin.toContinuousLinearMap := by
    ext x i
    have h0 := (hprojP x).1
    have h1 := (hprojP x).2.1
    have h2 := (hprojP x).2.2.1
    have h3 := (hprojP x).2.2.2
    fin_cases i <;>
      simp [Pp,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply,h0,h1,h2,h3,cp,b,Cp,Bm,pow_succ,
        ContinuousLinearMap.mul_apply,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,
        Fin.sum_univ_succ] <;> ring
  -- Integrate the actual projection-bearing polynomial, entry by entry.
  -- This is still its limit operator, never the finite-time exponential Gramian.
  have hpoly (a d : Fin 4 → ℝ) :
      (∫ t in (0 : ℝ)..1,
        (∑ k : Fin 4, a k*t^(k : ℕ))*(∑ l : Fin 4, d l*t^(l : ℕ))) =
        ∑ k : Fin 4, ∑ l : Fin 4,
          a k*d l/(((k : ℕ)+(l : ℕ)+1 : ℕ) : ℝ) := by
    have hmul (t : ℝ) :
        (∑ k : Fin 4, a k*t^(k : ℕ))*(∑ l : Fin 4, d l*t^(l : ℕ)) =
        ∑ k : Fin 4, ∑ l : Fin 4, (a k*d l)*t^((k : ℕ)+(l : ℕ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [pow_add]
      ring
    simp_rw [hmul]
    rw [intervalIntegral.integral_finsetSum Finset.univ (fun k _ => by
      apply Continuous.intervalIntegrable
      fun_prop)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_finsetSum Finset.univ (fun l _ => by
      apply Continuous.intervalIntegrable
      fun_prop)]
    simp [intervalIntegral.integral_const_mul,intervalIntegral.integral_pow,
      mul_div_assoc]
  let As : Matrix (Fin 4) (Fin 4) ℝ :=
    !![1,0,1,0; 0,1,0,2; 3/4,0,-3/4,0; 0,2/5,0,-1/5]
  let Ap0 : Matrix (Fin 4) (Fin 4) ℝ :=
    !![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0]
  let Ap1 : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0,0,1,0; 0,0,0,2; 0,0,0,0; 0,0,0,0]
  have hinnerS (t : ℝ) (i j : Fin 4) :
      ⟪Ps t (e i),Ps t (e j)⟫_ℝ =
        (∑ k : Fin 4, As k i*t^(k : ℕ))*(∑ l : Fin 4, As l j*t^(l : ℕ)) := by
    simp_rw [hPs]
    fin_cases i <;> fin_cases j <;>
      simp [As,e,EuclideanSpace.inner_eq_star_dotProduct,Matrix.toEuclideanLin,
        Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
  have hinnerP (t : ℝ) (i j : Fin 4) :
      ⟪Pp t (e i),Pp t (e j)⟫_ℝ =
        (∑ k : Fin 4, Ap0 k i*t^(k : ℕ))*(∑ l : Fin 4, Ap0 l j*t^(l : ℕ)) +
        (∑ k : Fin 4, Ap1 k i*t^(k : ℕ))*(∑ l : Fin 4, Ap1 l j*t^(l : ℕ)) := by
    simp_rw [hPp]
    fin_cases i <;> fin_cases j <;>
      simp [Ap0,Ap1,e,EuclideanSpace.inner_eq_star_dotProduct,Matrix.toEuclideanLin,
        Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
  have hHs : Hs = !![129/80,67/80,71/80,13/10;
      67/80,271/525,29/80,407/525;
      71/80,29/80,49/80,3/5; 13/10,407/525,3/5,619/525] := by
    ext i j
    change (∫ t in (0 : ℝ)..1, ⟪Ps t (e i),Ps t (e j)⟫_ℝ) = _
    simp_rw [hinnerS]
    rw [hpoly]
    fin_cases i <;> fin_cases j <;> norm_num [As,Fin.sum_univ_succ]
  have hHp : Hp = !![1,1/2,0,0; 1/2,1/3,0,0; 0,0,1,1; 0,0,1,4/3] := by
    ext i j
    change (∫ t in (0 : ℝ)..1, ⟪Pp t (e i),Pp t (e j)⟫_ℝ) = _
    simp_rw [hinnerP]
    rw [intervalIntegral.integral_add (by
      apply Continuous.intervalIntegrable
      fun_prop) (by
      apply Continuous.intervalIntegrable
      fun_prop),hpoly,hpoly]
    fin_cases i <;> fin_cases j <;> norm_num [Ap0,Ap1,Fin.sum_univ_succ]
  have hdetS : Hs.det = 1/2688000 := by
    rw [hHs]
    norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  have hdetP : Hp.det = 1/36 := by
    rw [hHp]
    norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  refine ⟨?_, ?_, ?_, hsdim, hpdim, hes, hep, hsbot, hsnon, hpbot, hpnon,
    hsobs, hpobs, hspan, hprojS, hprojP, hPs, hPp, hHs, hHp, hdetS, hdetP⟩
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Bm]
  · norm_num [Cs, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [Cp, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
end


-- Source segment: Original8899Theorem64Native.lean
/- Transient concrete application of the published native physical Gramian supplier.
   SOURCE ONLY, UNCOMPILED. The output concerns the actual exponential integral.
   This file does not assert either determinant coefficient or spectral transport. -/
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ContinuousLinearMap MeasureTheory Module WithLp Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Topology

private theorem actualNative (split : Bool) :
    let V := EuclideanSpace ℝ (Fin 4)
    let p := if split then 2 else 1
    let W := EuclideanSpace ℝ (Fin p)
    let Bm : Matrix (Fin 4) (Fin 4) ℝ :=
      !![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0]
    let Cm : Matrix (Fin p) (Fin 4) ℝ := fun i j =>
      if split then (if ((i : ℕ) = 0 ∧ j = 0) ∨ ((i : ℕ) = 1 ∧ j = 2) then 1 else 0)
      else (if j = 0 ∨ j = 2 then 1 else 0)
    let B := Bm.toEuclideanLin
    let C := Cm.toEuclideanLin
    let n := Module.finrank ℝ V
    let N : ℕ → Submodule ℝ V := fun j =>
      ⨅ k : Fin j, LinearMap.ker (C.comp (B ^ (k : ℕ)))
    let U : Submodule ℝ V := (N n)ᗮ
    let E : Fin n → Submodule ℝ V := fun j => N j ⊓ (N (j + 1))ᗮ
    let b : V →L[ℝ] V := B.toContinuousLinearMap
    let c : V →L[ℝ] W := C.toContinuousLinearMap
    let Q : Fin n → U →L[ℝ] U := fun j =>
      U.orthogonalProjectionOnto.comp ((E j).starProjection.comp U.subtypeL)
    let d : ℝ → U →L[ℝ] U := fun T =>
      ∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ)) • Q j
    let e : ℝ → U →L[ℝ] U := fun T =>
      ∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ))⁻¹ • Q j
    let A : ℝ → U →L[ℝ] W := fun t =>
      c.comp ((NormedSpace.exp (t • b)).comp U.subtypeL)
    let G : ℝ → U →L[ℝ] U := fun T =>
      ∫ t in (0 : ℝ)..T, (A t).adjoint.comp (A t)
    let F₀ : ℝ → U →L[ℝ] W := fun s =>
      ∑ j : Fin n, (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) •
        c.comp ((b ^ (j : ℕ)).comp ((E j).starProjection.comp U.subtypeL))
    let F₄ : ℝ → U →L[ℝ] W := fun s =>
      ∑ j : Fin 4, (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) •
        c.comp ((b ^ (j : ℕ)).comp
          ((N j ⊓ (N (j+1))ᗮ).starProjection.comp U.subtypeL))
    let H : U →L[ℝ] U := ∫ s in (0 : ℝ)..1, (F₀ s).adjoint.comp (F₀ s)
    U = ⊤ ∧
    (∀ T : ℝ, 0 < T →
      (d T).comp (e T) = ContinuousLinearMap.id ℝ U ∧
      (e T).comp (d T) = ContinuousLinearMap.id ℝ U ∧
      (e T).comp ((G T).comp (e T)) =
        ∫ s in (0 : ℝ)..1,
          (Real.sqrt T • (A (T * s)).comp (e T)).adjoint.comp
            (Real.sqrt T • (A (T * s)).comp (e T))) ∧
    (∀ x : U, x ≠ 0 → 0 < ⟪x, H x⟫_ℝ) ∧
    (∃ R : ℝ, 0 ≤ R ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T * ‖b‖ < 1 →
      ‖(e T).comp ((G T).comp (e T)) - H‖ ≤ R * T) ∧
    (∀ s : ℝ, F₀ s = F₄ s) ∧
    H = (∫ s in (0 : ℝ)..1, (F₄ s).adjoint.comp (F₄ s)) ∧
    Tendsto (fun T : ℝ => (e T).comp ((G T).comp (e T)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds H) := by
  classical
  intro V p W Bm Cm B C n N U E b c Q d e A G F₀ F₄ H
  have hn : n = 4 := by simp [n, V]
  have hobs (x : V) (hx : ∀ k : Fin 4, c ((b ^ (k : ℕ)) x) = 0) : x = 0 := by
    have h0 := hx (0 : Fin 4)
    have h1 := hx (1 : Fin 4)
    have h2 := hx (2 : Fin 4)
    have h3 := hx (3 : Fin 4)
    cases split
    · have h00 := congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) h0
      have h10 := congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) h1
      have h20 := congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) h2
      have h30 := congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) h3
      simp [c, b, Cm, Bm, p, pow_succ, ContinuousLinearMap.mul_apply,
        Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] at h00 h10 h20 h30
      apply (WithLp.ofLp_injective 2)
      funext i
      fin_cases i <;> simp only [WithLp.ofLp_zero, Pi.zero_apply] <;> linarith
    · have h00 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) h0
      have h01 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1) h0
      have h10 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) h1
      have h11 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1) h1
      simp [c, b, Cm, Bm, p, pow_succ, ContinuousLinearMap.mul_apply,
        Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] at h00 h01 h10 h11
      apply (WithLp.ofLp_injective 2)
      funext i
      fin_cases i <;> simp only [WithLp.ofLp_zero, Pi.zero_apply] <;> linarith
  have hN : N n = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    apply hobs x
    intro k
    have kk : (k : ℕ) < n := by simpa only [hn] using k.isLt
    exact ((Submodule.mem_iInf _).mp hx) ⟨k,kk⟩
  have hU : U = ⊤ := by simp only [U,hN,Submodule.bot_orthogonal_eq_top]
  have hnative :=
    D5.S3.Observer.Linear.DerivativeLayerNativeGramian.derivative_layer_native_gramian B C
  obtain ⟨hinverse,hpositive,R,hR,herror⟩ := hnative
  have hF (s : ℝ) : F₀ s = F₄ s := by
    apply Fintype.sum_equiv (finCongr hn)
    intro j
    simp only [E]
    rfl
  have hH : H = (∫ s in (0 : ℝ)..1, (F₄ s).adjoint.comp (F₄ s)) := by
    simp only [H,hF]
  have hlim : Tendsto (fun T : ℝ => (e T).comp ((G T).comp (e T)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds H) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := min 1 (min (1/(1+‖b‖)) (ε/(R+1)))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hsmall : ∀ᶠ T : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), T < δ :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    filter_upwards [self_mem_nhdsWithin,hsmall] with T hT hTδ
    have hT1 : T ≤ 1 := le_of_lt (lt_of_lt_of_le hTδ (min_le_left _ _))
    have hTb : T < 1/(1+‖b‖) := lt_of_lt_of_le hTδ
      ((min_le_right _ _).trans (min_le_left _ _))
    have hTε : T < ε/(R+1) := lt_of_lt_of_le hTδ
      ((min_le_right _ _).trans (min_le_right _ _))
    have hbn : 0 < 1+‖b‖ := by positivity
    have hRn : 0 < R+1 := by positivity
    have hbmul := (lt_div_iff₀ hbn).mp hTb
    have hRmul := (lt_div_iff₀ hRn).mp hTε
    have hTnorm : T*‖b‖ < 1 := by nlinarith
    have hRT : R*T < ε := by nlinarith
    rw [dist_eq_norm]
    exact (herror T hT hT1 hTnorm).trans_lt hRT
  exact ⟨hU,hinverse,hpositive,⟨R,hR,herror⟩,hF,hH,hlim⟩
end


-- Source segment: Original8899Theorem64FixedNoise.lean
/- Transient exact physical fixed-noise application; SOURCE ONLY, UNCOMPILED.
   beta and variance eta are fixed before the constants are chosen.
   This file attempts a physical log-determinant bound. The actual-law
   identification is separately present in the statistical source application. -/
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Module WithLp ContinuousLinearMap
open scoped BigOperators InnerProductSpace RealInnerProductSpace Matrix.Norms.L2Operator

private theorem actualFixedNoise (split : Bool) (β η : ℝ) (hβ : 0 < β) (hη : 0 < η) :
    let V := EuclideanSpace ℝ (Fin 4)
    let p := if split then 2 else 1
    let Bm : Matrix (Fin 4) (Fin 4) ℝ :=
      !![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0]
    let Cm : Matrix (Fin p) (Fin 4) ℝ := fun i j =>
      if split then (if ((i : ℕ) = 0 ∧ j = 0) ∨ ((i : ℕ) = 1 ∧ j = 2) then 1 else 0)
      else (if j = 0 ∨ j = 2 then 1 else 0)
    let b := Bm.toEuclideanLin.toContinuousLinearMap
    let c := Cm.toEuclideanLin.toContinuousLinearMap
    let G : ℝ → V →L[ℝ] V := fun T => ∫ t in (0 : ℝ)..T,
      (c.comp (NormedSpace.exp (t • b))).adjoint.comp
        (c.comp (NormedSpace.exp (t • b)))
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ T : ℝ, 0 < T → T ≤ δ →
      |(1/2 : ℝ) * Real.log ((ContinuousLinearMap.id ℝ V +
          (β*η)⁻¹ • G T).det) - T/(β*η)| ≤ K*T^2 := by
  classical
  intro V p Bm Cm b c G
  have hGram : c.adjoint.comp c =
      (Cm.transpose*Cm).toEuclideanLin.toContinuousLinearMap := by
    have ha := D5.S3.Observer.Linear.GaussianObservationLaw.action_adjoint Cm
    change c.adjoint = Cm.transpose.toEuclideanLin.toContinuousLinearMap at ha
    rw [ha]
    ext x
    change toLp 2 (Cm.transpose.mulVec (ofLp (toLp 2 (Cm.mulVec (ofLp x))))) =
      toLp 2 ((Cm.transpose*Cm).mulVec (ofLp x))
    simp only [ofLp_toLp,Matrix.mulVec_mulVec]
  have htrace : LinearMap.trace ℝ V (c.adjoint.comp c).toLinearMap = 2 := by
    rw [hGram]
    change LinearMap.trace ℝ V ((Cm.transpose*Cm).toEuclideanLin) = 2
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.trace_toLin_eq]
    cases split <;> norm_num [p,Cm,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ]
  obtain ⟨K,δ,hK,hδ,hbound⟩ :=
    D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information
      b c β η hβ hη
  refine ⟨K,δ,hK,hδ,?_⟩
  intro T hT hTδ
  have hh := hbound T hT hTδ
  rw [htrace] at hh
  convert hh using 1 <;> congr 1 <;> ring

-- Optional canonical-Poisson-to-energy normalization uses the published L,S.
-- Both sensor experiments above already use the common energy coordinates.
private theorem actualEnergy :
    let J : Matrix (Fin 4) (Fin 4) ℝ :=
      !![0,1,0,0; -1,0,0,0; 0,0,0,1; 0,0,-1,0]
    let B : Matrix (Fin 4) (Fin 4) ℝ :=
      !![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0]
    let L : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,1,2,1]
    let Li : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,1,1/2,1]
    let S : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,1,4,1]
    L.transpose*L = S ∧ L*Li = 1 ∧ Li*L = 1 ∧
      L*J*L.transpose = B ∧ L*(J*S)*Li = B := by
  intro J B L Li S
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [L,S,Matrix.mul_apply,Fin.sum_univ_succ]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [L,Li,Matrix.mul_apply,Fin.sum_univ_succ]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [L,Li,Matrix.mul_apply,Fin.sum_univ_succ]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [L,J,B,Matrix.mul_apply,Fin.sum_univ_succ]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [L,J,S,Li,B,Matrix.mul_apply,Fin.sum_univ_succ]
end

-- Consumes actualGeometry, the immutable Geometry proof with only its anonymous
-- example given a local consumed name. Its mathematical statement/body are unchanged.
-- The helper's ONE inclusion isometry and its pulled-back frame are used for
-- each physical normalized family, its exact determinant identity, and its limit.
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ContinuousLinearMap MeasureTheory Module WithLp Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Topology Matrix.Norms.L2Operator

private theorem actualDeterminants :
    let V := EuclideanSpace ℝ (Fin 4)
    let Bm : Matrix (Fin 4) (Fin 4) ℝ :=
      !![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0]
    let Cs : Matrix (Fin 1) (Fin 4) ℝ := !![1,0,1,0]
    let Cp : Matrix (Fin 2) (Fin 4) ℝ := !![1,0,0,0; 0,0,1,0]
    let b := Bm.toEuclideanLin.toContinuousLinearMap
    let cs := Cs.toEuclideanLin.toContinuousLinearMap
    let cp := Cp.toEuclideanLin.toContinuousLinearMap
    let e : Fin 4 → V := fun i => toLp 2 (Pi.single i (1 : ℝ))
    let Gs : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun T i j =>
      ∫ t in (0 : ℝ)..T,
        ⟪cs ((NormedSpace.exp (t • b)) (e i)), cs ((NormedSpace.exp (t • b)) (e j))⟫_ℝ
    let Gp : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun T i j =>
      ∫ t in (0 : ℝ)..T,
        ⟪cp ((NormedSpace.exp (t • b)) (e i)), cp ((NormedSpace.exp (t • b)) (e j))⟫_ℝ
    Tendsto (fun T => (Gs T).det / T ^ 16) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2688000 : ℝ)) ∧
    Tendsto (fun T => (Gp T).det / T ^ 8) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 36 : ℝ)) ∧
    (0 : ℝ) < 1 / 2688000 ∧ (0 : ℝ) < 1 / 36 := by
  classical
  intro V Bm Cs Cp b cs cp e Gs Gp
  let Ns : ℕ → Submodule ℝ V := fun j =>
    ⨅ k : Fin j, LinearMap.ker (cs.toLinearMap.comp (b.toLinearMap ^ (k : ℕ)))
  let Np : ℕ → Submodule ℝ V := fun j =>
    ⨅ k : Fin j, LinearMap.ker (cp.toLinearMap.comp (b.toLinearMap ^ (k : ℕ)))
  let Es : ℕ → Submodule ℝ V := fun j => Ns j ⊓ (Ns (j+1))ᗮ
  let Ep : ℕ → Submodule ℝ V := fun j => Np j ⊓ (Np (j+1))ᗮ
  let Ps : ℝ → V →L[ℝ] EuclideanSpace ℝ (Fin 1) := fun s =>
    ∑ j : Fin 4, (s^(j : ℕ)/(Nat.factorial (j : ℕ) : ℝ)) •
      cs.comp ((b^(j : ℕ)).comp (Es j).starProjection)
  let Pp : ℝ → V →L[ℝ] EuclideanSpace ℝ (Fin 2) := fun s =>
    ∑ j : Fin 4, (s^(j : ℕ)/(Nat.factorial (j : ℕ) : ℝ)) •
      cp.comp ((b^(j : ℕ)).comp (Ep j).starProjection)
  let Hs : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
    ∫ s in (0 : ℝ)..1, ⟪Ps s (e i), Ps s (e j)⟫_ℝ
  let Hp : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
    ∫ s in (0 : ℝ)..1, ⟪Pp s (e i), Pp s (e j)⟫_ℝ
  have hg := actualGeometry
  rcases hg with ⟨hskew, hgainS, hgainP, hdimS, hdimP, hes, hep,
    hsbot, hsnon, hpbot, hpnon, hsobs, hpobs, hspanS, hprojS, hprojP,
    hPs, hPp, hHs, hHp, hdetS, hdetP⟩
  have hn : finrank ℝ V = 4 := by simp [V]
  have hsN : Original8899NativeAmbient.N b cs (finrank ℝ V) = ⊥ := by
    simpa only [hn] using hsbot
  have hpN4 : Np 4 = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    apply hpobs x
    intro k
    exact (Submodule.mem_iInf _).mp hx k
  have hpN : Original8899NativeAmbient.N b cp (finrank ℝ V) = ⊥ := by
    simpa only [hn] using hpN4
  let std : OrthonormalBasis (Fin 4) ℝ V := EuclideanSpace.basisFun (Fin 4) ℝ
  have hstd (i : Fin 4) : std i = e i := by
    simp [std, e, EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  -- Reindex the complete projection-bearing weighted summand, without dropping
  -- the two zero layers of the split sensor or identifying spaces by dimensions.
  have hPS (s : ℝ) : Original8899NativeAmbient.P b cs s = Ps s := by
    unfold Original8899NativeAmbient.P Ps
    apply Fintype.sum_equiv (finCongr hn)
    intro j
    rfl
  have hPP (s : ℝ) : Original8899NativeAmbient.P b cp s = Pp s := by
    unfold Original8899NativeAmbient.P Pp
    apply Fintype.sum_equiv (finCongr hn)
    intro j
    rfl
  have hHS : Original8899NativeAmbient.coordinates std (Original8899NativeAmbient.H b cs) = Hs := by
    rw [Original8899NativeAmbient.H,
      Original8899NativeAmbient.matrix_integral_gram std _ (Original8899NativeAmbient.continuous_P b cs)]
    simp only [hPS, hstd, Hs]
  have hHP : Original8899NativeAmbient.coordinates std (Original8899NativeAmbient.H b cp) = Hp := by
    rw [Original8899NativeAmbient.H,
      Original8899NativeAmbient.matrix_integral_gram std _ (Original8899NativeAmbient.continuous_P b cp)]
    simp only [hPP, hstd, Hp]
  have hGS (T : ℝ) : Original8899NativeAmbient.coordinates std (Original8899NativeAmbient.G b cs T) = Gs T := by
    rw [Original8899NativeAmbient.G,
      Original8899NativeAmbient.matrix_integral_gram std _ (Original8899NativeAmbient.continuous_A b cs)]
    simp only [Original8899NativeAmbient.A, comp_apply, hstd, Gs]
  have hGP (T : ℝ) : Original8899NativeAmbient.coordinates std (Original8899NativeAmbient.G b cp T) = Gp T := by
    rw [Original8899NativeAmbient.G,
      Original8899NativeAmbient.matrix_integral_gram std _ (Original8899NativeAmbient.continuous_A b cp)]
    simp only [Original8899NativeAmbient.A, comp_apply, hstd, Gp]
  have hqs : (∑ j : Fin (finrank ℝ V),
      (2 * (j : ℕ) + 1) * finrank ℝ (Original8899NativeAmbient.E b cs j)) = 16 := by
    calc
      _ = ∑ j : Fin 4, (2 * (j : ℕ) + 1) * finrank ℝ (Es j) := by
        apply Fintype.sum_equiv (finCongr hn)
        intro j
        rfl
      _ = 16 := by simp_rw [hes]; norm_num [Fin.sum_univ_succ]
  have hqp : (∑ j : Fin (finrank ℝ V),
      (2 * (j : ℕ) + 1) * finrank ℝ (Original8899NativeAmbient.E b cp j)) = 8 := by
    calc
      _ = ∑ j : Fin 4, (2 * (j : ℕ) + 1) * finrank ℝ (Ep j) := by
        apply Fintype.sum_equiv (finCongr hn)
        intro j
        rfl
      _ = 8 := by simp_rw [hep]; norm_num [Fin.sum_univ_succ]
  obtain ⟨bs, hsExact, hsLimit, hsNativeGdet, hsNativeHdet, hsDet, hsPhysical⟩ :=
    Original8899NativeAmbient.physical_determinant_limit b cs hsN std
  obtain ⟨bp, hpExact, hpLimit, hpNativeGdet, hpNativeHdet, hpDet, hpPhysical⟩ :=
    Original8899NativeAmbient.physical_determinant_limit b cp hpN std
  -- hsExact/hpExact are the exact native congruence identities for EVERY T>0.
  -- hsLimit/hpLimit concern those SAME physical normalized matrices in bs/bp.
  -- hsNativeHdet/hpNativeHdet identify the actual H_U with Hs/Hp via hHS/hHP.
  -- hsDet/hpDet remove only the ON frame at the determinant; the integral and
  -- finite-time exponential trajectory stay fixed throughout the proof.
  let us := Original8899NativeAmbient.inclusionIsometry b cs hsN
  let up := Original8899NativeAmbient.inclusionIsometry b cp hpN
  let bsU := bs.map us.symm
  let bpU := bp.map up.symm
  let Hns (T : ℝ) := LinearMap.toMatrix bsU.toBasis bsU.toBasis
    ((Original8899NativeAmbient.eU b cs T).comp
      ((Original8899NativeAmbient.GU b cs T).comp (Original8899NativeAmbient.eU b cs T))).toLinearMap
  let Hnp (T : ℝ) := LinearMap.toMatrix bpU.toBasis bpU.toBasis
    ((Original8899NativeAmbient.eU b cp T).comp
      ((Original8899NativeAmbient.GU b cp T).comp (Original8899NativeAmbient.eU b cp T))).toLinearMap
  have hsExact16 (T : ℝ) (hT : 0 < T) : (Gs T).det / T ^ 16 = (Hns T).det := by
    simpa only [hqs, hGS] using hsExact T hT
  have hpExact8 (T : ℝ) (hT : 0 < T) : (Gp T).det / T ^ 8 = (Hnp T).det := by
    simpa only [hqp, hGP] using hpExact T hT
  have hsDetLimit : Tendsto (fun T => (Hns T).det)
      (𝓝[>] (0 : ℝ)) (𝓝 Hs.det) := by
    have hh := ((continuous_id.matrix_det).tendsto _).comp hsLimit
    simpa only [hsDet, hHS] using hh
  have hpDetLimit : Tendsto (fun T => (Hnp T).det)
      (𝓝[>] (0 : ℝ)) (𝓝 Hp.det) := by
    have hh := ((continuous_id.matrix_det).tendsto _).comp hpLimit
    simpa only [hpDet, hHP] using hh
  have hsPhysical' : Tendsto (fun T => (Gs T).det / T ^ 16)
      (𝓝[>] (0 : ℝ)) (𝓝 Hs.det) := by
    apply hsDetLimit.congr'
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact (hsExact16 T hT).symm
  have hpPhysical' : Tendsto (fun T => (Gp T).det / T ^ 8)
      (𝓝[>] (0 : ℝ)) (𝓝 Hp.det) := by
    apply hpDetLimit.congr'
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact (hpExact8 T hT).symm
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · simpa only [hdetS] using hsPhysical'
  · simpa only [hdetP] using hpPhysical'
end

end Original8899FixedTransport

namespace Original63SourceOnly

-- This conclusion uses the same matrix, physical Gramian, joint law and
-- posterior as the general experiment. It quantifies all measurable risks
-- through finiteExperiment, including competitors with infinite risk.
def physicalExperiment {n r : ℕ}
    (B : V (n + 1) →L[ℝ] V (n + 1)) (C : V (n + 1) →L[ℝ] V (r + 1))
    (T β σ : ℝ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  M.transpose * M = physicalG B C T ∧ finiteExperiment M β σ ∧
  GaussianObservationLaw.covariance M β (σ ^ 2)⁻¹ =
    (β • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) +
      (σ ^ 2)⁻¹ • physicalG B C T)⁻¹ ∧
  information M β (σ ^ 2) =
    Real.log ((1 + (β * σ ^ 2)⁻¹ • physicalG B C T).det) / 2 ∧
  information M β (σ ^ 2) =
    Real.log ((ContinuousLinearMap.id ℝ (V (n + 1)) +
      (β * σ ^ 2)⁻¹ • Original8899NativeAmbient.G B C T).det) / 2 ∧
  (InformationTheory.klDiv (GaussianObservationLaw.jointLaw M β (σ ^ 2)⁻¹)
    ((GaussianObservationLaw.jointLaw M β (σ ^ 2)⁻¹).fst.prod
      (GaussianObservationLaw.jointLaw M β (σ ^ 2)⁻¹).snd)).toReal =
    information M β (σ ^ 2) ∧
  bayesRisk M β (σ ^ 2) = ENNReal.ofReal
    (Matrix.trace ((β • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) +
      (σ ^ 2)⁻¹ • physicalG B C T)⁻¹) / 2)

private theorem actualPhysicalExperiment (n r : ℕ)
    (B : V (n + 1) →L[ℝ] V (n + 1)) (C : V (n + 1) →L[ℝ] V (r + 1))
    (hobs : observable B C) (T : ℝ) (hT : 0 < T)
    (basis : OrthonormalBasis (Fin (n + 1)) ℝ (trajectoryF B C hobs T hT).range)
    (β σ : ℝ) (hβ : 0 < β) (hσ : σ ≠ 0) :
    physicalExperiment B C T β σ (trajectoryM B C hobs T hT basis) := by
  classical
  let M := trajectoryM B C hobs T hT basis
  have hf := Classical.choose_spec
    (ObservableTrajectoryCoordinates.observable_trajectory_coordinates_all_bases
      (n + 1) (r + 1) B C T hT hobs)
  have hu := Classical.choose_spec (hf.2.2.2 basis)
  have hM := Classical.choose_spec hu
  have hGram : M.transpose * M = physicalG B C T := by
    simpa only [M, trajectoryM, physicalG] using hM.2.2.2.2.2.2.2.2
  have hphysical : GaussianObservationLaw.action (physicalG B C T) =
      Original8899NativeAmbient.G B C T := by
    rw [← hGram, Original8899NativeAmbient.action_gram]
    change (GaussianObservationLaw.action M).adjoint.comp (GaussianObservationLaw.action M) = _
    rw [hM.2.2.2.2.2.1]
    exact (hM.2.2.2.2.2.2.1).trans hM.2.2.2.2.2.2.2.1
  have hE := actualExperiment n β hβ M σ (sq_pos_of_ne_zero hσ)
  have hcov : GaussianObservationLaw.covariance M β (σ ^ 2)⁻¹ =
      (β • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) +
        (σ ^ 2)⁻¹ • physicalG B C T)⁻¹ := by
    simp only [GaussianObservationLaw.covariance, GaussianObservationLaw.precision, hGram]
  have hinfo : information M β (σ ^ 2) =
      Real.log ((1 + (β * σ ^ 2)⁻¹ • physicalG B C T).det) / 2 := by
    simpa only [hGram] using hE.2.2.2.1
  have hdetAction (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
      (GaussianObservationLaw.action A).det = A.det := by
    change LinearMap.det A.toEuclideanLin = A.det
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have haction : GaussianObservationLaw.action
      (1 + (β * σ ^ 2)⁻¹ • physicalG B C T) =
      ContinuousLinearMap.id ℝ (V (n + 1)) +
        (β * σ ^ 2)⁻¹ • Original8899NativeAmbient.G B C T := by
    rw [← hphysical]
    ext x
    simp [GaussianObservationLaw.action_apply, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, WithLp.toLp_add, WithLp.toLp_smul]
  refine ⟨hGram, hE, hcov, hinfo, ?_, rfl, ?_⟩
  · rw [hinfo, ← haction, hdetAction]
  · rw [← hcov]
    exact hE.2.1.2.2

end Original63SourceOnly

namespace Original8899FixedTransport
open Original63SourceOnly D5.S3.Observer.Linear

private def oscillatorB : V 4 →L[ℝ] V 4 :=
  (!![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0] : Matrix (Fin 4) (Fin 4) ℝ).
    toEuclideanLin.toContinuousLinearMap

private def sensorC (split : Bool) : V 4 →L[ℝ] V (if split then 2 else 1) :=
  (fun i j => if split then
    (if ((i : ℕ) = 0 ∧ j = 0) ∨ ((i : ℕ) = 1 ∧ j = 2) then 1 else 0)
    else (if j = 0 ∨ j = 2 then 1 else 0) :
      Matrix (Fin (if split then 2 else 1)) (Fin 4) ℝ).toEuclideanLin.toContinuousLinearMap

private theorem actualSensorSum : sensorC false =
    (!![1,0,1,0] : Matrix (Fin 1) (Fin 4) ℝ).toEuclideanLin.toContinuousLinearMap := by
  apply congrArg (fun M : Matrix (Fin 1) (Fin 4) ℝ => M.toEuclideanLin.toContinuousLinearMap)
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem actualSensorSplit : sensorC true =
    (!![1,0,0,0; 0,0,1,0] : Matrix (Fin 2) (Fin 4) ℝ).toEuclideanLin.toContinuousLinearMap := by
  apply congrArg (fun M : Matrix (Fin 2) (Fin 4) ℝ => M.toEuclideanLin.toContinuousLinearMap)
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem actualObservable (split : Bool) : observable oscillatorB (sensorC split) := by
  have hg := actualGeometry
  rcases hg with ⟨_, _, _, _, _, _, _, _, _, _, _, hs, hp, _⟩
  cases split
  · simpa [observable, oscillatorB, actualSensorSum, actualSensorSplit] using hs
  · simpa [observable, oscillatorB, actualSensorSum, actualSensorSplit] using hp

private theorem actualDepth (split : Bool) :
    depthSpec oscillatorB (sensorC split) (if split then 1 else 3) := by
  have hg := actualGeometry
  rcases hg with ⟨_, _, _, _, _, _, _, hsbot, hsnon, hpbot, hpnon, _⟩
  cases split
  · simpa [depthSpec, kernels, oscillatorB, actualSensorSum, actualSensorSplit] using
      (show (let Ns : ℕ → Submodule ℝ (V 4) := fun j =>
        ⨅ k : Fin j, LinearMap.ker
          ((sensorC false).toLinearMap.comp (oscillatorB.toLinearMap ^ (k : ℕ)))
        Ns 4 = ⊥ ∧ ∀ j < 3, Ns (j+1) ≠ ⊥) from
          ⟨by simpa [oscillatorB, actualSensorSum] using hsbot,
            fun j hj => by simpa [oscillatorB, actualSensorSum] using hsnon (j+1) (by omega)⟩)
  · simpa [depthSpec, kernels, oscillatorB, actualSensorSum, actualSensorSplit] using
      (show (let Np : ℕ → Submodule ℝ (V 4) := fun j =>
        ⨅ k : Fin j, LinearMap.ker
          ((sensorC true).toLinearMap.comp (oscillatorB.toLinearMap ^ (k : ℕ)))
        Np 2 = ⊥ ∧ ∀ j < 1, Np (j+1) ≠ ⊥) from
          ⟨by simpa [oscillatorB, actualSensorSplit] using hpbot,
            fun j hj => by simpa [oscillatorB, actualSensorSplit] using hpnon (j+1) (by omega)⟩)

-- Finite arithmetic of a monotone four-entry frame, including split zero layers.
private theorem actualFourWeights (split : Bool) (w : Fin 4 → ℕ)
    (hw : Monotone w) (hwm : ∀ i, w i ≤ (if split then 1 else 3))
    (hcard : ∀ j : Fin 4, (Finset.univ.filter (fun i => w i = (j : ℕ))).card =
      if split then (if (j : ℕ) < 2 then 2 else 0) else 1) :
    w = if split then ![0,0,1,1] else ![0,1,2,3] := by
  have h0 := hwm 0
  have h1 := hwm 1
  have h2 := hwm 2
  have h3 := hwm 3
  have h01 := hw (by decide : (0 : Fin 4) ≤ 1)
  have h12 := hw (by decide : (1 : Fin 4) ≤ 2)
  have h23 := hw (by decide : (2 : Fin 4) ≤ 3)
  have hc0 := hcard 0
  have hc1 := hcard 1
  have hc2 := hcard 2
  have hc3 := hcard 3
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ] at hc0 hc1 hc2 hc3
  cases split <;> simp only [Bool.false_eq_true_eq_False, ↓reduceIte] at *
  all_goals
    interval_cases h0' : w 0 <;> interval_cases h1' : w 1 <;>
      interval_cases h2' : w 2 <;> interval_cases h3' : w 3 <;>
      norm_num [h0', h1', h2', h3'] at *
    all_goals ext i; fin_cases i <;> simp_all

-- This is a whole-experiment bound: constants precede T, its image bases and
-- any realization of the independent Gaussian input. Both signs of sigma
-- are covered, and beta/sigma are fixed before the constants are chosen.
private theorem actualUniformFixedNoise (β σ : ℝ) (hβ : 0 < β) (hσ : σ ≠ 0) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ T : ℝ, ∀ hT : 0 < T, T ≤ δ →
      ∀ (bs : OrthonormalBasis (Fin 4) ℝ
          (trajectoryF oscillatorB (sensorC false) (actualObservable false) T hT).range)
        (bp : OrthonormalBasis (Fin 4) ℝ
          (trajectoryF oscillatorB (sensorC true) (actualObservable true) T hT).range),
        |information (trajectoryM oscillatorB (sensorC false) (actualObservable false) T hT bs)
            β (σ ^ 2) - T / (β * σ ^ 2)| ≤ K * T ^ 2 ∧
        |information (trajectoryM oscillatorB (sensorC true) (actualObservable true) T hT bp)
            β (σ ^ 2) - T / (β * σ ^ 2)| ≤ K * T ^ 2 := by
  obtain ⟨Ks, δs, hKs, hδs, hs⟩ := actualFixedNoise false β (σ ^ 2) hβ (sq_pos_of_ne_zero hσ)
  obtain ⟨Kp, δp, hKp, hδp, hp⟩ := actualFixedNoise true β (σ ^ 2) hβ (sq_pos_of_ne_zero hσ)
  refine ⟨max Ks Kp, min δs δp, le_trans hKs (le_max_left _ _), lt_min hδs hδp, ?_⟩
  intro T hT hTδ bs bp
  have hEs := actualPhysicalExperiment 3 0 oscillatorB (sensorC false) (actualObservable false)
    T hT bs β σ hβ hσ
  have hEp := actualPhysicalExperiment 3 1 oscillatorB (sensorC true) (actualObservable true)
    T hT bp β σ hβ hσ
  have hIs := hEs.2.2.2.2.1
  have hIp := hEp.2.2.2.2.1
  constructor
  · rw [hIs]
    have hh := hs T hT (hTδ.trans (min_le_left _ _))
    have hb : |Real.log ((ContinuousLinearMap.id ℝ (V 4) +
        (β * σ ^ 2)⁻¹ • Original8899NativeAmbient.G oscillatorB (sensorC false) T).det) / 2 -
        T / (β * σ ^ 2)| ≤ Ks * T ^ 2 := by
      simpa [oscillatorB, sensorC, Original8899NativeAmbient.G, Original8899NativeAmbient.A,
        div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg T))
  · rw [hIp]
    have hh := hp T hT (hTδ.trans (min_le_right _ _))
    have hb : |Real.log ((ContinuousLinearMap.id ℝ (V 4) +
        (β * σ ^ 2)⁻¹ • Original8899NativeAmbient.G oscillatorB (sensorC true) T).det) / 2 -
        T / (β * σ ^ 2)| ≤ Kp * T ^ 2 := by
      simpa [oscillatorB, sensorC, Original8899NativeAmbient.G, Original8899NativeAmbient.A,
        div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg T))

end Original8899FixedTransport

namespace Original63SourceOnly

private theorem actualPhysicalMatrix (n r : ℕ)
    (B : V (n + 1) →L[ℝ] V (n + 1)) (C : V (n + 1) →L[ℝ] V (r + 1))
    (hobs : observable B C) (T : ℝ) (hT : 0 < T) :
    physicalG B C T = fun i j => ∫ t in (0 : ℝ)..T,
      ⟪C ((NormedSpace.exp (t • B)) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)),
        C ((NormedSpace.exp (t • B)) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j))⟫_ℝ := by
  classical
  let F := trajectoryF B C hobs T hT
  have hf := Classical.choose_spec
    (ObservableTrajectoryCoordinates.observable_trajectory_coordinates_all_bases
      (n + 1) (r + 1) B C T hT hobs)
  have hdim : finrank ℝ F.range = n + 1 := hf.2.2.1
  let imageBasis : OrthonormalBasis (Fin (n + 1)) ℝ F.range :=
    (stdOrthonormalBasis ℝ F.range).reindex (finCongr hdim)
  have hu := Classical.choose_spec (hf.2.2.2 imageBasis)
  have hM := Classical.choose_spec hu
  let M := trajectoryM B C hobs T hT imageBasis
  have hGram : M.transpose * M = physicalG B C T := by
    simpa only [M, trajectoryM, physicalG] using hM.2.2.2.2.2.2.2.2
  have hphysical : GaussianObservationLaw.action (physicalG B C T) =
      Original8899NativeAmbient.G B C T := by
    rw [← hGram, Original8899NativeAmbient.action_gram]
    change (GaussianObservationLaw.action M).adjoint.comp (GaussianObservationLaw.action M) = _
    rw [hM.2.2.2.2.2.1]
    exact (hM.2.2.2.2.2.2.1).trans hM.2.2.2.2.2.2.2.1
  let std := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  have hc : Original8899NativeAmbient.coordinates std
      (GaussianObservationLaw.action (physicalG B C T)) = physicalG B C T := by
    ext i j
    simp [Original8899NativeAmbient.coordinates, std, LinearMap.toMatrix_apply,
      OrthonormalBasis.repr_apply_apply, GaussianObservationLaw.action_apply,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single, Matrix.mulVec, dotProduct]
  rw [← hc, hphysical]
  exact Original8899NativeAmbient.matrix_integral_gram std
    (Original8899NativeAmbient.A B C) (Original8899NativeAmbient.continuous_A B C) 0 T

end Original63SourceOnly

namespace Original8899FixedTransport
open Original63SourceOnly D5.S3.Observer.Linear

private theorem actualOriginal64 (β : ℝ) (hβ : 0 < β) :
    (∀ j : Fin 4, multiplicity oscillatorB (sensorC false) j = 1) ∧
    (∀ j : Fin 4, multiplicity oscillatorB (sensorC true) j = if (j : ℕ) < 2 then 2 else 0) ∧
    depthSpec oscillatorB (sensorC false) 3 ∧ depthSpec oscillatorB (sensorC true) 1 ∧
    Tendsto (fun T => (physicalG oscillatorB (sensorC false) T).det / T ^ 16)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2688000 : ℝ)) ∧
    Tendsto (fun T => (physicalG oscillatorB (sensorC true) T).det / T ^ 8)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 36 : ℝ)) ∧
    (∀ σ : ℝ, σ ≠ 0 → ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ T : ℝ, ∀ hT : 0 < T, T ≤ δ →
        ∀ (bs : OrthonormalBasis (Fin 4) ℝ
            (trajectoryF oscillatorB (sensorC false) (actualObservable false) T hT).range)
          (bp : OrthonormalBasis (Fin 4) ℝ
            (trajectoryF oscillatorB (sensorC true) (actualObservable true) T hT).range),
          |information (trajectoryM oscillatorB (sensorC false) (actualObservable false) T hT bs)
              β (σ ^ 2) - T / (β * σ ^ 2)| ≤ K * T ^ 2 ∧
          |information (trajectoryM oscillatorB (sensorC true) (actualObservable true) T hT bp)
              β (σ ^ 2) - T / (β * σ ^ 2)| ≤ K * T ^ 2) ∧
    (∀ (basisS : ∀ T (hT : 0 < T), OrthonormalBasis (Fin 4) ℝ
          (trajectoryF oscillatorB (sensorC false) (actualObservable false) T hT).range)
       (basisP : ∀ T (hT : 0 < T), OrthonormalBasis (Fin 4) ℝ
          (trajectoryF oscillatorB (sensorC true) (actualObservable true) T hT).range),
      let MS := trajectoryFamily oscillatorB (sensorC false) (actualObservable false) basisS
      let MP := trajectoryFamily oscillatorB (sensorC true) (actualObservable true) basisP
      (∀ T : ℝ, ∀ hT : 0 < T, ∀ σ : ℝ, σ ≠ 0 →
        physicalExperiment oscillatorB (sensorC false) T β σ (MS T) ∧
        physicalExperiment oscillatorB (sensorC true) T β σ (MP T)) ∧
      noiseConclusion oscillatorB (sensorC false) 3 MS β ∧
      noiseConclusion oscillatorB (sensorC true) 1 MP β ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ∃ (hs : (physicalG oscillatorB (sensorC false) T).IsHermitian)
          (hp : (physicalG oscillatorB (sensorC true) T).IsHermitian),
          gramEigenvalues (MS T) = (fun i => hs.eigenvalues₀
            ((Fin.castOrderIso (Fintype.card_fin 4)).symm i)) ∧
          gramEigenvalues (MP T) = (fun i => hp.eigenvalues₀
            ((Fin.castOrderIso (Fintype.card_fin 4)).symm i))) ∧
      (∃ cs Cs cp Cp : ℝ, 0 < cs ∧ 0 < Cs ∧ 0 < cp ∧ 0 < Cp ∧
        (∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ i : Fin 4,
          cs * T ^ (![1,3,5,7] i : ℕ) ≤ gramEigenvalues (MS T) i ∧
          gramEigenvalues (MS T) i ≤ Cs * T ^ (![1,3,5,7] i : ℕ) ∧
          cp * T ^ (![1,1,3,3] i : ℕ) ≤ gramEigenvalues (MP T) i ∧
          gramEigenvalues (MP T) i ≤ Cp * T ^ (![1,1,3,3] i : ℕ)) ∧
        (∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ v : ℝ, 0 < v →
          information (MS T) β v = (1 / 2 : ℝ) *
            ∑ i, Real.log (1 + gramEigenvalues (MS T) i / (β * v)) ∧
          (bayesRisk (MS T) β v).toReal = (1 / 2 : ℝ) *
            ∑ i, v / (β * v + gramEigenvalues (MS T) i) ∧
          information (MP T) β v = (1 / 2 : ℝ) *
            ∑ i, Real.log (1 + gramEigenvalues (MP T) i / (β * v)) ∧
          (bayesRisk (MP T) β v).toReal = (1 / 2 : ℝ) *
            ∑ i, v / (β * v + gramEigenvalues (MP T) i))) ∧
      ((fun T => information (MS T) β (T ^ (4 : ℕ)) - 2 * Real.log (1 / T))
        =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
      ((fun T => information (MP T) β (T ^ (4 : ℕ)) - 4 * Real.log (1 / T))
        =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
      Tendsto (fun T => (bayesRisk (MS T) β (T ^ (4 : ℕ))).toReal)
        (𝓝[>] 0) (𝓝 β⁻¹) ∧
      Tendsto (fun T => (bayesRisk (MP T) β (T ^ (4 : ℕ))).toReal)
        (𝓝[>] 0) (𝓝 0) ∧
      (∀ σ : ℝ → ℝ, (∀ T, 0 < T → σ T ^ 2 = T ^ (4 : ℕ)) →
        ((fun T => information (MS T) β (σ T ^ 2) - 2 * Real.log (1 / T))
          =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
        ((fun T => information (MP T) β (σ T ^ 2) - 4 * Real.log (1 / T))
          =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
        Tendsto (fun T => (bayesRisk (MS T) β (σ T ^ 2)).toReal)
          (𝓝[>] 0) (𝓝 β⁻¹) ∧
        Tendsto (fun T => (bayesRisk (MP T) β (σ T ^ 2)).toReal)
          (𝓝[>] 0) (𝓝 0))) := by
  classical
  have hg := actualGeometry
  rcases hg with ⟨hskew, hgainS, hgainP, hdimS, hdimP, hes, hep,
    hsbot, hsnon, hpbot, hpnon, hsobs, hpobs, hspanS, hprojS, hprojP,
    hPs, hPp, hHs, hHp, hdetS, hdetP⟩
  have hmulS (j : Fin 4) : multiplicity oscillatorB (sensorC false) j = 1 := by
    simpa [multiplicity, layer, kernels, oscillatorB, actualSensorSum] using hes j
  have hmulP (j : Fin 4) : multiplicity oscillatorB (sensorC true) j =
      if (j : ℕ) < 2 then 2 else 0 := by
    simpa [multiplicity, layer, kernels, oscillatorB, actualSensorSplit] using hep j
  have hd := actualDeterminants
  have hdetPhysicalS : Tendsto
      (fun T => (physicalG oscillatorB (sensorC false) T).det / T ^ 16)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2688000 : ℝ)) := by
    refine hd.1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with T hT
    rw [actualPhysicalMatrix 3 0 oscillatorB (sensorC false) (actualObservable false) T hT]
    simp [oscillatorB, actualSensorSum, actualSensorSplit, EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  have hdetPhysicalP : Tendsto
      (fun T => (physicalG oscillatorB (sensorC true) T).det / T ^ 8)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 36 : ℝ)) := by
    refine hd.2.1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with T hT
    rw [actualPhysicalMatrix 3 1 oscillatorB (sensorC true) (actualObservable true) T hT]
    simp [oscillatorB, actualSensorSum, actualSensorSplit, EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  refine ⟨hmulS, hmulP, actualDepth false, actualDepth true,
    hdetPhysicalS, hdetPhysicalP, (fun σ hσ => actualUniformFixedNoise β σ hβ hσ), ?_⟩
  intro basisS basisP MS MP
  have hS := actualTrajectory 3 0 3 oscillatorB (sensorC false)
    (actualObservable false) (actualDepth false) β hβ basisS
  have hP := actualTrajectory 3 1 1 oscillatorB (sensorC true)
    (actualObservable true) (actualDepth true) β hβ basisP
  have hNS := hS.2.1
  have hNP := hP.2.1
  obtain ⟨wS, cs, Cs, hwS, hwmS, hlastS, hcardS, hcs, hCs, hbS, hstatS⟩ := hS.2.2
  obtain ⟨wP, cp, Cp, hwP, hwmP, hlastP, hcardP, hcp, hCp, hbP, hstatP⟩ := hP.2.2
  have hwSEq : wS = ![0,1,2,3] := actualFourWeights false wS hwS hwmS
    (fun j => by simpa only [hmulS j] using hcardS j)
  have hwPEq : wP = ![0,0,1,1] := actualFourWeights true wP hwP hwmP
    (fun j => by simpa only [hmulP j] using hcardP j)
  have hIS : (fun T => information (MS T) β (T ^ (4 : ℕ)) - 2 * Real.log (1 / T))
      =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
    have hh := hNS.1 4
    convert hh using 1 <;> norm_num [hmulS, Fin.sum_univ_succ, Real.rpow_natCast]
  have hIP : (fun T => information (MP T) β (T ^ (4 : ℕ)) - 4 * Real.log (1 / T))
      =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
    have hh := hNP.1 4
    convert hh using 1 <;> norm_num [hmulP, Fin.sum_univ_succ, Real.rpow_natCast]
  have hRS : Tendsto (fun T => (bayesRisk (MS T) β (T ^ (4 : ℕ))).toReal)
      (𝓝[>] 0) (𝓝 β⁻¹) := by
    have hthreshold : ∀ j : Fin 4, 0 < multiplicity oscillatorB (sensorC false) j →
        (4 : ℝ) ≠ (2 * (j : ℕ) + 1 : ℕ) := by
      intro j _; fin_cases j <;> norm_num
    have hh := hNS.2.1 4 hthreshold
    convert hh using 1
    · simp only [Real.rpow_natCast]
    · simp [hmulS, Fin.sum_univ_succ]
      field_simp [hβ.ne']
      ring
  have hRP : Tendsto (fun T => (bayesRisk (MP T) β (T ^ (4 : ℕ))).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    have hthreshold : ∀ j : Fin 2, 0 < multiplicity oscillatorB (sensorC true) j →
        (4 : ℝ) ≠ (2 * (j : ℕ) + 1 : ℕ) := by
      intro j _; fin_cases j <;> norm_num
    have hh := hNP.2.1 4 hthreshold
    convert hh using 1 <;> norm_num [hmulP, Fin.sum_univ_succ, Real.rpow_natCast]
  refine ⟨?_, hNS, hNP, ?_, ?_, hIS, hIP, hRS, hRP, ?_⟩
  · intro T hT σ hσ
    have hs := actualPhysicalExperiment 3 0 oscillatorB (sensorC false) (actualObservable false)
      T hT (basisS T hT) β σ hβ hσ
    have hp := actualPhysicalExperiment 3 1 oscillatorB (sensorC true) (actualObservable true)
      T hT (basisP T hT) β σ hβ hσ
    simpa only [MS, MP, trajectoryFamily, dif_pos hT] using And.intro hs hp
  · intro T hT
    have hGs := (hS.1 T hT).1
    have hGp := (hP.1 T hT).1
    have hs : (physicalG oscillatorB (sensorC false) T).IsHermitian := by
      rw [← hGs]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.posSemidef_conjTranspose_mul_self (MS T)).isHermitian
    have hp : (physicalG oscillatorB (sensorC true) T).IsHermitian := by
      rw [← hGp]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.posSemidef_conjTranspose_mul_self (MP T)).isHermitian
    refine ⟨hs, hp, ?_, ?_⟩
    · unfold gramEigenvalues
      rw [hGs]
      rfl
    · unfold gramEigenvalues
      rw [hGp]
      rfl
  · refine ⟨cs, Cs, cp, Cp, hcs, hCs, hcp, hCp, ?_, ?_⟩
    · filter_upwards [hbS, hbP] with T hs hp
      intro i
      have hqs : 2 * wS i + 1 = (![1,3,5,7] i : ℕ) := by rw [hwSEq]; fin_cases i <;> norm_num
      have hqp : 2 * wP i + 1 = (![1,1,3,3] i : ℕ) := by rw [hwPEq]; fin_cases i <;> norm_num
      simpa only [hqs, hqp] using And.intro (hs i).1 (And.intro (hs i).2 (hp i))
    · filter_upwards [hstatS, hstatP] with T hs hp
      intro v hv
      exact ⟨(hs v hv).1, (hs v hv).2, (hp v hv).1, (hp v hv).2⟩
  · intro σ hσ
    have heIS : (fun T => information (MS T) β (σ T ^ 2) - 2 * Real.log (1 / T))
        =ᶠ[𝓝[>] 0] (fun T => information (MS T) β (T ^ (4 : ℕ)) - 2 * Real.log (1 / T)) := by
      filter_upwards [self_mem_nhdsWithin] with T hT
      rw [hσ T hT]
    have heIP : (fun T => information (MP T) β (σ T ^ 2) - 4 * Real.log (1 / T))
        =ᶠ[𝓝[>] 0] (fun T => information (MP T) β (T ^ (4 : ℕ)) - 4 * Real.log (1 / T)) := by
      filter_upwards [self_mem_nhdsWithin] with T hT
      rw [hσ T hT]
    have heRS : (fun T => (bayesRisk (MS T) β (σ T ^ 2)).toReal)
        =ᶠ[𝓝[>] 0] (fun T => (bayesRisk (MS T) β (T ^ (4 : ℕ))).toReal) := by
      filter_upwards [self_mem_nhdsWithin] with T hT
      rw [hσ T hT]
    have heRP : (fun T => (bayesRisk (MP T) β (σ T ^ 2)).toReal)
        =ᶠ[𝓝[>] 0] (fun T => (bayesRisk (MP T) β (T ^ (4 : ℕ))).toReal) := by
      filter_upwards [self_mem_nhdsWithin] with T hT
      rw [hσ T hT]
    exact ⟨hIS.congr' heIS.symm Filter.EventuallyEq.rfl,
      hIP.congr' heIP.symm Filter.EventuallyEq.rfl,
      hRS.congr' heRS.symm, hRP.congr' heRP.symm⟩

end Original8899FixedTransport

namespace Original63SourceOnly
private def Original63Clause : Prop :=
  ∀ (n r m cutoff : ℕ)
      (B : V (n + 1) →L[ℝ] V (n + 1))
      (C : V (n + 1) →L[ℝ] V (r + 1))
      (hobs : observable B C) (hm : depthSpec B C m) (hcut : m ≤ cutoff)
      (ell : Fin (cutoff + 1) → Polynomial ℝ) (hell : polynomialON cutoff ell)
      (β : ℝ) (hβ : 0 < β)
      (basis : ∀ T (hT : 0 < T), OrthonormalBasis (Fin (n + 1)) ℝ
        (trajectoryF B C hobs T hT).range),
      let MT := trajectoryFamily B C hobs basis
      let MM := momentM B C cutoff ell
      (∀ T (hT : 0 < T),
        (MT T).transpose * MT T = physicalG B C T ∧
        (∀ σ : ℝ, 0 < σ ^ 2 → finiteExperiment (MT T) β σ)) ∧
      actualMomentCoordinates B C hobs cutoff ell ∧
      normalizedMomentApproximation B C cutoff ell ∧
      (∀ T, 0 < T → ∀ σ : ℝ, 0 < σ ^ 2 → finiteExperiment (MM T) β σ) ∧
      noiseConclusion B C m MT β ∧ noiseConclusion B C m MM β
end Original63SourceOnly
namespace Original8899FixedTransport
private def GeometryClause : Prop :=
  let V := EuclideanSpace ℝ (Fin 4)
  let Bm : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0]
  let Cs : Matrix (Fin 1) (Fin 4) ℝ := !![1,0,1,0]
  let Cp : Matrix (Fin 2) (Fin 4) ℝ := !![1,0,0,0; 0,0,1,0]
  let b := Bm.toEuclideanLin.toContinuousLinearMap
  let cs := Cs.toEuclideanLin.toContinuousLinearMap
  let cp := Cp.toEuclideanLin.toContinuousLinearMap
  let Ns : ℕ → Submodule ℝ V := fun j =>
    ⨅ k : Fin j, LinearMap.ker (cs.toLinearMap.comp (b.toLinearMap ^ (k : ℕ)))
  let Np : ℕ → Submodule ℝ V := fun j =>
    ⨅ k : Fin j, LinearMap.ker (cp.toLinearMap.comp (b.toLinearMap ^ (k : ℕ)))
  let Es : ℕ → Submodule ℝ V := fun j => Ns j ⊓ (Ns (j+1))ᗮ
  let Ep : ℕ → Submodule ℝ V := fun j => Np j ⊓ (Np (j+1))ᗮ
  let vs : Fin 4 → V :=
    ![toLp 2 ![1,0,1,0], toLp 2 ![0,1,0,2],
      toLp 2 ![1,0,-1,0], toLp 2 ![0,2,0,-1]]
  let Ps : ℝ → V →L[ℝ] EuclideanSpace ℝ (Fin 1) := fun t =>
    ∑ j : Fin 4, (t^(j : ℕ)/(Nat.factorial (j : ℕ) : ℝ)) •
      cs.comp ((b^(j : ℕ)).comp ((Es j).starProjection))
  let Pp : ℝ → V →L[ℝ] EuclideanSpace ℝ (Fin 2) := fun t =>
    ∑ j : Fin 4, (t^(j : ℕ)/(Nat.factorial (j : ℕ) : ℝ)) •
      cp.comp ((b^(j : ℕ)).comp ((Ep j).starProjection))
  let e : Fin 4 → V := fun i => toLp 2 (Pi.single i (1 : ℝ))
  let Hs : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
    ∫ t in (0 : ℝ)..1, ⟪Ps t (e i),Ps t (e j)⟫_ℝ
  let Hp : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
    ∫ t in (0 : ℝ)..1, ⟪Pp t (e i),Pp t (e j)⟫_ℝ
  Bm.transpose = -Bm ∧ (Cs.transpose * Cs).trace = 2 ∧
  (Cp.transpose * Cp).trace = 2 ∧
  (∀ j : Fin 5, finrank ℝ (Ns j) = 4 - (j : ℕ)) ∧
  (∀ j : Fin 5, finrank ℝ (Np j) = if j = 0 then 4 else if j = 1 then 2 else 0) ∧
  (∀ j : Fin 4, finrank ℝ (Es j) = 1) ∧
  (∀ j : Fin 4, finrank ℝ (Ep j) = if (j : ℕ) < 2 then 2 else 0) ∧
  Ns 4 = ⊥ ∧ (∀ j < 4, Ns j ≠ ⊥) ∧
  Np 2 = ⊥ ∧ (∀ j < 2, Np j ≠ ⊥) ∧
  (∀ x : V, (∀ k : Fin 4, cs ((b ^ (k : ℕ)) x) = 0) → x = 0) ∧
  (∀ x : V, (∀ k : Fin 4, cp ((b ^ (k : ℕ)) x) = 0) → x = 0) ∧
  (∀ j : Fin 4, Es j = Submodule.span ℝ {vs j}) ∧
  (∀ j : Fin 4, ∀ x : V,
    (Es j).starProjection x = (⟪vs j,x⟫_ℝ/‖vs j‖^2) • vs j) ∧
  (∀ x : V,
    (Ep 0).starProjection x = toLp 2 ![x 0,0,x 2,0] ∧
    (Ep 1).starProjection x = toLp 2 ![0,x 1,0,x 3] ∧
    (Ep 2).starProjection x = 0 ∧ (Ep 3).starProjection x = 0) ∧
  (∀ t : ℝ, Ps t =
    (!![1+3*t^2/4,t+2*t^3/5,1-3*t^2/4,2*t-t^3/5] :
      Matrix (Fin 1) (Fin 4) ℝ).toEuclideanLin.toContinuousLinearMap) ∧
  (∀ t : ℝ, Pp t =
    (!![1,t,0,0; 0,0,1,2*t] : Matrix (Fin 2) (Fin 4) ℝ).
      toEuclideanLin.toContinuousLinearMap) ∧
  Hs = !![129/80,67/80,71/80,13/10;
    67/80,271/525,29/80,407/525;
    71/80,29/80,49/80,3/5; 13/10,407/525,3/5,619/525] ∧
  Hp = !![1,1/2,0,0; 1/2,1/3,0,0; 0,0,1,1; 0,0,1,4/3] ∧
  Hs.det = 1/2688000 ∧ Hp.det = 1/36
private def NativeClause : Prop :=
  ∀ (split : Bool),
      let V := EuclideanSpace ℝ (Fin 4)
      let p := if split then 2 else 1
      let W := EuclideanSpace ℝ (Fin p)
      let Bm : Matrix (Fin 4) (Fin 4) ℝ :=
        !![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0]
      let Cm : Matrix (Fin p) (Fin 4) ℝ := fun i j =>
        if split then (if ((i : ℕ) = 0 ∧ j = 0) ∨ ((i : ℕ) = 1 ∧ j = 2) then 1 else 0)
        else (if j = 0 ∨ j = 2 then 1 else 0)
      let B := Bm.toEuclideanLin
      let C := Cm.toEuclideanLin
      let n := Module.finrank ℝ V
      let N : ℕ → Submodule ℝ V := fun j =>
        ⨅ k : Fin j, LinearMap.ker (C.comp (B ^ (k : ℕ)))
      let U : Submodule ℝ V := (N n)ᗮ
      let E : Fin n → Submodule ℝ V := fun j => N j ⊓ (N (j + 1))ᗮ
      let b : V →L[ℝ] V := B.toContinuousLinearMap
      let c : V →L[ℝ] W := C.toContinuousLinearMap
      let Q : Fin n → U →L[ℝ] U := fun j =>
        U.orthogonalProjectionOnto.comp ((E j).starProjection.comp U.subtypeL)
      let d : ℝ → U →L[ℝ] U := fun T =>
        ∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ)) • Q j
      let e : ℝ → U →L[ℝ] U := fun T =>
        ∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ))⁻¹ • Q j
      let A : ℝ → U →L[ℝ] W := fun t =>
        c.comp ((NormedSpace.exp (t • b)).comp U.subtypeL)
      let G : ℝ → U →L[ℝ] U := fun T =>
        ∫ t in (0 : ℝ)..T, (A t).adjoint.comp (A t)
      let F₀ : ℝ → U →L[ℝ] W := fun s =>
        ∑ j : Fin n, (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) •
          c.comp ((b ^ (j : ℕ)).comp ((E j).starProjection.comp U.subtypeL))
      let F₄ : ℝ → U →L[ℝ] W := fun s =>
        ∑ j : Fin 4, (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) •
          c.comp ((b ^ (j : ℕ)).comp
            ((N j ⊓ (N (j+1))ᗮ).starProjection.comp U.subtypeL))
      let H : U →L[ℝ] U := ∫ s in (0 : ℝ)..1, (F₀ s).adjoint.comp (F₀ s)
      U = ⊤ ∧
      (∀ T : ℝ, 0 < T →
        (d T).comp (e T) = ContinuousLinearMap.id ℝ U ∧
        (e T).comp (d T) = ContinuousLinearMap.id ℝ U ∧
        (e T).comp ((G T).comp (e T)) =
          ∫ s in (0 : ℝ)..1,
            (Real.sqrt T • (A (T * s)).comp (e T)).adjoint.comp
              (Real.sqrt T • (A (T * s)).comp (e T))) ∧
      (∀ x : U, x ≠ 0 → 0 < ⟪x, H x⟫_ℝ) ∧
      (∃ R : ℝ, 0 ≤ R ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T * ‖b‖ < 1 →
        ‖(e T).comp ((G T).comp (e T)) - H‖ ≤ R * T) ∧
      (∀ s : ℝ, F₀ s = F₄ s) ∧
      H = (∫ s in (0 : ℝ)..1, (F₄ s).adjoint.comp (F₄ s)) ∧
      Tendsto (fun T : ℝ => (e T).comp ((G T).comp (e T)))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds H)
private def EnergyClause : Prop :=
  let J : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0,1,0,0; -1,0,0,0; 0,0,0,1; 0,0,-1,0]
  let B : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0,1,0,0; -1,0,0,0; 0,0,0,2; 0,0,-2,0]
  let L : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,1,2,1]
  let Li : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,1,1/2,1]
  let S : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,1,4,1]
  L.transpose*L = S ∧ L*Li = 1 ∧ Li*L = 1 ∧
    L*J*L.transpose = B ∧ L*(J*S)*Li = B
private def Original64Clause : Prop :=
  ∀ (β : ℝ) (hβ : 0 < β),
      (∀ j : Fin 4, multiplicity oscillatorB (sensorC false) j = 1) ∧
      (∀ j : Fin 4, multiplicity oscillatorB (sensorC true) j = if (j : ℕ) < 2 then 2 else 0) ∧
      depthSpec oscillatorB (sensorC false) 3 ∧ depthSpec oscillatorB (sensorC true) 1 ∧
      Tendsto (fun T => (physicalG oscillatorB (sensorC false) T).det / T ^ 16)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2688000 : ℝ)) ∧
      Tendsto (fun T => (physicalG oscillatorB (sensorC true) T).det / T ^ 8)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / 36 : ℝ)) ∧
      (∀ σ : ℝ, σ ≠ 0 → ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
        ∀ T : ℝ, ∀ hT : 0 < T, T ≤ δ →
          ∀ (bs : OrthonormalBasis (Fin 4) ℝ
              (trajectoryF oscillatorB (sensorC false) (actualObservable false) T hT).range)
            (bp : OrthonormalBasis (Fin 4) ℝ
              (trajectoryF oscillatorB (sensorC true) (actualObservable true) T hT).range),
            |information (trajectoryM oscillatorB (sensorC false) (actualObservable false) T hT bs)
                β (σ ^ 2) - T / (β * σ ^ 2)| ≤ K * T ^ 2 ∧
            |information (trajectoryM oscillatorB (sensorC true) (actualObservable true) T hT bp)
                β (σ ^ 2) - T / (β * σ ^ 2)| ≤ K * T ^ 2) ∧
      (∀ (basisS : ∀ T (hT : 0 < T), OrthonormalBasis (Fin 4) ℝ
            (trajectoryF oscillatorB (sensorC false) (actualObservable false) T hT).range)
         (basisP : ∀ T (hT : 0 < T), OrthonormalBasis (Fin 4) ℝ
            (trajectoryF oscillatorB (sensorC true) (actualObservable true) T hT).range),
        let MS := trajectoryFamily oscillatorB (sensorC false) (actualObservable false) basisS
        let MP := trajectoryFamily oscillatorB (sensorC true) (actualObservable true) basisP
        (∀ T : ℝ, ∀ hT : 0 < T, ∀ σ : ℝ, σ ≠ 0 →
          physicalExperiment oscillatorB (sensorC false) T β σ (MS T) ∧
          physicalExperiment oscillatorB (sensorC true) T β σ (MP T)) ∧
        noiseConclusion oscillatorB (sensorC false) 3 MS β ∧
        noiseConclusion oscillatorB (sensorC true) 1 MP β ∧
        (∀ T : ℝ, ∀ hT : 0 < T,
          ∃ (hs : (physicalG oscillatorB (sensorC false) T).IsHermitian)
            (hp : (physicalG oscillatorB (sensorC true) T).IsHermitian),
            gramEigenvalues (MS T) = (fun i => hs.eigenvalues₀
              ((Fin.castOrderIso (Fintype.card_fin 4)).symm i)) ∧
            gramEigenvalues (MP T) = (fun i => hp.eigenvalues₀
              ((Fin.castOrderIso (Fintype.card_fin 4)).symm i))) ∧
        (∃ cs Cs cp Cp : ℝ, 0 < cs ∧ 0 < Cs ∧ 0 < cp ∧ 0 < Cp ∧
          (∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ i : Fin 4,
            cs * T ^ (![1,3,5,7] i : ℕ) ≤ gramEigenvalues (MS T) i ∧
            gramEigenvalues (MS T) i ≤ Cs * T ^ (![1,3,5,7] i : ℕ) ∧
            cp * T ^ (![1,1,3,3] i : ℕ) ≤ gramEigenvalues (MP T) i ∧
            gramEigenvalues (MP T) i ≤ Cp * T ^ (![1,1,3,3] i : ℕ)) ∧
          (∀ᶠ T in 𝓝[>] (0 : ℝ), ∀ v : ℝ, 0 < v →
            information (MS T) β v = (1 / 2 : ℝ) *
              ∑ i, Real.log (1 + gramEigenvalues (MS T) i / (β * v)) ∧
            (bayesRisk (MS T) β v).toReal = (1 / 2 : ℝ) *
              ∑ i, v / (β * v + gramEigenvalues (MS T) i) ∧
            information (MP T) β v = (1 / 2 : ℝ) *
              ∑ i, Real.log (1 + gramEigenvalues (MP T) i / (β * v)) ∧
            (bayesRisk (MP T) β v).toReal = (1 / 2 : ℝ) *
              ∑ i, v / (β * v + gramEigenvalues (MP T) i))) ∧
        ((fun T => information (MS T) β (T ^ (4 : ℕ)) - 2 * Real.log (1 / T))
          =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
        ((fun T => information (MP T) β (T ^ (4 : ℕ)) - 4 * Real.log (1 / T))
          =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
        Tendsto (fun T => (bayesRisk (MS T) β (T ^ (4 : ℕ))).toReal)
          (𝓝[>] 0) (𝓝 β⁻¹) ∧
        Tendsto (fun T => (bayesRisk (MP T) β (T ^ (4 : ℕ))).toReal)
          (𝓝[>] 0) (𝓝 0) ∧
        (∀ σ : ℝ → ℝ, (∀ T, 0 < T → σ T ^ 2 = T ^ (4 : ℕ)) →
          ((fun T => information (MS T) β (σ T ^ 2) - 2 * Real.log (1 / T))
            =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
          ((fun T => information (MP T) β (σ T ^ 2) - 4 * Real.log (1 / T))
            =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ))) ∧
          Tendsto (fun T => (bayesRisk (MS T) β (σ T ^ 2)).toReal)
            (𝓝[>] 0) (𝓝 β⁻¹) ∧
          Tendsto (fun T => (bayesRisk (MP T) β (σ T ^ 2)).toReal)
            (𝓝[>] 0) (𝓝 0)))
end Original8899FixedTransport

-- WHOLE ORIGINAL §§6.3/6.4 ENDPOINT. No assumed expected conclusion.
-- All source above, including this endpoint, remains UNCOMPILED.
example : Original63SourceOnly.Original63Clause ∧
    Original8899FixedTransport.GeometryClause ∧
    Original8899FixedTransport.NativeClause ∧
    Original8899FixedTransport.EnergyClause ∧
    Original8899FixedTransport.Original64Clause := by
  exact ⟨Original63SourceOnly.actualOriginal63,
    Original8899FixedTransport.actualGeometry,
    Original8899FixedTransport.actualNative,
    Original8899FixedTransport.actualEnergy,
    Original8899FixedTransport.actualOriginal64⟩

end

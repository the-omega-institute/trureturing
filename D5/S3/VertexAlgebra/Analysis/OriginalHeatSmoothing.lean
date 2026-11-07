/- GID: D5/S3/VertexAlgebra/Analysis/OriginalHeatSmoothing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalHeatSmoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original positive-time heat smoothing on the existing coherent smooth domain. -/

import D5.S3.VertexAlgebra.Analysis.OriginalHeat
import D5.S3.VertexAlgebra.Analysis.OriginalSmoothDomain

/-!
The scalar estimate is global on all nonnegative real energies; finite sums are
used only for original algebraic proofs and finite-rank approximation. The input
to heatSmoothing and heatFamily is an arbitrary original Hilbert vector.

All original lattice/Hm/Sugawara, Mathlib Apache-2.0, PhysLean eigenbasis and
Scott Armstrong semigroup attributions from OriginalHeat remain in force.
The existing smoothFamilies/evaluation.range are used literally; no new smooth
carrier or hypothesis assuming coherence is introduced. Utility is none: these
are analytic constructions, not a finite computation or a proposed checker.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped BigOperators InnerProductSpace Topology NNReal VertexOperator
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open Lattice.OriginalChargedEnergy SourceBPZ.OriginalMatterHermitian
open Model
variable (M : Model)

attribute [local irreducible] Model.heat

/-- Finite for every positive time; order zero is exactly one. -/
def heatSmoothingConstant (k : ℕ) (t : ℝ) : ℝ := (max 1 ((k : ℝ) / t))^k

private theorem heat_scalar_bound (k : ℕ) (t E : ℝ) (ht : 0 < t) (hE : 0 ≤ E) :
    (1+E)^k * Real.exp (-t*E) ≤ heatSmoothingConstant k t := by
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero, one_mul, heatSmoothingConstant]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hE)
  · have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    let a := t/(k : ℝ)
    let B := max 1 ((k : ℝ) / t)
    have ha : 0 ≤ a := (div_pos ht hk').le
    have hB : 1 ≤ B := le_max_left _ _
    have hBa : 1 ≤ B*a := by
      calc
        1 = ((k : ℝ) / t)*a := by dsimp [a]; field_simp [ne_of_gt ht, ne_of_gt hk']
        _ ≤ B*a := mul_le_mul_of_nonneg_right (le_max_right _ _) ha
    have hlinear : 1+E ≤ B*(1+a*E) := by
      have hh := mul_le_mul_of_nonneg_right hBa hE
      nlinarith
    have hexp : 1+a*E ≤ Real.exp (a*E) := by
      simpa only [add_comm] using Real.add_one_le_exp (a*E)
    have hbase : 1+E ≤ B*Real.exp (a*E) :=
      hlinear.trans (mul_le_mul_of_nonneg_left hexp (by linarith))
    have hp : (1+E)^k ≤ (B*Real.exp (a*E))^k := by gcongr
    calc
      (1+E)^k * Real.exp (-t*E) ≤
          (B*Real.exp (a*E))^k * Real.exp (-t*E) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = B^k := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        have he : (k : ℝ) * (a * E) + (-t * E) = 0 := by
          dsimp [a]
          field_simp [ne_of_gt ht, ne_of_gt hk']
          ring
        rw [he, Real.exp_zero, mul_one]
      _ = heatSmoothingConstant k t := rfl

private theorem smoothing_constant_nonnegative (k : ℕ) (t : ℝ) :
    0 ≤ heatSmoothingConstant k t := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) k

private theorem smoothing_core_bound (k : ℕ) (t : ℝ≥0) (ht : 0 < t)
    (v : Carrier M.D) :
    ‖M.heat k t (M.embed k v)‖ ≤ heatSmoothingConstant k t * ‖M.embed 0 v‖ := by
  rw [heat_embed]
  apply finite_multiplier_bound M 0 k _ (smoothing_constant_nonnegative k t) v
  intro E hE
  have hE' : (0 : ℝ) ≤ (E : ℝ) := by
    exact_mod_cast stateEnergies_nonneg M.positive v E hE
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, mul_one]
  simpa only [mul_comm, add_comm] using heat_scalar_bound k t E ht hE'

/-- Dense-original-core extension into the literal k-th Sobolev completion, only at t>0. -/
def Model.heatSmoothing (k : ℕ) (t : ℝ≥0) (_ht : 0 < t) :
    M.Hilbert →L[ℂ] M.Sobolev k :=
  ((M.heat k t).toLinearMap.comp (M.embed k)).extendOfNorm (M.embed 0)

private theorem heatSmoothing_embed_heat (k : ℕ) (t : ℝ≥0) (ht : 0 < t)
    (v : Carrier M.D) :
    M.heatSmoothing k t ht (M.embed 0 v) = M.heat k t (M.embed k v) := by
  apply LinearMap.extendOfNorm_eq (embed_dense M 0)
  exact ⟨heatSmoothingConstant k t, smoothing_core_bound M k t ht⟩

/-- The smoothing extension has the same literal original Sugawara core, at every order. -/
theorem heatSmoothing_embed (k : ℕ) (t : ℝ≥0) (ht : 0 < t) (v : Carrier M.D) :
    M.heatSmoothing k t ht (M.embed 0 v) =
      M.embed k (∑ E ∈ stateEnergies M.D v,
        (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ) • gradeProjection M.D E v) := by
  rw [heatSmoothing_embed_heat, heat_embed]

/-- Global quantitative smoothing, for arbitrary original Hilbert inputs and every natural k. -/
theorem heatSmoothing_bound (k : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    ‖M.heatSmoothing k t ht‖ ≤ heatSmoothingConstant k t ∧
    ∀ x : M.Hilbert, ‖M.heatSmoothing k t ht x‖ ≤ heatSmoothingConstant k t * ‖x‖ := by
  constructor
  · exact LinearMap.opNorm_extendOfNorm_le (embed_dense M 0)
      (smoothing_constant_nonnegative k t) (smoothing_core_bound M k t ht)
  · exact LinearMap.norm_extendOfNorm_apply_le (embed_dense M 0)
      (heatSmoothingConstant k t) (smoothing_core_bound M k t ht)

attribute [local irreducible] Model.heatSmoothing

/-- One coherent lift through all the existing original inclusions. -/
theorem heatSmoothing_inclusion (j k : ℕ) (hjk : j ≤ k) (t : ℝ≥0) (ht : 0 < t) :
    (M.inclusion j k hjk).comp (M.heatSmoothing k t ht) = M.heatSmoothing j t ht := by
  ext x
  refine (embed_dense M 0).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [ContinuousLinearMap.comp_apply, heatSmoothing_embed_heat]
    simpa only [ContinuousLinearMap.comp_apply, inclusion_embed] using
      DFunLike.congr_fun (heat_inclusion M j k hjk t) (M.embed k v)

private theorem heatSmoothing_zero_order (t : ℝ≥0) (ht : 0 < t) :
    M.heatSmoothing 0 t ht = M.heat 0 t := by
  ext x
  refine (embed_dense M 0).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact heatSmoothing_embed_heat M 0 t ht

/-- Inclusion to H0 gives actual heat; restriction from Hk gives its actual Hk heat. -/
theorem heatSmoothing_hilbert (k : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    (M.inclusion 0 k (Nat.zero_le k)).comp (M.heatSmoothing k t ht) = M.heat 0 t ∧
    (M.heatSmoothing k t ht).comp (M.inclusion 0 k (Nat.zero_le k)) = M.heat k t := by
  constructor
  · rw [heatSmoothing_inclusion, heatSmoothing_zero_order]
  · ext x
    refine (embed_dense M k).induction_on x ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro v
      simp only [ContinuousLinearMap.comp_apply, inclusion_embed, heatSmoothing_embed, heat_embed]

/-- A coherent family in EXISTING smoothFamilies, for every arbitrary Hilbert vector. -/
def Model.heatFamily (t : ℝ≥0) (ht : 0 < t) : M.Hilbert →ₗ[ℂ] M.Smooth where
  toFun x := ⟨fun k => M.heatSmoothing k t ht x, by
    intro j k hjk
    exact DFunLike.congr_fun (heatSmoothing_inclusion M j k hjk t ht) x⟩
  map_add' x y := Subtype.ext (funext fun k => (M.heatSmoothing k t ht).map_add x y)
  map_smul' c x := Subtype.ext (funext fun k => (M.heatSmoothing k t ht).map_smul c x)

/-- The actual family witnesses evaluation.range membership in the original smooth domain. -/
theorem heat_smoothDomain (t : ℝ≥0) (ht : 0 < t) (x : M.Hilbert) :
    M.evaluation (M.heatFamily t ht x) = M.heat 0 t x ∧
    M.heat 0 t x ∈ M.smoothDomain := by
  have he : M.evaluation (M.heatFamily t ht x) = M.heat 0 t x := by
    change M.heatSmoothing 0 t ht x = M.heat 0 t x
    calc
      _ = M.inclusion 0 1 (Nat.zero_le 1) (M.heatSmoothing 1 t ht x) :=
        (DFunLike.congr_fun (heatSmoothing_inclusion M 0 1 (Nat.zero_le 1) t ht) x).symm
      _ = M.heat 0 t x :=
        DFunLike.congr_fun (heatSmoothing_hilbert M 1 t ht).1 x
  exact ⟨he, ⟨M.heatFamily t ht x, he⟩⟩

private theorem heatSmoothing_split (k : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    M.heatSmoothing k t ht =
      (M.heat k (t/2)).comp (M.heatSmoothing k (t/2) (by positivity)) := by
  have hadd := (original_heat M).2.2.1
  have htime : t/2+t/2 = t := add_halves t
  ext x
  refine (embed_dense M 0).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [ContinuousLinearMap.comp_apply, heatSmoothing_embed_heat]
    rw [← ContinuousLinearMap.comp_apply, ← hadd, htime]

/-- The actual original finite-rank positive-time smoothing approximant. -/
def Model.heatSmoothingTruncation (k : ℕ) (t : ℝ≥0) (ht : 0 < t) (N : ℕ) :
    M.Hilbert →L[ℂ] M.Sobolev k :=
  (M.heatTruncation k (t/2) N).comp (M.heatSmoothing k (t/2) (by positivity))

/-- The approximants are literally grade truncations, have finite original range, and satisfy
    the global H0-to-Hk tail C(t/2,k) exp(-t(N+1)/2). -/
theorem heatSmoothing_tail (k : ℕ) (t : ℝ≥0) (ht : 0 < t) (N : ℕ) :
    M.heatSmoothingTruncation k t ht N =
      (M.truncation k (M.energyCutoff N)).comp (M.heatSmoothing k t ht) ∧
    (M.heatSmoothingTruncation k t ht N).range ≤ M.cutoffSpace k N ∧
    FiniteDimensional ℂ (M.heatSmoothingTruncation k t ht N).range ∧
    ‖M.heatSmoothing k t ht - M.heatSmoothingTruncation k t ht N‖ ≤
      heatSmoothingConstant k ((t : ℝ) / 2) * Real.exp (-(t : ℝ) * ((N : ℝ) + 1)/2) := by
  have hsplit := heatSmoothing_split M k t ht
  have heq : M.heatSmoothingTruncation k t ht N =
      (M.truncation k (M.energyCutoff N)).comp (M.heatSmoothing k t ht) := by
    rw [hsplit]
    rfl
  have hr : (M.heatSmoothingTruncation k t ht N).range ≤ M.cutoffSpace k N := by
    dsimp only [Model.heatSmoothingTruncation]
    exact (LinearMap.range_comp_le_range
      (M.heatSmoothing k (t/2) (half_pos ht)).toLinearMap
      (M.heatTruncation k (t/2) N).toLinearMap).trans
      (heatTruncation_range M k (t/2) N).1
  refine ⟨heq, hr, Submodule.finiteDimensional_of_le hr, ?_⟩
  have herr : M.heatSmoothing k t ht - M.heatSmoothingTruncation k t ht N =
      (M.heat k (t/2) - M.heatTruncation k (t/2) N).comp
        (M.heatSmoothing k (t/2) (by positivity)) := by
    rw [hsplit]
    ext x
    rfl
  rw [herr]
  calc
    _ ≤ ‖M.heat k (t/2) - M.heatTruncation k (t/2) N‖ *
        ‖M.heatSmoothing k (t/2) (by positivity)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.exp (-((t/2 : ℝ≥0) : ℝ) * ((N : ℝ) + 1)) *
        heatSmoothingConstant k ((t/2 : ℝ≥0) : ℝ) :=
      mul_le_mul (heat_tail_bound M k (t/2) N)
        (heatSmoothing_bound M k (t/2) (by positivity)).1
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      change Real.exp (-((t : ℝ) / 2)*((N : ℝ) + 1)) *
        heatSmoothingConstant k ((t : ℝ) / 2) = _
      rw [mul_comm]
      congr 2
      ring

/-- Compact smoothing follows by composition with actual positive-time compact heat. -/
theorem heatSmoothing_compact (k : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    IsCompactOperator (M.heatSmoothing k t ht) := by
  rw [heatSmoothing_split M k t ht]
  simpa only [ContinuousLinearMap.coe_comp] using
    (heat_compact M k (t/2) (half_pos ht)).2.comp_clm
      (M.heatSmoothing k (t/2) (half_pos ht))

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing

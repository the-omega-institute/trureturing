/- GID: D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A Born rule for sequential measurements forces a scalar state or replacement channel. -/

import D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.Analysis.Matrix.Spectrum

/-! Universal sequential Born representations and their channel dichotomy. -/

noncomputable section
open scoped BigOperators Kronecker
open Matrix

namespace D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation (IsCPTP)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

/-- An orthogonal projection of arbitrary rank. -/
def IsProj {d : ℕ} (p : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  p * p = p ∧ p.IsHermitian

/-- One bipartite operator represents all pairs of sequential projective outcomes. -/
def BornRuleExists {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ) : Prop :=
  ∃ w : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ,
    ∀ p q, IsProj p → IsProj q →
      (w * (p ⊗ₖ q)).trace = (ε (p * ρ * p) * q).trace

/-- A channel discards its input and prepares one fixed density matrix. -/
def DiscardPrepare {d e : ℕ} (ε : MatrixMap (Fin d) (Fin e) ℂ) : Prop :=
  ∃ σ : Matrix (Fin e) (Fin e) ℂ, IsDensity σ ∧ ∀ x, ε x = x.trace • σ

/-- The spatiotemporal Born rule dichotomy in all positive finite dimensions. -/
def claim : Prop :=
  ∀ (d e : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ),
    IsDensity ρ → IsCPTP ε → 1 ≤ d → 1 ≤ e →
    (BornRuleExists ρ ε ↔ ρ = (1 / (d : ℂ)) • 1 ∨ DiscardPrepare ε)

private lemma proj_single {d : ℕ} (i : Fin d) :
    IsProj (single i i (1 : ℂ)) := by
  constructor
  · simp only [single_mul_single_same, mul_one]
  · simp only [IsHermitian, conjTranspose_single, star_one]

private lemma proj_conj {d : ℕ} (u : unitary (Matrix (Fin d) (Fin d) ℂ))
    (p : Matrix (Fin d) (Fin d) ℂ) (hp : IsProj p) :
    IsProj (Unitary.conjStarAlgAut ℂ _ u p) := by
  refine ⟨?_, ?_⟩
  · rw [← map_mul, hp.1]
  · exact (map_star (Unitary.conjStarAlgAut ℂ _ u) p).symm.trans
      (congrArg (Unitary.conjStarAlgAut ℂ _ u) hp.2)

private lemma projections_span (d : ℕ) :
    Submodule.span ℂ {p : Matrix (Fin d) (Fin d) ℂ | IsProj p} = ⊤ := by
  classical
  apply top_unique
  rw [← span_selfAdjoint (A := Matrix (Fin d) (Fin d) ℂ)]
  refine Submodule.span_le.mpr ?_
  intro x hx
  have hx' : x.IsHermitian := hx
  rw [hx'.spectral_theorem, ← sum_single_eq_diagonal, map_sum]
  apply Submodule.sum_mem
  intro i _
  have hs : single i i ((hx'.eigenvalues i : ℝ) : ℂ) =
      (hx'.eigenvalues i : ℂ) • single i i (1 : ℂ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  change Unitary.conjStarAlgAut ℂ _ hx'.eigenvectorUnitary
    (single i i (hx'.eigenvalues i : ℂ)) ∈ _
  rw [hs, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (proj_conj _ _ (proj_single i)))

private lemma trace_separates {e : ℕ} (x : Matrix (Fin e) (Fin e) ℂ)
    (h : ∀ q, IsProj q → (x * q).trace = 0) : x = 0 := by
  let f := (traceLinearMap (Fin e) ℂ ℂ).comp (LinearMap.mulLeft ℂ x)
  have hf : f = 0 := LinearMap.ext_on (projections_span e) h
  apply ext_iff_trace_mul_right.mpr
  intro q
  have hq := congrArg (fun f => f q) hf
  change (x * q).trace = 0 at hq
  simpa only [zero_mul, trace_zero] using hq

private lemma born_identity {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ) (h : BornRuleExists ρ ε) :
    ∀ p, IsProj p → ε (p * ρ + ρ * p) = (2 : ℂ) • ε (p * ρ * p) := by
  obtain ⟨w, hw⟩ := h
  intro p hp
  have hc : IsProj (1 - p) := by
    refine ⟨?_, isHermitian_one.sub hp.2⟩
    simp only [sub_mul, mul_sub, one_mul, mul_one, hp.1]
    abel
  have h1 : IsProj (1 : Matrix (Fin d) (Fin d) ℂ) :=
    ⟨one_mul _, isHermitian_one⟩
  apply sub_eq_zero.mp
  rw [← map_smul, ← map_sub]
  apply trace_separates
  intro q hq
  have ht : (w * (1 ⊗ₖ q)).trace =
      (w * (p ⊗ₖ q)).trace + (w * ((1 - p) ⊗ₖ q)).trace := by
    rw [← trace_add, ← mul_add, ← add_kronecker, add_sub_cancel]
  rw [hw 1 q h1 hq, hw p q hp hq, hw (1 - p) q hc hq] at ht
  simp only [one_mul, mul_one] at ht
  have ha : p * ρ + ρ * p - (2 : ℂ) • (p * ρ * p) =
      ρ - p * ρ * p - (1 - p) * ρ * (1 - p) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, two_smul ℂ]
    abel
  rw [ha, map_sub, map_sub, sub_mul, sub_mul, trace_sub, trace_sub]
  linear_combination ht

private def outer {d : ℕ} (u v : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  vecMulVec u (star v)

private lemma outer_star {d : ℕ} (u v : Fin d → ℂ) :
    (outer u v).conjTranspose = outer v u := by
  simp only [outer, conjTranspose_vecMulVec, star_star]

private lemma outer_sandwich {d : ℕ} (u v w t : Fin d → ℂ)
    (x : Matrix (Fin d) (Fin d) ℂ) :
    outer u v * x * outer w t = (star v ⬝ᵥ (x *ᵥ w)) • outer u t := by
  unfold outer
  rw [Matrix.mul_assoc, mul_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_smul]

private lemma outer_left {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (u v : Fin d → ℂ) (r : ℝ) (hu : ρ *ᵥ u = (r : ℂ) • u) :
    ρ * outer u v = (r : ℂ) • outer u v := by
  simp only [outer, mul_vecMulVec, hu, smul_vecMulVec]

private lemma outer_right {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.IsHermitian) (u v : Fin d → ℂ) (s : ℝ)
    (hv : ρ *ᵥ v = (s : ℂ) • v) :
    outer u v * ρ = (s : ℂ) • outer u v := by
  have h := congrArg Matrix.conjTranspose (outer_left ρ v u s hv)
  simpa only [conjTranspose_mul, outer_star, hρ.eq, conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal] using h

private lemma ray_proj {d : ℕ} (w : Fin d → ℂ) (c : ℝ) (hc : c ≠ 0)
    (hn : star w ⬝ᵥ w = (c : ℂ)) : IsProj ((c : ℂ)⁻¹ • outer w w) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  constructor
  · simp only [outer, Matrix.smul_mul, Matrix.mul_smul,
      vecMulVec_mul_vecMulVec, hn, vecMulVec_smul, smul_smul,
      inv_mul_cancel₀ hc', mul_one]
  · rw [IsHermitian, conjTranspose_smul, outer_star]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]

private lemma ray_identity {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ)
    (hid : ∀ p, IsProj p → ε (p * ρ + ρ * p) = (2 : ℂ) • ε (p * ρ * p))
    (w : Fin d → ℂ) (c : ℝ) (hc : c ≠ 0) (hn : star w ⬝ᵥ w = (c : ℂ)) :
    (c : ℂ) • ε (outer w w * ρ + ρ * outer w w) =
      (2 : ℂ) • ε (outer w w * ρ * outer w w) := by
  have h := hid _ (ray_proj w c hc hn)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, map_smul, smul_smul] at h
  have hh := congrArg (fun x => ((c : ℂ) * c) • x) h
  have hc2 : (c : ℂ) * ((c : ℂ) * (2 * ((c : ℂ)⁻¹ * (c : ℂ)⁻¹))) = 2 := by
    field_simp
  simpa only [smul_smul, mul_assoc, mul_inv_cancel₀ hc', mul_one, hc2] using hh

private lemma outer_combination {d : ℕ} (u v : Fin d → ℂ) (a b : ℂ) :
    outer (a • u + b • v) (a • u + b • v) =
      (a * star a) • outer u u + (b * star b) • outer v v +
      (a * star b) • outer u v + (b * star a) • outer v u := by
  ext i j
  simp only [outer, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_add, star_mul]
  ring

private lemma two_ray_equation {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.IsHermitian) (ε : MatrixMap (Fin d) (Fin e) ℂ)
    (hid : ∀ p, IsProj p → ε (p * ρ + ρ * p) = (2 : ℂ) • ε (p * ρ * p))
    (u v : Fin d → ℂ) (r s a b : ℝ) (z : ℂ) (hz : star z * z = 1)
    (hc : a ^ 2 + b ^ 2 ≠ 0)
    (hu : ρ *ᵥ u = (r : ℂ) • u) (hv : ρ *ᵥ v = (s : ℂ) • v)
    (huu : star u ⬝ᵥ u = 1) (hvv : star v ⬝ᵥ v = 1)
    (huv : star u ⬝ᵥ v = 0) (hvu : star v ⬝ᵥ u = 0) :
    ((a : ℂ)^2 + (b : ℂ)^2) • ε
      ((2 * r * (a : ℂ)^2) • outer u u + (2 * s * (b : ℂ)^2) • outer v v +
        (((r : ℂ) + s) * a * b * star z) • outer u v +
        (((r : ℂ) + s) * a * b * z) • outer v u) =
      (2 * ((r : ℂ) * (a : ℂ)^2 + s * (b : ℂ)^2)) • ε
        (((a : ℂ)^2) • outer u u + ((b : ℂ)^2) • outer v v +
          ((a : ℂ) * b * star z) • outer u v + ((a : ℂ) * b * z) • outer v u) := by
  simp only [Complex.star_def] at hz
  let w := (a : ℂ) • u + ((b : ℂ) * z) • v
  have hn : star w ⬝ᵥ w = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    simp only [w, star_add, star_smul, star_mul, Complex.star_def,
      Complex.conj_ofReal, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, huu, hvv, huv, hvu, smul_eq_mul]
    push_cast
    linear_combination (b : ℂ)^2 * hz
  have hm : outer w w =
      ((a : ℂ)^2) • outer u u + ((b : ℂ)^2) • outer v v +
      ((a : ℂ) * b * star z) • outer u v + ((a : ℂ) * b * z) • outer v u := by
    rw [outer_combination]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    match_scalars <;> ring_nf <;> linear_combination (b : ℂ)^2 * hz
  have ht : outer w w * ρ * outer w w =
      ((r : ℂ) * (a : ℂ)^2 + s * (b : ℂ)^2) • outer w w := by
    rw [outer_sandwich]
    congr 1
    simp only [w, mulVec_add, mulVec_smul, hu, hv, star_add, star_smul,
      star_mul, Complex.star_def, Complex.conj_ofReal, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, huu, hvv, huv, hvu,
      smul_eq_mul, smul_smul]
    linear_combination (s : ℂ) * (b : ℂ)^2 * hz
  have hs : outer w w * ρ + ρ * outer w w =
      (2 * r * (a : ℂ)^2) • outer u u + (2 * s * (b : ℂ)^2) • outer v v +
      (((r : ℂ) + s) * a * b * star z) • outer u v +
      (((r : ℂ) + s) * a * b * z) • outer v u := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      outer_left ρ u u r hu, outer_left ρ u v r hu,
      outer_left ρ v u s hv, outer_left ρ v v s hv,
      outer_right ρ hρ u u r hu, outer_right ρ hρ v u r hu,
      outer_right ρ hρ u v s hv, outer_right ρ hρ v v s hv]
    module
  have h := ray_identity ρ ε hid w (a ^ 2 + b ^ 2) hc hn
  rw [hs, ht, hm, map_smul, smul_smul] at h
  simpa only [Complex.ofReal_add, Complex.ofReal_pow] using h

private lemma two_eigenvector {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.IsHermitian) (ε : MatrixMap (Fin d) (Fin e) ℂ)
    (hid : ∀ p, IsProj p → ε (p * ρ + ρ * p) = (2 : ℂ) • ε (p * ρ * p))
    (u v : Fin d → ℂ) (r s : ℝ) (hrs : r ≠ s)
    (hu : ρ *ᵥ u = (r : ℂ) • u) (hv : ρ *ᵥ v = (s : ℂ) • v)
    (huu : star u ⬝ᵥ u = 1) (hvv : star v ⬝ᵥ v = 1)
    (huv : star u ⬝ᵥ v = 0) (hvu : star v ⬝ᵥ u = 0) :
    ε (outer u u) = ε (outer v v) ∧ ε (outer u v) = 0 ∧ ε (outer v u) = 0 := by
  have h0 := two_ray_equation ρ hρ ε hid u v r s 1 1 1 (by norm_num)
    (by norm_num) hu hv huu hvv huv hvu
  have h1 := two_ray_equation ρ hρ ε hid u v r s 3 4 1 (by norm_num)
    (by norm_num) hu hv huu hvv huv hvu
  have hi := two_ray_equation ρ hρ ε hid u v r s 3 4 Complex.I (by simp)
    (by norm_num) hu hv huu hvv huv hvu
  norm_num only [Complex.ofReal_one, Complex.ofReal_ofNat, one_pow, one_mul,
    mul_one, star_one, map_add, map_smul, Complex.star_def, Complex.conj_I] at h0 h1 hi
  have hrs' : (r : ℂ) - s ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hrs)
  have heq : ε (outer u u) = ε (outer v v) := by
    ext i j
    have hh := congrArg (fun x : Matrix (Fin e) (Fin e) ℂ => x i j) h0
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hh
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show ((r : ℂ) - s) *
      (ε (outer u u) i j - ε (outer v v) i j) = 0 by linear_combination hh / 2)).resolve_left hrs'
  refine ⟨heq, ?_, ?_⟩
  all_goals
    ext i j
    change _ = (0 : ℂ)
    have h1' := congrArg (fun x : Matrix (Fin e) (Fin e) ℂ => x i j) h1
    have hi' := congrArg (fun x : Matrix (Fin e) (Fin e) ℂ => x i j) hi
    simp only [heq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1' hi'
    have hs : ε (outer u v) i j + ε (outer v u) i j = 0 :=
      (mul_eq_zero.mp (show ((r : ℂ) - s) *
        (ε (outer u v) i j + ε (outer v u) i j) = 0 by
          linear_combination h1' / 84)).resolve_left hrs'
    have ht : -Complex.I * ε (outer u v) i j + Complex.I * ε (outer v u) i j = 0 :=
      (mul_eq_zero.mp (show ((r : ℂ) - s) *
        (-Complex.I * ε (outer u v) i j + Complex.I * ε (outer v u) i j) = 0 by
          linear_combination hi' / 84)).resolve_left hrs'
    have hz : ε (outer u v) i j = 0 :=
      (mul_eq_zero.mp (show (-2 * Complex.I) * ε (outer u v) i j = 0 by
        linear_combination ht - Complex.I * hs)).resolve_left (by norm_num)
    first | exact hz | linear_combination hs - hz

private lemma eigenbasis_assembly {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ) (hρ : IsDensity ρ) (hε : IsCPTP ε)
    (hd : 1 ≤ d)
    (hid : ∀ p, IsProj p → ε (p * ρ + ρ * p) = (2 : ℂ) • ε (p * ρ * p)) :
    ρ = (1 / (d : ℂ)) • 1 ∨ DiscardPrepare ε := by
  sorry

private lemma born_of_discard {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ) (h : DiscardPrepare ε) :
    BornRuleExists ρ ε := by
  obtain ⟨σ, _hσ, hε⟩ := h
  refine ⟨ρ ⊗ₖ σ, ?_⟩
  intro p q hp _hq
  rw [← mul_kronecker_mul, trace_kronecker, hε, smul_mul, trace_smul, smul_eq_mul]
  have ht : (p * ρ * p).trace = (ρ * p).trace := by
    rw [trace_mul_cycle, hp.1, trace_mul_comm]
  rw [ht]

private lemma born_of_scalar {d e : ℕ} (ε : MatrixMap (Fin d) (Fin e) ℂ) :
    BornRuleExists ((1 / (d : ℂ)) • 1) ε := by
  classical
  refine ⟨(1 / (d : ℂ)) • ∑ i : Fin d, ∑ j : Fin d,
    single i j (1 : ℂ) ⊗ₖ ε (single j i 1), ?_⟩
  intro p q hp _hq
  have hex : ε p = ∑ i : Fin d, ∑ j : Fin d, p j i • ε (single j i 1) := by
    conv_lhs => rw [matrix_eq_sum_single p]
    rw [map_sum]
    simp only [map_sum, ← map_smul, smul_single, smul_eq_mul, mul_one]
    rw [Finset.sum_comm]
  have hr : p * ((1 / (d : ℂ)) • 1) * p = (1 / (d : ℂ)) • p := by
    rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, hp.1]
  rw [hr, map_smul, smul_mul, trace_smul, smul_mul, trace_smul]
  congr 1
  simp only [Finset.sum_mul, trace_sum, ← mul_kronecker_mul, trace_kronecker,
    trace_single_mul]
  rw [hex]
  simp only [Finset.sum_mul, trace_sum, smul_mul, trace_smul, smul_eq_mul, one_mul]

/-- A universal LvN Born rule exists exactly in the two stated cases. -/
theorem result : claim := by
  intro d e ρ ε hρ hε hd _he
  constructor
  · intro h
    exact eigenbasis_assembly ρ ε hρ hε hd (born_identity ρ ε h)
  · rintro (rfl | h)
    · exact born_of_scalar ε
    · exact born_of_discard ρ ε h

end D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy

/- GID: D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affine overlaps of a fixed rank-one POVM determine the mean-output purity. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteTraceDistance

/-!
# Mean-output purity from affine pure-state overlaps

The effects and prepared states belong to one fixed finite Holevo representation. The affine
overlap equation determines the expectation of the mean state in every prepared vector, and hence
the purity of that state. Positivity of centered matrix squares controls both purity endpoints.

Admission: escape-witness; proof_shape: content. The endpoint rigidity argument
uses a zero Hilbert–Schmidt square to force all prepared projectors to coincide,
and uses the fixed POVM representation to contradict nonconstancy. All private
helpers are consumed on the live proof path. This proves an intermediate of
Theorem 5, not its norm-saturation equivalence or the necessity of rank-one
and pure-output factors. No numerical instance or reduction is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

namespace D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity

/-- Two unit complex vectors on the same ray have equal outer projectors. -/
theorem vecMulVec_eq_of_unit_ray {n : Type*} [Fintype n] {ψ χ : n → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hχ : star χ ⬝ᵥ χ = 1)
    (z : ℂ) (hz : ψ = z • χ) :
    vecMulVec ψ (star ψ) = vecMulVec χ (star χ) := by
  have hz1 : z * star z = 1 := by
    simpa only [hz, star_smul, smul_dotProduct, dotProduct_smul,
      hχ, smul_eq_mul, mul_one] using hψ
  rw [hz, star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul,
    hz1, one_smul]

/-- The actual complex matrix `|v⟩⟨v|`. -/
def projector {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  vecMulVec (fun i => v i) (fun i => star (v i))

/-- The output of the maximally mixed state in a fixed rank-one Holevo representation. -/
def meanOutput {d : ℕ} {ι : Type*} [Fintype ι] (α : ι → ℝ)
    (ψ : ι → EuclideanSpace ℂ (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ k, ((α k / d : ℝ) : ℂ) • projector (ψ k)

theorem projector_trace {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) :
    (projector v).trace = 1 := by
  rw [projector, trace_vecMulVec]
  exact inner_self_eq_one_of_norm_eq_one hv

private theorem projector_hermitian {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) :
    (projector v).IsHermitian := by
  apply Matrix.ext
  intro i j
  simp [projector, conjTranspose_apply, vecMulVec_apply, mul_comm]

theorem trace_projectors {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)) :
    (projector v * projector w).trace = (‖⟪v, w⟫_ℂ‖ ^ 2 : ℝ) := by
  rw [projector, projector, vecMulVec_mul_vecMulVec, trace_vecMulVec, dotProduct_smul]
  change (star (fun i => v i) ⬝ᵥ (fun i => w i)) *
    ((fun i => v i) ⬝ᵥ star (fun i => w i)) = _
  rw [dotProduct_comm (star (fun i => v i))]
  change ⟪v, w⟫_ℂ * ⟪w, v⟫_ℂ = _
  rw [← inner_conj_symm w v, Complex.mul_conj']
  norm_cast

private theorem expectation_trace {d : ℕ} (v : EuclideanSpace ℂ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℂ) :
    star (fun i => v i) ⬝ᵥ M *ᵥ (fun i => v i) = (M * projector v).trace := by
  rw [projector, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  rfl

private theorem povm_mass {d : ℕ} {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin d))
    (he : ∀ k, ‖e k‖ = 1)
    (hE : ∑ k, (α k : ℂ) • projector (e k) = 1) :
    ∑ k, α k = d := by
  have h := congrArg Matrix.trace hE
  simp only [trace_sum, trace_smul, projector_trace _ (he _), smul_eq_mul, mul_one,
    trace_one, Fintype.card_fin] at h
  exact_mod_cast h

private theorem povm_overlap {d : ℕ} {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin d))
    (he : ∀ k, ‖e k‖ = 1)
    (hE : ∑ k, (α k : ℂ) • projector (e k) = 1) (k : ι) :
    ∑ m, α m * ‖⟪e k, e m⟫_ℂ‖ ^ 2 = 1 := by
  have h := congrArg (fun M => (projector (e k) * M).trace) hE
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, trace_projectors,
    smul_eq_mul,
    mul_one, projector_trace _ (he k)] at h
  exact_mod_cast h

private theorem mean_trace {d : ℕ} {ι : Type*} [Fintype ι]
    (hd : 2 ≤ d) (α : ι → ℝ) (ψ : ι → EuclideanSpace ℂ (Fin d))
    (hψ : ∀ k, ‖ψ k‖ = 1) (hmass : ∑ k, α k = d) :
    (meanOutput α ψ).trace = 1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simp only [meanOutput, trace_sum, trace_smul, projector_trace _ (hψ _), smul_eq_mul,
    mul_one, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← Finset.sum_div]
  have hm : ∑ k, (α k : ℂ) = d := by exact_mod_cast hmass
  rw [hm, div_self hd0]

private theorem mean_positive {d : ℕ} {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (ψ : ι → EuclideanSpace ℂ (Fin d)) (hα : ∀ k, 0 < α k) :
    (meanOutput α ψ).PosSemidef := by
  unfold meanOutput
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact PosSemidef.zero
  · intro k _
    exact (posSemidef_vecMulVec_self_star (fun i => ψ k i)).smul
      (show (0 : ℂ) ≤ ((α k / d : ℝ) : ℂ) by
        exact_mod_cast div_nonneg (hα k).le (Nat.cast_nonneg d))

private theorem mean_pairing {d : ℕ} {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (ψ : ι → EuclideanSpace ℂ (Fin d)) (k : ι) :
    (projector (ψ k) * meanOutput α ψ).trace =
      ((∑ m, (α m / d) * ‖⟪ψ k, ψ m⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  simp only [meanOutput, Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul,
    trace_projectors,
    smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]

private theorem overlap_all_pairs {d : ℕ} {ι : Type*} (hd : 2 ≤ d)
    (e ψ : ι → EuclideanSpace ℂ (Fin d))
    (he : ∀ k, ‖e k‖ = 1) (hψ : ∀ k, ‖ψ k‖ = 1) (P : ℝ)
    (h : ∀ j k, j ≠ k → ‖⟪ψ j, ψ k⟫_ℂ‖ ^ 2 =
      P + (1 - P) * ((d : ℝ) * ‖⟪e j, e k⟫_ℂ‖ ^ 2 - 1) / ((d : ℝ) - 1)) :
    ∀ j k, ‖⟪ψ j, ψ k⟫_ℂ‖ ^ 2 =
      P + (1 - P) * ((d : ℝ) * ‖⟪e j, e k⟫_ℂ‖ ^ 2 - 1) / ((d : ℝ) - 1) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  intro j k
  by_cases hjk : j = k
  · subst k
    rw [inner_self_eq_one_of_norm_eq_one (hψ j), inner_self_eq_one_of_norm_eq_one (he j)]
    norm_num only [norm_one, one_pow, mul_one]
    field_simp [hd1]; ring
  · exact h j k hjk

private theorem overlap_weighted_mean {d : ℕ} {ι : Type*} [Fintype ι]
    (hd : 2 ≤ d) (α : ι → ℝ) (e ψ : ι → EuclideanSpace ℂ (Fin d))
    (he : ∀ k, ‖e k‖ = 1) (hψ : ∀ k, ‖ψ k‖ = 1)
    (hE : ∑ k, (α k : ℂ) • projector (e k) = 1) (P : ℝ)
    (h : ∀ j k, j ≠ k → ‖⟪ψ j, ψ k⟫_ℂ‖ ^ 2 =
      P + (1 - P) * ((d : ℝ) * ‖⟪e j, e k⟫_ℂ‖ ^ 2 - 1) / ((d : ℝ) - 1)) :
    ∀ k, ∑ m, (α m / d) * ‖⟪ψ k, ψ m⟫_ℂ‖ ^ 2 = P := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hmass := povm_mass α e he hE
  have hall := overlap_all_pairs hd e ψ he hψ P h
  intro k
  have hsum : ∑ m, α m * ‖⟪ψ k, ψ m⟫_ℂ‖ ^ 2 = (d : ℝ) * P := by
    simp_rw [hall]
    calc
      ∑ m, α m * (P + (1 - P) * ((d : ℝ) * ‖⟪e k, e m⟫_ℂ‖ ^ 2 - 1) /
          ((d : ℝ) - 1)) =
        ∑ m, (α m * P + (1 - P) / ((d : ℝ) - 1) *
          ((d : ℝ) * (α m * ‖⟪e k, e m⟫_ℂ‖ ^ 2) - α m)) := by
            apply Finset.sum_congr rfl
            intro m _
            ring
      _ = (d : ℝ) * P := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, povm_overlap α e he hE k]
        ring
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hsum]
  field_simp

private theorem purity_of_common_pairing {d : ℕ} {ι : Type*} [Fintype ι]
    (hd : 2 ≤ d) (α : ι → ℝ) (ψ : ι → EuclideanSpace ℂ (Fin d))
    (hmass : ∑ k, α k = d) (P : ℝ)
    (hP : ∀ k, (projector (ψ k) * meanOutput α ψ).trace = (P : ℂ)) :
    (meanOutput α ψ * meanOutput α ψ).trace = (P : ℂ) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hm : ∑ k, (α k : ℂ) = d := by exact_mod_cast hmass
  calc
    (meanOutput α ψ * meanOutput α ψ).trace =
      ((∑ k, ((α k / d : ℝ) : ℂ) • projector (ψ k)) * meanOutput α ψ).trace := rfl
    _ = ∑ k, ((α k / d : ℝ) : ℂ) * (P : ℂ) := by
      simp only [Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, hP, smul_eq_mul]
    _ = (P : ℂ) := by
      simp only [Complex.ofReal_div, Complex.ofReal_natCast]
      rw [← Finset.sum_mul, ← Finset.sum_div, hm, div_self hd0, one_mul]

private theorem hermitian_purity_lower_bound {d : ℕ} (hd : 2 ≤ d)
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.IsHermitian)
    (ht : M.trace = 1) (P : ℝ) (hP : (M * M).trace = (P : ℂ)) :
    1 / (d : ℝ) ≤ P := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hB : (M - (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)).IsHermitian :=
    hM.sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have h := (posSemidef_conjTranspose_mul_self
    (M - (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))).trace_nonneg
  have hid : ((M - (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ *
      (M - (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))).trace =
      (P : ℂ) - 1 / (d : ℂ) := by
    simp only [hB.eq, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul,
      trace_sub, trace_smul, hP, ht, trace_one, Fintype.card_fin, smul_eq_mul]
    field_simp; ring
  have hid' : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hid, hid', ← Complex.ofReal_sub] at h
  exact sub_nonneg.mp ((RCLike.nonneg_iff.mp h).1)

private theorem centered_pairing {d : ℕ} {ι : Type*}
    (ψ : ι → EuclideanSpace ℂ (Fin d)) (ρ : Matrix (Fin d) (Fin d) ℂ) (P : ℝ)
    (hP : ∀ k, (projector (ψ k) * ρ).trace = (P : ℂ))
    (hpurity : (ρ * ρ).trace = (P : ℂ)) (j k : ι) :
    ((projector (ψ j) - ρ) * (projector (ψ k) - ρ)).trace =
      (projector (ψ j) * projector (ψ k)).trace - (P : ℂ) := by
  rw [sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub,
    trace_mul_comm ρ (projector (ψ k)), hP j, hP k, hpurity]
  ring

/-- The overlap equation alone determines the purity and every output expectation for a fixed
rank-one Holevo representation. For a nonconstant channel its parameter lies in `[1/d, 1)`.
The final identity gives the centered Hilbert–Schmidt Gram matrix. This is the overlap-to-purity
part of the equality analysis; it does not assert nuclear-norm saturation or its converse. -/
theorem affine_overlap_purity_and_rigidity {d : ℕ} {ι : Type*} [Fintype ι]
    (hd : 2 ≤ d) (α : ι → ℝ) (e ψ : ι → EuclideanSpace ℂ (Fin d))
    (hα : ∀ k, 0 < α k) (he : ∀ k, ‖e k‖ = 1) (hψ : ∀ k, ‖ψ k‖ = 1)
    (hE : ∑ k, (α k : ℂ) • projector (e k) = 1)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ)
    (hΦ : ∀ X, Φ X = ∑ k, (((α k : ℂ) • projector (e k)) * X).trace • projector (ψ k))
    (hnonconstant : ¬ ∃ σ : Matrix (Fin d) (Fin d) ℂ, ∀ X, Φ X = X.trace • σ)
    (P : ℝ)
    (hoverlap : ∀ j k, j ≠ k → ‖⟪ψ j, ψ k⟫_ℂ‖ ^ 2 =
      P + (1 - P) * ((d : ℝ) * ‖⟪e j, e k⟫_ℂ‖ ^ 2 - 1) / ((d : ℝ) - 1)) :
    let ρ := meanOutput α ψ
    ρ.PosSemidef ∧ ρ.trace = 1 ∧
    Φ ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) = ρ ∧
    (∀ k, star (fun i => ψ k i) ⬝ᵥ ρ *ᵥ (fun i => ψ k i) = (P : ℂ)) ∧
    (ρ * ρ).trace = (P : ℂ) ∧ 1 / (d : ℝ) ≤ P ∧ P < 1 ∧
    ∀ j k, ((projector (ψ j) - ρ) * (projector (ψ k) - ρ)).trace =
      (((1 - P) * ((d : ℝ) * ‖⟪e j, e k⟫_ℂ‖ ^ 2 - 1) /
        ((d : ℝ) - 1) : ℝ) : ℂ) := by
  classical
  let ρ := meanOutput α ψ
  have hmass := povm_mass α e he hE
  have hpositive : ρ.PosSemidef := mean_positive α ψ hα
  have htrace : ρ.trace = 1 := mean_trace hd α ψ hψ hmass
  have hweights := overlap_weighted_mean hd α e ψ he hψ hE P hoverlap
  have hpair : ∀ k, (projector (ψ k) * ρ).trace = (P : ℂ) := by
    intro k
    rw [mean_pairing, hweights k]
  have hpurity : (ρ * ρ).trace = (P : ℂ) :=
    purity_of_common_pairing hd α ψ hmass P hpair
  have hcenter := centered_pairing ψ ρ P hpair hpurity
  have hdiag : ∀ k, ((projector (ψ k) - ρ)ᴴ * (projector (ψ k) - ρ)).trace =
      ((1 - P : ℝ) : ℂ) := by
    intro k
    rw [((projector_hermitian (ψ k)).sub hpositive.isHermitian).eq, hcenter,
      trace_projectors, inner_self_eq_one_of_norm_eq_one (hψ k)]
    norm_num
  have hι : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hmass
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    exact hd0 hmass.symm
  obtain ⟨k₀⟩ := hι
  have hle : P ≤ 1 := by
    have hh := (posSemidef_conjTranspose_mul_self (projector (ψ k₀) - ρ)).trace_nonneg
    rw [hdiag] at hh
    have hr : (0 : ℝ) ≤ 1 - P := (RCLike.nonneg_iff.mp hh).1
    linarith
  have hlt : P < 1 := by
    by_contra h
    have h1 : P = 1 := le_antisymm hle (not_lt.mp h)
    have hequal : ∀ k, projector (ψ k) = ρ := by
      intro k
      apply sub_eq_zero.mp
      apply trace_conjTranspose_mul_self_eq_zero_iff.mp
      rw [hdiag, h1]
      norm_num
    apply hnonconstant
    refine ⟨ρ, fun X => ?_⟩
    rw [hΦ]
    simp_rw [hequal]
    rw [← Finset.sum_smul]
    congr 1
    calc
      ∑ k, (((α k : ℂ) • projector (e k)) * X).trace =
          ((∑ k, (α k : ℂ) • projector (e k)) * X).trace := by
            rw [Matrix.sum_mul, trace_sum]
      _ = X.trace := by rw [hE, one_mul]
  refine ⟨hpositive, htrace, ?_, ?_, hpurity,
    hermitian_purity_lower_bound hd ρ hpositive.isHermitian htrace P hpurity, hlt, ?_⟩
  · rw [hΦ]
    change (∑ k, (((α k : ℂ) • projector (e k)) *
      ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))).trace • projector (ψ k)) =
        ∑ k, ((α k / d : ℝ) : ℂ) • projector (ψ k)
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_one, trace_smul, trace_smul,
      projector_trace _ (he k)]
    simp [smul_eq_mul, Complex.ofReal_natCast, div_eq_mul_inv]
  · intro k
    rw [expectation_trace, trace_mul_comm, hpair]
  · intro j k
    rw [hcenter, trace_projectors, overlap_all_pairs hd e ψ he hψ P hoverlap j k]
    push_cast
    ring

end D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity

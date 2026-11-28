/- GID: D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Odd integer relations among adjacency gaps bound the return amplitude of strongly cospectral twins. -/

/-
proof_shape: result: content
escape_witness: the twin difference lies in the full twin eigenspace, which forces half the
  return mass at the twin eigenvalue. The positive-time orbit criterion and the weighted
  character chord control the cancellation of the remaining half.
admission_basis: open-problem-resolution (#35281; Proved)
-/

import D5.S3.Fourier.WeightedIntegerRelations
import D5.S3.Fourier.WeightedPhaseRelationLattice
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation

/-! A relation-dependent adjacency return-amplitude floor for §9 of Meagher, Monterde and
Nguyen, *Sedentariness in Cayley graphs*, arXiv:2611.00567v1. Lemma 3.3 and Theorem 2.2(2) of
the paper give the twin eigenvector and the qualitative parity criterion, respectively. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.StronglyCospectralTwinAmplitudeBound

open Matrix Finset
open scoped Matrix.Norms.L2Operator
open D5.S3.Fourier.WeightedIntegerRelations (orbit_character weighted_character_chord)
open D5.S3.Fourier.WeightedPhaseRelationLattice (closure_real_phase_orbit)
open D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum (idempotent)
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity (exp_mulVec_of_eigenvector)
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (hamiltonianPropagator hamiltonianGenerator)
open D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation (StronglyCospectral)

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

local notation "hA" => (G.isHermitian_adjMatrix ℝ)

/-- The eigenvalue of the difference of the two twin vertex vectors. -/
def twinEigenvalue (u v : Fin n) : ℝ := if G.Adj u v then -1 else 0

/-- The distinct supported eigenvalues other than the twin eigenvalue. -/
def remainingSupport (u v : Fin n) : Finset ℝ := by
  classical
  exact (univ.image hA.eigenvalues).filter
    fun λ => λ ≠ twinEigenvalue G u v ∧ 0 < idempotent G λ u u

private theorem projector_column (u : Fin n) (λ : ℝ) :
    idempotent G λ *ᵥ Pi.single u 1 =
      ∑ i with hA.eigenvalues i = λ, hA.eigenvectorBasis i u • ⇑(hA.eigenvectorBasis i) := by
  classical
  rw [mulVec_single_one]
  funext x
  simp [idempotent, Matrix.sum_apply, vecMulVec_apply, mul_comm]

private theorem basis_expansion (w : Fin n → ℝ) :
    ∑ i, (⇑(hA.eigenvectorBasis i) ⬝ᵥ w) • ⇑(hA.eigenvectorBasis i) = w := by
  have h := congrArg WithLp.ofLp (hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 w))
  simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, star_trivial, dotProduct_comm] using h

private theorem twin_difference (u v : Fin n) (huv : u ≠ v)
    (htwin : ∀ x, x ≠ u → x ≠ v → (G.Adj x u ↔ G.Adj x v)) :
    G.adjMatrix ℝ *ᵥ (Pi.single u 1 - Pi.single v 1) =
      twinEigenvalue G u v • (Pi.single u 1 - Pi.single v 1) := by
  rw [mulVec_sub, mulVec_single_one, mulVec_single_one]
  funext x
  by_cases hxu : x = u
  · subst x
    by_cases ha : G.Adj u v <;>
      simp [SimpleGraph.adjMatrix_apply, twinEigenvalue, Pi.single_apply, huv, huv.symm, ha]
  by_cases hxv : x = v
  · subst x
    have he : G.Adj v u ↔ G.Adj u v := ⟨G.symm, G.symm⟩
    by_cases ha : G.Adj u v <;>
      simp [SimpleGraph.adjMatrix_apply, twinEigenvalue, Pi.single_apply, huv, huv.symm, he, ha]
  simp [SimpleGraph.adjMatrix_apply, Pi.single_apply, hxu, hxv, hxu.symm, hxv.symm, htwin x hxu hxv]

private theorem twin_projection (u v : Fin n) (huv : u ≠ v)
    (htwin : ∀ x, x ≠ u → x ≠ v → (G.Adj x u ↔ G.Adj x v)) (λ : ℝ) :
    idempotent G λ *ᵥ (Pi.single u 1 - Pi.single v 1) =
      if λ = twinEigenvalue G u v then (Pi.single u 1 - Pi.single v 1) else 0 := by
  classical
  let w : Fin n → ℝ := Pi.single u 1 - Pi.single v 1
  let θ := twinEigenvalue G u v
  have hz (i : Fin n) (hi : hA.eigenvalues i ≠ θ) : ⇑(hA.eigenvectorBasis i) ⬝ᵥ w = 0 :=
    LaplacianPeakTransferTrees.eig_dot_zero hA w θ (twin_difference G u v huv htwin) i hi
  change idempotent G λ *ᵥ w = if λ = θ then w else 0
  change (∑ i with hA.eigenvalues i = λ,
    vecMulVec ⇑(hA.eigenvectorBasis i) ⇑(hA.eigenvectorBasis i)) *ᵥ w = _
  simp only [sum_mulVec, vecMulVec_mulVec]
  by_cases hλ : λ = θ
  · subst λ
    rw [if_pos rfl]
    conv_rhs => rw [← basis_expansion G w]
    refine Finset.sum_subset (filter_subset _ _) ?_
    intro i _ hi
    simp [hz i (by simpa using hi)]
  · rw [if_neg hλ]
    refine Finset.sum_eq_zero fun i hi => ?_
    simp [hz i ((mem_filter.mp hi).2.trans_ne hλ)]

private theorem projector_weight_nonneg (u : Fin n) (λ : ℝ) : 0 ≤ idempotent G λ u u := by
  classical
  simp only [idempotent, Matrix.sum_apply, vecMulVec_apply]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (hA.eigenvectorBasis i u)

private theorem diagonal_weights_eq (u v : Fin n) (hc : StronglyCospectral G u v) (λ : ℝ) :
    idempotent G λ u u = idempotent G λ v v := by
  have hsym : idempotent G λ u v = idempotent G λ v u := by
    simp only [idempotent, Matrix.sum_apply, vecMulVec_apply, mul_comm]
  obtain ⟨c, hc, hcol⟩ := hc λ
  rw [mulVec_single_one, mulVec_single_one] at hcol
  have hu := congrFun hcol u
  have hv := congrFun hcol v
  simp only [Pi.smul_apply, smul_eq_mul] at hu hv
  rw [hu, hsym, hv, ← mul_assoc]
  have hc2 : c * c = 1 := by
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hc with h | h <;> norm_num [h]
  rw [hc2, one_mul]

private theorem twin_half_projection (u v : Fin n) (huv : u ≠ v)
    (htwin : ∀ x, x ≠ u → x ≠ v → (G.Adj x u ↔ G.Adj x v))
    (hc : StronglyCospectral G u v) :
    idempotent G (twinEigenvalue G u v) *ᵥ Pi.single u 1 =
      (1 / 2 : ℝ) • (Pi.single u 1 - Pi.single v 1) := by
  obtain ⟨c, hc, hcol⟩ := hc (twinEigenvalue G u v)
  have hp := twin_projection G u v huv htwin (twinEigenvalue G u v)
  rw [if_pos rfl, mulVec_sub] at hp
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hc with rfl | rfl
  · have hzero := congrFun hp u
    rw [← one_smul ℝ (idempotent G (twinEigenvalue G u v) *ᵥ Pi.single v 1), ← hcol,
      sub_self] at hzero
    simp [Pi.single_apply, huv, huv.symm] at hzero
  · have hneg : idempotent G (twinEigenvalue G u v) *ᵥ Pi.single v 1 =
        -(idempotent G (twinEigenvalue G u v) *ᵥ Pi.single u 1) := by
      rw [hcol, neg_one_smul, neg_neg]
    funext x
    have hx := congrFun hp x
    simp only [hneg, Pi.sub_apply, Pi.neg_apply] at hx
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith

private theorem adjacency_expansion (u : Fin n) (t : ℝ) :
    hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u =
      ∑ λ ∈ univ.image hA.eigenvalues, (idempotent G λ u u : ℂ) *
        (Circle.exp (λ * t) : ℂ) := by
  classical
  let b (i : Fin n) (x : Fin n) : ℂ := hA.eigenvectorBasis i x
  let B : Matrix (Fin n) (Fin n) ℂ := (-t) • hamiltonianGenerator (G.adjMatrix ℂ)
  have hb (i : Fin n) : G.adjMatrix ℂ *ᵥ b i = (hA.eigenvalues i : ℂ) • b i := by
    funext x
    have hx := congrFun (hA.mulVec_eigenvectorBasis i) x
    have hcast := congrArg Complex.ofReal hx
    simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
      Pi.smul_apply, smul_eq_mul] at hcast ⊢
    convert hcast using 3
    · simp [SimpleGraph.adjMatrix_apply]
    · rfl
  have hphase (i : Fin n) : NormedSpace.exp B *ᵥ b i =
      (Circle.exp (hA.eigenvalues i * t) : ℂ) • b i := by
    rw [Circle.coe_exp]
    apply exp_mulVec_of_eigenvector
    rw [B, hamiltonianGenerator, smul_mulVec, smul_mulVec, hb, smul_smul, smul_smul]
    congr 1
    simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  have he : (Pi.single u 1 : Fin n → ℂ) = ∑ i, b i u • b i := by
    funext x
    have hx := congrArg Complex.ofReal (congrFun (basis_expansion G (Pi.single u 1)) x)
    simpa [dotProduct_single, Finset.sum_apply, b, Pi.single_apply] using hx.symm
  have hentry := congrFun (congrArg ((NormedSpace.exp B).mulVec) he) u
  simp only [mulVec_single_one, mulVec_sum, mulVec_smul, hphase, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hentry
  change NormedSpace.exp B u u = _
  rw [hentry]
  calc
    _ = ∑ λ ∈ univ.image hA.eigenvalues, ∑ i with hA.eigenvalues i = λ,
        b i u * ((Circle.exp (hA.eigenvalues i * t) : ℂ) * b i u) :=
      (sum_fiberwise_of_maps_to (fun i _ => mem_image_of_mem _ (mem_univ i)) _).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun λ _ => ?_
      simp only [idempotent, Matrix.sum_apply, vecMulVec_apply, Complex.ofReal_sum,
        Complex.ofReal_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(mem_filter.mp hi).2]
      dsimp [b]
      ring

private theorem total_weight (u : Fin n) :
    ∑ λ ∈ univ.image hA.eigenvalues, idempotent G λ u u = 1 := by
  classical
  have h := adjacency_expansion G u 0
  simp only [neg_zero, hamiltonianPropagator, zero_smul, NormedSpace.exp_zero,
    Matrix.one_apply_eq, mul_zero, Circle.exp_zero, Circle.coe_one, mul_one] at h
  exact_mod_cast h.symm

private theorem dephased_expansion (u v : Fin n)
    (hhalf : idempotent G (twinEigenvalue G u v) u u = 1 / 2) (t : ℝ) :
    hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u =
      (Circle.exp (twinEigenvalue G u v * t) : ℂ) *
        (1 / 2 + ∑ λ ∈ remainingSupport G u v, (idempotent G λ u u : ℂ) *
          (Circle.exp ((λ - twinEigenvalue G u v) * t) : ℂ)) := by
  classical
  let θ := twinEigenvalue G u v
  let S := univ.image hA.eigenvalues
  have hθ : θ ∈ S := by
    by_contra hn
    have hempty : (univ.filter fun i => hA.eigenvalues i = θ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hn (mem_image.mpr ⟨i, mem_univ _, (mem_filter.mp hi).2⟩)
    have hz : idempotent G θ u u = 0 := by simp [idempotent, hempty]
    linarith
  rw [adjacency_expansion G u t, ← add_sum_erase S _ hθ]
  have hsum : (∑ λ ∈ S.erase θ, (idempotent G λ u u : ℂ) * (Circle.exp (λ * t) : ℂ)) =
      ∑ λ ∈ remainingSupport G u v, (idempotent G λ u u : ℂ) * (Circle.exp (λ * t) : ℂ) := by
    symm
    apply Finset.sum_subset
    · intro λ hλ
      obtain ⟨hS, hne, _⟩ := mem_filter.mp hλ
      exact mem_erase.mpr ⟨hne, hS⟩
    · intro λ hλ hno
      have hz : idempotent G λ u u = 0 := by
        have hm := mem_erase.mp hλ
        have hn : ¬ 0 < idempotent G λ u u := fun hp => hno (mem_filter.mpr ⟨hm.2, hm.1, hp⟩)
        exact le_antisymm (le_of_not_gt hn) (projector_weight_nonneg G u λ)
      simp [hz]
  change idempotent G θ u u * (Circle.exp (θ * t) : ℂ) + _ = _
  rw [hsum, hhalf, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_add,
    Finset.mul_sum, mul_comm (1 / 2 : ℂ)]
  congr 1
  refine Finset.sum_congr rfl fun λ _ => ?_
  rw [← mul_left_comm, ← Circle.coe_mul, ← Circle.exp_add]
  congr 3
  ring

-- The result below uses the same remaining support for the spectral series and character.


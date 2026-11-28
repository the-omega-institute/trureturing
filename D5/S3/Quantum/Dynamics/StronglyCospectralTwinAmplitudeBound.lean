/- GID: D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Odd relations among adjacency gaps bound the return amplitude of twins. -/

/-
proof_shape: result: content
escape_witness: adjacency_expansion identifies the diagonal of the actual adjacency walk
  with the sum over full-eigenspace projector weights. The dephased form transports the
  weighted character chord estimate to every odd relation for that same graph.
admission_basis: open-problem-resolution (#35281; Proved)
-/

import OmegaBuild.Commands
import D5.S3.Fourier.WeightedIntegerRelations
import D5.S3.Fourier.WeightedPhaseRelationLattice
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation

/-! A relation-dependent adjacency return-amplitude floor for §9 of Meagher, Monterde and
Nguyen, *Sedentariness in Cayley graphs*, arXiv:2611.00567v1. Lemma 3.3 and Theorem 2.2(2) of
the paper give the twin eigenvector and the qualitative parity criterion, respectively. -/

compile_only_with_mathlib

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
  exact (univ.image (hA).eigenvalues).filter
    fun e => e ≠ twinEigenvalue G u v ∧ 0 < idempotent G e u u

private theorem basis_expansion (w : Fin n → ℝ) :
    ∑ i, (⇑((hA).eigenvectorBasis i) ⬝ᵥ w) • ⇑((hA).eigenvectorBasis i) = w := by
  have h := congrArg WithLp.ofLp ((hA).eigenvectorBasis.sum_repr' (WithLp.toLp 2 w))
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
      simp [SimpleGraph.adjMatrix_apply, twinEigenvalue, huv, ha]
  by_cases hxv : x = v
  · subst x
    have he : G.Adj v u ↔ G.Adj u v := G.adj_comm v u
    by_cases ha : G.Adj u v <;>
      simp [SimpleGraph.adjMatrix_apply, twinEigenvalue, huv.symm, he, ha]
  simp [SimpleGraph.adjMatrix_apply, hxu, hxv, htwin x hxu hxv]

private theorem twin_projection (u v : Fin n) (huv : u ≠ v)
    (htwin : ∀ x, x ≠ u → x ≠ v → (G.Adj x u ↔ G.Adj x v)) (e : ℝ) :
    idempotent G e *ᵥ (Pi.single u 1 - Pi.single v 1) =
      if e = twinEigenvalue G u v then (Pi.single u 1 - Pi.single v 1) else 0 := by
  classical
  let w : Fin n → ℝ := Pi.single u 1 - Pi.single v 1
  let θ := twinEigenvalue G u v
  have hz (i : Fin n) (hi : (hA).eigenvalues i ≠ θ) : ⇑((hA).eigenvectorBasis i) ⬝ᵥ w = 0 :=
    LaplacianPeakTransferTrees.eig_dot_zero hA w θ (twin_difference G u v huv htwin) i hi
  change idempotent G e *ᵥ w = if e = θ then w else 0
  change (∑ i with (hA).eigenvalues i = e,
    vecMulVec ⇑((hA).eigenvectorBasis i) ⇑((hA).eigenvectorBasis i)) *ᵥ w = _
  simp only [sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  by_cases heig : e = θ
  · subst e
    rw [if_pos rfl]
    conv_rhs => rw [← basis_expansion G w]
    refine Finset.sum_subset (filter_subset _ _) ?_
    intro i _ hi
    simp [hz i (by simpa using hi)]
  · rw [if_neg heig]
    refine Finset.sum_eq_zero fun i hi => ?_
    simp [hz i ((mem_filter.mp hi).2.trans_ne heig)]

private theorem projector_weight_nonneg (u : Fin n) (e : ℝ) : 0 ≤ idempotent G e u u := by
  classical
  simp only [idempotent, Matrix.sum_apply, vecMulVec_apply]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((hA).eigenvectorBasis i u)

private theorem diagonal_weights_eq (u v : Fin n) (hc : StronglyCospectral G u v) (e : ℝ) :
    idempotent G e u u = idempotent G e v v := by
  have hsym : idempotent G e u v = idempotent G e v u := by
    simp only [idempotent, Matrix.sum_apply, vecMulVec_apply, mul_comm]
  obtain ⟨c, hc, hcol⟩ := hc e
  rw [mulVec_single_one, mulVec_single_one] at hcol
  have hu := congrFun hcol u
  have hv := congrFun hcol v
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at hu hv
  rw [hu, hsym, hv, ← mul_assoc]
  have hc2 : c * c = 1 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hc with h | h <;> norm_num [h]
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
    simp [huv] at hzero
  · have hneg : idempotent G (twinEigenvalue G u v) *ᵥ Pi.single v 1 =
        -(idempotent G (twinEigenvalue G u v) *ᵥ Pi.single u 1) := by
      rw [hcol, neg_one_smul, neg_neg]
    funext x
    have hx := congrFun hp x
    simp only [hneg, Pi.sub_apply, Pi.neg_apply] at hx
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    linarith

private theorem adjacency_expansion (u : Fin n) (t : ℝ) :
    hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u =
      ∑ e ∈ univ.image (hA).eigenvalues, (idempotent G e u u : ℂ) *
        (Circle.exp (e * t) : ℂ) := by
  classical
  let b (i : Fin n) (x : Fin n) : ℂ := (hA).eigenvectorBasis i x
  let B : Matrix (Fin n) (Fin n) ℂ := (-t) • hamiltonianGenerator (G.adjMatrix ℂ)
  have hb (i : Fin n) : G.adjMatrix ℂ *ᵥ b i = ((hA).eigenvalues i : ℂ) • b i := by
    funext x
    have hx := congrFun ((hA).mulVec_eigenvectorBasis i) x
    have hcast := congrArg Complex.ofReal hx
    simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
      Pi.smul_apply, smul_eq_mul] at hcast ⊢
    convert hcast using 3
    simp only [SimpleGraph.adjMatrix_apply]
    split <;> simp_all
  have hphase (i : Fin n) : NormedSpace.exp B *ᵥ b i =
      (Circle.exp ((hA).eigenvalues i * t) : ℂ) • b i := by
    rw [Circle.coe_exp]
    apply exp_mulVec_of_eigenvector
    change ((-t) • hamiltonianGenerator (G.adjMatrix ℂ)) *ᵥ b i = _
    rw [hamiltonianGenerator, smul_mulVec, smul_mulVec, hb, smul_smul, ← smul_assoc]
    congr 1
    simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  have he : (Pi.single u 1 : Fin n → ℂ) = ∑ i, b i u • b i := by
    funext x
    have hx := congrArg Complex.ofReal (congrFun (basis_expansion G (Pi.single u 1)) x)
    by_cases h : x = u <;>
      simpa [dotProduct_single, Finset.sum_apply, b, Pi.single_apply, h] using hx.symm
  have hentry := congrFun (congrArg ((NormedSpace.exp B).mulVec) he) u
  simp only [mulVec_single_one, mulVec_sum, mulVec_smul, hphase, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at hentry
  change NormedSpace.exp B u u = _
  rw [hentry]
  calc
    _ = ∑ e ∈ univ.image (hA).eigenvalues, ∑ i with (hA).eigenvalues i = e,
        b i u * ((Circle.exp ((hA).eigenvalues i * t) : ℂ) * b i u) :=
      (sum_fiberwise_of_maps_to (fun i _ => mem_image_of_mem _ (mem_univ i)) _).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [idempotent, Matrix.sum_apply, vecMulVec_apply, Complex.ofReal_sum,
        Complex.ofReal_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(mem_filter.mp hi).2]
      dsimp [b]
      ring

private theorem dephased_expansion (u v : Fin n)
    (hhalf : idempotent G (twinEigenvalue G u v) u u = 1 / 2) (t : ℝ) :
    hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u =
      (Circle.exp (twinEigenvalue G u v * t) : ℂ) *
        (1 / 2 + ∑ e ∈ remainingSupport G u v, (idempotent G e u u : ℂ) *
          (Circle.exp ((e - twinEigenvalue G u v) * t) : ℂ)) := by
  classical
  let θ := twinEigenvalue G u v
  let S := univ.image (hA).eigenvalues
  have hθ : θ ∈ S := by
    by_contra hn
    have hempty : (univ.filter fun i => (hA).eigenvalues i = θ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hn (mem_image.mpr ⟨i, mem_univ _, (mem_filter.mp hi).2⟩)
    have hz : idempotent G θ u u = 0 := by simp [idempotent, hempty]
    linarith
  rw [adjacency_expansion G u t, ← add_sum_erase S _ hθ]
  have hsum : (∑ e ∈ S.erase θ, (idempotent G e u u : ℂ) * (Circle.exp (e * t) : ℂ)) =
      ∑ e ∈ remainingSupport G u v, (idempotent G e u u : ℂ) * (Circle.exp (e * t) : ℂ) := by
    symm
    apply Finset.sum_subset
    · intro e heig
      obtain ⟨hS, hne, _⟩ := mem_filter.mp heig
      exact mem_erase.mpr ⟨hne, hS⟩
    · intro e heig hno
      have hz : idempotent G e u u = 0 := by
        have hm := mem_erase.mp heig
        have hn : ¬ 0 < idempotent G e u u := fun hp => hno (mem_filter.mpr ⟨hm.2, hm.1, hp⟩)
        exact le_antisymm (le_of_not_gt hn) (projector_weight_nonneg G u e)
      simp [hz]
  change idempotent G θ u u * (Circle.exp (θ * t) : ℂ) + _ = _
  rw [hsum, hhalf, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_add,
    Finset.mul_sum, mul_comm (1 / 2 : ℂ)]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← mul_left_comm, ← Circle.coe_mul, ← Circle.exp_add]
  congr 3
  ring

private theorem remaining_weight (u v : Fin n)
    (hhalf : idempotent G (twinEigenvalue G u v) u u = 1 / 2) :
    ∑ e ∈ remainingSupport G u v, idempotent G e u u = 1 / 2 := by
  have h := dephased_expansion G u v hhalf 0
  simp only [neg_zero, hamiltonianPropagator, zero_smul, NormedSpace.exp_zero,
    Matrix.one_apply_eq, mul_zero, Circle.exp_zero, Circle.coe_one, mul_one, one_mul] at h
  have hr := congrArg Complex.re h
  simp only [Complex.one_re, Complex.add_re, Complex.re_sum, Complex.ofReal_re] at hr
  rw [show (1 / 2 : ℂ).re = 1 / 2 by norm_num] at hr
  linarith

private theorem constant_character {J : Type*} [Fintype J] (q : Circle) (k : J → ℤ) :
    ((∏ j, q ^ k j : Circle) : ℂ) = (q : ℂ) ^ (∑ j, k j) := by
  have h := congrArg Additive.toMul
    (map_sum (zmultiplesHom (Additive Circle) (Additive.ofMul q)) k Finset.univ)
  rw [toMul_sum] at h
  change q ^ (∑ j, k j) = ∏ j, q ^ k j at h
  rw [← h, Circle.coe_zpow]

private theorem circle_chord_add_sq (z : Circle) :
    ‖(z : ℂ) + 1‖ ^ 2 = 2 + 2 * (z : ℂ).re := by
  have hz := Circle.normSq_coe z
  rw [Complex.normSq_apply] at hz
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
  nlinarith only [hz]

/-- Distinct strongly cospectral twins have half their spectral mass at the twin eigenvalue
and identical return amplitudes. A positive uniform floor on positive times exists exactly
when the remaining spectral gaps have an odd integer relation. Each such relation yields
the displayed floor for every real time. -/
theorem result (u v : Fin n) (huv : u ≠ v)
    (htwin : ∀ x, x ≠ u → x ≠ v → (G.Adj x u ↔ G.Adj x v))
    (hc : StronglyCospectral G u v) :
    let θ := twinEigenvalue G u v
    let J := ↥(remainingSupport G u v)
    let a (e : J) := idempotent G e u u
    let γ (e : J) := (e : ℝ) - θ
    let U (t : ℝ) := hamiltonianPropagator (G.adjMatrix ℂ) (-t)
    let certificate (ℓ : J → ℤ) := (∑ e, (ℓ e : ℝ) * γ e) = 0 ∧ Odd (∑ e, ℓ e)
    let D (ℓ : J → ℤ) := ∑ e, (ℓ e : ℝ) ^ 2 / a e
    idempotent G θ *ᵥ Pi.single u 1 = (1 / 2 : ℝ) • (Pi.single u 1 - Pi.single v 1) ∧
    idempotent G θ u u = 1 / 2 ∧ (∀ e, 0 < a e) ∧ (∑ e, a e) = 1 / 2 ∧
    (∀ t, U t u u = U t v v) ∧
    ((∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → C ≤ ‖U t u u‖) ↔ ∃ ℓ, certificate ℓ) ∧
    ∀ ℓ, certificate ℓ → 0 < D ℓ ∧ ∀ t : ℝ, 2 / D ℓ ≤ ‖U t u u‖ := by
  classical
  intro θ J a γ U certificate D
  have hprojection := twin_half_projection G u v huv htwin hc
  have hhalf : idempotent G θ u u = 1 / 2 := by
    have h := congrFun hprojection u
    rw [mulVec_single_one] at h
    simpa [θ, Pi.single_apply, huv, huv.symm] using h
  have ha (e : J) : 0 < a e := (mem_filter.mp e.property).2.2
  have hsum : ∑ e, a e = 1 / 2 := by
    change (∑ e : ↥(remainingSupport G u v), idempotent G (e : ℝ) u u) = 1 / 2
    rw [Finset.sum_coe_sort (remainingSupport G u v) (fun e => idempotent G e u u)]
    exact remaining_weight G u v hhalf
  have heq (t : ℝ) : U t u u = U t v v := by
    simp only [U, adjacency_expansion, diagonal_weights_eq G u v hc]
  let F (p : J → Circle) : ℂ := 1 / 2 + ∑ j, (a j : ℂ) * (p j : ℂ)
  let orbit (t : ℝ) (j : J) : Circle := Circle.exp (γ j * t)
  have hnorm (t : ℝ) : ‖U t u u‖ = ‖F (orbit t)‖ := by
    have he : U t u u = (Circle.exp (θ * t) : ℂ) * F (orbit t) := by
      dsimp only [U, F, orbit, γ, a, J]
      rw [Finset.sum_coe_sort (remainingSupport G u v)
        (fun e => (idempotent G e u u : ℂ) * (Circle.exp ((e - θ) * t) : ℂ))]
      exact dephased_expansion G u v hhalf t
    rw [he, norm_mul, Circle.norm_coe, one_mul]
  let q : Circle := Circle.exp Real.pi
  have hq : (q : ℂ) = -1 := Complex.exp_pi_mul_I
  have hbound (ℓ : J → ℤ) (hℓ : certificate ℓ) :
      0 < D ℓ ∧ ∀ t : ℝ, 2 / D ℓ ≤ ‖U t u u‖ := by
    have hnonzero : ∃ j : J, ℓ j ≠ 0 := by
      by_contra! hz
      exact (by simpa [hz] using hℓ.2 : False)
    obtain ⟨j, hj⟩ := hnonzero
    have hD : 0 < D ℓ := by
      exact Finset.sum_pos' (fun i _ => div_nonneg (sq_nonneg _) (ha i).le)
        ⟨j, mem_univ _, div_pos (sq_pos_of_ne_zero (by exact_mod_cast hj)) (ha j)⟩
    refine ⟨hD, fun t => ?_⟩
    have hchar : (∏ j, orbit t j ^ ℓ j) = 1 :=
      orbit_character univ γ ℓ hℓ.1 t
    have htarget : ((∏ j : J, q ^ ℓ j : Circle) : ℂ) = -1 := by
      rw [constant_character, hq, hℓ.2.neg_one_zpow]
    have hchord := weighted_character_chord univ (univ : Finset Unit) (orbit t)
      (fun _ => q) a (fun _ => ℓ) (fun _ => 1) (fun i _ => ha i) (fun _ _ => zero_le_one)
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, sq_abs, hchar, Circle.coe_one,
      htarget, hq, sub_neg_eq_add] at hchord
    change ‖(1 : ℂ) + 1‖ ^ 2 ≤ D ℓ * ∑ j, a j * ‖(orbit t j : ℂ) + 1‖ ^ 2 at hchord
    have henergy : ∑ j, a j * ‖(orbit t j : ℂ) + 1‖ ^ 2 = 2 * (F (orbit t)).re := by
      simp only [circle_chord_add_sq, mul_add, Finset.sum_add_distrib,
        mul_left_comm (a _) 2, ← Finset.mul_sum,
        F, Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [show (1 / 2 : ℂ).re = 1 / 2 by norm_num, ← Finset.sum_mul, hsum]
      ring
    rw [henergy, show ‖(1 : ℂ) + 1‖ = 2 by norm_num [show (1 : ℂ) + 1 = 2 by norm_num]] at hchord
    have hreal : 2 / D ℓ ≤ (F (orbit t)).re := by
      apply (div_le_iff₀ hD).2
      nlinarith only [hchord]
    rw [hnorm]
    exact hreal.trans (Complex.re_le_norm _)
  refine ⟨hprojection, hhalf, ha, hsum, heq, ⟨?_, ?_⟩, hbound⟩
  · rintro ⟨C, hC, hCtime⟩
    by_contra hnone
    let target : J → Circle := fun _ => q
    have hclosure : target ∈ closure (orbit '' Set.Ioi 0) := by
      rw [((closure_real_phase_orbit γ).2 0).2, (closure_real_phase_orbit γ).1]
      intro k hk
      have hev : Even (∑ j, k j) := Int.not_odd_iff_even.mp (fun ho => hnone ⟨k, hk, ho⟩)
      apply Subtype.ext
      change ((∏ j : J, q ^ k j : Circle) : ℂ) = (1 : Circle)
      rw [constant_character, hq, hev.neg_one_zpow, Circle.coe_one]
    have hcontinuous : Continuous F := by
      exact continuous_const.add (continuous_finsetSum _ fun j _ =>
        continuous_const.mul (continuous_subtype_val.comp (continuous_apply j)))
    have hclosed : IsClosed {p : J → Circle | C ≤ ‖F p‖} :=
      isClosed_le continuous_const hcontinuous.norm
    have hcontain : orbit '' Set.Ioi 0 ⊆ {p : J → Circle | C ≤ ‖F p‖} := by
      rintro _ ⟨t, ht, rfl⟩
      change C ≤ ‖F (orbit t)‖
      rw [← hnorm t]
      exact hCtime t ht
    have hcq := closure_minimal hcontain hclosed hclosure
    have hF : F target = 0 := by
      have hcast := congrArg Complex.ofReal hsum
      simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat] at hcast
      simp_rw [F, target, hq, mul_neg_one, Finset.sum_neg_distrib, hcast, add_neg_cancel]
    change C ≤ ‖F target‖ at hcq
    rw [hF, norm_zero] at hcq
    exact hC.not_ge hcq
  · rintro ⟨ℓ, hℓ⟩
    obtain ⟨hD, hfloor⟩ := hbound ℓ hℓ
    exact ⟨2 / D ℓ, div_pos (by norm_num) hD, fun t _ => hfloor t⟩

#print axioms result

end D5.S3.Quantum.Dynamics.StronglyCospectralTwinAmplitudeBound

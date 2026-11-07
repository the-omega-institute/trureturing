/- GID: D5/S3/VertexAlgebra/Analysis/OriginalHeat
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalHeat
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal original-energy cylinder heat, inclusion bridge and finite-rank tails. -/

import D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis
import D5.S3.Quantum.Analysis.DiagonalHeat
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
DiagonalHeat.multiplier and heat are the UNIQUE generic multiplier/semigroup
implementation. Their whole-space contraction and continuity proofs, including
Scott Armstrong's Apache-2.0 semigroup material, are reused. Its imported
EigenbasisClosure retains the PhysLean attribution and its existing trace imports
remain supplier dependencies, not original-model thermal-trace assertions.

The new bridge constructs the genuine basis from OriginalEnergyBasis and proves
its scalar action on ACTUAL original grades, the literal finite-core formula,
projection/inclusion compatibility and original finite-dimensional approximants.
Heat uses Sugawara energy E; only the Sobolev norm uses (1+E)^k. All ranks,
including rank zero, and all five Model fields remain quantified. No generator,
unbounded-domain, trace-class, locality or full-VOA completion claim is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped BigOperators InnerProductSpace Topology NNReal VertexOperator
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open LatticeAllStateField Lattice.OriginalChargedEnergy SourceBPZ.OriginalMatterHermitian
open Model
variable (M : Model)

/-- The actual original positive-time propagator on the entire original completion. -/
def Model.heat (k : ℕ) (t : ℝ≥0) : M.Sobolev k →L[ℂ] M.Sobolev k :=
  D5.S3.Quantum.Analysis.DiagonalHeat.heat (M.energyBasis k)
    (fun i => (i.1 : ℝ)) (fun i => by exact_mod_cast energyIndex_nonnegative M k i) t

private theorem heat_energy_basis (k : ℕ) (t : ℝ≥0) (i : M.energyIndex k) :
    M.heat k t (M.energyBasis k i) =
      (Real.exp (-(t : ℝ) * (i.1 : ℝ)) : ℂ) • M.energyBasis k i := by
  change D5.S3.Quantum.Analysis.DiagonalHeat.heat (M.energyBasis k)
    (fun i => (i.1 : ℝ)) _ t (M.energyBasis k i) = _
  rw [D5.S3.Quantum.Analysis.DiagonalHeat.heat_basis]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

/-- Scalar action on an original completed energy grade; no spectral premise is supplied. -/
theorem heat_completedGrade (k : ℕ) (t : ℝ≥0) (E : ℤ)
    (x : M.completedGrade k E) :
    M.heat k t (x : M.Sobolev k) =
      (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ) • (x : M.Sobolev k) := by
  classical
  have hexp : (x : M.Sobolev k) =
      ∑ j, (M.energyGradeBasis k E).repr x j • M.energyBasis k ⟨E,j⟩ := by
    have h := congrArg (M.completedGrade k E).subtype
      ((M.energyGradeBasis k E).sum_repr x)
    simpa only [map_sum, map_smul, energyBasis_coe M k, Model.energyVector, Submodule.subtype_apply] using h.symm
  rw [hexp, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, heat_energy_basis]
  exact smul_comm _ _ _

private theorem heat_grade (k : ℕ) (t : ℝ≥0) (E : ℤ)
    (v : Carrier M.D) (hv : v ∈ grade M.D E) :
    M.heat k t (M.embed k v) =
      (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ) • M.embed k v :=
  heat_completedGrade M k t E ⟨M.embed k v, ⟨⟨v,hv⟩,rfl⟩⟩

/-- Literal original finite-core identity with unshifted Sugawara energy. -/
theorem heat_embed (k : ℕ) (t : ℝ≥0) (v : Carrier M.D) :
    M.heat k t (M.embed k v) =
      M.embed k (∑ E ∈ stateEnergies M.D v,
        (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ) • gradeProjection M.D E v) := by
  classical
  conv_lhs => rw [← sum_gradeProjections M.D v, map_sum, map_sum]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun E _ =>
    heat_grade M k t E _ (gradeProjection_mem M.D E v)

private theorem heat_semigroup (k : ℕ) :
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (M.Sobolev k),
      ∀ t, S t = (M.heat k t).restrictScalars ℝ := by
  obtain ⟨_, _, _, _, _, _, S, hS, _, _⟩ :=
    D5.S3.Quantum.Analysis.DiagonalHeat.diagonal_heat (M.energyBasis k)
      (fun i => (i.1 : ℝ))
      (fun i => by exact_mod_cast energyIndex_nonnegative M k i)
  exact ⟨S,hS⟩

private theorem heat_zero (k : ℕ) :
    M.heat k 0 = ContinuousLinearMap.id ℂ (M.Sobolev k) := by
  obtain ⟨S,hS⟩ := heat_semigroup M k
  ext x
  have h := DFunLike.congr_fun S.operator_zero x
  simpa only [hS, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.id_apply] using h

private theorem heat_add (k : ℕ) (s t : ℝ≥0) :
    M.heat k (s+t) = (M.heat k s).comp (M.heat k t) := by
  obtain ⟨S,hS⟩ := heat_semigroup M k
  ext x
  have h := DFunLike.congr_fun (S.operator_add s t) x
  simpa only [hS, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.comp_apply] using h

private theorem heat_norm (k : ℕ) (t : ℝ≥0) (x : M.Sobolev k) :
    ‖M.heat k t x‖ ≤ ‖x‖ :=
  D5.S3.Quantum.Analysis.DiagonalHeat.heat_contraction (M.energyBasis k)
    (fun i => (i.1 : ℝ))
    (fun i => by exact_mod_cast energyIndex_nonnegative M k i) t x

private theorem heat_orbit_continuous (k : ℕ) (x : M.Sobolev k) :
    Continuous (fun t : ℝ≥0 => M.heat k t x) :=
  D5.S3.Quantum.Analysis.DiagonalHeat.heat_continuous (M.energyBasis k)
    (fun i => (i.1 : ℝ))
    (fun i => by exact_mod_cast energyIndex_nonnegative M k i) x

private theorem heat_positive (k : ℕ) (t : ℝ≥0) : (M.heat k t).IsPositive := by
  obtain ⟨_,_,_,_,_,hpos,_⟩ :=
    D5.S3.Quantum.Analysis.DiagonalHeat.diagonal_heat (M.energyBasis k)
      (fun i => (i.1 : ℝ))
      (fun i => by exact_mod_cast energyIndex_nonnegative M k i)
  exact hpos t

/-- The actual inclusions intertwine the original core heat formula at every order. -/
theorem heat_inclusion (j k : ℕ) (hjk : j ≤ k) (t : ℝ≥0) :
    (M.inclusion j k hjk).comp (M.heat k t) =
      (M.heat j t).comp (M.inclusion j k hjk) := by
  have hdense : Dense ((M.embed k).range : Set (M.Sobolev k)) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    rw [finiteCore_eq_energyBasis_span M k, (M.energyBasis k).dense_span]
  change DenseRange (M.embed k) at hdense
  ext x
  refine hdense.induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [ContinuousLinearMap.comp_apply, heat_embed, inclusion_embed]

/-- Both orders of composition with the genuine original projection have its heat weight. -/
theorem heat_projection (k : ℕ) (t : ℝ≥0) (E : ℤ) (x : M.Sobolev k) :
    M.heat k t (M.projection k E x) =
        (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ) • M.projection k E x ∧
    M.projection k E (M.heat k t x) =
        (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ) • M.projection k E x := by
  constructor
  · exact heat_completedGrade M k t E
      ⟨M.projection k E x, (M.completedGrade k E).starProjection_apply_mem x⟩
  · refine (embed_dense M k).induction_on x ?_ ?_
    · exact isClosed_eq
        ((M.projection k E).continuous.comp (M.heat k t).continuous)
        ((M.projection k E).continuous.const_smul (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ))
    · intro v
      conv_lhs => rw [← sum_gradeProjections M.D v, map_sum, map_sum, map_sum]
      conv_rhs => rw [← sum_gradeProjections M.D v, map_sum, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro F _
      rw [heat_grade M k t F _ (gradeProjection_mem M.D F v), map_smul,
        projection_grade M k F E _ (gradeProjection_mem M.D F v)]
      split_ifs with h
      · subst F; rfl
      · simp

private theorem projection_negative (k : ℕ) (E : ℤ) (hE : E < 0)
    (x : M.Sobolev k) : M.projection k E x = 0 := by
  have h := (M.completedGrade k E).starProjection_apply_mem x
  exact (completedGrade_negative M k E hE).le h

/-- The scalar cutoff includes the vacuum even at N=0. -/
def Model.energyCutoff (_M : Model) (N : ℕ) : Finset ℤ := Finset.Icc 0 (N : ℤ)

/-- The finite sum of the actual original completed energy grades 0,...,N. -/
def Model.cutoffSpace (k N : ℕ) : Submodule ℂ (M.Sobolev k) :=
  (M.energyCutoff N).sup (M.completedGrade k)

instance (k N : ℕ) : FiniteDimensional ℂ (M.cutoffSpace k N) := by
  unfold Model.cutoffSpace
  infer_instance

/-- The original finite-rank propagator, with arbitrary completed inputs. -/
def Model.heatTruncation (k : ℕ) (t : ℝ≥0) (N : ℕ) :
    M.Sobolev k →L[ℂ] M.Sobolev k :=
  (M.truncation k (M.energyCutoff N)).comp (M.heat k t)

private theorem truncation_mem_cutoff (k N : ℕ) (x : M.Sobolev k) :
    M.truncation k (M.energyCutoff N) x ∈ M.cutoffSpace k N := by
  classical
  simp only [Model.truncation, ContinuousLinearMap.sum_apply]
  apply Submodule.sum_mem
  intro E hE
  exact (Finset.le_sup (f := M.completedGrade k) hE)
    ((M.completedGrade k E).starProjection_apply_mem x)

/-- Genuine finite-dimensional range in the original finite sum, with no multiplicity assumption. -/
theorem heatTruncation_range (k : ℕ) (t : ℝ≥0) (N : ℕ) :
    (M.heatTruncation k t N).range ≤ M.cutoffSpace k N ∧
    FiniteDimensional ℂ (M.heatTruncation k t N).range := by
  have hr : (M.heatTruncation k t N).range ≤ M.cutoffSpace k N := by
    rintro x ⟨y,rfl⟩
    exact truncation_mem_cutoff M k N (M.heat k t y)
  exact ⟨hr, Submodule.finiteDimensional_of_le hr⟩

private theorem heat_tail_core (k : ℕ) (t : ℝ≥0) (N : ℕ) (v : Carrier M.D) :
    (M.heat k t - M.heatTruncation k t N) (M.embed k v) =
      M.embed k (∑ E ∈ stateEnergies M.D v,
        (if E ∈ M.energyCutoff N then (0 : ℂ)
          else (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ)) • gradeProjection M.D E v) := by
  classical
  conv_lhs => rw [← sum_gradeProjections M.D v, map_sum, map_sum]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro E _
  change M.heat k t (M.embed k _) -
    M.truncation k (M.energyCutoff N) (M.heat k t (M.embed k _)) = _
  have hh := (heat_projection M k t E (M.embed k (gradeProjection M.D E v))).1
  rw [projection_grade M k E E _ (gradeProjection_mem M.D E v), if_pos rfl] at hh
  rw [hh, map_smul,
    truncation_grade M k (M.energyCutoff N) E _ (gradeProjection_mem M.D E v)]
  split_ifs <;> simp

/-- Uniform operator-norm tail for the actual integer-energy truncations, including t=0. -/
theorem heat_tail_bound (k : ℕ) (t : ℝ≥0) (N : ℕ) :
    ‖M.heat k t - M.heatTruncation k t N‖ ≤
      Real.exp (-(t : ℝ) * ((N : ℝ) + 1)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro x
  refine (embed_dense M k).induction_on x ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro v
    rw [heat_tail_core]
    apply finite_multiplier_bound M k k _ (Real.exp_pos _).le v
    intro E hE
    have h0 := stateEnergies_nonneg M.positive v E hE
    have hweight : (0 : ℝ) ≤ ((E : ℝ) + 1) ^ k := by
      have : (0 : ℝ) ≤ (E : ℝ) := by exact_mod_cast h0
      positivity
    split_ifs with hcut
    · simp only [norm_zero, zero_mul]
      positivity
    · have hlarge : (N : ℤ)+1 ≤ E := by
        have := hcut
        simp only [Model.energyCutoff, Finset.mem_Icc, not_and] at this
        have := this h0
        omega
      have hlarge' : (N : ℝ) + 1 ≤ (E : ℝ) := by exact_mod_cast hlarge
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hlarge' (neg_nonpos.mpr t.coe_nonneg))) hweight

private theorem cutoff_strong (k : ℕ) (x : M.Sobolev k) :
    Tendsto (fun N : ℕ => M.truncation k (M.energyCutoff N) x) atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v,hv⟩ := Metric.denseRange_iff.mp (embed_dense M k) x (ε/3) (by positivity)
  let K := (stateEnergies M.D v).sup Int.toNat
  refine ⟨K, fun N hN => ?_⟩
  have hs : stateEnergies M.D v ⊆ M.energyCutoff N := by
    intro E hE
    have h0 := stateEnergies_nonneg M.positive v E hE
    have hle : E.toNat ≤ N := (Finset.le_sup (f := Int.toNat) hE).trans hN
    have hle' : (E.toNat : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    exact Finset.mem_Icc.mpr ⟨h0, by simpa only [Int.toNat_of_nonneg h0] using hle'⟩
  have he := truncation_embed_of_subset M k (M.energyCutoff N) v hs
  calc
    dist (M.truncation k (M.energyCutoff N) x) x ≤
        dist (M.truncation k (M.energyCutoff N) x)
          (M.truncation k (M.energyCutoff N) (M.embed k v)) + dist (M.embed k v) x := by
            rw [he]; exact dist_triangle _ _ _
    _ ≤ dist x (M.embed k v) + dist (M.embed k v) x := by
      refine add_le_add ?_ le_rfl
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact truncation_norm M k (M.energyCutoff N) _
    _ < ε := by rw [dist_comm (M.embed k v) x]; linarith

private theorem heatTruncation_compact (k : ℕ) (t : ℝ≥0) (N : ℕ) :
    IsCompactOperator (M.heatTruncation k t N) := by
  let V := (M.heatTruncation k t N).range
  haveI : FiniteDimensional ℂ V := (heatTruncation_range M k t N).2
  let A : M.Sobolev k →L[ℂ] V :=
    (M.heatTruncation k t N).codRestrict V (fun x => ⟨x,rfl⟩)
  have hA : IsCompactOperator A := isCompactOperator_of_locallyCompactSpace_dom A
  exact hA.clm_comp V.subtypeL

private theorem heat_tail_tendsto (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun N : ℕ => Real.exp (-(t : ℝ) * ((N : ℝ) + 1))) atTop (𝓝 0) := by
  have ht' : (0 : ℝ) < (t : ℝ) := ht
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.exp_pos (-(t : ℝ))).le (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht'))
  have hlim := hpow.mul_const (Real.exp (-(t : ℝ)))
  convert hlim using 1
  · funext N
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  · simp

/-- Positive-time original heat is compact, with explicit original finite-rank approximants. -/
theorem heat_compact (k : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun N : ℕ => M.heatTruncation k t N) atTop (𝓝 (M.heat k t)) ∧
    IsCompactOperator (M.heat k t) := by
  have hlim : Tendsto (fun N : ℕ => M.heatTruncation k t N) atTop (𝓝 (M.heat k t)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsmall : ∀ᶠ N : ℕ in atTop,
        Real.exp (-(t : ℝ) * ((N : ℝ) + 1)) < ε := by
      simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        Metric.tendsto_nhds.mp (heat_tail_tendsto t ht) ε hε
    filter_upwards [hsmall] with N hN
    calc
      dist (M.heatTruncation k t N) (M.heat k t) =
          ‖M.heat k t - M.heatTruncation k t N‖ := by rw [dist_eq_norm, norm_sub_rev]
      _ ≤ Real.exp (-(t : ℝ) * ((N : ℝ) + 1)) := heat_tail_bound M k t N
      _ < ε := hN
  exact ⟨hlim, isCompactOperator_of_tendsto hlim
    (Eventually.of_forall (heatTruncation_compact M k t))⟩

/-- Original metric, grade/core and inclusion bridge together with the reused whole-space laws. -/
theorem original_heat :
    (∀ k t v, M.heat k t (M.embed k v) = M.embed k
      (∑ E ∈ stateEnergies M.D v,
        (Real.exp (-(t : ℝ) * (E : ℝ)) : ℂ) • gradeProjection M.D E v)) ∧
    (∀ k, M.heat k 0 = ContinuousLinearMap.id ℂ (M.Sobolev k)) ∧
    (∀ k s t, M.heat k (s+t) = (M.heat k s).comp (M.heat k t)) ∧
    (∀ k t x, ‖M.heat k t x‖ ≤ ‖x‖) ∧
    (∀ k t, ‖M.heat k t‖ ≤ 1) ∧
    (∀ k x, Continuous (fun t : ℝ≥0 => M.heat k t x)) ∧
    (∀ k t, (M.heat k t).IsPositive) ∧
    (∀ k E, E < 0 → ∀ x, M.projection k E x = 0) ∧
    (∀ k x, Tendsto (fun N : ℕ => M.truncation k (M.energyCutoff N) x) atTop (𝓝 x)) ∧
    (∀ k t, M.heat k t (M.embed k (vacuum M.D)) = M.embed k (vacuum M.D)) := by
  refine ⟨heat_embed M, heat_zero M, heat_add M, heat_norm M, ?_,
    heat_orbit_continuous M, heat_positive M, projection_negative M, cutoff_strong M, ?_⟩
  · intro k t
    exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (fun x => by simpa only [one_mul] using heat_norm M k t x)
  · intro k t
    have hv : vacuum M.D ∈ grade M.D 0 := by
      rw [grade_zero M.D M.positive]
      exact Submodule.subset_span (Set.mem_singleton _)
    simpa only [Int.cast_zero, mul_zero, Real.exp_zero, Complex.ofReal_one, one_smul] using
      heat_grade M k t 0 (vacuum M.D) hv

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing

/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/RankSeparation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/RankSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cardinal range-rank bounds reconstructed from completed Bargmann kernel sections. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.CoefficientOperator
import D5.S3.Analytic.Entire.SeparatedKernel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Completed Hilbert reconstruction gives the exact Cardinal rank/separation bridge. -/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal
open Filter Topology

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter DisplacementCovariance
open D5.S3.Analytic.Entire

/-- Finite pointwise separation bounds the actual Hilbert-space operator range. The supplied
factors need not belong to Bargmann Fock space: the proof works with spans of actual evaluation
sections, embeds them by the injective Bargmann map into the given finite function span, then
uses finite-dimensional closedness and totalness of the completed exponential family. -/
theorem coefficient_rank_le_of_separation (V : TwoMode) (k : ℕ)
    (g h : Fin k → (ℂ → ℂ))
    (hsep : ∀ z w, kernel V z w = ∑ i, g i z * h i w) :
    rangeRank (coefficientOperator V) ≤ (k : Cardinal) := by
  classical
  let C := coefficientOperator V
  let S : Submodule ℂ Fock := Submodule.span ℂ (Set.range (fun w => C (exponentialVector w)))
  let G : Submodule ℂ (ℂ → ℂ) := Submodule.span ℂ (Set.range g)
  have hm : S ≤ G.comap transformLinear := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    change transform (C (exponentialVector w)) ∈ G
    have heq : transform (C (exponentialVector w)) = ∑ i, h i w • g i := by
      funext z
      rw [← kernel_eq_coefficient_operator, hsep]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    rw [heq]
    exact G.sum_mem (fun i _ => G.smul_mem (h i w) (Submodule.subset_span ⟨i, rfl⟩))
  let L : S →ₗ[ℂ] G :=
    (transformLinear.comp S.subtype).codRestrict G (fun x => hm x.property)
  have hL : Function.Injective L := by
    intro x y heq
    apply Subtype.ext
    apply injective
    exact congrArg Subtype.val heq
  letI : FiniteDimensional ℂ G := FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  letI : FiniteDimensional ℂ S := FiniteDimensional.of_injective L hL
  have hclosed : IsClosed (S : Set Fock) := S.closed_of_finiteDimensional
  let P : Submodule ℂ Fock := S.comap C.toLinearMap
  have hpreclosed : IsClosed (P : Set Fock) := hclosed.preimage C.continuous
  have hdense : Submodule.span ℂ (Set.range exponentialVector) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact Submodule.subset_span ⟨w, rfl⟩
  have htop : (⊤ : Submodule ℂ Fock) ≤ P := by
    rw [← exponential_dense_span]
    exact Submodule.topologicalClosure_minimal _ hdense hpreclosed
  have hrange : LinearMap.range C.toLinearMap ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact htop (Submodule.mem_top)
  have hG : Module.rank ℂ G ≤ (k : Cardinal) := by
    calc
      Module.rank ℂ G ≤ Cardinal.mk (Set.range g) := rank_span_le _
      _ ≤ Cardinal.mk (Fin k) := Cardinal.mk_range_le
      _ = (k : Cardinal) := by simp
  exact (Submodule.rank_mono hrange).trans ((LinearMap.rank_le_of_injective L hL).trans hG)

theorem reduced_rank_le_of_separated (V : TwoMode) (k : ℕ)
    (hsep : SeparatedLE k (kernel V)) :
    rangeRank (purePartialTrace V) ≤ (k : Cardinal) := by
  obtain ⟨g, h, _, _, hsep⟩ := hsep
  have hC := coefficient_rank_le_of_separation V k g h hsep
  rw [pure_partial_trace_eq]
  apply le_trans (Submodule.rank_mono ?_) hC
  rintro _ ⟨x, rfl⟩
  exact ⟨star (coefficientOperator V) x, rfl⟩

theorem separated_succ {k : ℕ} {F : ℂ → ℂ → ℂ} (hF : SeparatedLE k F) :
    SeparatedLE (k + 1) F := by
  classical
  obtain ⟨g, h, hg, hh, hF⟩ := hF
  refine ⟨Fin.lastCases 0 g, Fin.lastCases 0 h, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      change Differentiable ℂ (fun _ : ℂ => (0 : ℂ))
      exact differentiable_const _
    · simpa only [Fin.lastCases_castSucc] using hg j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      change Differentiable ℂ (fun _ : ℂ => (0 : ℂ))
      exact differentiable_const _
    · simpa only [Fin.lastCases_castSucc] using hh j
  · intro z w
    rw [Fin.sum_univ_castSucc]
    simpa using hF z w

theorem separated_mono {m k : ℕ} {F : ℂ → ℂ → ℂ} (hmk : m ≤ k)
    (hF : SeparatedLE m F) : SeparatedLE k F := by
  induction k, hmk using Nat.le_induction with
  | base => exact hF
  | succ k _ ih => exact separated_succ ih

/-- The closures of the ranges of C and C C* agree without a finite-rank premise. -/
theorem closure_range_self_adjoint (C : Fock →L[ℂ] Fock) :
    (LinearMap.range (C * star C).toLinearMap).topologicalClosure =
      (LinearMap.range C.toLinearMap).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    ← Submodule.orthogonal_orthogonal_eq_closure]
  congr 1
  change (C ∘L ContinuousLinearMap.adjoint C).rangeᗮ = C.rangeᗮ
  rw [ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.orthogonal_range,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.ker_self_comp_adjoint]

/-- A finite actual reduced range reconstructs both separated families as transforms of
genuine Hilbert vectors. Finite dimension is established from cardinal rank before finrank
or a finite orthonormal basis is used. -/
theorem separated_of_reduced_rank_le (V : TwoMode) (k : ℕ)
    (hV : rangeRank (purePartialTrace V) ≤ (k : Cardinal)) :
    SeparatedLE k (kernel V) := by
  classical
  let C := coefficientOperator V
  let S := LinearMap.range (purePartialTrace V).toLinearMap
  have hfinite : Module.rank ℂ S < Cardinal.aleph0 :=
    lt_of_le_of_lt hV Cardinal.natCast_lt_aleph0
  letI : FiniteDimensional ℂ S := Module.rank_lt_aleph0_iff.mp hfinite
  have hSclosed : S.topologicalClosure = S :=
    S.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  have hclosure : (LinearMap.range C.toLinearMap).topologicalClosure = S := by
    rw [← closure_range_self_adjoint C]
    change (LinearMap.range
      (coefficientOperator V * star (coefficientOperator V)).toLinearMap).topologicalClosure = S
    rw [← pure_partial_trace_eq V]
    exact hSclosed
  have hrange : LinearMap.range C.toLinearMap ≤ S := by
    rw [← hclosure]
    exact (LinearMap.range C.toLinearMap).le_topologicalClosure
  let m := Module.finrank ℂ S
  let b : OrthonormalBasis (Fin m) ℂ S := stdOrthonormalBasis ℂ S
  let u : Fin m → Fock := fun i => (b i : Fock)
  let v : Fin m → Fock := fun i => star (ContinuousLinearMap.adjoint C (u i))
  have hsep : SeparatedLE m (kernel V) := by
    refine ⟨fun i => transform (u i), fun i => transform (v i),
      fun i => entire _, fun i => entire _, ?_⟩
    intro z w
    have hm : C (exponentialVector w) ∈ S := hrange ⟨_, rfl⟩
    have hb := congrArg (fun x : S => (x : Fock))
      (b.sum_repr' ⟨C (exponentialVector w), hm⟩)
    have hsum : ∑ i, inner ℂ (u i) (C (exponentialVector w)) • u i =
        C (exponentialVector w) := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner, u] using hb
    calc
      kernel V z w = transform (C (exponentialVector w)) z := kernel_eq_coefficient_operator V z w
      _ = transform (∑ i, inner ℂ (u i) (C (exponentialVector w)) • u i) z :=
        congrArg (fun a => transform a z) hsum.symm
      _ = ∑ i, inner ℂ (u i) (C (exponentialVector w)) * transform (u i) z := by
        simp only [transform, inner_sum, inner_smul_right]
      _ = ∑ i, transform (u i) z * transform (v i) w := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← ContinuousLinearMap.adjoint_inner_left,
          ← transform_star]
        exact mul_comm _ _
  have hmk : m ≤ k := by
    exact Module.finrank_le_of_rank_le hV
  exact separated_mono hmk hsep

/-- Exact completed-space rank/separation correspondence, with cardinal range rank and
arbitrary entire factors in the separation predicate. -/
theorem reduced_rank_le_iff_separated (V : TwoMode) (k : ℕ) :
    rangeRank (purePartialTrace V) ≤ (k : Cardinal) ↔ SeparatedLE k (kernel V) :=
  ⟨separated_of_reduced_rank_le V k, reduced_rank_le_of_separated V k⟩

#print axioms coefficient_rank_le_of_separation
#print axioms reduced_rank_le_of_separated
#print axioms separated_of_reduced_rank_le
#print axioms reduced_rank_le_iff_separated

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann

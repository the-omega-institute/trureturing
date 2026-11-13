/- GID: D5/S3/Quantum/Foundation/NativePSDModel
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/NativePSDModel
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The original entire EB3 regular-anchor family has a native qutrit inhabitant. -/

import D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
import D5.S3.Quantum.Foundation.HermitianExclusionBall
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Sqrt
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Unitary
import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Native PSD effects, entire exclusion faces and the full qutrit family. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix InnerProductSpace RealInnerProductSpace ComplexOrder

namespace D5.S3.Quantum.Foundation.NativePSDModel

open CircuitBalancedConfirmation FacetZeroGluing OrthogonalJointCompletion
open RegularAnchorContactCriterion SectionROGFrame
open D5.S3.Quantum.Measurement.FourQubitParentConstruction
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The entire PSD cone on the native Hermitian real carrier. -/
abbrev cone : PointedCone ℝ (HermitianMat d ℂ) :=
  HermitianExclusionKernel.cone

/-- The real trace unit. -/
abbrev unit : HermitianMat d ℂ →ₗ[ℝ] ℝ := HermitianExclusionKernel.unit

/-- The real trace pairing, defined on the entire original carrier. -/
def effect (E : HermitianMat d ℂ) : HermitianMat d ℂ →ₗ[ℝ] ℝ :=
  HermitianMat.innerₗ E

private theorem unit_apply (X : HermitianMat d ℂ) : unit X = X.trace :=
  rfl

private theorem effect_apply (E X : HermitianMat d ℂ) : effect E X = ⟪E, X⟫ := rfl

private theorem effect_surjective : Function.Surjective (effect (d := d)) := by
  intro f
  refine ⟨(InnerProductSpace.toDual ℝ (HermitianMat d ℂ)).symm
    f.toContinuousLinearMap, ?_⟩
  ext X
  change ⟪(InnerProductSpace.toDual ℝ (HermitianMat d ℂ)).symm
    f.toContinuousLinearMap, X⟫_ℝ = f X
  exact InnerProductSpace.toDual_symm_apply

private theorem proper_iff (E : HermitianMat d ℂ) :
    proper cone unit (effect E) ↔ 0 ≤ E ∧ E ≤ 1 := by
  constructor
  · intro h
    refine ⟨(HermitianMat.nonneg_iff_inner_nonneg E).2 (fun X hX => (h X hX).1), ?_⟩
    apply sub_nonneg.mp
    apply (HermitianMat.nonneg_iff_inner_nonneg (1 - E)).2
    intro X hX
    have hh := (h X hX).2
    simpa [effect_apply, unit_apply, inner_sub_left, HermitianMat.one_inner]
      using sub_nonneg.mpr hh
  · rintro ⟨hE, hI⟩ X hX
    refine ⟨HermitianMat.inner_ge_zero hE hX, ?_⟩
    simpa [effect_apply, unit_apply, HermitianMat.one_inner] using
      HermitianMat.inner_mono' hX hI

private theorem base_iff (X : HermitianMat d ℂ) :
    X ∈ CircuitBalancedConfirmation.base cone unit ↔ 0 ≤ X ∧ X.trace = 1 := by
  simp only [CircuitBalancedConfirmation.base, Set.mem_ofPred_eq,
    PointedCone.mem_positive, unit_apply]

private theorem rank_one_confirms (v : EuclideanSpace ℂ d) (hv : ‖v‖ = 1) :
    confirms cone unit (rankOne v) (effect (rankOne v)) := by
  refine ⟨(proper_iff _).2 ⟨rankOne_nonneg v, ?_⟩, rankOne_self v hv⟩
  have h := HermitianMat.le_trace_smul_one (rankOne_nonneg (v : d → ℂ))
  simpa only [rankOne_trace_norm, hv, one_pow, one_smul] using h

/-- Every mixed exclusion of a native unit rank one point is precisely the
whole normalized PSD face with zero pairing against that projection. -/
theorem whole_mixed_exclusion (v : EuclideanSpace ℂ d) (hv : ‖v‖ = 1) :
    exclusion cone unit (rankOne v) =
      {X : HermitianMat d ℂ | 0 ≤ X ∧ X.trace = 1 ∧ ⟪rankOne v, X⟫_ℝ = 0} := by
  ext X
  rw [HermitianExclusionKernel.exclusion_iff_kernel v hv X]
  constructor
  · rintro ⟨hX, ht, hk⟩
    refine ⟨hX, ht, ?_⟩
    apply RCLike.ofReal_injective (K := ℂ)
    rw [real_inner_comm, pair_rankOne (𝕜 := ℂ) X (v : d → ℂ), hk]
    simp
  · rintro ⟨hX, ht, hz⟩
    refine ⟨hX, ht, ?_⟩
    apply (HermitianMat.zero_le_iff.mp hX).dotProduct_mulVec_zero_iff.mp
    rw [← pair_rankOne (𝕜 := ℂ) X (v : d → ℂ), real_inner_comm, hz]
    simp

private theorem complement_state (v : EuclideanSpace ℂ d) (hv : ‖v‖ = 1)
    (hd : 1 < Fintype.card d) :
    ((Fintype.card d : ℝ) - 1)⁻¹ • (1 - rankOne v) ∈ exclusion cone unit (rankOne v) := by
  have ht : (rankOne v).trace = 1 := by rw [rankOne_trace_norm, hv, one_pow]
  have hp := (proper_iff _).mp (rank_one_confirms v hv).1
  have hdim : 0 < (Fintype.card d : ℝ) - 1 := by
    have hh : (1 : ℝ) < Fintype.card d := by exact_mod_cast hd
    linarith
  rw [whole_mixed_exclusion v hv]
  refine ⟨smul_nonneg (inv_nonneg.mpr hdim.le) (sub_nonneg.mpr hp.2), ?_, ?_⟩
  · rw [HermitianMat.trace_smul, HermitianMat.trace_sub, HermitianMat.trace_one, ht,
      inv_mul_cancel₀ hdim.ne']
  · rw [real_inner_smul_right, inner_sub_right, HermitianMat.inner_one, ht,
      rankOne_self v hv]
    ring

/-- Common effects are unique in the entire real linear dual, in every native
matrix dimension at least two. -/
theorem whole_common_unique (v : EuclideanSpace ℂ d) (hv : ‖v‖ = 1)
    (hd : 1 < Fintype.card d) (f : HermitianMat d ℂ →ₗ[ℝ] ℝ) :
    common cone unit (rankOne v) f ↔ f = effect (rankOne v) := by
  constructor
  · intro hf
    obtain ⟨E, rfl⟩ := effect_surjective f
    obtain ⟨hE, hI⟩ := (proper_iff E).mp hf.1.1
    have hz := hf.2 _ (complement_state v hv hd)
    have hdim : ((Fintype.card d : ℝ) - 1) ≠ 0 := by
      have hh : (1 : ℝ) < Fintype.card d := by exact_mod_cast hd
      linarith
    change ⟪E, ((Fintype.card d : ℝ) - 1)⁻¹ • (1 - rankOne v)⟫_ℝ = 0 at hz
    have hconf : ⟪E, rankOne v⟫_ℝ = 1 := hf.1.2
    rw [real_inner_smul_right, inner_sub_right, HermitianMat.inner_one, hconf,
      mul_eq_zero] at hz
    have ht : E.trace = 1 := sub_eq_zero.mp (hz.resolve_left (inv_ne_zero hdim))
    exact congrArg effect (pairing_one_unique v hv E hE ht
      (by rw [real_inner_comm]; exact hconf))
  · rintro rfl
    refine ⟨rank_one_confirms v hv, ?_⟩
    intro X hX
    exact ((Set.ext_iff.mp (whole_mixed_exclusion v hv)) X).mp hX |>.2.2

private theorem top_rog : ROG (⊤ : Submodule ℝ (HermitianMat d ℂ)) := by
  classical
  intro X _ hX
  let w : d → EuclideanSpace ℂ d := fun j => WithLp.toLp 2 (fun i => X.sqrt.mat i j)
  have hsum : (∑ j : d, rankOne (w j)) = X := by
    apply HermitianMat.ext
    rw [HermitianMat.mat_finset_sum, ← HermitianMat.sqrt_sq hX]
    ext i k
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    change (∑ j : d, X.sqrt.mat i j * star (X.sqrt.mat k j)) =
      ∑ j : d, X.sqrt.mat i j * X.sqrt.mat j k
    apply Finset.sum_congr rfl
    intro j _
    rw [← Matrix.conjTranspose_apply, X.sqrt.H.eq]
  let s : Finset d := Finset.univ.filter fun j => w j ≠ 0
  let m := Fintype.card s
  let e : s ≃ Fin m := Fintype.equivFin s
  refine ⟨m, (fun i => w (e.symm i)), (fun i => ⟨?_, Submodule.mem_top⟩), ?_⟩
  · exact (Finset.mem_filter.mp (e.symm i).property).2
  · have hf : (∑ j ∈ s, rankOne (w j)) = ∑ j : d, rankOne (w j) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hz : w j = 0 := by simpa only [s, Finset.mem_filter, Finset.mem_univ,
        true_and, not_not] using hj
      rw [hz]
      apply HermitianMat.ext
      change Matrix.vecMulVec (0 : d → ℂ) (star (0 : d → ℂ)) = 0
      simp
    calc
      X = ∑ j ∈ s, rankOne (w j) := hsum.symm.trans hf.symm
      _ = ∑ j : s, rankOne (w j) := (Finset.sum_attach s _).symm
      _ = ∑ i : Fin m, rankOne (w (e.symm i)) :=
        Fintype.sum_equiv e _ _ (fun j => by simp)

/-- Every original extreme point is a normalized native rank one matrix, and
every such matrix is an original extreme point of the entire normalized base. -/
theorem native_pure_iff (X : HermitianMat d ℂ) :
    X ∈ pure cone unit ↔
      ∃ v : EuclideanSpace ℂ d, ‖v‖ = 1 ∧ rankOne v = X := by
  have hb : CircuitBalancedConfirmation.base cone (unit (d := d)) =
      SectionROGFrame.base ⊤ := by
    ext Y
    simp only [base_iff, SectionROGFrame.base, Set.mem_ofPred_eq,
      Submodule.mem_top, true_and]
  change X ∈ (CircuitBalancedConfirmation.base cone unit).extremePoints ℝ ↔ _
  rw [hb, whole_pure_carrier _ top_rog]
  simp only [pureRanks, Set.mem_ofPred_eq, Submodule.mem_top, and_true]

/-- The entire original mixed exclusion identifies every native pure label. -/
theorem native_exclusion_injective (hd : 1 < Fintype.card d) :
    Function.Injective (fun p : pure (cone (d := d)) unit =>
      exclusion cone unit (p : HermitianMat d ℂ)) := by
  intro p q hpq
  change exclusion cone unit (p : HermitianMat d ℂ) =
    exclusion cone unit (q : HermitianMat d ℂ) at hpq
  obtain ⟨v, hv, hp⟩ := (native_pure_iff (p : HermitianMat d ℂ)).mp p.property
  obtain ⟨w, hw, hq⟩ := (native_pure_iff (q : HermitianMat d ℂ)).mp q.property
  let t : ℝ := (Fintype.card d : ℝ) - 1
  have ht : t ≠ 0 := by
    have hcard : (1 : ℝ) < Fintype.card d := by exact_mod_cast hd
    dsimp [t]
    linarith
  have hmem : t⁻¹ • (1 - rankOne v) ∈ exclusion cone unit (rankOne w) := by
    rw [hq, ← hpq, ← hp]
    exact complement_state v hv hd
  rw [whole_mixed_exclusion w hw] at hmem
  have hz := hmem.2.2
  rw [real_inner_smul_right, inner_sub_right, HermitianMat.inner_one,
    rankOne_trace_norm, hw, one_pow, mul_eq_zero] at hz
  have hpair : ⟪rankOne w, rankOne v⟫_ℝ = 1 :=
    (sub_eq_zero.mp (hz.resolve_left (inv_ne_zero ht))).symm
  have heq : rankOne w = rankOne v :=
    pairing_one_unique v hv (rankOne w) (rankOne_nonneg w)
      (by rw [rankOne_trace_norm, hw, one_pow])
      (by rw [real_inner_comm]; exact hpair)
  apply Subtype.ext
  rw [← hp, ← hq]
  exact heq.symm


def vzero : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![1, 0, 0]

theorem vzero_unit : ‖vzero‖ = 1 := by
  simp [vzero, EuclideanSpace.norm_eq, Fin.sum_univ_three]

theorem native_EB3 : EB3 (cone (d := Fin 3)) unit := by
  intro p
  obtain ⟨⟨d, hd, param, hinj, hwhole⟩, rfl⟩ :=
    HermitianExclusionBall.all_pure_charts p
  exact ⟨⟨param, hinj, hwhole⟩⟩

noncomputable def anchorChart : FullBall3Chart (cone (d := Fin 3)) unit (rankOne vzero) :=
  (native_EB3 ⟨rankOne vzero, (native_pure_iff _).mpr ⟨vzero, vzero_unit, rfl⟩⟩).some

/-- A concrete inhabitant of the complete original telescope, together with its
application to the original contact criterion. All effects and pure labels keep
their original full domains. -/
theorem original_family_inhabited :
    ∃ (p : pure (cone (d := Fin 3)) unit)
      (e : HermitianMat (Fin 3) ℂ →ₗ[ℝ] ℝ)
      (a : FullBall3Chart (cone (d := Fin 3)) unit (p : HermitianMat (Fin 3) ℂ)),
      IsClosed (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) ∧
      (∀ X ∈ cone (d := Fin 3), X ≠ 0 → 0 < unit X) ∧
      Submodule.span ℝ (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) = ⊤ ∧
      EB3 (cone (d := Fin 3)) unit ∧
      Function.Injective (fun q : pure (cone (d := Fin 3)) unit =>
        exclusion cone unit (q : HermitianMat (Fin 3) ℂ)) ∧
      common (cone (d := Fin 3)) unit (p : HermitianMat (Fin 3) ℂ) e ∧
      Regular (cone (d := Fin 3)) unit (p : HermitianMat (Fin 3) ℂ) ∧
      ∃ n : NativeChart (cone (d := Fin 3)) unit p e a, ContactCriterion n := by
  let p : pure (cone (d := Fin 3)) unit :=
    ⟨rankOne vzero, (native_pure_iff _).mpr ⟨vzero, vzero_unit, rfl⟩⟩
  let e := effect (rankOne vzero)
  have hc : IsClosed (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) :=
    HermitianMat.isClosed_nonneg
  have hs : ∀ X ∈ cone (d := Fin 3), X ≠ 0 → 0 < unit X := by
    intro X hX hne
    change 0 < X.trace
    exact HermitianMat.trace_pos (lt_of_le_of_ne hX (Ne.symm hne))
  have hg : Submodule.span ℝ (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) = ⊤ := by
    apply top_unique
    intro X _
    rw [← HermitianMat.posPart_add_negPart X]
    exact Submodule.sub_mem _
      (Submodule.subset_span (HermitianMat.posPart_nonneg X))
      (Submodule.subset_span (HermitianMat.negPart_nonneg X))
  have hinj := native_exclusion_injective (d := Fin 3) (by decide)
  have he : common (cone (d := Fin 3)) unit (p : HermitianMat (Fin 3) ℂ) e :=
    (whole_common_unique vzero vzero_unit (by decide) e).mpr rfl
  have hreg : Regular (cone (d := Fin 3)) unit (p : HermitianMat (Fin 3) ℂ) := by
    refine ⟨e, he, ?_⟩
    intro f hf
    exact (whole_common_unique vzero vzero_unit (by decide) f).mp hf
  exact ⟨p, e, anchorChart, hc, hs, hg, native_EB3, hinj, he, hreg,
    regular_anchor_contact_criterion hc hs hg native_EB3 hinj p e he hreg anchorChart⟩


#print axioms whole_mixed_exclusion
#print axioms whole_common_unique
#print axioms native_pure_iff
#print axioms native_exclusion_injective
#print axioms native_EB3
#print axioms original_family_inhabited

end D5.S3.Quantum.Foundation.NativePSDModel

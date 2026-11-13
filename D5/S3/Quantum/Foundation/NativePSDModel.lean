/- GID: D5/S3/Quantum/Foundation/NativePSDModel
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/NativePSDModel
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The original entire EB3 regular-anchor family has a native qutrit inhabitant. -/

import D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
import D5.S3.Quantum.Foundation.SectionROGFrame
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Sqrt
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Unitary
import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open scoped BigOperators Matrix InnerProductSpace RealInnerProductSpace ComplexOrder

namespace D5.S3.Quantum.Foundation.NativePSDModel

open CircuitBalancedConfirmation FacetZeroGluing OrthogonalJointCompletion
open RegularAnchorNormalChart RegularAnchorContactCriterion SectionROGFrame
open D5.S3.Quantum.Measurement.FourQubitParentConstruction
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The entire PSD cone on the native Hermitian real carrier. -/
abbrev cone : PointedCone ℝ (HermitianMat d ℂ) :=
  PointedCone.positive ℝ (HermitianMat d ℂ)

/-- The real trace unit. -/
def unit : HermitianMat d ℂ →ₗ[ℝ] ℝ := HermitianMat.innerₗ 1

/-- The real trace pairing, defined on the entire original carrier. -/
def effect (E : HermitianMat d ℂ) : HermitianMat d ℂ →ₗ[ℝ] ℝ :=
  HermitianMat.innerₗ E

private theorem unit_apply (X : HermitianMat d ℂ) : unit X = X.trace :=
  HermitianMat.one_inner X

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
  simp only [CircuitBalancedConfirmation.base, Set.mem_setOf_eq,
    PointedCone.mem_positive, unit_apply]

private theorem rank_one_self (v : EuclideanSpace ℂ d) (hv : ‖v‖ = 1) :
    (rankOne v).mat * (rankOne v).mat = (rankOne v).mat := by
  change Matrix.vecMulVec (v : d → ℂ) (star (v : d → ℂ)) *
    Matrix.vecMulVec (v : d → ℂ) (star (v : d → ℂ)) = _
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hn : star v.ofLp ⬝ᵥ v.ofLp = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [hv]
  rw [hn, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A confirming positive contraction dominates the confirmed unit projection.
The proof constructs its positive complementary block on the same carrier. -/
theorem confirming_dominates (v : EuclideanSpace ℂ d) (hv : ‖v‖ = 1)
    (E : HermitianMat d ℂ) (hE : 0 ≤ E) (hI : E ≤ 1)
    (hconfirm : ⟪E, rankOne v⟫ = 1) : rankOne v ≤ E := by
  let P := rankOne v
  have hPtr : P.trace = 1 := by
    dsimp [P]
    rw [rankOne_trace_norm, hv]
    norm_num
  have hzero : ⟪1 - E, P⟫_ℝ = 0 := by
    rw [inner_sub_left, HermitianMat.one_inner, hPtr, hconfirm]
    ring
  have hmul : (1 - E).mat * P.mat = 0 := by
    have hz : P.support ≤ (1 - E).ker :=
      (HermitianMat.inner_zero_iff (rankOne_nonneg v) (sub_nonneg.mpr hI)).mp
        (by rw [real_inner_comm]; exact hzero)
    change LinearMap.range (Matrix.toEuclideanLin P.mat) ≤
      LinearMap.ker (Matrix.toEuclideanLin (1 - E).mat) at hz
    have hh := LinearMap.range_le_ker_iff.mp hz
    apply Matrix.toEuclideanLin.injective
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, map_zero] using hh
  have hEP : E.mat * P.mat = P.mat := by
    exact (sub_eq_zero.mp (by simpa only [HermitianMat.mat_sub, Matrix.sub_mul,
      HermitianMat.mat_one, Matrix.one_mul] using hmul)).symm
  have hPE : P.mat * E.mat = P.mat := by
    have hh := congrArg Matrix.conjTranspose hEP
    simpa [Matrix.conjTranspose_mul] using hh
  have hblock : E.conj (1 - P.mat) = E - P := by
    apply HermitianMat.ext
    change (1 - P.mat) * E.mat * (1 - P.mat).conjTranspose = E.mat - P.mat
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, P.H.eq,
      Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      hPE, hEP, show P.mat * P.mat = P.mat from rank_one_self v hv]
    abel
  have hp := HermitianMat.conj_nonneg (M := 1 - P.mat) hE
  rw [hblock] at hp
  exact sub_nonneg.mp hp

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
  constructor
  · rintro ⟨hX, f, hf, hfX⟩
    obtain ⟨E, rfl⟩ := effect_surjective f
    obtain ⟨hE, hI⟩ := (proper_iff E).mp hf.1
    have hdom := confirming_dominates v hv E hE hI hf.2
    have hx := (base_iff X).mp hX
    refine ⟨hx.1, hx.2, le_antisymm ?_ (HermitianMat.inner_ge_zero (rankOne_nonneg v) hx.1)⟩
    exact (HermitianMat.inner_mono' hx.1 hdom).trans_eq hfX
  · rintro ⟨hX, ht, hz⟩
    exact ⟨(base_iff X).mpr ⟨hX, ht⟩, effect (rankOne v), rank_one_confirms v hv, hz⟩

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
    simp only [base_iff, SectionROGFrame.base, Set.mem_setOf_eq,
      Submodule.mem_top, true_and]
  change X ∈ (CircuitBalancedConfirmation.base cone unit).extremePoints ℝ ↔ _
  rw [hb, whole_pure_carrier _ top_rog]
  simp only [pureRanks, Set.mem_setOf_eq, Submodule.mem_top, and_true]

/-- The entire original mixed exclusion identifies every native pure label. -/
theorem native_exclusion_injective (hd : 1 < Fintype.card d) :
    Function.Injective (fun p : pure (cone (d := d)) unit => exclusion cone unit p) := by
  intro p q hpq
  obtain ⟨v, hv, hp⟩ := (native_pure_iff p).mp p.property
  obtain ⟨w, hw, hq⟩ := (native_pure_iff q).mp q.property
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


private def blochLinear : ThreeSpace →ₗ[ℝ] HermitianMat (Fin 2) ℂ where
  toFun r := ⟨B r, by simpa only [scalarB, Complex.ofReal_zero, zero_smul, zero_add]
    using scalarB_hermitian 0 r⟩
  map_add' a b := by
    apply HermitianMat.ext
    change B (a + b) = B a + B b
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      using B_sum Finset.univ ![a, b]
  map_smul' c a := by
    apply HermitianMat.ext
    exact B_real_smul c a

private def beta : ThreeSpace →ᵃ[ℝ] HermitianMat (Fin 2) ℂ :=
  ((1 / 2 : ℝ) • blochLinear).toAffineMap +
    AffineMap.const ℝ ThreeSpace ((1 / 2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ))

private theorem beta_mat (r : ThreeSpace) : (beta r).mat = blochMatrix 1 r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [beta, blochLinear, B_formula, blochMatrix, HermitianMat.smul_apply,
      Complex.real_smul, Matrix.one_apply] <;> ring

private theorem beta_trace (r : ThreeSpace) : (beta r).trace = 1 := by
  rw [HermitianMat.trace_eq_re_trace, beta_mat, blochMatrix_trace]
  norm_num

private theorem beta_positive (r : ThreeSpace) : 0 ≤ beta r ↔ ‖r‖ ≤ 1 := by
  rw [HermitianMat.zero_le_iff]
  have hm : (beta r).mat = (1 / 2 : ℂ) • scalarB 1 r := by
    rw [beta_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blochMatrix, scalarB, B_formula] <;> ring
  rw [hm]
  exact half_scalarB_posSemidef_iff 1 r

private theorem beta_inverse (X : HermitianMat (Fin 2) ℂ) (ht : X.trace = 1) :
    beta (bloch X.mat) = X := by
  apply HermitianMat.ext
  rw [beta_mat]
  have h := (bloch_geometry_of_isHermitian X.mat X.H).1
  rw [← HermitianMat.trace_eq_re_trace, ht] at h
  exact h.symm

private theorem beta_injective : Function.Injective beta := by
  intro r s h
  have hh := congrArg (fun X : HermitianMat (Fin 2) ℂ => bloch X.mat) h
  simpa only [beta_mat, bloch_blochMatrix] using hh

private def W : Matrix (Fin 3) (Fin 2) ℂ := !![0, 0; 1, 0; 0, 1]

private theorem W_isometry : W.conjTranspose * W = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W, Matrix.mul_apply, Fin.sum_univ_three]

private def compress (X : HermitianMat (Fin 3) ℂ) : HermitianMat (Fin 2) ℂ :=
  X.conj W.conjTranspose

private theorem compress_embed (X : HermitianMat (Fin 2) ℂ) :
    compress (X.conj W) = X := by
  rw [compress, HermitianMat.conj_conj, W_isometry, HermitianMat.conj_one]

private theorem embed_trace (X : HermitianMat (Fin 2) ℂ) :
    (X.conj W).trace = X.trace := by
  rw [HermitianMat.trace_eq_re_trace, HermitianMat.conj_apply_mat,
    Matrix.trace_mul_cycle, W_isometry, Matrix.one_mul,
    ← HermitianMat.trace_eq_re_trace]

def vzero : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![1, 0, 0]

theorem vzero_unit : ‖vzero‖ = 1 := by
  simp [vzero, EuclideanSpace.norm_eq, Fin.sum_univ_three]

private theorem anchor_reading (X : HermitianMat (Fin 3) ℂ) :
    ⟪rankOne vzero, X⟫_ℝ = (X.mat 0 0).re := by
  simp [HermitianMat.inner_eq_re_trace, rankOne, vzero, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMulVec_apply]

private theorem embed_zero (X : HermitianMat (Fin 2) ℂ) :
    ⟪rankOne vzero, X.conj W⟫_ℝ = 0 := by
  rw [anchor_reading]
  simp [HermitianMat.conj_apply_mat, W, Matrix.mul_apply, Fin.sum_univ_two]

private theorem reconstruct (X : HermitianMat (Fin 3) ℂ) (hX : 0 ≤ X)
    (hz : ⟪rankOne vzero, X⟫_ℝ = 0) : (compress X).conj W = X := by
  have h00 : X.mat 0 0 = 0 := by
    apply Complex.ext
    · exact (anchor_reading X).symm.trans hz
    · exact X.complex_im_eq_zero 0
  have hquad : star vzero.ofLp ⬝ᵥ (X.mat *ᵥ vzero.ofLp) = 0 := by
    simpa [vzero, dotProduct, Matrix.mulVec, Fin.sum_univ_three] using h00
  have hcol := (HermitianMat.zero_le_iff.mp hX).dotProduct_mulVec_zero_iff.mp hquad
  have hc (i : Fin 3) : X.mat i 0 = 0 := by
    simpa [vzero, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hcol i
  have hr (j : Fin 3) : X.mat 0 j = 0 := by
    rw [← X.H.eq]
    simp [Matrix.conjTranspose_apply, hc]
  apply HermitianMat.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compress, HermitianMat.conj_apply_mat, W, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, hc, hr]

/-- The chart is affine and injective on the whole three-space, and its closed
unit ball is exactly the entire original mixed exclusion of the first projection. -/
def anchorChart : FullBall3Chart (cone (d := Fin 3)) unit (rankOne vzero) where
  param := (HermitianMat.conjLinear ℝ W).toAffineMap.comp beta
  injective := by
    intro r s h
    apply beta_injective
    have hh := congrArg compress h
    simpa only [AffineMap.comp_apply, LinearMap.toAffineMap_coe,
      HermitianMat.conjLinear_apply, compress_embed] using hh
  whole := by
    ext X
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [whole_mixed_exclusion vzero vzero_unit]
      change 0 ≤ (beta r).conj W ∧ ((beta r).conj W).trace = 1 ∧ _
      refine ⟨HermitianMat.conj_nonneg ((beta_positive r).mpr ?_), ?_, embed_zero _⟩
      · simpa using hr
      · rw [embed_trace, beta_trace]
    · intro hX
      rw [whole_mixed_exclusion vzero vzero_unit] at hX
      have hpos : 0 ≤ compress X := HermitianMat.conj_nonneg hX.1
      have hre := reconstruct X hX.1 hX.2.2
      have ht : (compress X).trace = 1 := by
        rw [← embed_trace (compress X), hre]
        exact hX.2.1
      refine ⟨bloch (compress X).mat, ?_, ?_⟩
      · have hn := norm_bloch_le_trace_of_posSemidef (compress X).mat
          (HermitianMat.zero_le_iff.mp hpos)
        rw [← HermitianMat.trace_eq_re_trace, ht] at hn
        simpa using hn
      · change (beta (bloch (compress X).mat)).conj W = X
        rw [beta_inverse _ ht, hre]

private theorem unitary_to (v : EuclideanSpace ℂ (Fin 3)) (hv : ‖v‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin 3) ℂ,
      (rankOne vzero).conj U.val = rankOne v := by
  have hsingle : Orthonormal ℂ (({0} : Set (Fin 3)).domRestrict
      (fun _ : Fin 3 => v)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [hv]
  obtain ⟨b, hb⟩ := hsingle.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let a := EuclideanSpace.basisFun (Fin 3) ℂ
  let U : Matrix.unitaryGroup (Fin 3) ℂ :=
    ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b⟩
  refine ⟨U, ?_⟩
  have hcol (i : Fin 3) : U.val i 0 = v i := by
    change a.toBasis.repr (b 0) i = v i
    rw [hb 0 (Set.mem_singleton 0)]
    rfl
  apply HermitianMat.ext
  ext i j
  simp [HermitianMat.conj_apply_mat, rankOne, vzero, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.vecMulVec_apply, hcol]

private theorem undo_conj (X : HermitianMat (Fin 3) ℂ)
    (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    (X.conj U.val).conj (star U).val = X := by
  rw [HermitianMat.conj_conj]
  have h : (star U).val * U.val = 1 := U.property.1
  rw [h, HermitianMat.conj_one]

/-- Every original pure qutrit label has a full three-ball chart of its entire
mixed exclusion, with an affine parameterization injective on all three-space. -/
theorem native_EB3 : EB3 (cone (d := Fin 3)) unit := by
  intro p
  obtain ⟨v, hv, hp⟩ := (native_pure_iff p).mp p.property
  obtain ⟨U, hU⟩ := unitary_to v hv
  refine ⟨{
    param := (HermitianMat.conjLinear ℝ U.val).toAffineMap.comp anchorChart.param
    injective := ?_
    whole := ?_ }⟩
  · intro r s h
    apply anchorChart.injective
    have hh := congrArg (fun X : HermitianMat (Fin 3) ℂ => X.conj (star U).val) h
    simpa only [AffineMap.comp_apply, LinearMap.toAffineMap_coe,
      HermitianMat.conjLinear_apply, undo_conj] using hh
  · ext X
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hx : anchorChart.param r ∈ exclusion cone unit (rankOne vzero) :=
        anchorChart.whole ▸ Set.mem_image_of_mem _ hr
      rw [whole_mixed_exclusion vzero vzero_unit] at hx
      rw [← hp, whole_mixed_exclusion v hv]
      change 0 ≤ (anchorChart.param r).conj U.val ∧
        ((anchorChart.param r).conj U.val).trace = 1 ∧ _
      refine ⟨HermitianMat.conj_nonneg hx.1,
        (HermitianMat.trace_conj_unitary _ U).trans hx.2.1, ?_⟩
      rw [← hU, HermitianMat.inner_conj_unitary]
      exact hx.2.2
    · intro hX
      rw [← hp, whole_mixed_exclusion v hv] at hX
      have hy : X.conj (star U).val ∈ exclusion cone unit (rankOne vzero) := by
        rw [whole_mixed_exclusion vzero vzero_unit]
        refine ⟨HermitianMat.conj_nonneg hX.1,
          (HermitianMat.trace_conj_unitary _ (star U)).trans hX.2.1, ?_⟩
        have heq : (rankOne v).conj (star U).val = rankOne vzero := by
          rw [← hU, undo_conj]
        rw [← heq, HermitianMat.inner_conj_unitary]
        exact hX.2.2
      obtain ⟨r, hr, hre⟩ := anchorChart.whole.symm ▸ hy
      refine ⟨r, hr, ?_⟩
      change (anchorChart.param r).conj U.val = X
      rw [hre]
      exact undo_conj X (star U)

/-- A concrete inhabitant of the complete original telescope, together with its
application to the original contact criterion. All effects and pure labels keep
their original full domains. -/
theorem original_family_inhabited :
    ∃ (p : pure (cone (d := Fin 3)) unit)
      (e : HermitianMat (Fin 3) ℂ →ₗ[ℝ] ℝ)
      (a : FullBall3Chart cone unit p),
      IsClosed (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) ∧
      (∀ X ∈ cone (d := Fin 3), X ≠ 0 → 0 < unit X) ∧
      Submodule.span ℝ (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) = ⊤ ∧
      EB3 (cone (d := Fin 3)) unit ∧
      Function.Injective (fun q : pure (cone (d := Fin 3)) unit => exclusion cone unit q) ∧
      common cone unit p e ∧ Regular cone unit p ∧
      ∃ n : NativeChart cone unit p e a, ContactCriterion n := by
  let p : pure (cone (d := Fin 3)) unit :=
    ⟨rankOne vzero, (native_pure_iff _).mpr ⟨vzero, vzero_unit, rfl⟩⟩
  let e := effect (rankOne vzero)
  have hc : IsClosed (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) :=
    HermitianMat.isClosed_nonneg
  have hs : ∀ X ∈ cone (d := Fin 3), X ≠ 0 → 0 < unit X := by
    intro X hX hne
    change 0 < ⟪(1 : HermitianMat (Fin 3) ℂ), X⟫_ℝ
    rw [HermitianMat.one_inner]
    exact HermitianMat.trace_pos (lt_of_le_of_ne hX (Ne.symm hne))
  have hg : Submodule.span ℝ (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) = ⊤ := by
    apply top_unique
    intro X _
    rw [← HermitianMat.posPart_add_negPart X]
    exact Submodule.sub_mem _
      (Submodule.subset_span (HermitianMat.posPart_nonneg X))
      (Submodule.subset_span (HermitianMat.negPart_nonneg X))
  have hinj := native_exclusion_injective (d := Fin 3) (by decide)
  have he : common cone unit p e :=
    (whole_common_unique vzero vzero_unit (by decide) e).mpr rfl
  have hreg : Regular cone unit p := by
    refine ⟨e, he, ?_⟩
    intro f hf
    exact (whole_common_unique vzero vzero_unit (by decide) f).mp hf
  exact ⟨p, e, anchorChart, hc, hs, hg, native_EB3, hinj, he, hreg,
    regular_anchor_contact_criterion hc hs hg native_EB3 hinj p e he hreg anchorChart⟩


#print axioms confirming_dominates
#print axioms whole_mixed_exclusion
#print axioms whole_common_unique
#print axioms native_pure_iff
#print axioms native_exclusion_injective
#print axioms native_EB3
#print axioms original_family_inhabited

end D5.S3.Quantum.Foundation.NativePSDModel

/- GID: D5/S3/HomologicalAlgebra/FiniteIncidenceGreen
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FiniteIncidenceGreen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Incidence support propagation and Green series repair in finite dimensions. -/

import D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Green series for a finite incidence matrix

A nonzero matrix entry is an adjacency between a face and an edge. The
two-step face balls and the one-step edge extension record all possible
support of the Green series terms. The norm estimate uses contraction on
the image of the edge-to-face operator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Filter
open scoped BigOperators Topology

namespace D5.S3.HomologicalAlgebra.FiniteIncidenceGreen

variable {F E : Type*} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]

/-- The faces within (2j) incidence steps of the initial face. Each round
keeps the current faces and crosses from them through a common edge. -/
def faceBall (A : Matrix F E ℝ) (f : F) : ℕ → Set F
  | 0 => {f}
  | j + 1 => {g | g ∈ faceBall A f j ∨
      ∃ h ∈ faceBall A f j, ∃ e, A h e ≠ 0 ∧ A g e ≠ 0}

/-- The edges within (2j+1) incidence steps of the initial face. -/
noncomputable def edgeBall (A : Matrix F E ℝ) (f : F) (j : ℕ) : Finset E := by
  classical
  exact Finset.univ.filter fun e => ∃ g ∈ faceBall A f j, A g e ≠ 0

/-- The matrix as a bounded operator in the simplex bases. -/
noncomputable def incidence (A : Matrix F E ℝ) :
    EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ F :=
  A.toEuclideanLin.toContinuousLinearMap

private theorem incidence_apply (A : Matrix F E ℝ) (x : EuclideanSpace ℝ E) (f : F) :
    incidence A x f = ∑ e, A f e * x e := by
  change (A.toEuclideanLin x) f = _
  rw [Matrix.toLpLin_apply]
  rfl

private theorem incidence_transpose_eq_adjoint (A : Matrix F E ℝ) :
    incidence Aᵀ = (incidence A).adjoint := by
  rw [incidence, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  rfl

/-- One Neumann step for the face Laplacian. -/
noncomputable def residual (A : Matrix F E ℝ) (M : ℝ) :
    EuclideanSpace ℝ F →L[ℝ] EuclideanSpace ℝ F :=
  1 - (M ^ 2)⁻¹ • ((incidence A).comp (incidence Aᵀ))

/-- The face unit vector in the Euclidean coordinate space. -/
noncomputable def faceUnit (f : F) : EuclideanSpace ℝ F :=
  EuclideanSpace.single f 1

private theorem faceUnit_norm (f : F) : ‖faceUnit f‖ = 1 := by
  simp [faceUnit]

private theorem transpose_vanishes (A : Matrix F E ℝ) (f : F) (j : ℕ)
    (z : EuclideanSpace ℝ F) (hz : ∀ g ∉ faceBall A f j, z g = 0)
    (e : E) (he : e ∉ edgeBall A f j) : incidence Aᵀ z e = 0 := by
  classical
  rw [incidence_apply]
  apply Finset.sum_eq_zero
  intro g _
  by_cases hg : g ∈ faceBall A f j
  · have hge : A g e = 0 := by
      by_contra h
      exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hg, h⟩)
    simp [hge]
  · simp [hz g hg]

private theorem laplacian_vanishes (A : Matrix F E ℝ) (f : F) (j : ℕ)
    (z : EuclideanSpace ℝ F) (hz : ∀ g ∉ faceBall A f j, z g = 0)
    (g : F) (hg : g ∉ faceBall A f (j + 1)) :
    incidence A (incidence Aᵀ z) g = 0 := by
  classical
  rw [incidence_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases hge : A g e = 0
  · simp [hge]
  · have he : e ∉ edgeBall A f j := by
      intro he
      obtain ⟨h, hh, hhe⟩ := (Finset.mem_filter.mp he).2
      exact hg (Or.inr ⟨h, hh, e, hhe, hge⟩)
    rw [transpose_vanishes A f j z hz e he, mul_zero]

private theorem residual_pow_vanishes (A : Matrix F E ℝ) (M : ℝ) (f : F) (j : ℕ) :
    ∀ g ∉ faceBall A f j, ((residual A M ^ j) (faceUnit f)) g = 0 := by
  induction j with
  | zero =>
      intro g hg
      have hgf : g ≠ f := hg
      simp [faceUnit, hgf]
  | succ j ih =>
      intro g hg
      have hprev : g ∉ faceBall A f j := fun h => hg (Or.inl h)
      rw [pow_succ']
      change ((residual A M) ((residual A M ^ j) (faceUnit f))) g = 0
      change ((residual A M ^ j) (faceUnit f)) g -
        (M ^ 2)⁻¹ * incidence A (incidence Aᵀ ((residual A M ^ j) (faceUnit f))) g = 0
      rw [ih g hprev, laplacian_vanishes A f j _ ih g hg, mul_zero, sub_zero]

/-- The transpose of the incidence matrix extends the support of the (j)-th
residual iterate by at most one edge step. -/
theorem transpose_residual_pow_vanishes (A : Matrix F E ℝ) (M : ℝ) (f : F) (j : ℕ)
    (e : E) (he : e ∉ edgeBall A f j) :
    incidence Aᵀ ((residual A M ^ j) (faceUnit f)) e = 0 :=
  transpose_vanishes A f j _ (residual_pow_vanishes A M f j) e he

private theorem residual_mem_range (A : Matrix F E ℝ) (M : ℝ) (z : EuclideanSpace ℝ F)
    (hz : z ∈ LinearMap.range (incidence A).toLinearMap) :
    residual A M z ∈ LinearMap.range (incidence A).toLinearMap := by
  let H := LinearMap.range (incidence A).toLinearMap
  change z - (M ^ 2)⁻¹ • incidence A (incidence Aᵀ z) ∈ H
  exact H.sub_mem hz (H.smul_mem _ (LinearMap.mem_range_self _ _))

private theorem residual_pow_bound (A : Matrix F E ℝ) (M q : ℝ) (hq : 0 ≤ q)
    (hcontract : ∀ z ∈ LinearMap.range (incidence A).toLinearMap,
      ‖residual A M z‖ ≤ q * ‖z‖)
    (f : F) (hf : faceUnit f ∈ LinearMap.range (incidence A).toLinearMap) (j : ℕ) :
    (residual A M ^ j) (faceUnit f) ∈ LinearMap.range (incidence A).toLinearMap ∧
      ‖(residual A M ^ j) (faceUnit f)‖ ≤ q ^ j := by
  induction j with
  | zero => simpa [faceUnit_norm] using hf
  | succ j ih =>
      rw [pow_succ']
      change residual A M ((residual A M ^ j) (faceUnit f)) ∈ _ ∧ _
      refine ⟨residual_mem_range A M _ ih.1, ?_⟩
      calc
        ‖residual A M ((residual A M ^ j) (faceUnit f))‖ ≤
            q * ‖(residual A M ^ j) (faceUnit f)‖ := hcontract _ ih.1
        _ ≤ q ^ (j + 1) := by
          rw [pow_succ']
          exact mul_le_mul_of_nonneg_left ih.2 hq

/-- The (j)-th edge term of the Neumann Green series. -/
noncomputable def neumannTerm (A : Matrix F E ℝ) (M : ℝ) (f : F) (j : ℕ) :
    EuclideanSpace ℝ E :=
  (M ^ 2)⁻¹ • incidence Aᵀ ((residual A M ^ j) (faceUnit f))

private theorem incidence_neumannTerm (A : Matrix F E ℝ) (M : ℝ) (f : F) (j : ℕ) :
    incidence A (neumannTerm A M f j) =
      (residual A M ^ j) (faceUnit f) - (residual A M ^ (j + 1)) (faceUnit f) := by
  rw [neumannTerm, map_smul, pow_succ' (residual A M) j]
  change (M ^ 2)⁻¹ • incidence A (incidence Aᵀ ((residual A M ^ j) (faceUnit f))) =
    (residual A M ^ j) (faceUnit f) -
      ((residual A M ^ j) (faceUnit f) -
        (M ^ 2)⁻¹ • incidence A (incidence Aᵀ ((residual A M ^ j) (faceUnit f))))
  rw [sub_sub_cancel]

private theorem norm_neumannTerm_le (A : Matrix F E ℝ) {M : ℝ} (hM : 0 < M)
    (hA : ‖incidence A‖ ≤ M) (f : F) (j : ℕ) {b : ℝ}
    (hb : ‖(residual A M ^ j) (faceUnit f)‖ ≤ b) :
    ‖neumannTerm A M f j‖ ≤ M⁻¹ * b := by
  have hAt : ‖incidence Aᵀ‖ ≤ M := by
    rwa [incidence_transpose_eq_adjoint, LinearIsometryEquiv.norm_map]
  rw [neumannTerm, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (M ^ 2)⁻¹)]
  calc
    _ ≤ (M ^ 2)⁻¹ * (‖incidence Aᵀ‖ * ‖(residual A M ^ j) (faceUnit f)‖) :=
      mul_le_mul_of_nonneg_left ((incidence Aᵀ).le_opNorm _) (by positivity)
    _ ≤ (M ^ 2)⁻¹ * (M * b) := by gcongr
    _ = M⁻¹ * b := by field_simp

private theorem sum_abs_le_ball (A : Matrix F E ℝ) (f : F) (j : ℕ)
    (x : EuclideanSpace ℝ E) (hx : ∀ e ∉ edgeBall A f j, x e = 0) :
    (∑ e, |x e|) ≤ Real.sqrt (edgeBall A f j).card * ‖x‖ := by
  let s := edgeBall A f j
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun e _ he => by simp [hx e he])]
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => 1) (fun e => |x e|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun e _ _ => sq_nonneg ‖x e‖)

private theorem continuous_sum_abs (s : Finset E) :
    Continuous (fun x : EuclideanSpace ℝ E => ∑ e ∈ s, |x e|) := by
  exact continuous_finsetSum _ fun e _ => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : E => ℝ) e).continuous.abs

private theorem sum_abs_hasSum_le (s : Finset E) {u : ℕ → EuclideanSpace ℝ E}
    {x : EuclideanSpace ℝ E} {b : ℕ → ℝ} (hu : HasSum u x) (hb : Summable b)
    (hbound : ∀ j, (∑ e ∈ s, |u j e|) ≤ b j) :
    (∑ e ∈ s, |x e|) ≤ ∑' j, b j := by
  apply le_of_tendsto_of_tendsto' ((continuous_sum_abs s).continuousAt.tendsto.comp
    hu.tendsto_sum_nat) hb.hasSum.tendsto_sum_nat
  intro n
  calc
    (∑ e ∈ s, |(∑ j ∈ Finset.range n, u j) e|) ≤
        ∑ e ∈ s, ∑ j ∈ Finset.range n, |u j e| := by
      apply Finset.sum_le_sum
      intro e _
      change |(PiLp.proj (𝕜 := ℝ) 2 (fun _ : E => ℝ) e) (∑ j ∈ Finset.range n, u j)| ≤ _
      rw [map_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, b j := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun j _ => hbound j

private theorem faceBall_mono (A : Matrix F E ℝ) (f : F) : Monotone (faceBall A f) :=
  monotone_nat_of_le_succ fun _ _ hg => Or.inl hg

private theorem edgeBall_mono (A : Matrix F E ℝ) (f : F) : Monotone (edgeBall A f) := by
  classical
  intro j k hjk e he
  obtain ⟨g, hg, hge⟩ := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, faceBall_mono A f hjk hg, hge⟩

private theorem sum_abs_tail_le (A : Matrix F E ℝ) (f : F)
    {u : ℕ → EuclideanSpace ℝ E} {x : EuclideanSpace ℝ E} {b : ℕ → ℝ}
    (hu : HasSum u x) (hb : Summable b)
    (hbound : ∀ j, (∑ e, |u j e|) ≤ b j)
    (hsupport : ∀ j e, e ∉ edgeBall A f j → u j e = 0) (J : ℕ) :
    (∑ e ∈ Finset.univ \ edgeBall A f J, |x e|) ≤ ∑' j, b (j + (J + 1)) := by
  classical
  let s := Finset.univ \ edgeBall A f J
  let tail := ∑' j, u (j + (J + 1))
  have htail : Summable (fun j => u (j + (J + 1))) :=
    (summable_nat_add_iff (J + 1)).mpr hu.summable
  have hsplit : (∑ j ∈ Finset.range (J + 1), u j) + tail = x :=
    (hu.summable.sum_add_tsum_nat_add (J + 1)).trans hu.tsum_eq
  have hcoords (e : E) (he : e ∈ s) : x e = tail e := by
    have hprefix : (∑ j ∈ Finset.range (J + 1), u j) e = 0 := by
      change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : E => ℝ) e) (∑ j ∈ Finset.range (J + 1), u j) = 0
      rw [map_sum]
      exact Finset.sum_eq_zero fun j hj => hsupport j e fun h =>
        (Finset.mem_sdiff.mp he).2 (edgeBall_mono A f (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) h)
    rw [← hsplit]
    change (∑ j ∈ Finset.range (J + 1), u j) e + tail e = tail e
    rw [hprefix, zero_add]
  calc
    (∑ e ∈ s, |x e|) = ∑ e ∈ s, |tail e| :=
      Finset.sum_congr rfl fun e he => congrArg abs (hcoords e he)
    _ ≤ ∑' j, b (j + (J + 1)) :=
      sum_abs_hasSum_le s htail.hasSum ((summable_nat_add_iff (J + 1)).mpr hb)
        fun j => (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun e _ _ => abs_nonneg (u _ e))).trans (hbound _)

/-- The weighted volume majorant for the Neumann series is summable on every
finite incidence graph when the residual rate lies in ([0,1)). -/
noncomputable def neumannWeight (A : Matrix F E ℝ) (M q : ℝ) (f : F) (j : ℕ) : ℝ :=
  M⁻¹ * (Real.sqrt (edgeBall A f j).card * q ^ j)

private theorem neumannWeight_summable (A : Matrix F E ℝ) {M q : ℝ} (hM : 0 < M)
    (hq : 0 ≤ q) (hq' : q < 1) (f : F) : Summable (neumannWeight A M q f) := by
  apply Summable.of_nonneg_of_le (f := fun j => (M⁻¹ * Real.sqrt (Fintype.card E)) * q ^ j)
  · intro j
    unfold neumannWeight
    positivity
  · intro j
    rw [neumannWeight, ← mul_assoc]
    gcongr
    exact Finset.card_le_univ _
  · exact (summable_geometric_of_lt_one hq hq').mul_left _

/-- The Neumann series solves the unit syndrome, with an incidence-volume
bound on its absolute norm and on the absolute mass outside each ball. -/
theorem neumann_repair (A : Matrix F E ℝ) {M q : ℝ} (hM : 0 < M)
    (hq : 0 ≤ q) (hq' : q < 1) (hA : ‖incidence A‖ ≤ M)
    (hcontract : ∀ z ∈ LinearMap.range (incidence A).toLinearMap,
      ‖residual A M z‖ ≤ q * ‖z‖)
    (f : F) (hf : faceUnit f ∈ LinearMap.range (incidence A).toLinearMap) :
    ∃ x : EuclideanSpace ℝ E, HasSum (neumannTerm A M f) x ∧
      incidence A x = faceUnit f ∧
      (∑ e, |x e|) ≤ ∑' j, neumannWeight A M q f j ∧
      ∀ J, (∑ e ∈ Finset.univ \ edgeBall A f J, |x e|) ≤
        ∑' j, neumannWeight A M q f (j + (J + 1)) := by
  let u := neumannTerm A M f
  have hpow j := (residual_pow_bound A M q hq hcontract f hf j).2
  have hunorm j : ‖u j‖ ≤ M⁻¹ * q ^ j := norm_neumannTerm_le A hM hA f j (hpow j)
  have hu : Summable u :=
    ((summable_geometric_of_lt_one hq hq').mul_left M⁻¹).of_norm_bounded hunorm
  have hsupport j e (he : e ∉ edgeBall A f j) : u j e = 0 := by
    change (M ^ 2)⁻¹ * incidence Aᵀ ((residual A M ^ j) (faceUnit f)) e = 0
    rw [transpose_residual_pow_vanishes A M f j e he, mul_zero]
  have hweight j : (∑ e, |u j e|) ≤ neumannWeight A M q f j := by
    calc
      _ ≤ Real.sqrt (edgeBall A f j).card * ‖u j‖ :=
        sum_abs_le_ball A f j (u j) (hsupport j)
      _ ≤ Real.sqrt (edgeBall A f j).card * (M⁻¹ * q ^ j) :=
        mul_le_mul_of_nonneg_left (hunorm j) (Real.sqrt_nonneg _)
      _ = _ := by unfold neumannWeight; ring
  refine ⟨∑' j, u j, hu.hasSum, ?_,
    sum_abs_hasSum_le Finset.univ hu.hasSum (neumannWeight_summable A hM hq hq' f) hweight,
    sum_abs_tail_le A f hu.hasSum (neumannWeight_summable A hM hq hq' f) hweight hsupport⟩
  have htelescope (n : ℕ) :
      incidence A (∑ j ∈ Finset.range n, u j) =
        faceUnit f - (residual A M ^ n) (faceUnit f) := by
    rw [map_sum]
    simp only [u, incidence_neumannTerm]
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        abel
  have hzero : Tendsto (fun n : ℕ => (residual A M ^ n) (faceUnit f)) atTop (𝓝 0) :=
    squeeze_zero_norm hpow (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq')
  apply tendsto_nhds_unique
    ((incidence A).continuous.continuousAt.tendsto.comp hu.hasSum.tendsto_sum_nat)
  have heq : (⇑(incidence A) ∘ fun n => ∑ j ∈ Finset.range n, u j) =
      fun n => faceUnit f - (residual A M ^ n) (faceUnit f) := funext htelescope
  rw [heq]
  simpa only [sub_zero] using (tendsto_const_nhds (x := faceUnit f)).sub hzero

/-- The Neumann volume bound transfers to integer absolute norm and to
support over every `ZMod n`, using the same incidence matrix. -/
theorem neumann_integer_and_zmod_repair (D : Matrix F E ℤ) (hD : D.IsTotallyUnimodular)
    {M q : ℝ} (hM : 0 < M) (hq : 0 ≤ q) (hq' : q < 1)
    (hA : ‖incidence (D.map (Int.castRingHom ℝ))‖ ≤ M)
    (hcontract : ∀ z ∈ LinearMap.range (incidence (D.map (Int.castRingHom ℝ))).toLinearMap,
      ‖residual (D.map (Int.castRingHom ℝ)) M z‖ ≤ q * ‖z‖)
    (f : F) (hf : faceUnit f ∈ LinearMap.range (incidence (D.map (Int.castRingHom ℝ))).toLinearMap) :
    let b : F → ℤ := fun g => if g = f then 1 else 0
    let B := ∑' j, neumannWeight (D.map (Int.castRingHom ℝ)) M q f j
    ∃ z : E → ℤ, D *ᵥ z = b ∧ (∑ e, |(z e : ℝ)|) ≤ B ∧
      ∀ n : ℕ, (D.map (Int.castRingHom (ZMod n)) *ᵥ (fun e => (z e : ZMod n)) =
        fun g => (b g : ZMod n)) ∧
        ((TotalUnimodularL1Repair.nonzeroSupport (fun e => (z e : ZMod n))).card : ℝ) ≤ B := by
  dsimp only
  obtain ⟨x, _, hx, hcost, _⟩ := neumann_repair _ hM hq hq' hA hcontract f hf
  let b : F → ℤ := fun g => if g = f then 1 else 0
  have hsol : D.map (Int.castRingHom ℝ) *ᵥ (fun e => x e) = fun g => (b g : ℝ) := by
    funext g
    change (∑ e, (D.map (Int.castRingHom ℝ)) g e * x e) = (b g : ℝ)
    rw [← incidence_apply (D.map (Int.castRingHom ℝ)) x g, hx]
    by_cases h : g = f
    · subst g
      simp [b, faceUnit]
    · simp [b, faceUnit, h]
  obtain ⟨z, hz, hzcost⟩ := TotalUnimodularL1Repair.exists_integer_l1_repair D hD b _ hsol
  refine ⟨z, hz, hzcost.trans hcost, fun n => ?_⟩
  obtain ⟨hmod, hsub⟩ := TotalUnimodularL1Repair.reduce_integer_solution D b z hz n
  exact ⟨hmod, (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    ((TotalUnimodularL1Repair.support_card_le_sum_abs z).trans (hzcost.trans hcost))⟩

/-- The face Laplacian restricted to the real incidence image. -/
noncomputable def laplacianOnRange (A : Matrix F E ℝ) :
    Module.End ℝ (LinearMap.range (incidence A).toLinearMap) :=
  ((incidence A).comp (incidence Aᵀ)).toLinearMap.restrict
    (fun z _ => LinearMap.mem_range_self (incidence A).toLinearMap (incidence Aᵀ z))

private theorem laplacianOnRange_symmetric (A : Matrix F E ℝ) :
    (laplacianOnRange A).IsSymmetric := by
  unfold laplacianOnRange
  apply LinearMap.IsSymmetric.restrict_invariant
  rw [incidence_transpose_eq_adjoint]
  exact LinearMap.isSymmetric_self_comp_adjoint _

private theorem laplacianOnRange_eigenvalue_bounds (A : Matrix F E ℝ)
    {M : ℝ} (hM : 0 < M) (hA : ‖incidence A‖ ≤ M)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue (laplacianOnRange A) μ) :
    0 < μ ∧ μ ≤ M ^ 2 := by
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have hz0 : z ≠ 0 := hz.2
  have hAz : incidence A (incidence Aᵀ z.val) = μ • z.val :=
    congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hz.1)
  have hzval : z.val ≠ 0 := fun h => hz0 (Subtype.ext h)
  have hzpos : 0 < ‖z.val‖ := norm_pos_iff.mpr hzval
  have ht : ‖incidence Aᵀ z.val‖ ^ 2 = μ * ‖z.val‖ ^ 2 := by
    have h := (incidence Aᵀ).apply_norm_sq_eq_inner_adjoint_left z.val
    rw [← incidence_transpose_eq_adjoint Aᵀ, Matrix.transpose_transpose] at h
    change _ = RCLike.re (inner ℝ (incidence A (incidence Aᵀ z.val)) z.val) at h
    rw [hAz, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    exact h
  have hnz : incidence Aᵀ z.val ≠ 0 := by
    intro hzero
    obtain ⟨w, hw⟩ := z.property
    change incidence A w = z.val at hw
    have hinner : inner ℝ z.val z.val = 0 := by
      rw [← hw, ← ContinuousLinearMap.adjoint_inner_right]
      rw [hw, ← incidence_transpose_eq_adjoint, hzero, inner_zero_right]
    exact hzval (inner_self_eq_zero.mp hinner)
  have hAt : ‖incidence Aᵀ‖ ≤ M := by
    rwa [incidence_transpose_eq_adjoint, LinearIsometryEquiv.norm_map]
  have hup : ‖incidence Aᵀ z.val‖ ≤ M * ‖z.val‖ :=
    ((incidence Aᵀ).le_opNorm _).trans (mul_le_mul_of_nonneg_right hAt (norm_nonneg _))
  constructor
  · exact pos_of_mul_pos_left (ht ▸ sq_pos_of_pos (norm_pos_iff.mpr hnz)) (sq_nonneg _)
  · apply le_of_mul_le_mul_right _ (sq_pos_of_pos hzpos)
    rw [← ht, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hup _

/-- The lower spectral bound on the incidence image and the incidence
operator norm imply the usual Neumann contraction rate. -/
theorem residual_contracts_of_spectral_gap (A : Matrix F E ℝ) {M σ : ℝ}
    (hσ : 0 < σ) (hσM : σ ≤ M) (hA : ‖incidence A‖ ≤ M)
    (hgap : ∀ μ > 0, Module.End.HasEigenvalue (laplacianOnRange A) μ → σ ^ 2 ≤ μ)
    (z : EuclideanSpace ℝ F) (hz : z ∈ LinearMap.range (incidence A).toLinearMap) :
    ‖residual A M z‖ ≤ (1 - σ ^ 2 / M ^ 2) * ‖z‖ := by
  have hM := hσ.trans_le hσM
  have hM2 : 0 < M ^ 2 := by positivity
  let hsym := laplacianOnRange_symmetric A
  let H := LinearMap.range (incidence A).toLinearMap
  let n := Module.finrank ℝ H
  let basis := hsym.eigenvectorBasis (n := n) rfl
  let eigenvalues := hsym.eigenvalues (n := n) rfl
  let v : H := ⟨z, hz⟩
  let w : H := ⟨residual A M z, residual_mem_range A M z hz⟩
  have hw : w = v - (M ^ 2)⁻¹ • laplacianOnRange A v := by
    apply Subtype.ext
    rfl
  have hcoord (i : Fin n) : basis.repr w i =
      (1 - eigenvalues i / M ^ 2) * basis.repr v i := by
    have hd := hsym.eigenvectorBasis_apply_self_apply (n := n) rfl v i
    change basis.repr (laplacianOnRange A v) i = eigenvalues i * basis.repr v i at hd
    rw [hw, map_sub, map_smul]
    change basis.repr v i - (M ^ 2)⁻¹ * basis.repr (laplacianOnRange A v) i = _
    rw [hd, div_eq_mul_inv]
    ring
  let q := 1 - σ ^ 2 / M ^ 2
  have hq : 0 ≤ q := sub_nonneg.mpr ((div_le_iff₀ hM2).mpr (by nlinarith))
  change ‖w‖ ≤ q * ‖v‖
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _)),
    ← basis.repr.norm_map w, ← basis.repr.norm_map v, mul_pow,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hcoord, mul_pow]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ?_ ?_ 2) (sq_nonneg _)
  · have h := laplacianOnRange_eigenvalue_bounds A hM hA (hsym.hasEigenvalue_eigenvalues rfl i)
    exact sub_nonneg.mpr ((div_le_iff₀ hM2).mpr (by simpa using h.2))
  · have he := hsym.hasEigenvalue_eigenvalues (n := n) rfl i
    have h := laplacianOnRange_eigenvalue_bounds A hM hA he
    exact sub_le_sub_left (div_le_div_of_nonneg_right (hgap _ h.1 he) hM2.le) _

private noncomputable def chebIter {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V) (v : V) : ℕ → V
  | 0 => v
  | 1 => T v
  | j + 2 => (2 : ℝ) • T (chebIter T v (j + 1)) - chebIter T v j

private theorem map_chebIter {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (T : Module.End ℝ V) (S : Module.End ℝ W)
    (L : V →ₗ[ℝ] W) (hL : ∀ v, L (T v) = S (L v)) (v : V) (j : ℕ) :
    L (chebIter T v j) = chebIter S (L v) j := by
  induction j using Nat.twoStepInduction with
  | zero => rfl
  | one => exact hL v
  | more j ih0 ih1 => simp only [chebIter, map_sub, map_smul, hL, ih0, ih1]

private noncomputable def centered (A : Matrix F E ℝ) (c h : ℝ) :
    Module.End ℝ (EuclideanSpace ℝ F) :=
  h⁻¹ • (((incidence A).comp (incidence Aᵀ)).toLinearMap - c • 1)

private theorem centered_vanishes (A : Matrix F E ℝ) (c h : ℝ) (f : F) (j : ℕ)
    (z : EuclideanSpace ℝ F) (hz : ∀ g ∉ faceBall A f j, z g = 0)
    (g : F) (hg : g ∉ faceBall A f (j + 1)) : centered A c h z g = 0 := by
  change h⁻¹ * (incidence A (incidence Aᵀ z) g - c * z g) = 0
  rw [laplacian_vanishes A f j z hz g hg, hz g (fun hprev => hg (Or.inl hprev))]
  ring

private theorem chebIter_vanishes (A : Matrix F E ℝ) (c h : ℝ) (f : F) (j : ℕ) :
    ∀ g ∉ faceBall A f j, chebIter (centered A c h) (faceUnit f) j g = 0 := by
  have hbase : ∀ g ∉ faceBall A f 0, faceUnit f g = 0 := by
    intro g hg
    have hgf : g ≠ f := hg
    simp [faceUnit, hgf]
  induction j using Nat.twoStepInduction with
  | zero => exact hbase
  | one => exact centered_vanishes A c h f 0 _ hbase
  | more j ih0 ih1 =>
      intro g hg
      have hprev : g ∉ faceBall A f j := fun hs =>
        hg (faceBall_mono A f (Nat.le_add_right j 2) hs)
      change (2 : ℝ) * centered A c h (chebIter (centered A c h) (faceUnit f) (j + 1)) g -
        chebIter (centered A c h) (faceUnit f) j g = 0
      rw [centered_vanishes A c h f (j + 1) _ ih1 g hg, ih0 g hprev, mul_zero, sub_zero]

private noncomputable def chebValue (t : ℝ) (j : ℕ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval t

@[simp] private theorem chebValue_zero (t : ℝ) : chebValue t 0 = 1 := by
  simp [chebValue]

@[simp] private theorem chebValue_one (t : ℝ) : chebValue t 1 = t := by
  simp [chebValue]

private theorem chebValue_add_two (t : ℝ) (j : ℕ) :
    chebValue t (j + 2) = 2 * t * chebValue t (j + 1) - chebValue t j := by
  simp [chebValue, Polynomial.Chebyshev.T_add_two]

private theorem chebIter_real (t v : ℝ) (j : ℕ) :
    chebIter (t • (1 : Module.End ℝ ℝ)) v j = chebValue t j * v := by
  induction j using Nat.twoStepInduction with
  | zero => simp [chebIter]
  | one => simp [chebIter, smul_eq_mul]
  | more j ih0 ih1 =>
      have hone (a : ℝ) : (1 : Module.End ℝ ℝ) a = a := rfl
      simp only [chebIter, LinearMap.smul_apply, hone, smul_eq_mul, ih0, ih1,
        chebValue_add_two]
      ring

private def chebMultiplicity (j : ℕ) : ℝ := if j = 0 then 1 else 2

private theorem cheb_scalar_sum {r t s : ℝ} (hs : HasSum (fun j : ℕ =>
    chebMultiplicity j * r ^ j * chebValue t j) s) :
    (1 - 2 * r * t + r ^ 2) * s = 1 - r ^ 2 := by
  let u := fun j : ℕ => r ^ j * chebValue t j
  have hshift : HasSum (fun j : ℕ => 2 * u (j + 1)) (s - 1) := by
    simpa [chebMultiplicity, u, mul_assoc] using (hasSum_nat_add_iff' 1).mpr hs
  have hshift' : HasSum (fun j : ℕ => 2 * u (j + 2)) (s - 1 - 2 * (r * t)) := by
    simpa [u, Nat.add_assoc] using (hasSum_nat_add_iff' 1).mpr hshift
  have hu : HasSum u (1 + (2 : ℝ)⁻¹ * (s - 1)) := by
    have hs' : HasSum (fun j : ℕ => u (j + 1)) ((2 : ℝ)⁻¹ * (s - 1)) := by
      simpa [← mul_assoc] using hshift.mul_left (2 : ℝ)⁻¹
    simpa [u, add_comm] using (hasSum_nat_add_iff 1).mp hs'
  have hrec (j : ℕ) : 2 * u (j + 2) =
      (2 * r * t) * (2 * u (j + 1)) - (2 * r ^ 2) * u j := by
    simp only [u, chebValue_add_two]
    rw [pow_succ r (j + 1), pow_succ r j]
    ring
  have hrecsum := (hshift.mul_left (2 * r * t)).sub (hu.mul_left (2 * r ^ 2))
  have heq := hshift'.unique (hrecsum.congr_fun hrec)
  linear_combination heq

/-- The (j)-th edge term of the Chebyshev Green series. -/
noncomputable def chebyshevTerm (A : Matrix F E ℝ) (M σ : ℝ) (f : F) (j : ℕ) :
    EuclideanSpace ℝ E :=
  let c := (M ^ 2 + σ ^ 2) / 2
  let h := (M ^ 2 - σ ^ 2) / 2
  let r := (σ - M) / (M + σ)
  ((M * σ)⁻¹ * chebMultiplicity j * r ^ j) •
    incidence Aᵀ (chebIter (centered A c h) (faceUnit f) j)

/-- The Chebyshev series has the same support radius as the Neumann series. -/
theorem chebyshevTerm_vanishes (A : Matrix F E ℝ) (M σ : ℝ) (f : F) (j : ℕ)
    (e : E) (he : e ∉ edgeBall A f j) : chebyshevTerm A M σ f j e = 0 := by
  change _ * incidence Aᵀ (chebIter (centered A _ _) (faceUnit f) j) e = 0
  rw [transpose_vanishes A f j _ (chebIter_vanishes A _ _ f j) e he, mul_zero]

/-- The weighted volume majorant for the Chebyshev series. -/
noncomputable def chebyshevWeight (A : Matrix F E ℝ) (M σ : ℝ) (f : F) (j : ℕ) : ℝ :=
  σ⁻¹ * (chebMultiplicity j * ((M - σ) / (M + σ)) ^ j) * Real.sqrt (edgeBall A f j).card

/-- On the real incidence image, the Chebyshev Green series solves the unit
syndrome and bounds both its absolute norm and its tails outside incidence balls. -/
theorem chebyshev_repair (A : Matrix F E ℝ) {M σ : ℝ}
    (hσ : 0 < σ) (hσM : σ < M) (hA : ‖incidence A‖ ≤ M)
    (hgap : ∀ μ > 0, Module.End.HasEigenvalue (laplacianOnRange A) μ → σ ^ 2 ≤ μ)
    (f : F) (hf : faceUnit f ∈ LinearMap.range (incidence A).toLinearMap) :
    ∃ x : EuclideanSpace ℝ E, HasSum (chebyshevTerm A M σ f) x ∧
      incidence A x = faceUnit f ∧ (∑ e, |x e|) ≤ ∑' j, chebyshevWeight A M σ f j ∧
      ∀ J, (∑ e ∈ Finset.univ \ edgeBall A f J, |x e|) ≤
        ∑' j, chebyshevWeight A M σ f (j + (J + 1)) := by
  have hM := hσ.trans hσM
  have hsumPos : 0 < M + σ := by positivity
  let c := (M ^ 2 + σ ^ 2) / 2
  let h := (M ^ 2 - σ ^ 2) / 2
  let r := (σ - M) / (M + σ)
  let ρ := (M - σ) / (M + σ)
  have hh : 0 < h := by dsimp [h]; nlinarith
  have hρ : 0 ≤ ρ := div_nonneg (sub_nonneg.mpr hσM.le) hsumPos.le
  have hρ' : ρ < 1 := (div_lt_one hsumPos).mpr (by linarith)
  have hr : |r| = ρ := by
    dsimp [r, ρ]
    rw [abs_div, abs_of_nonpos (sub_nonpos.mpr hσM.le), abs_of_pos hsumPos, neg_sub]
  have hmult0 j : 0 ≤ chebMultiplicity j := by unfold chebMultiplicity; split <;> norm_num
  have hmult2 j : chebMultiplicity j ≤ 2 := by unfold chebMultiplicity; split <;> norm_num
  let H := LinearMap.range (incidence A).toLinearMap
  let v : H := ⟨faceUnit f, hf⟩
  let L := laplacianOnRange A
  let T : Module.End ℝ H := h⁻¹ • (L - c • 1)
  let hsym := laplacianOnRange_symmetric A
  let n := Module.finrank ℝ H
  let basis := hsym.eigenvectorBasis (n := n) rfl
  let eigenvalues := hsym.eigenvalues (n := n) rfl
  let t := fun i => (eigenvalues i - c) / h
  have ht (i : Fin n) : |t i| ≤ 1 := by
    have he := hsym.hasEigenvalue_eigenvalues (n := n) rfl i
    have hμ := laplacianOnRange_eigenvalue_bounds A hM hA he
    have hlo : σ ^ 2 ≤ eigenvalues i := hgap _ hμ.1 he
    have hhi : eigenvalues i ≤ M ^ 2 := hμ.2
    apply abs_le.mpr
    dsimp only [t]
    constructor
    · apply (le_div_iff₀ hh).mpr
      dsimp [c, h]
      linarith
    · apply (div_le_iff₀ hh).mpr
      dsimp [c, h]
      linarith
  let coord (i : Fin n) : H →L[ℝ] ℝ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).comp
      basis.repr.toLinearIsometry.toContinuousLinearMap
  have hcoord (i : Fin n) (j : ℕ) :
      coord i (chebIter T v j) = chebValue (t i) j * coord i v := by
    rw [← chebIter_real]
    exact map_chebIter T (t i • 1) (coord i).toLinearMap (fun w => by
      have hd := hsym.eigenvectorBasis_apply_self_apply (n := n) rfl w i
      change coord i (L w) = eigenvalues i * coord i w at hd
      change coord i (h⁻¹ • (L w - c • w)) = t i * coord i w
      rw [map_smul, map_sub, map_smul, hd]
      simp only [smul_eq_mul, t, div_eq_mul_inv]
      ring) v j
  have hcheb (i : Fin n) (j : ℕ) : |chebValue (t i) j| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (ht i)
  have hnorm (j : ℕ) : ‖chebIter T v j‖ ≤ 1 := by
    have hv : ‖v‖ = 1 := faceUnit_norm f
    rw [← hv, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      ← basis.repr.norm_map (chebIter T v j), ← basis.repr.norm_map v,
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change (coord i (chebIter T v j)) ^ 2 ≤ (coord i v) ^ 2
    rw [hcoord, mul_pow]
    have hsq : chebValue (t i) j ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hcheb i j) 2
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (coord i v))
  let u (j : ℕ) : H := (chebMultiplicity j * r ^ j) • chebIter T v j
  have huNorm (j : ℕ) : ‖u j‖ ≤ chebMultiplicity j * ρ ^ j := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, hr, abs_of_nonneg (hmult0 j)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hnorm j) (mul_nonneg (hmult0 j) (pow_nonneg hρ j))
  have hu : Summable u := by
    refine ((summable_geometric_of_lt_one hρ hρ').mul_left 2).of_norm_bounded fun j => ?_
    exact (huNorm j).trans (mul_le_mul_of_nonneg_right (hmult2 j) (pow_nonneg hρ j))
  let s := ∑' j, u j
  have hLs : L s = (M * σ) • v := by
    apply basis.repr.injective
    ext i
    have hs := hu.hasSum.map (coord i).toLinearMap.toAddMonoidHom (coord i).continuous
    have hs' : HasSum (fun j => chebMultiplicity j * r ^ j * chebValue (t i) j * coord i v)
        (coord i s) := by
      refine hs.congr_fun fun j => ?_
      symm
      change coord i (u j) = _
      dsimp only [u]
      rw [map_smul, hcoord, smul_eq_mul, ← mul_assoc]
    let b := fun j : ℕ => chebMultiplicity j * r ^ j * chebValue (t i) j
    have hb : Summable b := by
      refine ((summable_geometric_of_lt_one hρ hρ').mul_left 2).of_norm_bounded fun j => ?_
      change |chebMultiplicity j * r ^ j * chebValue (t i) j| ≤ 2 * ρ ^ j
      rw [abs_mul, abs_mul, abs_of_nonneg (hmult0 j), abs_pow, hr]
      calc
        _ ≤ (chebMultiplicity j * ρ ^ j) * 1 :=
          mul_le_mul_of_nonneg_left (hcheb i j) (mul_nonneg (hmult0 j) (pow_nonneg hρ j))
        _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right (hmult2 j) (pow_nonneg hρ j)
    let B := ∑' j, b j
    have hscalar := cheb_scalar_sum (s := B) hb.hasSum
    have hcoordSum : coord i s = B * coord i v := hs'.unique (hb.hasSum.mul_right _)
    have hden : eigenvalues i =
        (M + σ) ^ 2 / 4 * (1 - 2 * r * t i + r ^ 2) := by
      dsimp only [r, t, c, h]
      have hdiff : M ^ 2 - σ ^ 2 ≠ 0 := by dsimp [h] at hh; linarith
      field_simp
      ring
    have hnum : M * σ = (M + σ) ^ 2 / 4 * (1 - r ^ 2) := by
      dsimp only [r]
      field_simp
      ring
    have hd := hsym.eigenvectorBasis_apply_self_apply (n := n) rfl s i
    change coord i (L s) = eigenvalues i * coord i s at hd
    change coord i (L s) = coord i ((M * σ) • v)
    have hscale : eigenvalues i * B = M * σ := by
      rw [hden, mul_assoc, hscalar, ← hnum]
    rw [hd, hcoordSum, map_smul, smul_eq_mul, ← mul_assoc, hscale]
  let lift : H →L[ℝ] EuclideanSpace ℝ E :=
    (M * σ)⁻¹ • (incidence Aᵀ).comp H.subtypeL
  have hlift (j : ℕ) : lift (u j) = chebyshevTerm A M σ f j := by
    have hproj := map_chebIter T (centered A c h) H.subtype (fun _ => rfl) v j
    change (M * σ)⁻¹ • incidence Aᵀ ((u j : H) : EuclideanSpace ℝ F) = _
    change (M * σ)⁻¹ • incidence Aᵀ (H.subtype (u j)) = _
    dsimp only [u]
    rw [map_smul, hproj, map_smul, smul_smul, ← mul_assoc]
    rfl
  have hAt : ‖incidence Aᵀ‖ ≤ M := by
    rwa [incidence_transpose_eq_adjoint, LinearIsometryEquiv.norm_map]
  have hterm (j : ℕ) :
      ‖chebyshevTerm A M σ f j‖ ≤ σ⁻¹ * (chebMultiplicity j * ρ ^ j) := by
    rw [← hlift]
    change ‖(M * σ)⁻¹ • incidence Aᵀ ((u j : H) : EuclideanSpace ℝ F)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (M * σ)⁻¹)]
    calc
      _ ≤ (M * σ)⁻¹ * (‖incidence Aᵀ‖ * ‖u j‖) :=
        mul_le_mul_of_nonneg_left ((incidence Aᵀ).le_opNorm _) (by positivity)
      _ ≤ (M * σ)⁻¹ * (M * (chebMultiplicity j * ρ ^ j)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hAt (huNorm j) (norm_nonneg _) hM.le) (by positivity)
      _ = _ := by field_simp
  have hweight (j : ℕ) : (∑ e, |chebyshevTerm A M σ f j e|) ≤ chebyshevWeight A M σ f j := by
    refine (sum_abs_le_ball A f j _ (fun e => chebyshevTerm_vanishes A M σ f j e)).trans ?_
    rw [chebyshevWeight, mul_comm _ (Real.sqrt _)]
    exact mul_le_mul_of_nonneg_left (hterm j) (Real.sqrt_nonneg _)
  have hwSummable : Summable (chebyshevWeight A M σ f) := by
    apply Summable.of_nonneg_of_le
      (f := fun j => (σ⁻¹ * 2 * Real.sqrt (Fintype.card E)) * ρ ^ j)
    · intro j
      change 0 ≤ σ⁻¹ * (chebMultiplicity j * ρ ^ j) * Real.sqrt (edgeBall A f j).card
      exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (hmult0 j) (pow_nonneg hρ j)))
        (Real.sqrt_nonneg _)
    · intro j
      change σ⁻¹ * (chebMultiplicity j * ρ ^ j) * Real.sqrt (edgeBall A f j).card ≤ _
      calc
        _ ≤ σ⁻¹ * (2 * ρ ^ j) * Real.sqrt (Fintype.card E) := by
          gcongr
          · exact hmult2 j
          · exact Finset.card_le_univ _
        _ = _ := by ring
    · exact (summable_geometric_of_lt_one hρ hρ').mul_left _
  have hx := (hu.hasSum.map lift.toLinearMap.toAddMonoidHom lift.continuous).congr_fun
    (fun j => (hlift j).symm)
  refine ⟨lift s, hx, ?_, sum_abs_hasSum_le Finset.univ hx hwSummable hweight,
    sum_abs_tail_le A f hx hwSummable hweight (chebyshevTerm_vanishes A M σ f)⟩
  have hface : incidence A (incidence Aᵀ (s : EuclideanSpace ℝ F)) =
      (M * σ) • faceUnit f := congrArg Subtype.val hLs
  change incidence A ((M * σ)⁻¹ • incidence Aᵀ (s : EuclideanSpace ℝ F)) = faceUnit f
  rw [map_smul, hface, smul_smul, inv_mul_cancel₀ (mul_ne_zero hM.ne' hσ.ne'), one_smul]

end D5.S3.HomologicalAlgebra.FiniteIncidenceGreen

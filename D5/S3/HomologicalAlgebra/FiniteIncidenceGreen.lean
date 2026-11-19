/- GID: D5/S3/HomologicalAlgebra/FiniteIncidenceGreen
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FiniteIncidenceGreen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Incidence support propagation and Green series repair in finite dimensions. -/

import D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
import Mathlib.Analysis.InnerProductSpace.Spectrum
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

end D5.S3.HomologicalAlgebra.FiniteIncidenceGreen

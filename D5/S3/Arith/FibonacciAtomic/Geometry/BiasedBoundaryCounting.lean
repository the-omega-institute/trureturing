/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual finite spectral cutoffs and stopping spaces give the original multiplicity-aware counting bounds. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy
import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm

/-! Finite cutoffs count repeated positive boundary modes with their original indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting

open FiniteSourceHardy (H)
open BiasedBoundaryTrace (G J b)
open BiasedBoundaryPathSplit (constG)
open BiasedBoundaryCentering (Pi C mean centered_suffix_residual)
open BiasedBoundaryStopping (G0 Threshold A Qt Vt Vt0 actual_stopping_partition actual_stopping_residual)
open BiasedBoundaryFreeRootForm (D K Sigma energy mean_Pi lift free_root_least_energy weakGraph)
open BiasedBoundaryOperator (boundaryOperator actual_self_adjoint_realization actual_covariance_eigenspaces)
open BiasedBoundarySpectralForm (actual_spectral_form_energy)
open BiasedBoundaryTrialEnergy (actual_stopping_trial_energy)
open InnerProductSpace Filter
open scoped Topology ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The span of an arbitrary finite selection of actual positive boundary modes. -/
def modeSpace (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (e '' (s : Set ℕ))

instance (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ) : FiniteDimensional ℝ (modeSpace e s) :=
  FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image e)

/-- The finite orthogonal spectral projection, including every selected repeated mode. -/
def modeProjection (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ) : E →L[ℝ] E :=
  ∑ i ∈ s, (innerSL ℝ (e i)).smulRight (e i)

private theorem modeProjection_coeff (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ)
    (u : E) (i : ℕ) :
    e.repr (modeProjection e s u) i = if i ∈ s then e.repr u i else 0 := by
  classical
  simp [modeProjection, map_sum, map_smul, e.repr_self, lp.single_apply, Pi.single_apply,
    e.repr_apply_apply, innerSL_apply_apply]

private theorem modeProjection_mem (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ) (u : E) :
    modeProjection e s u ∈ modeSpace e s := by
  classical
  simp only [modeProjection,sum_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)

private theorem modeSpace_support (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ)
    {u : E} (hu : u ∈ modeSpace e s) (i : ℕ) (hi : i ∉ s) : e.repr u i = 0 := by
  classical
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,hj,rfl⟩ := hx
    simp only [e.repr_self, lp.single_apply, Pi.single_apply]
    split_ifs with he
    · exact (hi (he ▸ hj)).elim
    · rfl
  | zero => simp
  | add x y hx hy ihx ihy => simpa using congrArg₂ (· + ·) ihx ihy
  | smul a x hx ih => simpa using congrArg (a * ·) ih

private theorem modeProjection_fixed (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ)
    {u : E} (hu : u ∈ modeSpace e s) : modeProjection e s u = u := by
  classical
  apply e.repr.injective
  apply lp.ext
  funext i
  rw [modeProjection_coeff]
  split_ifs with hi
  · rfl
  · exact (modeSpace_support e s hu i hi).symm

private theorem modeSpace_iff (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ) (u : E) :
    u ∈ modeSpace e s ↔ ∀ i, i ∉ s → e.repr u i = 0 := by
  classical
  constructor
  · exact fun hu i hi => modeSpace_support e s hu i hi
  · intro hu
    have he : modeProjection e s u = u := by
      apply e.repr.injective
      apply lp.ext
      funext i
      rw [modeProjection_coeff]
      split_ifs with hi
      · rfl
      · exact (hu i hi).symm
    rw [← he]
    exact modeProjection_mem e s u

private theorem modeSpace_dimension (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ) :
    Module.finrank ℝ (modeSpace e s) = s.card := by
  classical
  have hr : Set.range (fun i : s => e i.val) = e '' (s : Set ℕ) := by
    ext u
    simp
  unfold modeSpace
  rw [← hr]
  simpa only [Fintype.card_coe, Function.comp_def] using
    (finrank_span_eq_card (e.orthonormal.linearIndependent.comp
      (fun i : s => i.val) Subtype.val_injective))

private theorem modeProjection_range (e : HilbertBasis ℕ ℝ E) (s : Finset ℕ) :
    (modeProjection e s).range = modeSpace e s := by
  apply le_antisymm
  · rintro u ⟨v,rfl⟩
    exact modeProjection_mem e s v
  · intro u hu
    exact ⟨u,modeProjection_fixed e s hu⟩

private theorem cutoff_finite (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hf : ∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite) (lam : ℝ) :
    {i | (mu i)⁻¹ ≤ lam}.Finite := by
  by_cases hl : 0 < lam
  · apply (hf lam⁻¹ (inv_pos.mpr hl)).subset
    intro i hi
    exact (inv_le_comm₀ hl (hp i)).mpr hi
  · have he : {i | (mu i)⁻¹ ≤ lam} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr ((le_of_not_gt hl).trans_lt (inv_pos.mpr (hp i)))
    rw [he]
    exact Set.finite_empty

private theorem strict_cutoff_finite (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hf : ∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite) (lam : ℝ) :
    {i | (mu i)⁻¹ < lam}.Finite :=
  (cutoff_finite mu hp hf lam).subset (fun i hi => (show (mu i)⁻¹ < lam from hi).le)

private theorem modeSpace_domain (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hg : ∀ i, ((e i).val,(mu i)⁻¹ • (e i).val) ∈ boundaryOperator.graph)
    (s : Finset ℕ) {u : G0} (hu : u ∈ modeSpace e s) : u.val ∈ D := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,_,rfl⟩ := hx
    exact ((actual_self_adjoint_realization.2.2.2.2.2.2.1 _ _).mp (hg i)).1
  | zero => exact D.zero_mem
  | add x y hx hy ihx ihy => exact D.add_mem ihx ihy
  | smul a x hx ih => exact D.smul_mem a ih

private theorem low_mode_energy (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (he : ∀ F : D, HasSum (fun i =>
      (e.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2 / mu i) (energy F.val))
    (s : Finset ℕ) (lam : ℝ) (hs : ∀ i ∈ s, (mu i)⁻¹ ≤ lam)
    (F : D) (hmean : mean F.val = 0) (hF : (⟨F.val,hmean⟩ : G0) ∈ modeSpace e s) :
    energy F.val ≤ lam * ‖F.val‖^2 := by
  have hpi : Pi F.val = F.val := by
    rw [centered_suffix_residual.2.2.1, hmean,
      map_zero,sub_zero]
  have hn : HasSum (fun i => (e.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2) (‖F.val‖^2) := by
    have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      (e.repr ⟨Pi F.val,mean_Pi F.val⟩)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
      e.repr.norm_map] at h
    change HasSum _ (‖Pi F.val‖^2) at h
    simpa only [hpi] using h
  apply hasSum_le _ (he F) (hn.mul_left lam)
  intro i
  by_cases hi : i ∈ s
  · simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_right (hs i hi)
        (sq_nonneg (e.repr ⟨Pi F.val,mean_Pi F.val⟩ i))
  · have hz : e.repr ⟨Pi F.val,mean_Pi F.val⟩ i = 0 := by
      simpa only [hpi] using modeSpace_support e s hF i hi
    rw [hz]
    simp

private def trialInclusion (t : Threshold) : Vt0 t →ₗ[ℝ] G0 where
  toFun F := ⟨F.val.val, F.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def trialCut (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ) (t : Threshold) :
    Vt0 t →ₗ[ℝ] modeSpace e s :=
  (((modeProjection e s).toLinearMap.comp (trialInclusion t)).codRestrict
    (modeSpace e s) (fun F => modeProjection_mem e s (trialInclusion t F)))

private theorem lower_rank (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hsupport : ∀ (lam : ℝ) (F : D),
      (∀ i, (mu i)⁻¹ < lam → e.repr ⟨Pi F.val,mean_Pi F.val⟩ i = 0) →
      lam * ‖Pi F.val‖^2 ≤ energy F.val)
    (t : Threshold) (lam : ℝ) (hthreshold : (b * t.val)⁻¹ = lam)
    (s : Finset ℕ) (hs : ∀ i, i ∈ s ↔ (mu i)⁻¹ < lam) :
    Function.Injective (trialCut e s t) ∧ (A t).card - 1 ≤ s.card := by
  classical
  have hinj : Function.Injective (trialCut e s t) := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro F hF
    change F = 0
    have hz : trialCut e s t F = 0 := hF
    obtain ⟨z,_,_,_,hD,_,_,htrial⟩ := actual_stopping_trial_energy t F.val
    have hv : F.val.val = 0 := by
      by_contra hne
      have hlo := (htrial hne).2.2
      rw [hthreshold] at hlo
      let U : D := ⟨F.val.val,hD⟩
      have hhi := hsupport lam U (by
        intro i hi
        have hh := congrArg (fun v : modeSpace e s => e.repr v.val i) hz
        change e.repr (modeProjection e s (trialInclusion t F)) i = _ at hh
        rw [modeProjection_coeff, if_pos ((hs i).mpr hi)] at hh
        have hpi : Pi F.val.val = F.val.val := by
          rw [centered_suffix_residual.2.2.1,
            show mean F.val.val = 0 from F.property, map_zero, sub_zero]
        have hh0 : e.repr (trialInclusion t F) i = 0 := by simpa using hh
        simpa only [U,hpi,trialInclusion,LinearMap.coe_mk,AddHom.coe_mk] using hh0)
      have hpi : Pi U.val = F.val.val := by
        rw [centered_suffix_residual.2.2.1,
          show mean U.val = 0 from F.property,map_zero,sub_zero]
      rw [hpi] at hhi
      exact (not_lt_of_ge hhi hlo).elim
    exact Subtype.ext (Subtype.ext hv)
  refine ⟨hinj, ?_⟩
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  rw [modeSpace_dimension] at hd
  have ht := (actual_stopping_residual t).2.2.2.2.2.2.2.2.2.2.1
  change Module.finrank ℝ (Vt0 t) = (A t).card - 1 at ht
  rwa [ht] at hd

private theorem stopping_mean_zero (t : Threshold) (u : G0) : mean (Qt t u.val) = 0 := by
  have hp : Pi u.val = u.val := by
    rw [centered_suffix_residual.2.2.1,show mean u.val = 0 from u.property,map_zero,sub_zero]
  have he := (actual_stopping_residual t).2.2.2.2.2.2.2.2.1 u.val
  rw [hp] at he
  rw [he]
  exact mean_Pi _

private def stoppingMap (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ) (t : Threshold) :
    modeSpace e s →ₗ[ℝ] Vt0 t where
  toFun u := ⟨⟨Qt t u.val.val,by
    rw [(actual_stopping_residual t).2.1]
    exact Submodule.starProjection_apply_mem _ _⟩,stopping_mean_zero t u.val⟩
  map_add' u v := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' a u := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

private theorem upper_rank (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hg : ∀ i, ((e i).val,(mu i)⁻¹ • (e i).val) ∈ boundaryOperator.graph)
    (he : ∀ F : D, HasSum (fun i =>
      (e.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2 / mu i) (energy F.val))
    (t : Threshold) (lam : ℝ)
    (ht : Real.goldenRatio * t.val * lam < 1)
    (s : Finset ℕ) (hs : ∀ i ∈ s, (mu i)⁻¹ ≤ lam) :
    Function.Injective (stoppingMap e s t) ∧ s.card ≤ (A t).card - 1 := by
  have hinj : Function.Injective (stoppingMap e s t) := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro u hu
    change u = 0
    have hz : Qt t u.val.val = 0 :=
      congrArg (fun F : Vt0 t => F.val.val) hu
    let F : D := ⟨u.val.val,modeSpace_domain e mu hg s u.property⟩
    have helo := low_mode_energy e mu he s lam hs F u.val.property u.property
    have hr := (actual_stopping_residual t).2.2.2.2.2.2.1 (lift F)
    rw [(free_root_least_energy F).2.1] at hr
    have hpi : Pi F.val = u.val.val := by
      rw [centered_suffix_residual.2.2.1,
        show mean F.val = 0 from u.val.property,map_zero,sub_zero]
    rw [hpi,hz,sub_zero, ← (free_root_least_energy F).2.2.2.1] at hr
    have hnn : 0 ≤ Real.goldenRatio * t.val :=
      mul_nonneg Real.goldenRatio_pos.le t.property.1.le
    have hbound := hr.trans (mul_le_mul_of_nonneg_left helo hnn)
    change ‖u.val.val‖^2 ≤ Real.goldenRatio * t.val * (lam * ‖u.val.val‖^2) at hbound
    have hv : u.val.val = 0 := by
      apply norm_eq_zero.mp
      by_contra hne
      have hn : 0 < ‖u.val.val‖^2 := sq_pos_of_ne_zero hne
      have hc : Real.goldenRatio * t.val * (lam * ‖u.val.val‖^2) < ‖u.val.val‖^2 := by
        simpa only [mul_assoc,one_mul] using mul_lt_mul_of_pos_right ht hn
      exact (not_lt_of_ge hbound hc).elim
    exact Subtype.ext (Subtype.ext hv)
  refine ⟨hinj, ?_⟩
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  rw [modeSpace_dimension] at hd
  have ht := (actual_stopping_residual t).2.2.2.2.2.2.2.2.2.2.1
  change Module.finrank ℝ (Vt0 t) = (A t).card - 1 at ht
  rwa [ht] at hd

/-- The inclusive positive eigenvalue count; each basis index counts once. -/
def positiveCount (mu : ℕ → ℝ) (lam : ℝ) : ℕ :=
  {i : ℕ | (mu i)⁻¹ ≤ lam}.ncard

/-- The strict positive eigenvalue count. -/
def strictCount (mu : ℕ → ℝ) (lam : ℝ) : ℕ :=
  {i : ℕ | (mu i)⁻¹ < lam}.ncard

/-- Original one-based positive eigenvalue indexing. -/
def positiveEigenvalue (mu : ℕ → ℝ) (j : ℕ) : ℝ := (mu (j-1))⁻¹

/-- The source constant, shared by the global upper and eigenvalue bounds. -/
def B : ℝ := 2 * Real.goldenRatio / b

private theorem count_gap (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i)
    (hg : ∀ i, ((e i).val,(mu i)⁻¹ • (e i).val) ∈ boundaryOperator.graph) :
    (∀ i, Real.goldenRatio⁻¹ ≤ (mu i)⁻¹) ∧
    (∀ lam : ℝ, lam < Real.goldenRatio⁻¹ → positiveCount mu lam = 0) := by
  have hgap (i : ℕ) : Real.goldenRatio⁻¹ ≤ (mu i)⁻¹ := by
    apply (actual_covariance_eigenspaces (mu i) (hp i)).2.2.2.2.2
      ⟨(e i).val,hg i⟩
    intro hz
    exact e.orthonormal.ne_zero i (Subtype.ext hz)
  refine ⟨hgap,?_⟩
  intro lam hl
  have hs : {i : ℕ | (mu i)⁻¹ ≤ lam} = ∅ := by
    ext i
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    exact not_le.mpr (hl.trans_le (hgap i))
  simp [positiveCount,hs]

private theorem upper_count (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i)
    (hg : ∀ i, ((e i).val,(mu i)⁻¹ • (e i).val) ∈ boundaryOperator.graph)
    (hf : ∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite)
    (he : ∀ F : D, HasSum (fun i =>
      (e.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2 / mu i) (energy F.val)) :
    ∀ lam : ℝ, 0 ≤ lam → (positiveCount mu lam : ℝ) ≤ B * lam := by
  intro lam hl
  have hb : 0 < b := pow_pos BiasedBoundaryTrace.a_pos 2
  have hB : 0 < B := div_pos (mul_pos (by norm_num) Real.goldenRatio_pos) hb
  by_cases hgap : lam < Real.goldenRatio⁻¹
  · rw [(count_gap e mu hp hg).2 lam hgap]
    exact_mod_cast mul_nonneg hB.le hl
  · have hph : 0 < Real.goldenRatio := Real.goldenRatio_pos
    have hlp : 0 < lam := (inv_pos.mpr hph).trans_le (le_of_not_gt hgap)
    have hprod : 1 ≤ Real.goldenRatio * lam := by
      have hh := (inv_le_iff_one_le_mul₀ hph).mp (le_of_not_gt hgap)
      simpa only [mul_comm] using hh
    let t : Threshold := ⟨(2 * Real.goldenRatio * lam)⁻¹,
      inv_pos.mpr (by positivity), by
        apply (inv_lt_one₀ (by positivity : 0 < 2 * Real.goldenRatio * lam)).mpr
        nlinarith⟩
    have ht : Real.goldenRatio * t.val * lam = 1/2 := by
      dsimp [t]
      field_simp
    let s := (cutoff_finite mu hp hf lam).toFinset
    have hs : ∀ i ∈ s, (mu i)⁻¹ ≤ lam := by
      intro i hi
      exact (cutoff_finite mu hp hf lam).mem_toFinset.mp hi
    have hr := (upper_rank e mu hg he t lam (by rw [ht]; norm_num) s hs).2
    have hcard := (actual_stopping_partition t).2.2.2.2.2.2.2.2
    change ((A t).card : ℝ) < 1 / (b * t.val) at hcard
    have hn : (positiveCount mu lam : ℝ) ≤ ((A t).card : ℝ) := by
      have hle : positiveCount mu lam ≤ (A t).card := by
        change {i : ℕ | (mu i)⁻¹ ≤ lam}.ncard ≤ _
        rw [Set.ncard_eq_toFinset_card _ (cutoff_finite mu hp hf lam)]
        exact hr.trans (Nat.sub_le _ _)
      exact_mod_cast hle
    have heq : 1 / (b * t.val) = B * lam := by
      dsimp [t,B]
      field_simp
    exact hn.trans (by rw [← heq]; exact hcard.le)

private theorem lower_strict_count (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i)
    (hf : ∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite)
    (hsupport : ∀ (lam : ℝ) (F : D),
      (∀ i, (mu i)⁻¹ < lam → e.repr ⟨Pi F.val,mean_Pi F.val⟩ i = 0) →
      lam * ‖Pi F.val‖^2 ≤ energy F.val) :
    ∀ lam : ℝ, b⁻¹ < lam → b * lam - 1 ≤ (strictCount mu lam : ℝ) := by
  intro lam hl
  have hb : 0 < b := pow_pos BiasedBoundaryTrace.a_pos 2
  have hlp : 0 < lam := (inv_pos.mpr hb).trans hl
  have hprod : 1 < b * lam := by
    have hh := (inv_lt_iff_one_lt_mul₀ hb).mp hl
    simpa only [mul_comm] using hh
  let t : Threshold := ⟨(b * lam)⁻¹,inv_pos.mpr (mul_pos hb hlp),
    (inv_lt_one₀ (mul_pos hb hlp)).mpr hprod⟩
  have hthreshold : (b * t.val)⁻¹ = lam := by
    dsimp [t]
    field_simp
  let s := (strict_cutoff_finite mu hp hf lam).toFinset
  have hs : ∀ i, i ∈ s ↔ (mu i)⁻¹ < lam := by
    intro i
    exact (strict_cutoff_finite mu hp hf lam).mem_toFinset
  have hr := (lower_rank e mu hsupport t lam hthreshold s hs).2
  have hcard := (actual_stopping_partition t).2.2.2.2.2.2.2.1
  change 1 / t.val ≤ ((A t).card : ℝ) at hcard
  have heq : 1 / t.val = b * lam := by simp [t]
  rw [heq] at hcard
  have hn : (A t).card ≤ s.card + 1 := by omega
  have hnR : ((A t).card : ℝ) ≤ (s.card : ℝ) + 1 := by exact_mod_cast hn
  have hsR : (s.card : ℝ) = (strictCount mu lam : ℝ) := by
    congr 1
    exact (Set.ncard_eq_toFinset_card _ (strict_cutoff_finite mu hp hf lam)).symm
  rw [hsR] at hnR
  linarith

private theorem ordered_eigenvalue_bounds (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hm : Monotone (fun i => (mu i)⁻¹))
    (hf : ∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite)
    (hu : ∀ lam : ℝ, 0 ≤ lam → (positiveCount mu lam : ℝ) ≤ B * lam)
    (hl : ∀ lam : ℝ, b⁻¹ < lam → b * lam - 1 ≤ (strictCount mu lam : ℝ)) :
    ∀ j : ℕ, 1 ≤ j → (j : ℝ) / B ≤ positiveEigenvalue mu j ∧
      positiveEigenvalue mu j ≤ (j : ℝ) / b := by
  intro j hj
  have hb : 0 < b := pow_pos BiasedBoundaryTrace.a_pos 2
  have hB : 0 < B := div_pos (mul_pos (by norm_num) Real.goldenRatio_pos) hb
  have hpj : 0 < positiveEigenvalue mu j := inv_pos.mpr (hp _)
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  constructor
  · have hc : j ≤ positiveCount mu (positiveEigenvalue mu j) := by
      rw [positiveCount, Set.ncard_eq_toFinset_card _ (cutoff_finite mu hp hf _)]
      have hsub : Finset.range j ⊆ (cutoff_finite mu hp hf (positiveEigenvalue mu j)).toFinset := by
        intro i hi
        apply (cutoff_finite mu hp hf (positiveEigenvalue mu j)).mem_toFinset.mpr
        exact hm (by have := Finset.mem_range.mp hi; omega)
      simpa using Finset.card_le_card hsub
    have hcR : (j : ℝ) ≤ (positiveCount mu (positiveEigenvalue mu j) : ℝ) := by exact_mod_cast hc
    exact (div_le_iff₀ hB).mpr (hcR.trans (by simpa [mul_comm] using hu _ hpj.le))
  · by_cases hsmall : positiveEigenvalue mu j ≤ b⁻¹
    · exact hsmall.trans (by simpa [one_div] using div_le_div_of_nonneg_right hjR hb.le)
    · have hc : strictCount mu (positiveEigenvalue mu j) ≤ j-1 := by
        apply (Set.ncard_le_ncard (t := Set.Iio (j-1)) ?_ (Set.finite_Iio _)).trans
          (by simp)
        intro i hi
        change (mu i)⁻¹ < (mu (j-1))⁻¹ at hi
        by_contra hge
        exact (not_lt_of_ge (hm (le_of_not_gt hge)) hi).elim
      have hcR : (strictCount mu (positiveEigenvalue mu j) : ℝ) ≤ (j : ℝ)-1 := by
        have hh : (strictCount mu (positiveEigenvalue mu j) : ℝ) ≤ ((j-1 : ℕ) : ℝ) := by exact_mod_cast hc
        simpa only [Nat.cast_sub hj,Nat.cast_one] using hh
      have hh := hl (positiveEigenvalue mu j) (lt_of_not_ge hsmall)
      apply (le_div_iff₀ hb).mpr
      nlinarith

/-- A full cutoff includes the constant mode exactly when its interval contains zero. -/
def fullModeSpace (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ)
    (includeConstant : Prop) : Submodule ℝ G := by
  classical
  exact (if includeConstant then ℝ ∙ constG 1 else ⊥) ⊔ (modeSpace e s).map G0.subtype

private theorem fullModeSpace_dimension (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ)
    (includeConstant : Prop) [Decidable includeConstant] :
    Module.finrank ℝ (fullModeSpace e s includeConstant) =
      (if includeConstant then 1 else 0) + s.card := by
  classical
  by_cases hinc : includeConstant
  · have hspace : fullModeSpace e s includeConstant =
        (ℝ ∙ constG 1) ⊔ (modeSpace e s).map G0.subtype := by
      simp only [fullModeSpace,if_pos hinc]
    rw [hspace,if_pos hinc]
    have hconst : constG 1 ≠ 0 := by
      intro hz
      have h := centered_suffix_residual.2.1 1
      rw [hz,map_zero] at h
      norm_num at h
    have hd : Disjoint (ℝ ∙ constG 1) ((modeSpace e s).map G0.subtype) := by
      apply Submodule.disjoint_def.mpr
      intro u hc hu
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hc
      obtain ⟨v,hv,he⟩ := hu
      have hm : mean (c • constG 1) = 0 := by rw [← he]; exact v.property
      rw [map_smul,centered_suffix_residual.2.1,smul_eq_mul,mul_one] at hm
      simp [hm]
    have he := Submodule.finrank_sup_add_finrank_inf_eq
      (ℝ ∙ constG 1) ((modeSpace e s).map G0.subtype)
    rw [hd.eq_bot,finrank_bot,add_zero,
      finrank_span_singleton hconst,
      ← (Submodule.equivMapOfInjective G0.subtype G0.subtype_injective (modeSpace e s)).finrank_eq,
      modeSpace_dimension] at he
    exact he

  · have hspace : fullModeSpace e s includeConstant =
        (modeSpace e s).map G0.subtype := by
      simp only [fullModeSpace,if_neg hinc,bot_sup_eq]
    rw [hspace,if_neg hinc,zero_add,← (Submodule.equivMapOfInjective G0.subtype G0.subtype_injective
      (modeSpace e s)).finrank_eq,modeSpace_dimension]

/-- The complete source counting inequalities on one actual ordered spectral family.
The two projections count inclusive and strict cutoffs, including multiplicities. -/
theorem actual_spectral_counting :
    B = 2 * Real.goldenRatio^3 ∧
    ∃ (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ),
      (∀ i, 0 < mu i) ∧ Antitone mu ∧ Tendsto mu atTop (nhds 0) ∧
      Monotone (fun i => (mu i)⁻¹) ∧ Tendsto (fun i => (mu i)⁻¹) atTop atTop ∧
      (∀ i, ((e i).val,(mu i)⁻¹ • (e i).val) ∈ boundaryOperator.graph) ∧
      (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
      (∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) ∧
      (∀ lam : ℝ, ∃ s q : Finset ℕ,
        (∀ i, i ∈ s ↔ (mu i)⁻¹ ≤ lam) ∧
        (∀ i, i ∈ q ↔ (mu i)⁻¹ < lam) ∧
        (modeProjection e s).range = modeSpace e s ∧
        (modeProjection e q).range = modeSpace e q ∧
        (modeProjection k s).range = modeSpace k s ∧
        (modeProjection k q).range = modeSpace k q ∧
        (∀ u : G0, u ∈ modeSpace e s ↔ ∀ i, i ∉ s → e.repr u i = 0) ∧
        (∀ u : G0, u ∈ modeSpace e q ↔ ∀ i, i ∉ q → e.repr u i = 0) ∧
        (∀ x : K, x ∈ modeSpace k s ↔ ∀ i, i ∉ s → k.repr x i = 0) ∧
        (∀ x : K, x ∈ modeSpace k q ↔ ∀ i, i ∉ q → k.repr x i = 0) ∧
        Module.finrank ℝ (modeSpace e s) = positiveCount mu lam ∧
        Module.finrank ℝ (modeSpace e q) = strictCount mu lam ∧
        Module.finrank ℝ (modeSpace k s) = positiveCount mu lam ∧
        Module.finrank ℝ (modeSpace k q) = strictCount mu lam ∧
        Module.finrank ℝ (fullModeSpace e s (0 ≤ lam)) =
          (if 0 ≤ lam then 1 else 0) + positiveCount mu lam ∧
        Module.finrank ℝ (fullModeSpace e q (0 < lam)) =
          (if 0 < lam then 1 else 0) + strictCount mu lam) ∧
      positiveCount mu 0 = 0 ∧ strictCount mu 0 = 0 ∧
      (∀ lam : ℝ, 0 ≤ lam → lam < Real.goldenRatio⁻¹ → positiveCount mu lam = 0) ∧
      (∀ lam : ℝ, 0 ≤ lam → (positiveCount mu lam : ℝ) ≤ B * lam) ∧
      (∀ lam : ℝ, b⁻¹ < lam → b * lam - 1 ≤ (strictCount mu lam : ℝ) ∧
        b * lam - 1 ≤ (positiveCount mu lam : ℝ)) ∧
      (∀ lam : ℝ, 2 / b ≤ lam →
        (b/2) * lam ≤ (positiveCount mu lam : ℝ) ∧
        (positiveCount mu lam : ℝ) ≤ B * lam) ∧
      (∀ j : ℕ, 1 ≤ j → (j : ℝ) / B ≤ positiveEigenvalue mu j ∧
        positiveEigenvalue mu j ≤ (j : ℝ) / b) := by
  classical
  constructor
  · dsimp [B,BiasedBoundaryTrace.b,FiniteSourceMass.a]
    field_simp
  obtain ⟨e,k,mu,hp,hm,ht,hmi,hti,hg,hk,hC,hf,he,hsupport⟩ := actual_spectral_form_energy
  have hu := upper_count e mu hp hg hf he
  have hl := lower_strict_count e mu hp hf hsupport
  have hcount (lam : ℝ) : strictCount mu lam ≤ positiveCount mu lam :=
    Set.ncard_le_ncard (fun i hi => (show (mu i)⁻¹ < lam from hi).le) (cutoff_finite mu hp hf lam)
  have hb : 0 < b := pow_pos BiasedBoundaryTrace.a_pos 2
  refine ⟨e,k,mu,hp,hm,ht,hmi,hti,hg,hk,hC,?_,?_,?_,?_,hu,?_,?_,
    ordered_eigenvalue_bounds mu hp hmi hf hu hl⟩
  · intro lam
    let s := (cutoff_finite mu hp hf lam).toFinset
    let q := (strict_cutoff_finite mu hp hf lam).toFinset
    have hs : s.card = positiveCount mu lam :=
      (Set.ncard_eq_toFinset_card _ (cutoff_finite mu hp hf lam)).symm
    have hq : q.card = strictCount mu lam :=
      (Set.ncard_eq_toFinset_card _ (strict_cutoff_finite mu hp hf lam)).symm
    exact ⟨s,q,(fun _ => (cutoff_finite mu hp hf lam).mem_toFinset),
      (fun _ => (strict_cutoff_finite mu hp hf lam).mem_toFinset),
      modeProjection_range e s,modeProjection_range e q,
      modeProjection_range k s,modeProjection_range k q,
      modeSpace_iff e s,modeSpace_iff e q,modeSpace_iff k s,modeSpace_iff k q,
      (modeSpace_dimension e s).trans hs,(modeSpace_dimension e q).trans hq,
      (modeSpace_dimension k s).trans hs,(modeSpace_dimension k q).trans hq,
      (fullModeSpace_dimension e s (0 ≤ lam)).trans (congrArg (_ + ·) hs),
      (fullModeSpace_dimension e q (0 < lam)).trans (congrArg (_ + ·) hq)⟩
  · exact (count_gap e mu hp hg).2 0 (inv_pos.mpr Real.goldenRatio_pos)
  · have h := hcount 0
    rw [(count_gap e mu hp hg).2 0 (inv_pos.mpr Real.goldenRatio_pos)] at h
    exact Nat.eq_zero_of_le_zero h
  · intro lam _ hl
    exact (count_gap e mu hp hg).2 lam hl
  · intro lam hlam
    refine ⟨hl lam hlam,(hl lam hlam).trans ?_⟩
    exact_mod_cast hcount lam
  · intro lam hlam
    have hprod : 2 ≤ b * lam := by
      have hh := (div_le_iff₀ hb).mp hlam
      nlinarith
    have hthreshold : b⁻¹ < lam := by
      apply (inv_lt_iff_one_lt_mul₀ hb).mpr
      nlinarith
    have hcR : (strictCount mu lam : ℝ) ≤ (positiveCount mu lam : ℝ) := by
      exact_mod_cast hcount lam
    have hh := (hl lam hthreshold).trans hcR
    have hl0 : 0 ≤ lam := (div_pos (by norm_num) hb).le.trans hlam
    exact ⟨by nlinarith,hu lam hl0⟩

#print axioms actual_spectral_counting

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting

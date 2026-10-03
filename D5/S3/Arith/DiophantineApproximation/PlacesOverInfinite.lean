/- GID: D5/S3/Arith/DiophantineApproximation/PlacesOverInfinite
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/PlacesOverInfinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An absolute value above an infinite place is an infinite place upstairs. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

-- Used only inside proofs.

public section

open Filter NumberField

/-- An absolute value of `ℂ` that restricts to the usual absolute value on `ℝ` is the usual
absolute value. -/
theorem AbsoluteValue.eq_norm_of_apply_ofReal {N : AbsoluteValue ℂ ℝ}
    (h : ∀ r : ℝ, N (r : ℂ) = |r|) (z : ℂ) : N z = ‖z‖ := by
  have hI : N Complex.I = 1 := by
    have h2 : N Complex.I ^ 2 = 1 := by
      rw [← map_pow, Complex.I_sq, show ((-1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num, h]
      norm_num
    nlinarith [N.nonneg Complex.I]
  have hupper : ∀ y : ℂ, N y ≤ 2 * ‖y‖ := by
    intro y
    have hy : y = (y.re : ℂ) + (y.im : ℂ) * Complex.I := (Complex.re_add_im y).symm
    calc N y ≤ N ((y.re : ℂ)) + N ((y.im : ℂ) * Complex.I) := by
          conv_lhs => rw [hy]
          exact N.add_le _ _
      _ = |y.re| + |y.im| := by rw [map_mul, hI, mul_one, h, h]
      _ ≤ 2 * ‖y‖ := by
          have h1 := Complex.abs_re_le_norm y
          have h2 := Complex.abs_im_le_norm y
          linarith
  have hle : ∀ y : ℂ, N y ≤ ‖y‖ := by
    intro y
    by_contra hcon
    push Not at hcon
    have hNy : 0 < N y := lt_of_le_of_lt (norm_nonneg y) hcon
    set q := ‖y‖ / N y with hq
    have hq0 : 0 ≤ q := div_nonneg (norm_nonneg y) hNy.le
    have hq1 : q < 1 := (div_lt_one hNy).mpr hcon
    have hone : ∀ n : ℕ, (1 : ℝ) ≤ 2 * q ^ n := by
      intro n
      have hn := hupper (y ^ n)
      rw [map_pow, norm_pow] at hn
      rw [hq, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hNy n), one_mul]
      exact hn
    have hlim : Tendsto (fun n : ℕ => 2 * q ^ n) atTop (nhds 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rwa [abs_of_nonneg hq0])).const_mul 2
    linarith [ge_of_tendsto' hlim hone]
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · refine le_antisymm (hle z) ?_
    have h1 := hle z⁻¹
    rw [map_inv₀, norm_inv] at h1
    have hNz : 0 < N z := N.pos hz0
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    exact (inv_le_inv₀ hNz hnz).mp h1

theorem AbsoluteValue.isInfinitePlace_of_realRingHom {F : Type*} [Field F]
    {w : AbsoluteValue F ℝ} (ι : ℝ →+* w.Completion) (hι : ∀ r : ℝ, ‖ι r‖ = ‖r‖) :
    IsInfinitePlace w := by
  let _ : Algebra ℝ w.Completion := ι.toAlgebra
  have hmap : ∀ r : ℝ, algebraMap ℝ w.Completion r = ι r := fun _ => rfl
  let _ : NormedAlgebra ℝ w.Completion :=
    { norm_smul_le := fun r x => by
        rw [Algebra.smul_def, hmap, norm_mul, hι] }
  obtain ⟨ψ, hψ⟩ : ∃ ψ : w.Completion →+* ℂ, ∀ x, ‖ψ x‖ = ‖x‖ := by
    rcases NormedAlgebra.Real.nonempty_algEquiv_or w.Completion with hr | hr
    · obtain ⟨e⟩ := hr
      have hs : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖ := fun r => by
        rw [show e.symm r = algebraMap ℝ w.Completion r by simpa using e.symm.commutes r, hmap, hι]
      refine ⟨Complex.ofRealHom.comp e.toRingHom, fun x => ?_⟩
      rw [RingHom.comp_apply]
      rw [show (Complex.ofRealHom (e.toRingHom x)) = ((e x : ℝ) : ℂ) from rfl,
        Complex.norm_real, ← hs (e x), AlgEquiv.symm_apply_apply]
    · obtain ⟨e⟩ := hr
      have hs : ∀ r : ℝ, ‖e.symm (r : ℂ)‖ = ‖r‖ := fun r => by
        rw [show e.symm (r : ℂ) = algebraMap ℝ w.Completion r by
          simpa using e.symm.commutes r, hmap, hι]
      let N : AbsoluteValue ℂ ℝ :=
        { toFun := fun z => ‖e.symm z‖,
          map_mul' := fun x y => by rw [map_mul, norm_mul],
          nonneg' := fun _ => norm_nonneg _,
          eq_zero' := fun z => by rw [norm_eq_zero, EmbeddingLike.map_eq_zero_iff],
          add_le' := fun x y => by rw [map_add]; exact norm_add_le _ _ }
      have hNr : ∀ r : ℝ, N (r : ℂ) = |r| := fun r => by
        change ‖e.symm (r : ℂ)‖ = |r|
        rw [hs r, Real.norm_eq_abs]
      have hN : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖ := AbsoluteValue.eq_norm_of_apply_ofReal hNr
      refine ⟨e.toRingHom, fun x => ?_⟩
      change ‖e x‖ = ‖x‖
      rw [← hN (e x), AlgEquiv.symm_apply_apply]
  refine ⟨ψ.comp ((UniformSpace.Completion.coeRingHom).comp (WithAbs.equiv w).symm.toRingHom), ?_⟩
  refine AbsoluteValue.ext fun x => ?_
  rw [place_apply, RingHom.comp_apply, hψ]
  change ‖((WithAbs.toAbs w x : WithAbs w) : w.Completion)‖ = w x
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]

open NumberField.InfinitePlace in
/-- An isometric copy of `ℝ` inside the completion of `F` at an absolute value lying over an
infinite place of `K`. -/
theorem NumberField.exists_realRingHom_completion_of_liesOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : NumberField.InfinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ ι : ℝ →+* w.Completion, ∀ r : ℝ, ‖ι r‖ = ‖r‖ := by
  have hmap : Isometry (WithAbs.map v.1 w (algebraMap K F)) := by
    apply (AddMonoidHomClass.isometry_iff_norm _).mpr
    intro x
    change w (algebraMap K F x.ofAbs) = v.1 x.ofAbs
    exact congrArg (fun a : AbsoluteValue K ℝ => a x.ofAbs)
      (AbsoluteValue.LiesOver.comp_eq w v.1)
  let g : (v.1).Completion →+* w.Completion :=
    UniformSpace.Completion.mapRingHom (WithAbs.map v.1 w (algebraMap K F))
      hmap.continuous
  have hg : ∀ y : (v.1).Completion, ‖g y‖ = ‖y‖ :=
    (AddMonoidHomClass.isometry_iff_norm g).mp
      hmap.isometry_mapRingHom
  have hq : ∀ y : NumberField.InfinitePlace.Completion v,
      ‖(NumberField.InfinitePlace.Completion.equiv v) y‖ = ‖y‖ := fun y =>
    NumberField.InfinitePlace.Completion.norm_toCompletion v y
  rcases v.isReal_or_isComplex with hv | hv
  · refine ⟨g.comp ((NumberField.InfinitePlace.Completion.equiv v).toRingHom.comp
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toRingHom),
      fun r => ?_⟩
    have hemb : ∀ y : NumberField.InfinitePlace.Completion v,
        ‖NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv y‖ = ‖y‖ :=
      (AddMonoidHomClass.isometry_iff_norm _).mp
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv)
    have hr : ‖(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r‖ = ‖r‖ := by
      rw [← hemb ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r),
        ← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv,
        RingEquiv.apply_symm_apply]
    change ‖g ((NumberField.InfinitePlace.Completion.equiv v)
      ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r))‖ = ‖r‖
    rw [hg, hq, hr]
  · refine ⟨g.comp ((NumberField.InfinitePlace.Completion.equiv v).toRingHom.comp
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toRingHom.comp
        Complex.ofRealHom)), fun r => ?_⟩
    have hemb : ∀ y : NumberField.InfinitePlace.Completion v,
        ‖NumberField.InfinitePlace.Completion.extensionEmbedding v y‖ = ‖y‖ :=
      (AddMonoidHomClass.isometry_iff_norm _).mp
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v)
    have hr : ‖(NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
        (r : ℂ)‖ = ‖r‖ := by
      rw [← hemb ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
          (r : ℂ)),
        ← NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv,
        RingEquiv.apply_symm_apply, Complex.norm_real]
    change ‖g ((NumberField.InfinitePlace.Completion.equiv v)
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
        (Complex.ofRealHom r)))‖ = ‖r‖
    rw [hg, hq]
    exact hr

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Layer 0.1, the archimedean half.** An absolute value of `F` lying over an infinite place of
`K` is the absolute value of an infinite place of `F`. ⚠ No finiteness of `F / K` is used. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w :=
  let ⟨ι, hι⟩ := exists_realRingHom_completion_of_liesOver v w
  AbsoluteValue.isInfinitePlace_of_realRingHom ι hι


end NumberField

section Examples

end Examples

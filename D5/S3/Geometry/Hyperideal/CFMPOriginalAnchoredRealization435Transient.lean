import D5.S3.Geometry.Hyperideal.CFMPOriginalFutureFrame435Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology Matrix.Norms.Elementwise
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicTopology
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalFutureFrame435Transient

namespace CFMPOriginalAnchoredRealization435Transient

def realize (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hcenter : 0 < (center ᵥ* M) 3) (v : cutBody l) : HyperbolicThreeSpace :=
  project ((radial l v.val) ᵥ* M)
    ((CFMPActualPlaneIsometry435Transient.frame_quadratic l M hG _).trans
      ((shared_radial_body l hl).2.2.2.2.2.2.2.2.1 v.val v.property))
    (future_whole_body l hl M hG hcenter v).1

theorem realize_contract (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hcenter : 0 < (center ᵥ* M) 3) (v : cutBody l) :
    ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (realize l hl M hG hcenter v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)) := by
  refine ⟨_,rfl,?_,(future_whole_body l hl M hG hcenter v).1,rfl⟩
  exact (CFMPActualPlaneIsometry435Transient.frame_quadratic l M hG _).trans
    ((shared_radial_body l hl).2.2.2.2.2.2.2.2.1 v.val v.property)

theorem realize_lift (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hcenter : 0 < (center ᵥ* M) 3) (v : cutBody l) :
    lift (realize l hl M hG hcenter v) = (radial l v.val) ᵥ* M := by
  obtain ⟨y,hy,hu,ht,hcoord⟩ := realize_contract l hl M hG hcenter v
  exact (lift_of_coordinates _ y hu ht hcoord).trans hy

theorem realize_continuous (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hcenter : 0 < (center ᵥ* M) 3) : Continuous (realize l hl M hG hcenter) := by
  let y : cutBody l → Fin 4 → ℝ := fun v => (radial l v.val) ᵥ* M
  have hy : Continuous y := by
    have hr : Continuous (fun v : cutBody l => radial l v.val) :=
      (shared_radial_body l hl).2.2.2.2.1.domRestrict
    apply continuous_pi
    intro k
    change Continuous (fun v : cutBody l => ∑ i, radial l v.val i * M i k)
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp hr).mul continuous_const)
  have hyk (k : Fin 4) : Continuous (fun v => y v k) := (continuous_apply k).comp hy
  have hd (v : cutBody l) : 0 < y v 3-y v 2 :=
    (future_whole_body l hl M hG hcenter v).2
  have hden : Continuous (fun v => y v 3-y v 2) := (hyk 3).sub (hyk 2)
  let coords : cutBody l → UpperHalfSpace ℂ := fun v =>
    (realize l hl M hG hcenter v).coordinates
  have hc : Continuous coords := by
    apply Continuous.subtype_mk
    apply (WithLp.prod_continuous_toLp 2 ℂ ℝ).comp
    apply Continuous.prodMk
    · have ha := Complex.continuous_ofReal.comp ((hyk 0).div hden (fun v => (hd v).ne'))
      have hb := Complex.continuous_ofReal.comp ((hyk 1).div hden (fun v => (hd v).ne'))
      convert ha.add (hb.mul (continuous_const (y := Complex.I))) using 1
      funext v
      change Complex.mk (y v 0/(y v 3-y v 2)) (y v 1/(y v 3-y v 2)) =
        Complex.ofReal (y v 0/(y v 3-y v 2)) +
          Complex.ofReal (y v 1/(y v 3-y v 2)) * Complex.I
      apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.mul_re,
        Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im] <;> ring
    · exact continuous_const.div hden (fun v => (hd v).ne')
  exact coordinatesHomeomorph.symm.continuous.comp hc

theorem realize_injective (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hcenter : 0 < (center ᵥ* M) 3) :
    Function.Injective (realize l hl M hG hcenter) := by
  intro v w heq
  have h := congrArg lift heq
  rw [realize_lift,realize_lift] at h
  have hm : IsUnit M := M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hM)
  have hr := Matrix.vecMul_injective_of_isUnit hm h
  exact Subtype.ext ((shared_radial_body l hl).2.2.2.2.2.1 v.property w.property hr)

theorem realize_compact (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hcenter : 0 < (center ᵥ* M) 3) :
    IsCompact (range (realize l hl M hG hcenter)) := by
  letI : CompactSpace (cutBody l) := isCompact_iff_compactSpace.mp (shared_radial_body l hl).1
  exact isCompact_range (realize_continuous l hl M hG hcenter)

-- This equality identifies the supplied original map pointwise, not merely its volume.
theorem realize_eq_original (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hcenter : 0 < (center ᵥ* M) 3) (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))) :
    realize l hl M hG hcenter = f := by
  funext v
  apply lift_injective
  rw [realize_lift]
  obtain ⟨y,hy,hu,ht,hcoord⟩ := hf v
  exact ((lift_of_coordinates (f v) y hu ht hcoord).trans hy).symm

end CFMPOriginalAnchoredRealization435Transient

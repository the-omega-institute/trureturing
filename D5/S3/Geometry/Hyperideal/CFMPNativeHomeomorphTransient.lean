import D5.S3.Geometry.Hyperideal.CFMPNativeInverseTransient
import Mathlib.Topology.Homeomorph.Lemmas

/-! UNCOMPILED transient source-only structural repair of the supplied
homeomorph.lean. The imported inverse supplier and native input structure are
unchanged. Every private helper below is consumed by the original public
statement. No compiler option or resource budget is changed. All new source
has zero canonical retention; independent compilation and acceptance belong
to the parent. -/

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments

namespace NativeCornerExtractionSource
open D5.S3.Geometry.HyperbolicTopology

-- Isolate the scalar-to-complex conversion from the geometric projection.
private theorem homeomorph_continuous_complex_mk
    {X : Type*} [TopologicalSpace X] (a b : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => Complex.mk (a x) (b x)) := by
  have ha' := Complex.continuous_ofReal.comp ha
  have hb' := Complex.continuous_ofReal.comp hb
  convert ha'.add (hb'.mul (continuous_const (y := Complex.I))) using 1
  funext x
  change Complex.mk (a x) (b x) =
    Complex.ofReal (a x) + Complex.ofReal (b x) * Complex.I
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] <;> ring

-- Only finite row multiplication is elaborated in this declaration.
private theorem homeomorph_continuous_row_combination
    {X : Type*} [TopologicalSpace X] (r : X → Fin 4 → ℝ)
    (C : Matrix (Fin 4) (Fin 4) ℝ) (hr : Continuous r) :
    Continuous (fun x => (r x) ᵥ* C) := by
  apply continuous_pi
  intro k
  change Continuous (fun x : X => ∑ i, r x i * C i k)
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hr).mul continuous_const

-- The proof-dependent project/coordinates coercions are confined here.
-- The formulas and strict future-sheet denominator are the original ones.
private theorem homeomorph_continuous_project_coordinates
    {X : Type*} [TopologicalSpace X] (y : X → Fin 4 → ℝ)
    (hy : Continuous y)
    (hyunit : ∀ x, lorentz (y x) (y x) = -1)
    (hytime : ∀ x, 0 < y x 3) :
    Continuous (fun x => (project (y x) (hyunit x) (hytime x)).coordinates) := by
  have hyk (k : Fin 4) : Continuous (fun x => y x k) :=
    (continuous_apply k).comp hy
  have hden : Continuous (fun x => y x 3 - y x 2) :=
    (hyk 3).sub (hyk 2)
  have hd (x : X) : 0 < y x 3 - y x 2 :=
    future_den (y x) (hyunit x) (hytime x)
  apply Continuous.subtype_mk
  apply (WithLp.prod_continuous_toLp 2 ℂ ℝ).comp
  apply Continuous.prodMk
  · exact homeomorph_continuous_complex_mk
      (fun x => y x 0 / (y x 3 - y x 2))
      (fun x => y x 1 / (y x 3 - y x 2))
      ((hyk 0).div hden (fun x => (hd x).ne'))
      ((hyk 1).div hden (fun x => (hd x).ne'))
  · exact continuous_const.div hden (fun x => (hd x).ne')

-- Recover the very same F from its lift; no replacement forward map is chosen.
private theorem homeomorph_continuous_of_exact_lift
    {X : Type*} [TopologicalSpace X] (F : X → HyperbolicThreeSpace)
    (y : X → Fin 4 → ℝ) (hlift : ∀ x, lift (F x) = y x)
    (hy : Continuous y) : Continuous F := by
  have hyunit (x : X) : lorentz (y x) (y x) = -1 := by
    rw [← hlift x]
    exact lift_unit (F x)
  have hytime (x : X) : 0 < y x 3 := by
    rw [← hlift x]
    exact lift_time (F x)
  have hcoords := homeomorph_continuous_project_coordinates y hy hyunit hytime
  have hproject (x : X) : project (y x) (hyunit x) (hytime x) = F x := by
    apply lift_injective
    exact (lift_of_coordinates _ _ (hyunit x) (hytime x) rfl).trans (hlift x).symm
  exact (coordinatesHomeomorph.symm.continuous.comp hcoords).congr hproject

-- Project only the needed facts from the existing radial-body supplier.
private theorem homeomorph_native_radial_continuous (d : NativeSupportCorners) :
    Continuous (fun v : cutBody (actualLengths d) => radial (actualLengths d) v.val) := by
  obtain ⟨_, _, _, _, hradial, _, _, _, _, _⟩ :=
    shared_radial_body (actualLengths d) (actualLengths_positive d)
  exact hradial.domRestrict

private theorem homeomorph_native_cutBody_compact (d : NativeSupportCorners) :
    IsCompact (cutBody (actualLengths d)) :=
  (shared_radial_body (actualLengths d) (actualLengths_positive d)).1

private theorem homeomorph_native_forward_continuous (d : NativeSupportCorners)
    (F : cutBody (actualLengths d) → HyperbolicThreeSpace)
    (hlift : ∀ v, lift (F v) =
      (radial (actualLengths d) v.val) ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) :
    Continuous F := by
  let r : cutBody (actualLengths d) → Fin 4 → ℝ :=
    fun v => radial (actualLengths d) v.val
  have hr : Continuous r := homeomorph_native_radial_continuous d
  have hy := homeomorph_continuous_row_combination r d.cap hr
  exact homeomorph_continuous_of_exact_lift F (fun v => (r v) ᵥ* d.cap) hlift hy

-- Package the supplied F and I once, with explicit pointwise equalities.
-- The final theorem uses these equalities instead of unfolding this package.
private theorem homeomorph_of_exact_maps
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] (P : Set Y)
    (F : X → Y) (I : P → X) (hrange : Set.range F = P)
    (hF : Continuous F) (hright : ∀ p, F (I p) = p.val)
    (hleft : ∀ v (hp : F v ∈ P), I ⟨F v, hp⟩ = v) :
    ∃ h : X ≃ₜ P,
      (∀ v, (h v).val = F v) ∧ (∀ p, h.symm p = I p) := by
  have hmem (v : X) : F v ∈ P := by
    rw [← hrange]
    exact Set.mem_range_self v
  let e : X ≃ P :=
    { toFun := fun v => ⟨F v, hmem v⟩
      invFun := I
      left_inv := fun v => hleft v (hmem v)
      right_inv := fun p => Subtype.ext (hright p) }
  have he : Continuous (e : X → P) := hF.subtype_mk hmem
  let h : X ≃ₜ P := he.homeoOfEquivCompactToT2
  exact ⟨h, fun _ => rfl, fun _ => rfl⟩

theorem native_body_exact_homeomorph (d : NativeSupportCorners) :
    let l := actualLengths d
    let C : Matrix (Fin 4) (Fin 4) ℝ := d.cap
    ∃ h : cutBody l ≃ₜ d.P,
      (∀ v, lift (h v).val = (radial l v.val) ᵥ* C) ∧
      (∀ p, let a := (lift p.val) ᵥ* C⁻¹
        let s := ∑ i, a i
        0 < s ∧ (h.symm p).val = (fun i => a i / s) ∧
          gramQuadratic l a = -1 ∧
          gramQuadratic l (h.symm p).val = -1 / s ^ 2 ∧
          Real.sqrt (-gramQuadratic l (h.symm p).val) = 1 / s ∧
          radial l (h.symm p).val = a) ∧
      IsCompact d.P ∧ d.P.Nonempty := by
  classical
  -- Introduce the exact original let bindings without restating the target.
  intro l C
  obtain ⟨F, hlift, hrange, _, I, hI, hright, hleft⟩ :=
    NativeFutureSheet.native_body_exact_inverse d
  have hF : Continuous F := homeomorph_native_forward_continuous d F hlift
  letI : CompactSpace (cutBody l) :=
    isCompact_iff_compactSpace.mp (homeomorph_native_cutBody_compact d)
  obtain ⟨h, hforward, hinverse⟩ :=
    homeomorph_of_exact_maps d.P F I hrange hF hright hleft
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · intro v
    exact (congrArg lift (hforward v)).trans (hlift v)
  · intro p
    simpa only [hinverse p] using hI p
  · simpa only [hrange] using isCompact_range hF
  · exact ⟨d.corner 0 1, d.corner_mem 0 1 (by decide)⟩

end NativeCornerExtractionSource

#check NativeCornerExtractionSource.native_body_exact_homeomorph
#print axioms NativeCornerExtractionSource.native_body_exact_homeomorph

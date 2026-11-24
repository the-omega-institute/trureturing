/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedMultiplicityOne
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedMultiplicityOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every lawful Leech mixed field is a unique scalar multiple of the native field. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedFieldScalars
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeQuadraticZhuCurrent
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeReverseMixedChargedZhu
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddCurrentTopDetection

/-!
Quadratic covariance gives a common ground map in each parity direction.
The transverse charged identities make these maps scalar, and the current
coefficients determine the entire lawful mixed field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace (actualGrade)
open LatticeLightConeCoordinates (E g g_symm g_zero_right chargeVector standardBasis)
open LatticeRealNullFrame (complexify)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open HalfFock.NormFourLowestGrades (actualGrade_one_eq_span)
open MvPolynomial (X)

open private zhuTopEvaluation_smul_input from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedChargedZhu

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det}

local instance multiplicityTopAddCommGroup (t : Bool) : AddCommGroup (twistedTop D hu t) :=
  @Submodule.addCommGroup ℂ (Twisted D hu t) _ _ _ (twistedTop D hu t)

private theorem halfOscillator_basis_eq (j : Fin D.rank) (x : ActualGround D hu) :
    oddTopHalfOscillator D hu (standardBasis D j) x = quadraticOddTopOscillator D hu j x := by
  apply Subtype.ext
  apply Subtype.ext
  exact oddTopHalfOscillator_basis_val j x

private theorem halfOscillator_eq_sum (w : E D) (x : ActualGround D hu) :
    oddTopHalfOscillator D hu w x = ∑ j, w j • quadraticOddTopOscillator D hu j x := by
  have hw : (∑ j, w j • standardBasis D j) = w := by
    simpa only [standardBasis, Pi.basisFun_repr] using (standardBasis D).sum_repr w
  calc
    _ = oddTopHalfOscillator D hu (∑ j, w j • standardBasis D j) x :=
      congrArg (fun a => oddTopHalfOscillator D hu a x) hw.symm
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        halfOscillator_basis_eq]

private theorem evenCurrent_vector (F : LawfulMixedField D hu false)
    (f : Module.End ℂ (ActualGround D hu))
    (h : ∀ i x, zhuTopEvaluation F (evenTopGroundEquiv D hu x) (oddCurrent D i) =
      quadraticOddTopOscillator D hu i (f x))
    (v : E D) (x : ActualGround D hu) :
    zhuTopEvaluation F (evenTopGroundEquiv D hu x) (oddCurrentVector D v) =
      oddTopHalfOscillator D hu v (f x) := by
  simp only [oddCurrentVector_eq_sum, map_sum, map_smul, h, halfOscillator_eq_sum]

private theorem reverseCurrentGroundMap_eq (F : LawfulMixedField D hu true)
    (f : Module.End ℂ (ActualGround D hu))
    (h : ∀ i j x, zhuTopEvaluation F (quadraticOddTopOscillator D hu j x) (oddCurrent D i) =
      (D.G i j : ℂ) • evenTopGroundEquiv D hu (f x))
    (v w : E D) (x : ActualGround D hu) :
    reverseCurrentGroundMap F v w x = g D v w • f x := by
  have entry (i : Fin D.rank) :
      zhuCurrentEvaluation F i (oddTopHalfOscillator D hu w x) =
        ∑ j, w j • ((D.G i j : ℂ) • evenTopGroundEquiv D hu (f x)) := by
    rw [halfOscillator_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    exact congrArg (fun y => w j • y) (h i j x)
  let read : twistedTop D hu false →ₗ[ℂ] ActualGround D hu :=
    (evenTopGroundEquiv D hu).symm.toLinearMap
  rw [reverseCurrentGroundMap_apply]
  change read (zhuTopEvaluation F (oddTopHalfOscillator D hu w x) (oddCurrentVector D v)) = _
  simp only [oddCurrentVector_eq_sum, map_sum, map_smul]
  calc
    _ = ∑ i, v i • (∑ j, w j • ((D.G i j : ℂ) • f x)) := by
      apply Finset.sum_congr rfl
      intro i _
      change v i • read (zhuCurrentEvaluation F i (oddTopHalfOscillator D hu w x)) = _
      rw [entry]
      simp only [map_sum, map_smul, read, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    _ = _ := by
      simp only [g, Finset.sum_smul, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show v i * (w j * (D.G i j : ℂ)) = v i * (D.G i j : ℂ) * w j by ring]

private theorem evenChargedZero_apply
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (c : Charge D) (x : ActualGround D hu) :
    fixedChargedZero hD false c (evenTopGroundEquiv D hu x) =
      ((2 : ℂ) * chargeScalar D c) • evenTopGroundEquiv D hu (groundAction D hu c x) := by
  have h := LinearMap.congr_fun (fixedChargedTopZero_conj D hu hD c) x
  change (evenTopGroundEquiv D hu).symm
      (fixedChargedZero hD false c (evenTopGroundEquiv D hu x)) =
    ((2 : ℂ) * chargeScalar D c) • groundAction D hu c x at h
  apply (evenTopGroundEquiv D hu).symm.injective
  rw [map_smul, LinearEquiv.symm_apply_apply]
  exact h

private theorem evenCurrent_ground_commutes
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (F : LawfulMixedField D hu false) (f : Module.End ℂ (ActualGround D hu))
    (h : ∀ i x, zhuTopEvaluation F (evenTopGroundEquiv D hu x) (oddCurrent D i) =
      quadraticOddTopOscillator D hu i (f x))
    (c : Charge D) (v : E D) (hv : g D v (chargeVector c) = 0)
    (hv0 : v ≠ 0) (x : ActualGround D hu) :
    groundAction D hu c (f x) = f (groundAction D hu c x) := by
  have hw : g D (chargeVector c) v = 0 := (g_symm D _ _).trans hv
  have hc := chargedZhu_currentVector_commutator hD F c v (evenTopGroundEquiv D hu x)
  change fixedChargedZero hD true c
      (zhuTopEvaluation F (evenTopGroundEquiv D hu x) (oddCurrentVector D v)) -
    (show twistedTop D hu true from
      zhuTopEvaluation F (fixedChargedZero hD false c (evenTopGroundEquiv D hu x))
        (oddCurrentVector D v)) = _ at hc
  rw [hv, neg_zero, zero_smul, sub_eq_zero, evenChargedZero_apply,
    zhuTopEvaluation_smul_input F _ _ _ 1 (oddCurrentVector_grade_one v)] at hc
  simp only [evenCurrent_vector F f h] at hc
  rw [fixedChargedZero_oddTopHalfOscillator, hw, mul_zero, zero_smul, sub_zero] at hc
  exact oddTopHalfOscillator_injective v hv0
    (smul_right_injective _ (fixedChargedScalar_ne_zero D c) hc)

private theorem ground_scalar_of_commutes
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (f : Module.End ℂ (ActualGround D hu))
    (h : ∀ c x, groundAction D hu c (f x) = f (groundAction D hu c x)) :
    ∃ z : ℂ, f = z • 1 := by
  let C := (evenTopGroundEquiv D hu).symm.conjAlgEquiv ℂ
  let A := C.symm f
  have hcomm (c : Charge D) :
      A * fixedChargedTopZero D hu hD c = fixedChargedTopZero D hu hD c * A := by
    apply C.injective
    rw [map_mul, map_mul]
    change C (C.symm f) * C (fixedChargedTopZero D hu hD c) =
      C (fixedChargedTopZero D hu hD c) * C (C.symm f)
    have hC := fixedChargedTopZero_conj D hu hD c
    change C (fixedChargedTopZero D hu hD c) = _ at hC
    rw [AlgEquiv.apply_symm_apply, hC, mul_smul_comm, smul_mul_assoc]
    have hf : f * groundAction D hu c = groundAction D hu c * f :=
      LinearMap.ext fun x => (h c x).symm
    rw [hf]
  obtain ⟨z, hz⟩ := (fixedChargedTopZero_scalar_commutant D hu hD A).mp hcomm
  refine ⟨z, ?_⟩
  simpa only [A, AlgEquiv.apply_symm_apply, map_smul, map_one] using congrArg C hz

private theorem nativeCurrent_even (i : Fin D.rank) (x : ActualGround D hu) :
    zhuTopEvaluation (nativeMixedField D hu false) (evenTopGroundEquiv D hu x) (oddCurrent D i) =
      quadraticOddTopOscillator D hu i x := by
  apply Subtype.ext
  apply Subtype.ext
  exact nativeCurrentEven_tensor i x

private theorem nativeCurrent_odd (i j : Fin D.rank) (x : ActualGround D hu) :
    zhuTopEvaluation (nativeMixedField D hu true) (quadraticOddTopOscillator D hu j x)
      (oddCurrent D i) = ((D.G i j : ℂ) / 2) • evenTopGroundEquiv D hu x := by
  rw [← nativeCurrent_even]
  exact nativeCurrent_gram_return i j x

private theorem oddTop_span :
    Submodule.span ℂ (Set.range (fun p : Fin D.rank × ActualGround D hu =>
      quadraticOddTopOscillator D hu p.1 p.2)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun p : Fin D.rank × ActualGround D hu =>
    quadraticOddTopOscillator D hu p.1 p.2))
  let A : twistedTop D hu true →ₗ[ℂ] ActualTensor D hu :=
    (paritySpace D hu (paritySign true)).subtype.comp (twistedTop D hu true).subtype
  have hA : Function.Injective A := fun _ _ he => Subtype.ext (Subtype.ext he)
  have hgrade : actualGrade D hu 1 ≤ S.map A := by
    rw [actualGrade_one_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, x⟩, rfl⟩
    apply Submodule.mem_map.mpr
    exact ⟨quadraticOddTopOscillator D hu i x, Submodule.subset_span ⟨(i, x), rfl⟩, rfl⟩
  apply top_unique
  intro v _
  obtain ⟨u, huS, huv⟩ := Submodule.mem_map.mp (hgrade v.property)
  exact hA huv ▸ huS

private theorem oddCurrent_agrees_of_oscillators (F G : LawfulMixedField D hu true)
    (i : Fin D.rank)
    (h : ∀ j x, zhuTopEvaluation F (quadraticOddTopOscillator D hu j x) (oddCurrent D i) =
      zhuTopEvaluation G (quadraticOddTopOscillator D hu j x) (oddCurrent D i))
    (v : twistedTop D hu true) :
    zhuTopEvaluation F v (oddCurrent D i) = zhuTopEvaluation G v (oddCurrent D i) := by
  let A (H : LawfulMixedField D hu true) : twistedTop D hu true →ₗ[ℂ] twistedTop D hu false :=
    zhuCurrentEvaluation H i
  let B := A F - A G
  have hspan : Submodule.span ℂ (Set.range (fun p : Fin D.rank × ActualGround D hu =>
      quadraticOddTopOscillator D hu p.1 p.2)) ≤ LinearMap.ker B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, x⟩, rfl⟩
    change quadraticOddTopOscillator D hu j x ∈ LinearMap.ker B
    apply LinearMap.mem_ker.mpr
    exact sub_eq_zero.mpr (h j x)
  rw [oddTop_span] at hspan
  have hz := LinearMap.mem_ker.mp (hspan (Submodule.mem_top (x := v)))
  exact sub_eq_zero.mp hz

private def firstLeechDirection : Fin leechData.rank :=
  ⟨0, by simpa only [leech_spec.1] using (by decide : 0 < 24)⟩

/-- Every lawful even-to-odd mixed Leech field is a unique scalar multiple of the native field. -/
theorem leech_mixed_evenToOdd_multiplicity_one (F : LawfulMixedField leechData leechUnit false) :
    ∃! z : ℂ, F = (nativeMixedField leechData leechUnit false).scale z := by
  obtain ⟨f, hf⟩ := neutralPair_evenCurrent_commonGround leech_spec.2.2.1 F firstLeechDirection
  change ∀ i x, zhuTopEvaluation F (evenTopGroundEquiv leechData leechUnit x)
    (oddCurrent leechData i) = quadraticOddTopOscillator leechData leechUnit i (f x) at hf
  have hcomm (c : Charge leechData) (x : ActualGround leechData leechUnit) :
      groundAction leechData leechUnit c (f x) = f (groundAction leechData leechUnit c x) := by
    obtain ⟨u, _, hperp, hnorm⟩ := leech_exists_real_transverse c
    let v := complexify leechData u
    have hv : v ≠ 0 := by
      intro hz
      apply hnorm
      change g leechData v v = 0
      rw [hz, g_zero_right]
    exact evenCurrent_ground_commutes leech_spec.2.2.1 F f hf c v hperp hv x
  obtain ⟨z, hz⟩ := ground_scalar_of_commutes leech_spec.2.2.1 f hcomm
  have hfield : F = (nativeMixedField leechData leechUnit false).scale z := by
    apply leech_eq_of_zhuTopEvaluation_agrees_on_currents
    intro i v
    obtain ⟨x, rfl⟩ := (evenTopGroundEquiv leechData leechUnit).surjective v
    rw [hf, hz, zhuTopEvaluation_scale_current, nativeCurrent_even]
    exact map_smul (quadraticOddTopOscillator leechData leechUnit i) z x
  refine ⟨z, hfield, fun y hy => ?_⟩
  exact leech_nativeMixedField_scale_injective false (hy.symm.trans hfield)

/-- Every lawful odd-to-even mixed Leech field is a unique scalar multiple of the native field. -/
theorem leech_mixed_oddToEven_multiplicity_one (F : LawfulMixedField leechData leechUnit true) :
    ∃! z : ℂ, F = (nativeMixedField leechData leechUnit true).scale z := by
  obtain ⟨f, hf⟩ := neutralPair_oddCurrent_commonGround leech_spec.2.2.1 F firstLeechDirection
  change ∀ i j x, zhuTopEvaluation F (quadraticOddTopOscillator leechData leechUnit j x)
    (oddCurrent leechData i) =
      (leechData.G i j : ℂ) • evenTopGroundEquiv leechData leechUnit (f x) at hf
  have hcomm (c : Charge leechData) (x : ActualGround leechData leechUnit) :
      groundAction leechData leechUnit c (f x) = f (groundAction leechData leechUnit c x) := by
    obtain ⟨u, _, hperp, hnorm⟩ := leech_exists_real_transverse c
    let v := complexify leechData u
    have h := chargedZhu_reverseCurrent_ground_equivariant leech_spec.2.2.1 F c v v hperp
      ((g_symm leechData _ _).trans hperp) x
    simp only [reverseCurrentGroundMap_eq F f hf, map_smul] at h
    exact smul_right_injective _ hnorm h
  obtain ⟨z, hz⟩ := ground_scalar_of_commutes leech_spec.2.2.1 f hcomm
  have hfield : F = (nativeMixedField leechData leechUnit true).scale (2 * z) := by
    apply leech_eq_of_zhuTopEvaluation_agrees_on_currents
    intro i v
    apply oddCurrent_agrees_of_oscillators _ _ i _ v
    intro j x
    rw [hf, hz, zhuTopEvaluation_scale_current, nativeCurrent_odd]
    change (leechData.G i j : ℂ) • evenTopGroundEquiv leechData leechUnit (z • x) =
      (2 * z) • (((leechData.G i j : ℂ) / 2) • evenTopGroundEquiv leechData leechUnit x)
    have hcoeff : (leechData.G i j : ℂ) * z = (2 * z) * ((leechData.G i j : ℂ) / 2) := by
      ring
    rw [map_smul, smul_smul, smul_smul, hcoeff]
  refine ⟨2 * z, hfield, fun y hy => ?_⟩
  exact leech_nativeMixedField_scale_injective true (hy.symm.trans hfield)

/-- For either parity the whole space of lawful Leech mixed fields is parametrized
by the coefficients of the native field scaled by a unique complex number. -/
theorem leech_mixed_multiplicity_one (s : Bool) (F : LawfulMixedField leechData leechUnit s) :
    ∃! z : ℂ, F = (nativeMixedField leechData leechUnit s).scale z := by
  cases s
  · exact leech_mixed_evenToOdd_multiplicity_one F
  · exact leech_mixed_oddToEven_multiplicity_one F

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

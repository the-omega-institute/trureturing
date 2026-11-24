/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeQuadraticZhuCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeQuadraticZhuCurrent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual neutral quadratic covariance and the common ground map on currents. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeEvenGroundZhuCommutant
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralPairs
import D5.S3.VertexAlgebra.Lattice.ActualZhuCurrentRelations
import D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades
import Batteries.Tactic.OpenPrivate

/-!
Neutral quadratic zero modes control the weight-one mixed Zhu evaluations.
The two parity directions give an oscillator insertion and a Gram contraction,
respectively, each with a single endomorphism of the actual twisted ground.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeFiniteNegativeGeneration LatticeAllStateField
open LatticeActualConformalState LatticeSugawaraCurrents
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeHalfFockParityT MvPolynomial
open Lattice.ActualFixedC2 (neutralPair)
open Lattice.ActualZhuCurrentRelations (single_weighted_grade)
open HalfFock.NormFourLowestGrades (actualGrade_one_eq_span)
open HalfFock.LatticeHalfFockParityField (paritySpace)

open private mixed_commutator_one fixedAction_val
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
open private oddCurrent_grade_one mem_parity
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private quadratic_ground_zero quadratic_X_zero
  from D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

local instance (D : LatticeData) (hu : IsUnit D.G.det) (t : Bool) :
    AddCommGroup (twistedTop D hu t) :=
  @Submodule.addCommGroup ℂ (Twisted D hu t) _ _ _ (twistedTop D hu t)

private theorem current_val (i : Fin D.rank) :
    (oddCurrent D i).val = currentState D i := by
  change neutralMode D i (-1) (vacuum D) = _
  simpa only [neutralField_ncoeff] using current_state_creation D i

/-- The fixed neutral pair with both creation indices zero has source weight two. -/
theorem neutralPair_weight_two (i j : Fin D.rank) :
    (neutralPair D i j 0 0).val ∈ grade D 2 := by
  have hx (k : Fin D.rank) :
      IsWeightedHomogeneous (oscillatorWeight D) (X (k, 0) : Oscillator D) 1 :=
    MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (oscillatorWeight D) (k, 0)
  change Finsupp.single (0 : Charge D) (X (i, 0) * X (j, 0)) ∈ grade D 2
  simpa [chargeEnergy, bilinear] using
    single_weighted_grade D 0 (X (i, 0) * X (j, 0)) 2 ((hx i).mul (hx j))

private theorem quadratic_mode_on_current (i j k : Fin D.rank) (m : ℤ)
    (hm : 0 ≤ m + 1) :
    (oddMode D (neutralPair D i j 0 0) (m + 1) (oddCurrent D k)).val =
      (D.G j k : ℂ) • neutralMode D i (m - 1) (vacuum D) +
      (D.G i k : ℂ) • neutralMode D j (m - 1) (vacuum D) := by
  have field : Y D (neutralPair D i j 0 0).val = quadraticSummand D i j :=
    quadratic_state_field D i j
  have kill : ((quadraticSummand D i j)[[m + 1]]) (vacuum D) = 0 := by
    rw [← field]
    exact stateField_creativity D _ _ hm
  have h := LinearMap.congr_fun
    (quadraticSummand_current_commutator D i j k m (-1)) (vacuum D)
  change ((Y D (neutralPair D i j 0 0).val)[[m + 1]])
    (neutralMode D k (-1) (vacuum D)) = _
  rw [field]
  simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, kill, map_zero, sub_zero, Int.cast_neg, Int.cast_one,
    neg_neg, one_smul, show m + (-1 : ℤ) = m - 1 by omega] using h

/-- In the actual untwisted vertex algebra the first mode contracts either current. -/
theorem neutralPair_oddCurrent_one (i j k : Fin D.rank) :
    oddMode D (neutralPair D i j 0 0) 1 (oddCurrent D k) =
      (D.G j k : ℂ) • oddCurrent D i + (D.G i k : ℂ) • oddCurrent D j := by
  apply Subtype.ext
  exact quadratic_mode_on_current i j k 0 (by norm_num)

/-- The actual zeroth mode is the translation of the first-mode contraction. -/
theorem neutralPair_oddCurrent_zero (i j k : Fin D.rank) :
    oddMode D (neutralPair D i j 0 0) 0 (oddCurrent D k) =
      oddTranslation D (oddMode D (neutralPair D i j 0 0) 1 (oddCurrent D k)) := by
  rw [neutralPair_oddCurrent_one, map_add, map_smul, map_smul]
  have translate (l : Fin D.rank) :
      (oddTranslation D (oddCurrent D l)).val = neutralMode D l (-2) (vacuum D) := by
    change LatticeSugawaraConformal.translation D (oddCurrent D l).val = _
    rw [current_val, LatticeActualVertexAlgebra.translation_as_mode,
      current_state_field, neutralField_ncoeff]
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, translate]
  exact quadratic_mode_on_current i j k (-1) (by norm_num)

/-- The commutator of the two actual quadratic top zero modes with the weight-one
mixed coefficient. The physical index is −1/2 from the even top and 1/2 from the
odd top, so the sum of the derivative and first-mode coefficients is respectively
1/2 and −1/2. -/
theorem neutralPair_zhuTopCurrent_commutator (F : LawfulMixedField D hu s)
    (i j k : Fin D.rank) (v : twistedTop D hu s) :
    let a := neutralPair D i j 0 0
    let b := oddCurrent D k
    let ha := neutralPair_weight_two i j
    fixedTopZero (!s) a 2 ha (zhuTopEvaluation F v b) -
        zhuTopEvaluation F (fixedTopZero s a 2 ha v) b =
      (if s then (-1 / 2 : ℂ) else (1 / 2 : ℂ)) •
        zhuTopEvaluation F v (oddMode D a 1 b) := by
  dsimp only
  let a := neutralPair D i j 0 0
  let b := oddCurrent D k
  let c := oddMode D a 1 b
  let ha := neutralPair_weight_two i j
  let n := twistedTopZhuIndex s 1
  have hc : c.val ∈ grade D 1 := by
    dsimp only [a, b, c]
    rw [neutralPair_oddCurrent_one]
    exact (grade D 1).add_mem
      ((grade D 1).smul_mem _ (oddCurrent_grade_one D i))
      ((grade D 1).smul_mem _ (oddCurrent_grade_one D j))
  have hb : b.val ∈ grade D 1 := oddCurrent_grade_one D k
  apply Subtype.ext
  change fixedAction (!s) a 1 (zhuTopEvaluation F v b).val -
    (zhuTopEvaluation F (fixedTopZero s a 2 ha v) b).val =
      (if s then (-1 / 2 : ℂ) else (1 / 2 : ℂ)) • (zhuTopEvaluation F v c).val
  rw [zhuTopEvaluation_homogeneous F v 1 b hb,
    zhuTopEvaluation_homogeneous F _ 1 b hb, zhuTopEvaluation_homogeneous F v 1 c hc]
  change fixedAction (!s) a 1 (F.coeff n b v.val) -
    F.coeff n b (fixedAction s a 1 v.val) =
      (if s then (-1 / 2 : ℂ) else (1 / 2 : ℂ)) • F.coeff n c v.val
  rw [mixed_commutator_one F a b v.val n, neutralPair_oddCurrent_zero i j k]
  change F.coeff (n + 1) (oddTranslation D c) v.val + F.coeff n c v.val = _
  rw [F.derivative, show n + 1 - 1 = n by omega]
  calc
    _ = (-(((n + 1 : ℤ) : ℂ) + 1 / 2) + 1) • F.coeff n c v.val := by
      rw [add_smul, one_smul]
    _ = _ := by
      congr 1
      cases s <;> norm_num [n, twistedTopZhuIndex]

private def tensorTop (t : Bool) (A : ActualGround D hu →ₗ[ℂ] ActualTensor D hu)
    (hA : ∀ x, A x ∈ actualGrade D hu (twistedTopGrade t)) :
    ActualGround D hu →ₗ[ℂ] twistedTop D hu t :=
  LinearMap.codRestrict _ (LinearMap.codRestrict _ A (fun x =>
    (mem_parity D hu (paritySign t) _).mpr (by
      have hp := actualParity_on_actualGrade D hu (twistedTopGrade t) ⟨A x, hA x⟩
      cases t <;> simpa [twistedTopGrade, paritySign] using hp)))
    (fun x => hA x)

/-- Vacuum oscillator tensored with the actual ground vector in the even top. -/
abbrev quadraticEvenTopGround (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualGround D hu →ₗ[ℂ] twistedTop D hu false :=
  (evenTopGroundEquiv D hu).toLinearMap

/-- One creation oscillator tensored with the actual ground vector in the odd top. -/
def quadraticOddTopOscillator (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) :
    ActualGround D hu →ₗ[ℂ] twistedTop D hu true :=
  tensorTop true (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu) (X (i, 0)))
    (fun x => by
      change (X (i, 0) ⊗ₜ[ℂ] x : ActualTensor D hu) ∈ actualGrade D hu 1
      rw [actualGrade_one_eq_span]
      exact Submodule.subset_span ⟨(i, x), rfl⟩)

private abbrev quadraticTop (t : Bool) (i j : Fin D.rank) :
    Module.End ℂ (twistedTop D hu t) :=
  fixedTopZero t (neutralPair D i j 0 0) 2 (neutralPair_weight_two i j)

private theorem quadraticTop_val (t : Bool) (i j : Fin D.rank)
    (v : twistedTop D hu t) :
    (quadraticTop t i j v).val.val =
      (correctedField D hu (neutralPair D i j 0 0).val).coeff (-4) v.val.val := by
  change (fixedAction t (neutralPair D i j 0 0) 1 v.val).val = _
  exact fixedAction_val t (neutralPair D i j 0 0) 1 v.val

/-- The scalar term of the native zero mode on a vacuum tensor. -/
theorem neutralPair_fixedTopZero_even (i j : Fin D.rank) (x : ActualGround D hu) :
    quadraticTop false i j (quadraticEvenTopGround D hu x) =
      ((D.G i j : ℂ) / 8) • quadraticEvenTopGround D hu x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [quadraticTop_val]
  exact quadratic_ground_zero D hu i j x

/-- The native zero mode on a first oscillator includes one half of the symmetric
Gram contraction and the same scalar as on the vacuum tensor. -/
theorem neutralPair_fixedTopZero_odd (i j k : Fin D.rank) (x : ActualGround D hu) :
    quadraticTop true i j (quadraticOddTopOscillator D hu k x) =
      ((D.G j k : ℂ) / 2) • quadraticOddTopOscillator D hu i x +
        ((D.G i k : ℂ) / 2) • quadraticOddTopOscillator D hu j x +
        ((D.G i j : ℂ) / 8) • quadraticOddTopOscillator D hu k x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [quadraticTop_val]
  exact quadratic_X_zero D hu i j k x

/-- Evaluation on a weight-one current as a linear map in the actual input top. -/
def zhuCurrentEvaluation (F : LawfulMixedField D hu s) (k : Fin D.rank) :
    twistedTop D hu s →ₗ[ℂ] twistedTop D hu (!s) where
  toFun v := zhuTopEvaluation F v (oddCurrent D k)
  map_add' v w := by
    apply Subtype.ext
    change (zhuTopEvaluation F (v + w) (oddCurrent D k)).val =
      (zhuTopEvaluation F v (oddCurrent D k)).val +
        (zhuTopEvaluation F w (oddCurrent D k)).val
    simp only [zhuTopEvaluation_homogeneous F _ 1 _ (oddCurrent_grade_one D k),
      Submodule.coe_add, map_add]
  map_smul' c v := by
    apply Subtype.ext
    change (zhuTopEvaluation F (c • v) (oddCurrent D k)).val =
      c • (zhuTopEvaluation F v (oddCurrent D k)).val
    simp only [zhuTopEvaluation_homogeneous F _ 1 _ (oddCurrent_grade_one D k),
      Submodule.coe_smul, map_smul]

private theorem current_covariance (F : LawfulMixedField D hu s)
    (i j k : Fin D.rank) (v : twistedTop D hu s) :
    quadraticTop (!s) i j (zhuCurrentEvaluation F k v) -
        zhuCurrentEvaluation F k (quadraticTop s i j v) =
      (if s then (-1 / 2 : ℂ) else (1 / 2 : ℂ)) •
        ((D.G j k : ℂ) • zhuCurrentEvaluation F i v +
          (D.G i k : ℂ) • zhuCurrentEvaluation F j v) := by
  have h := neutralPair_zhuTopCurrent_commutator F i j k v
  dsimp only at h
  rw [neutralPair_oddCurrent_one] at h
  simpa only [quadraticTop, zhuCurrentEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    map_add, map_smul] using h

private abbrev evenCurrentTop (F : LawfulMixedField D hu false) (i : Fin D.rank)
    (x : ActualGround D hu) : twistedTop D hu true :=
  zhuCurrentEvaluation F i (quadraticEvenTopGround D hu x)

private theorem even_current_covariance (F : LawfulMixedField D hu false)
    (i j k : Fin D.rank) (x : ActualGround D hu) :
    quadraticTop true i j (evenCurrentTop F k x) -
        ((D.G i j : ℂ) / 8) • evenCurrentTop F k x =
      ((D.G j k : ℂ) / 2) • evenCurrentTop F i x +
        ((D.G i k : ℂ) / 2) • evenCurrentTop F j x := by
  have h := current_covariance F i j k (quadraticEvenTopGround D hu x)
  change quadraticTop true i j (evenCurrentTop F k x) -
      (show twistedTop D hu true from
        zhuCurrentEvaluation F k (quadraticTop false i j (quadraticEvenTopGround D hu x))) =
    (1 / 2 : ℂ) • ((D.G j k : ℂ) • evenCurrentTop F i x +
      (D.G i k : ℂ) • evenCurrentTop F j x) at h
  rw [neutralPair_fixedTopZero_even, map_smul] at h
  change quadraticTop true i j (evenCurrentTop F k x) -
      ((D.G i j : ℂ) / 8) • evenCurrentTop F k x = _ at h
  rw [h]
  module

private abbrev topAmbient (t : Bool) : twistedTop D hu t →ₗ[ℂ] ActualTensor D hu :=
  (paritySpace D hu (paritySign t)).subtype.comp (twistedTop D hu t).subtype

private theorem topAmbient_injective (t : Bool) :
    Function.Injective (topAmbient (D := D) (hu := hu) t) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

private def oscillatorRead (i : Fin D.rank) : ActualTensor D hu →ₗ[ℂ] ActualGround D hu :=
  (TensorProduct.lid ℂ (ActualGround D hu)).toLinearMap.comp
    (TensorProduct.map (MvPolynomial.lcoeff ℂ (Finsupp.single (i, 0) 1)) LinearMap.id)

private theorem oscillatorRead_insert (i : Fin D.rank) (x : ActualGround D hu) :
    oscillatorRead i (topAmbient true (quadraticOddTopOscillator D hu i x)) = x := by
  change oscillatorRead i ((X (i, 0) : Oscillator D) ⊗ₜ[ℂ] x) = x
  simp [oscillatorRead]

private theorem quadraticOddTopOscillator_injective (i : Fin D.rank) :
    Function.Injective (quadraticOddTopOscillator D hu i) := by
  intro x y h
  have hr := congrArg (fun w => oscillatorRead i (topAmbient true w)) h
  simpa only [oscillatorRead_insert] using hr

private theorem quadratic_diagonal_range (i : Fin D.rank) (w : twistedTop D hu true) :
    ∃ y : ActualGround D hu,
      quadraticOddTopOscillator D hu i y =
        quadraticTop true i i w - ((D.G i i : ℂ) / 8) • w := by
  let A : Module.End ℂ (ActualTensor D hu) :=
    (correctedField D hu (neutralPair D i i 0 0).val).coeff (-4) -
      ((D.G i i : ℂ) / 8) • LinearMap.id
  let B := (topAmbient true).comp (quadraticOddTopOscillator D hu i)
  have hspan : actualGrade D hu 1 ≤ (LinearMap.range B).comap A := by
    rw [actualGrade_one_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, x⟩, rfl⟩
    change A ((X (k, 0) : Oscillator D) ⊗ₜ[ℂ] x) ∈ LinearMap.range B
    refine ⟨(D.G i k : ℂ) • x, ?_⟩
    change (X (i, 0) : Oscillator D) ⊗ₜ[ℂ] ((D.G i k : ℂ) • x) = _
    simp only [A, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    change _ = (correctedField D hu
      (Finsupp.single 0 (X (i, 0) * X (i, 0)))).coeff (-4)
        ((X (k, 0) : Oscillator D) ⊗ₜ[ℂ] x) - _
    rw [quadratic_X_zero, add_sub_cancel_right, TensorProduct.tmul_smul]
    module
  obtain ⟨y, hy⟩ := hspan w.property
  refine ⟨y, topAmbient_injective true ?_⟩
  calc
    _ = A w.val.val := hy
    _ = _ := by simp only [A, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul, topAmbient, LinearMap.comp_apply,
      Submodule.subtype_apply, quadraticTop_val]

private def evenCurrentGroundEntry (F : LawfulMixedField D hu false) (i : Fin D.rank) :
    Module.End ℂ (ActualGround D hu) :=
  (oscillatorRead i).comp ((topAmbient true).comp
    ((zhuCurrentEvaluation F i).comp (quadraticEvenTopGround D hu)))

private theorem even_current_diagonal (F : LawfulMixedField D hu false)
    (i : Fin D.rank) (hi : (D.G i i : ℂ) ≠ 0) (x : ActualGround D hu) :
    evenCurrentTop F i x =
      quadraticOddTopOscillator D hu i (evenCurrentGroundEntry F i x) := by
  let w := evenCurrentTop F i x
  obtain ⟨y, hy⟩ := quadratic_diagonal_range i w
  have h := even_current_covariance F i i i x
  change quadraticTop true i i w - ((D.G i i : ℂ) / 8) • w =
    ((D.G i i : ℂ) / 2) • w + ((D.G i i : ℂ) / 2) • w at h
  have he : quadraticOddTopOscillator D hu i y = (D.G i i : ℂ) • w := by
    rw [hy, h]
    module
  have hw : w = quadraticOddTopOscillator D hu i ((D.G i i : ℂ)⁻¹ • y) := by
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hi, one_smul]
  have hg := congrArg (fun z => oscillatorRead i (topAmbient true z)) hw
  change evenCurrentGroundEntry F i x =
    oscillatorRead i (topAmbient true
      (quadraticOddTopOscillator D hu i ((D.G i i : ℂ)⁻¹ • y))) at hg
  rw [oscillatorRead_insert] at hg
  rw [hg]
  exact hw

private theorem gram_diagonal_ne_zero
    (hD : (D.G.map (Int.castRingHom ℝ)).PosDef) (i : Fin D.rank) :
    (D.G i i : ℂ) ≠ 0 := by
  have hp : 0 < (D.G i i : ℝ) := hD.diag_pos (i := i)
  exact_mod_cast (show D.G i i ≠ 0 from by exact_mod_cast hp.ne')

/-- All even-to-odd weight-one evaluations use the same linear map on the
actual ground space, placed in the oscillator direction of the source current. -/
theorem neutralPair_evenCurrent_commonGround
    (hD : (D.G.map (Int.castRingHom ℝ)).PosDef)
    (F : LawfulMixedField D hu false) (i₀ : Fin D.rank) :
    ∃ f : Module.End ℂ (ActualGround D hu), ∀ i x,
      zhuTopEvaluation F (quadraticEvenTopGround D hu x) (oddCurrent D i) =
        quadraticOddTopOscillator D hu i (f x) := by
  refine ⟨evenCurrentGroundEntry F i₀, fun i x => ?_⟩
  let fi := evenCurrentGroundEntry F i₀ x
  let fj := evenCurrentGroundEntry F i x
  have hi := gram_diagonal_ne_zero hD i₀
  have hj := gram_diagonal_ne_zero hD i
  have hc := even_current_covariance F i₀ i i₀ x
  rw [even_current_diagonal F i₀ hi, even_current_diagonal F i hj,
    neutralPair_fixedTopZero_odd] at hc
  change (((D.G i i₀ : ℂ) / 2) • quadraticOddTopOscillator D hu i₀ fi +
      ((D.G i₀ i₀ : ℂ) / 2) • quadraticOddTopOscillator D hu i fi +
      ((D.G i₀ i : ℂ) / 8) • quadraticOddTopOscillator D hu i₀ fi) -
      ((D.G i₀ i : ℂ) / 8) • quadraticOddTopOscillator D hu i₀ fi =
    ((D.G i i₀ : ℂ) / 2) • quadraticOddTopOscillator D hu i₀ fi +
      ((D.G i₀ i₀ : ℂ) / 2) • quadraticOddTopOscillator D hu i fj at hc
  rw [add_sub_cancel_right] at hc
  have he := add_left_cancel hc
  have hs := (smul_right_injective _ (div_ne_zero hi (by norm_num))) he
  have hf := quadraticOddTopOscillator_injective i hs
  change evenCurrentTop F i x =
    quadraticOddTopOscillator D hu i fi
  rw [even_current_diagonal F i hj]
  exact congrArg (quadraticOddTopOscillator D hu i) hf.symm

private theorem quadraticTop_on_even (i j : Fin D.rank) (v : twistedTop D hu false) :
    quadraticTop false i j v = ((D.G i j : ℂ) / 8) • v := by
  obtain ⟨x, rfl⟩ := (evenTopGroundEquiv D hu).surjective v
  exact neutralPair_fixedTopZero_even i j x

private def oddCurrentTopEntry (F : LawfulMixedField D hu true) (k l : Fin D.rank) :
    ActualGround D hu →ₗ[ℂ] twistedTop D hu false :=
  (zhuCurrentEvaluation F k).comp (quadraticOddTopOscillator D hu l)

private theorem odd_current_covariance (F : LawfulMixedField D hu true)
    (i j k l : Fin D.rank) (x : ActualGround D hu) :
    (D.G j k : ℂ) • oddCurrentTopEntry F i l x +
        (D.G i k : ℂ) • oddCurrentTopEntry F j l x =
      (D.G j l : ℂ) • oddCurrentTopEntry F k i x +
        (D.G i l : ℂ) • oddCurrentTopEntry F k j x := by
  have h := current_covariance F i j k (quadraticOddTopOscillator D hu l x)
  change quadraticTop false i j (oddCurrentTopEntry F k l x) -
      (show twistedTop D hu false from
        zhuCurrentEvaluation F k (quadraticTop true i j (quadraticOddTopOscillator D hu l x))) =
    (-1 / 2 : ℂ) • ((D.G j k : ℂ) • oddCurrentTopEntry F i l x +
      (D.G i k : ℂ) • oddCurrentTopEntry F j l x) at h
  rw [quadraticTop_on_even, neutralPair_fixedTopZero_odd] at h
  simp only [map_add, map_smul] at h
  change ((D.G i j : ℂ) / 8) • oddCurrentTopEntry F k l x -
      (((D.G j l : ℂ) / 2) • oddCurrentTopEntry F k i x +
       ((D.G i l : ℂ) / 2) • oddCurrentTopEntry F k j x +
       ((D.G i j : ℂ) / 8) • oddCurrentTopEntry F k l x) = _ at h
  apply smul_right_injective _ (show (-1 / 2 : ℂ) ≠ 0 by norm_num)
  change (-1 / 2 : ℂ) • ((D.G j k : ℂ) • oddCurrentTopEntry F i l x +
      (D.G i k : ℂ) • oddCurrentTopEntry F j l x) =
    (-1 / 2 : ℂ) • ((D.G j l : ℂ) • oddCurrentTopEntry F k i x +
      (D.G i l : ℂ) • oddCurrentTopEntry F k j x)
  rw [← h]
  module

/-- In the original lattice coordinates the odd-to-even entry is the Gram pairing
times the common ground map. In dual coordinates these are the diagonal entries
of the same ground map. -/
theorem neutralPair_oddCurrent_commonGround
    (hD : (D.G.map (Int.castRingHom ℝ)).PosDef)
    (F : LawfulMixedField D hu true) (i₀ : Fin D.rank) :
    ∃ f : Module.End ℂ (ActualGround D hu), ∀ i j x,
      zhuTopEvaluation F (quadraticOddTopOscillator D hu j x) (oddCurrent D i) =
        (D.G i j : ℂ) • quadraticEvenTopGround D hu (f x) := by
  let W := (D.G i₀ i₀ : ℂ)⁻¹ • oddCurrentTopEntry F i₀ i₀
  let f := (evenTopGroundEquiv D hu).symm.toLinearMap.comp W
  refine ⟨f, fun i j x => ?_⟩
  change oddCurrentTopEntry F i j x =
    (D.G i j : ℂ) • evenTopGroundEquiv D hu ((evenTopGroundEquiv D hu).symm (W x))
  rw [LinearEquiv.apply_symm_apply]
  have hi₀ := gram_diagonal_ne_zero hD i₀
  have hi := gram_diagonal_ne_zero hD i
  have hdiag : (D.G i₀ i₀ : ℂ) • oddCurrentTopEntry F i i x =
      (D.G i i : ℂ) • oddCurrentTopEntry F i₀ i₀ x := by
    have h := odd_current_covariance F i₀ i i₀ i x
    rw [D.symmetric i i₀] at h
    rw [add_comm ((D.G i i : ℂ) • oddCurrentTopEntry F i₀ i₀ x)] at h
    exact add_left_cancel h
  have hrow : (D.G i i : ℂ) • oddCurrentTopEntry F i j x =
      (D.G i j : ℂ) • oddCurrentTopEntry F i i x := by
    have h := odd_current_covariance F i i i j x
    rw [← two_smul ℂ, ← two_smul ℂ] at h
    exact (smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0)) h
  have hrow' : oddCurrentTopEntry F i j x =
      (D.G i j : ℂ) • ((D.G i i : ℂ)⁻¹ • oddCurrentTopEntry F i i x) := by
    have h := congrArg (fun w : twistedTop D hu false => (D.G i i : ℂ)⁻¹ • w) hrow
    change (D.G i i : ℂ)⁻¹ • ((D.G i i : ℂ) • oddCurrentTopEntry F i j x) =
      (D.G i i : ℂ)⁻¹ • ((D.G i j : ℂ) • oddCurrentTopEntry F i i x) at h
    rw [smul_smul, inv_mul_cancel₀ hi, one_smul] at h
    exact h.trans (smul_comm _ _ _)
  have hdiag' : (D.G i i : ℂ)⁻¹ • oddCurrentTopEntry F i i x = W x := by
    apply smul_right_injective _ hi₀
    change (D.G i₀ i₀ : ℂ) • ((D.G i i : ℂ)⁻¹ • oddCurrentTopEntry F i i x) =
      (D.G i₀ i₀ : ℂ) • ((D.G i₀ i₀ : ℂ)⁻¹ • oddCurrentTopEntry F i₀ i₀ x)
    rw [smul_comm (D.G i₀ i₀ : ℂ) (D.G i i : ℂ)⁻¹, hdiag]
    rw [smul_smul, inv_mul_cancel₀ hi, one_smul, smul_smul, mul_inv_cancel₀ hi₀, one_smul]
  rw [hrow', hdiag']
end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

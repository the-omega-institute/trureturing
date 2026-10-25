/- GID: D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/NormalScalarTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial]
   utility: none
   digest: Signed current transpose, finite original scalar supports and original normal-source transpose with Corr-expanded corrected readout. -/

import D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import Mathlib.RingTheory.Binomial

/-!
Native implementation of the independent finite normal scalar transpose proposal.
Classical bilinear Wick/Fock normalization; no literature novelty claim.
The original ActualTensor, flatCoefficient, wordField, polynomialField, sourceField,
and actual Corr coefficients are retained. The ground form keeps its given
orientation. No symmetry, positivity, rank restriction or finite full weight space
is assumed. Original Corr covariance, exact weight conservation and source L1
are separate dependencies; full corrected exp(L1) inversion remains open.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open LatticeHalfFockFockNormalField SignedOscillatorWick
open TwistedGround.ActualChargedAdjoint
open LatticeHalfFockFiniteCorrection (wordWeight sourceWeight Corr)
open LatticeHalfFockCorrectedField

private theorem oscillator_current_transpose (D : LatticeData)
    (i : Fin D.rank) (k : ℤ) (p q : Oscillator D) :
    wick D (current D i k p) q = -wick D p (current D i (-k-1) q) := by
  by_cases hk : k < 0
  · have hn : 0 ≤ -k-1 := by omega
    have he : (((-k-1).toNat : ℕ) : ℤ) = -k-1 := Int.toNat_of_nonneg hn
    simp only [current, if_pos hk, if_neg (not_lt.mpr hn),
      LinearMap.mulLeft_apply, LinearMap.smul_apply]
    rw [wick_creation]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, he, frequency_opposite]
    ring
  · have hn : 0 ≤ k := by omega
    have he : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hn
    have hr : -k-1 < 0 := by omega
    simp only [current, if_neg hk, if_pos hr, LinearMap.smul_apply,
      LinearMap.mulLeft_apply]
    have h := wick_lowering D i k.toNat p q
    rw [he] at h
    have hi : (-(-k-1)-1).toNat = k.toNat := by congr 1; omega
    rw [hi]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h ⊢
    linear_combination -h

/- This private transfer is consumed immediately. The ground form is arbitrary;
   unfolding actualForm supplies its existing chosen form without naming either
   selectedGroundPairing or the private actualForm_tmul. -/
private theorem tensor_current_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (G : LinearMap.BilinForm ℂ (ActualGround D hu)) (i : Fin D.rank) (k : ℤ)
    (x y : ActualTensor D hu) :
    (wick D).tmul G (tensorCurrent D (ActualGround D hu) i k x) y =
      -(wick D).tmul G x (tensorCurrent D (ActualGround D hu) i (-k-1) y) := by
  induction x using TensorProduct.inductionOn generalizing y with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]; ring
  | tmul p u =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]; ring
    | tmul q v =>
      simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply]
      change G u v * wick D (current D i k p) q =
        -(G u v * wick D p (current D i (-k-1) q))
      rw [oscillator_current_transpose]
      ring

theorem actual_current_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (k : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu (tensorCurrent D (ActualGround D hu) i k x) y =
      -actualForm D hu x (tensorCurrent D (ActualGround D hu) i (-k-1) y) := by
  unfold actualForm
  exact tensor_current_transpose D hu _ i k x y

private abbrev Cutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (U : ℕ) (x : ActualTensor D hu) : Prop :=
  ∀ (i : Fin D.rank) (k : ℤ), (U : ℤ) ≤ k →
    tensorCurrent D (ActualGround D hu) i k x = 0

private theorem cutoff_current (D : LatticeData) (hu : IsUnit D.G.det)
    (U : ℕ) (x : ActualTensor D hu) (hx : Cutoff D hu U x)
    (i : Fin D.rank) (k : ℤ) (hk : 0 ≤ k) :
    Cutoff D hu U (tensorCurrent D (ActualGround D hu) i k x) := by
  intro j l hl
  rw [tensor_current_same_sign D hu j i l k (Or.inr ⟨by omega, hk⟩),
    hx j l hl, map_zero]

private theorem cutoff_jet (D : LatticeData) (hu : IsUnit D.G.det)
    (U : ℕ) (x : ActualTensor D hu) (hx : Cutoff D hu U x)
    (i : Index D) (k : ℤ) (hk : 0 ≤ k) :
    Cutoff D hu U (jetCurrent D hu i k x) := by
  intro j l hl
  simp only [jetCurrent, LinearMap.smul_apply, map_smul]
  rw [cutoff_current D hu U x hx i.1 k hk j l hl, smul_zero]

/- The elementary transpose premise is discharged below by the constructed
   actual_current_transpose; there is no premise about a normal field. -/
private theorem scalar_rectangle (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (ActualTensor D hu))
    (hB : ∀ i k x y, B (tensorCurrent D (ActualGround D hu) i k x) y =
      -B x (tensorCurrent D (ActualGround D hu) i (-k-1) y))
    (F : NativeField D hu) (w : List (Index D)) (Ux Uy : ℕ)
    (x y : ActualTensor D hu) (hx : Cutoff D hu Ux x) (hy : Cutoff D hu Uy y)
    (e : ℤ) (m : ModeTuple D w)
    (hn : B (flatCoefficient D hu F w m e x) y ≠ 0) :
    m ∈ modeBox D w (-(Uy : ℤ)) ((Ux : ℤ)-1) := by
  induction w generalizing x y e with
  | nil => cases m; simp [modeBox]
  | cons i w ih =>
    rcases m with ⟨k, t⟩
    change (k, t) ∈ (Finset.Icc (-(Uy : ℤ)) ((Ux : ℤ)-1)).product _
    apply (Finset.mem_product (s := Finset.Icc (-(Uy : ℤ)) ((Ux : ℤ)-1))
      (t := modeBox D w (-(Uy : ℤ)) ((Ux : ℤ)-1)) (p := (k,t))).mpr
    rw [Finset.mem_Icc]
    by_cases hk : k < 0
    · have ht : B (flatCoefficient D hu F w t
          (e+2*k+2*i.2+3) x) (tensorCurrent D (ActualGround D hu) i.1 (-k-1) y) ≠ 0 := by
        intro hz
        apply hn
        simp only [flatCoefficient, if_pos hk, Module.End.mul_apply, jetCurrent,
          LinearMap.smul_apply, map_smul, hB, hz, neg_zero, smul_zero]
      have lower : -(Uy : ℤ) ≤ k := by
        by_contra outside
        have hz := hy i.1 (-k-1) (by omega)
        exact ht (by rw [hz, map_zero])
      exact ⟨⟨lower, by omega⟩,
        ih x _ hx (cutoff_current D hu Uy y hy i.1 (-k-1) (by omega)) _ t ht⟩
    · have ht : B (flatCoefficient D hu F w t
          (e+2*k+2*i.2+3) (jetCurrent D hu i k x)) y ≠ 0 := by
        simpa only [flatCoefficient, if_neg hk, Module.End.mul_apply] using hn
      have upper : k ≤ (Ux : ℤ)-1 := by
        by_contra outside
        have hz : jetCurrent D hu i k x = 0 := by
          simp [jetCurrent, hx i.1 k (by omega)]
        exact ht (by rw [hz, map_zero, map_zero]; rfl)
      exact ⟨⟨by omega, upper⟩,
        ih _ y (cutoff_jet D hu Ux x hx i k (by omega)) hy _ t ht⟩

private def currentCutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (x : ActualTensor D hu) : ℕ :=
  Classical.choose (tensor_current_truncation D (ActualGround D hu) x)

private theorem currentCutoff_spec (D : LatticeData) (hu : IsUnit D.G.det)
    (x : ActualTensor D hu) : Cutoff D hu (currentCutoff D hu x) x :=
  Classical.choose_spec (tensor_current_truncation D (ActualGround D hu) x)

def scalarModeRectangle (D : LatticeData) (hu : IsUnit D.G.det)
    (w : List (Index D)) (x y : ActualTensor D hu) : Finset (ModeTuple D w) :=
  modeBox D w (-(currentCutoff D hu y : ℤ)) ((currentCutoff D hu x : ℤ)-1)

theorem actual_flat_scalar_mode_support (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (w : List (Index D)) (e : ℤ) (x y : ActualTensor D hu) :
    Function.support (fun m => actualForm D hu (flatCoefficient D hu F w m e x) y) ⊆
      scalarModeRectangle D hu w x y := by
  intro m hm
  exact scalar_rectangle D hu (actualForm D hu) (actual_current_transpose D hu)
    F w _ _ x y (currentCutoff_spec D hu x) (currentCutoff_spec D hu y) e m hm

/- This is an adjoint of the finite leftAction, not a replacement field. -/
private def leftTranspose (D : LatticeData) (hu : IsUnit D.G.det) :
    (w : List (Index D)) → ModeTuple D w → Module.End ℂ (ActualTensor D hu)
  | [], _ => 1
  | i :: w, m =>
    if m.1 < 0 then leftTranspose D hu w m.2 *
      ((-jetScalar i.2 m.1) • tensorCurrent D (ActualGround D hu) i.1 (-m.1-1))
    else leftTranspose D hu w m.2

private theorem leftAction_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (w : List (Index D)) (m : ModeTuple D w) (x y : ActualTensor D hu) :
    actualForm D hu (leftAction D hu w m x) y =
      actualForm D hu x (leftTranspose D hu w m y) := by
  induction w generalizing x y with
  | nil => simp [leftAction, leftTranspose]
  | cons i w ih =>
    simp only [leftAction, leftTranspose]
    split_ifs with hk
    · simp only [Module.End.mul_apply, jetCurrent, LinearMap.smul_apply,
        map_smul, LinearMap.smul_apply]
      rw [actual_current_transpose]
      rw [← ih]
      simp only [map_smul, smul_eq_mul]
      ring
    · apply ih

private theorem charged_coeff_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) (x : ActualTensor D hu) :
    (chargedField D hu a).coeff e x = chargedCoefficient D hu a e x := by
  rw [chargedField, HVertexOperator.coeff_of_coeff]

private def chargedOrder (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (x : ActualTensor D hu) : ℤ :=
  ((HahnModule.of ℂ).symm (chargedField D hu a x)).order

private theorem charged_below_order (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (x : ActualTensor D hu) (e : ℤ) (he : e < chargedOrder D hu a x) :
    chargedCoefficient D hu a e x = 0 := by
  rw [← charged_coeff_eq]
  exact HahnSeries.coeff_eq_zero_of_lt_order he

private def chargedScalarWindow (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (x y : ActualTensor D hu) : Finset ℤ :=
  Finset.Icc (chargedOrder D hu a x) (-chargedOrder D hu a y-2*chargeNorm D a)

private theorem charged_scalar_support (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (x y : ActualTensor D hu) :
    Function.support (fun e => actualForm D hu (chargedCoefficient D hu a e x) y) ⊆
      chargedScalarWindow D hu a x y := by
  intro e he
  change _ ≠ (0 : ℂ) at he
  dsimp only at he
  change e ∈ Finset.Icc (chargedOrder D hu a x) (-chargedOrder D hu a y-2*chargeNorm D a)
  rw [Finset.mem_Icc]
  constructor
  · by_contra h
    exact he (by rw [charged_below_order D hu a x e (by omega), map_zero]; rfl)
  · by_contra h
    apply he
    rw [actual_charged_coefficient_adjoint,
      charged_below_order D hu a y (-e-2*chargeNorm D a) (by omega), map_zero, mul_zero]

private def flatExponentWindow (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (m : ModeTuple D w)
    (x y : ActualTensor D hu) : Finset ℤ :=
  (chargedScalarWindow D hu a (rightAction D hu w m x) (leftTranspose D hu w m y)).image
    (fun q => q-2*modeSum D w m-jetShift D w)

private theorem flat_exponent_support (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (m : ModeTuple D w)
    (x y : ActualTensor D hu) :
    Function.support (fun e => actualForm D hu
      (flatCoefficient D hu (chargedField D hu a) w m e x) y) ⊆
      flatExponentWindow D hu a w m x y := by
  intro e he
  change _ ≠ (0 : ℂ) at he
  dsimp only at he
  have hn : actualForm D hu
      (chargedCoefficient D hu a (e+2*modeSum D w m+jetShift D w)
        (rightAction D hu w m x)) (leftTranspose D hu w m y) ≠ 0 := by
    simpa only [flatCoefficient_factorization, Module.End.mul_apply,
      leftAction_transpose, charged_coeff_eq] using he
  exact Finset.mem_image.mpr ⟨_, charged_scalar_support D hu a _ _ hn, by ring⟩

theorem actual_word_scalar_rectangle (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (w : List (Index D)) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((wordField D hu F w).coeff e x) y =
      ∑ m ∈ scalarModeRectangle D hu w x y,
        actualForm D hu (flatCoefficient D hu F w m e x) y := by
  rw [wordField_coefficient]
  change (actualForm D hu).flip y (∑ᶠ m, flatTerm D hu F w e x m) = _
  rw [map_finsum _ (flatTerm_finite D hu F w e x)]
  exact finsum_eq_sum_of_support_subset _ (actual_flat_scalar_mode_support D hu F w e x y)

def wordExponentWindow (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (x y : ActualTensor D hu) : Finset ℤ :=
  (scalarModeRectangle D hu w x y).biUnion (fun m => flatExponentWindow D hu a w m x y)

theorem actual_word_scalar_exponent_support (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (x y : ActualTensor D hu) :
    Function.support (fun e => actualForm D hu
      ((chargedWordField D hu a w).coeff e x) y) ⊆ wordExponentWindow D hu a w x y := by
  intro e he
  change _ ≠ (0 : ℂ) at he
  dsimp only at he
  by_contra outside
  apply he
  rw [chargedWordField, actual_word_scalar_rectangle]
  apply Finset.sum_eq_zero
  intro m hm
  by_contra hn
  exact outside (Finset.mem_biUnion.mpr ⟨m, hm, flat_exponent_support D hu a w m x y hn⟩)

private theorem jetScalar_choose (r : ℕ) (k : ℤ) :
    jetScalar r k = Ring.choose (-(k : ℂ)-3/2) r := by
  rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def,
    ← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range]
  simp only [jetScalar, smul_eq_mul, div_eq_mul_inv]
  ring

theorem jetScalar_reflection (r : ℕ) (k : ℤ) :
    jetScalar r (-k-1) = (-1 : ℂ)^r *
      ∑ s ∈ Finset.range (r+1), ((r+1).choose (s+1) : ℂ) * jetScalar s k := by
  rw [jetScalar_choose]
  have ha : (-((-k-1 : ℤ) : ℂ)-3/2) = -(-(k : ℂ)-3/2+2) := by push_cast; ring
  rw [ha, Ring.choose_neg]
  have hb : (-(k : ℂ)-3/2+2) + (r : ℂ)-1 =
      (-(k : ℂ)-3/2) + ((r+1 : ℕ) : ℂ) := by push_cast; ring
  rw [hb, Ring.add_choose_eq r (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
  rw [Ring.choose_natCast, ← Nat.choose_symm (by omega : r-s ≤ r+1),
    show r+1-(r-s) = s+1 by omega, ← jetScalar_choose]
  ring

private def jetTriangle (r : ℕ) (s : Fin (r+1)) : ℂ :=
  (-1 : ℂ)^(r+1) * ((r+1).choose (s.val+1) : ℂ)

private theorem negative_jet_reflection (r : ℕ) (k : ℤ) :
    -jetScalar r k = ∑ s : Fin (r+1), jetTriangle r s * jetScalar s.val (-k-1) := by
  have h := jetScalar_reflection r (-k-1)
  rw [show -(-k-1)-1 = k by omega] at h
  calc
    -jetScalar r k = ∑ s ∈ Finset.range (r+1),
        (-1 : ℂ)^(r+1) * ((r+1).choose (s+1) : ℂ) * jetScalar s (-k-1) := by
      rw [h, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      rw [pow_succ]
      ring
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun s : ℕ => (-1 : ℂ)^(r+1) * ((r+1).choose (s+1) : ℂ) *
        jetScalar s (-k-1)) (r+1)).symm

private theorem jet_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Index D) (k : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu (jetCurrent D hu i k x) y =
      ∑ s : Fin (i.2+1), jetTriangle i.2 s *
        actualForm D hu x (jetCurrent D hu (i.1,s.val) (-k-1) y) := by
  simp only [jetCurrent, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  rw [actual_current_transpose]
  calc
    _ = (-jetScalar i.2 k) * actualForm D hu x
        (tensorCurrent D (ActualGround D hu) i.1 (-k-1) y) := by ring
    _ = _ := by
      rw [negative_jet_reflection, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      ring

/- Finite choices of lowered orders, retaining every colour and occurrence.
   ModeTuple itself remains the original Unit/(ℤ × tail) type. -/
abbrev JetTuple (D : LatticeData) : List (Index D) → Type
  | [] => Unit
  | i :: w => Fin (i.2+1) × JetTuple D w

instance jetTupleFintype (D : LatticeData) (w : List (Index D)) : Fintype (JetTuple D w) := by
  induction w with
  | nil => exact inferInstanceAs (Fintype Unit)
  | cons i w ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin (i.2+1) × JetTuple D w))

def lowerWord (D : LatticeData) : (w : List (Index D)) → JetTuple D w → List (Index D)
  | [], _ => []
  | i :: w, s => (i.1,s.1.val) :: lowerWord D w s.2

def triangleCoefficient (D : LatticeData) : (w : List (Index D)) → JetTuple D w → ℂ
  | [], _ => 1
  | i :: w, s => jetTriangle i.2 s.1 * triangleCoefficient D w s.2

private def reflectModes (D : LatticeData) :
    (w : List (Index D)) → (s : JetTuple D w) → ModeTuple D w → ModeTuple D (lowerWord D w s)
  | [], _, _ => ()
  | _ :: w, s, m => (-m.1-1, reflectModes D w s.2 m.2)

private def unreflectModes (D : LatticeData) :
    (w : List (Index D)) → (s : JetTuple D w) → ModeTuple D (lowerWord D w s) → ModeTuple D w
  | [], _, _ => ()
  | _ :: w, s, m => (-m.1-1, unreflectModes D w s.2 m.2)

private def modeReflection (D : LatticeData) (w : List (Index D)) (s : JetTuple D w) :
    ModeTuple D w ≃ ModeTuple D (lowerWord D w s) where
  toFun := reflectModes D w s
  invFun := unreflectModes D w s
  left_inv := by
    intro m
    induction w with
    | nil => cases m; rfl
    | cons i w ih =>
      rcases s with ⟨s,t⟩
      rcases m with ⟨k,m⟩
      simp only [reflectModes, unreflectModes, Prod.mk.injEq]
      exact ⟨by omega, ih t m⟩
  right_inv := by
    intro m
    induction w with
    | nil => cases m; rfl
    | cons i w ih =>
      rcases s with ⟨s,t⟩
      rcases m with ⟨k,m⟩
      change (-(-k-1)-1, reflectModes D w t (unreflectModes D w t m)) = (k,m)
      apply Prod.ext
      · dsimp only; omega
      · exact ih t m

def transposeExponent (D : LatticeData) (a : Charge D) (w : List (Index D))
    (s : JetTuple D w) (e : ℤ) : ℤ :=
  -e-2*chargeNorm D a-2*(wordWeight D w : ℤ)-2*(wordWeight D (lowerWord D w s) : ℤ)

/- Exact original flatCoefficient transpose. No assumption about normal-field
   adjointness, equivariance, Corr or a recursively reflected field occurs. -/
theorem actual_flat_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (m : ModeTuple D w) (e : ℤ)
    (x y : ActualTensor D hu) :
    actualForm D hu (flatCoefficient D hu (chargedField D hu a) w m e x) y =
      ∑ s : JetTuple D w,
        paritySign (bilinear D a a / 2) * triangleCoefficient D w s *
          actualForm D hu x (flatCoefficient D hu (chargedField D hu a)
            (lowerWord D w s) (reflectModes D w s m) (transposeExponent D a w s e) y) := by
  induction w generalizing e x y with
  | nil =>
    cases m
    simp only [flatCoefficient, lowerWord, reflectModes, transposeExponent, wordWeight,
      Nat.cast_zero, mul_zero, sub_zero, triangleCoefficient, List.map_nil, List.sum_nil, Fintype.sum_unique, mul_one,
      charged_coeff_eq]
    exact actual_charged_coefficient_adjoint D hu a e x y
  | cons i w ih =>
    rcases m with ⟨k,m⟩
    by_cases hk : k < 0
    · rw [flatCoefficient, if_pos hk, Module.End.mul_apply, jet_transpose]
      simp_rw [ih]
      simp only [Fintype.sum_prod_type, triangleCoefficient, lowerWord, reflectModes,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      have hr : ¬ -k-1 < 0 := by omega
      have he : transposeExponent D a (i :: w) (s,t) e + 2*(-k-1) + 2*s.val+3 =
          transposeExponent D a w t (e+2*k+2*i.2+3) := by
        simp only [transposeExponent, wordWeight, lowerWord, List.map_cons, List.sum_cons,
          sourceWeight, Nat.cast_add, Nat.cast_one]
        ring
      simp only [flatCoefficient, if_neg hr, Module.End.mul_apply]
      rw [he]
      ring
    · rw [flatCoefficient, if_neg hk, Module.End.mul_apply, ih]
      simp_rw [jet_transpose]
      simp only [Finset.mul_sum, Fintype.sum_prod_type, triangleCoefficient,
        lowerWord, reflectModes]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      have hr : -k-1 < 0 := by omega
      have he : transposeExponent D a (i :: w) (s,t) e + 2*(-k-1) + 2*s.val+3 =
          transposeExponent D a w t (e+2*k+2*i.2+3) := by
        simp only [transposeExponent, wordWeight, lowerWord, List.map_cons, List.sum_cons,
          sourceWeight, Nat.cast_add, Nat.cast_one]
        ring
      simp only [flatCoefficient, if_pos hr, Module.End.mul_apply]
      rw [he]
      ring

/- The finite sum exchange uses actual vector support at the reflected fixed
   exponent, followed by a scalar linear map and a genuine tuple bijection. -/
private theorem reflected_scalar_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (s : JetTuple D w) (e : ℤ)
    (x y : ActualTensor D hu) :
    Function.HasFiniteSupport (fun m : ModeTuple D w =>
      paritySign (bilinear D a a / 2) * triangleCoefficient D w s *
        actualForm D hu x (flatCoefficient D hu (chargedField D hu a)
          (lowerWord D w s) (reflectModes D w s m) (transposeExponent D a w s e) y)) := by
  have h := (flatTerm_finite D hu (chargedField D hu a) (lowerWord D w s)
    (transposeExponent D a w s e) y).fun_comp (map_zero (actualForm D hu x))
  have h' := Function.HasFiniteSupport.fun_comp_of_injective
    (modeReflection D w s).injective h
  exact Function.HasFiniteSupport.mul_right
    (fun _ => paritySign (bilinear D a a / 2) * triangleCoefficient D w s) h'

theorem actual_word_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((chargedWordField D hu a w).coeff e x) y =
      ∑ s : JetTuple D w,
        paritySign (bilinear D a a / 2) * triangleCoefficient D w s *
          actualForm D hu x ((chargedWordField D hu a (lowerWord D w s)).coeff
            (transposeExponent D a w s e) y) := by
  rw [chargedWordField, wordField_coefficient]
  change (actualForm D hu).flip y (∑ᶠ m, flatTerm D hu (chargedField D hu a) w e x m) = _
  rw [map_finsum _ (flatTerm_finite D hu (chargedField D hu a) w e x)]
  change (∑ᶠ m : ModeTuple D w,
    actualForm D hu (flatCoefficient D hu (chargedField D hu a) w m e x) y) = _
  simp_rw [actual_flat_transpose]
  rw [finsum_sum_comm Finset.univ _ (fun s _ => reflected_scalar_finite D hu a w s e x y)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← mul_finsum]
  congr 1
  calc
    _ = ∑ᶠ n : ModeTuple D (lowerWord D w s),
        actualForm D hu x (flatCoefficient D hu (chargedField D hu a)
          (lowerWord D w s) n (transposeExponent D a w s e) y) :=
      finsum_comp (modeReflection D w s) (modeReflection D w s).bijective
    _ = _ := by
      rw [chargedWordField, wordField_coefficient]
      exact (map_finsum (actualForm D hu x)
        (flatTerm_finite D hu (chargedField D hu a) (lowerWord D w s)
          (transposeExponent D a w s e) y)).symm

def wordPolynomial (D : LatticeData) : List (Index D) → Oscillator D
  | [] => 1
  | i :: w => MvPolynomial.X i * wordPolynomial D w

private theorem polynomialField_word (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) :
    polynomialField D hu a (wordPolynomial D w) = chargedWordField D hu a w := by
  induction w with
  | nil =>
    simpa [wordPolynomial, occurrences, chargedWordField] using
      polynomialField_monomial_public D hu a 0
  | cons i w ih =>
    rw [wordPolynomial, polynomialField_X_mul, ih, chargedWordField,
      ← wordField_cons_singleton]
    rfl

/- This consumer ends in the ORIGINAL polynomialField. In particular it is
   not an identity only about a newly defined reflectedWord construction. -/
theorem actual_polynomial_monomial_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (m : Index D →₀ ℕ) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((polynomialField D hu a (MvPolynomial.monomial m 1)).coeff e x) y =
      ∑ s : JetTuple D (occurrences D m),
        paritySign (bilinear D a a / 2) * triangleCoefficient D (occurrences D m) s *
          actualForm D hu x ((polynomialField D hu a
            (wordPolynomial D (lowerWord D (occurrences D m) s))).coeff
              (transposeExponent D a (occurrences D m) s e) y) := by
  rw [polynomialField_monomial_public]
  change actualForm D hu ((chargedWordField D hu a (occurrences D m)).coeff e x) y = _
  rw [actual_word_transpose]
  simp only [polynomialField_word]

theorem lowerWord_weight_le (D : LatticeData) (w : List (Index D))
    (s : JetTuple D w) : wordWeight D (lowerWord D w s) ≤ wordWeight D w := by
  induction w with
  | nil => simp [lowerWord, wordWeight]
  | cons i w ih =>
    have hs := s.1.isLt
    have ht := ih s.2
    change s.1.val+1+wordWeight D (lowerWord D w s.2) ≤ i.2+1+wordWeight D w
    omega

def weightLoss (D : LatticeData) (w : List (Index D)) (s : JetTuple D w) : ℕ :=
  wordWeight D w - wordWeight D (lowerWord D w s)

theorem transposeExponent_loss (D : LatticeData) (a : Charge D)
    (w : List (Index D)) (s : JetTuple D w) (e : ℤ) :
    transposeExponent D a w s e =
      -e-2*chargeNorm D a-4*(wordWeight D w : ℤ)+2*(weightLoss D w s : ℤ) := by
  have h := lowerWord_weight_le D w s
  rw [transposeExponent, weightLoss, Int.ofNat_sub h]
  ring

def binomialProduct (D : LatticeData) : (w : List (Index D)) → JetTuple D w → ℂ
  | [], _ => 1
  | i :: w, s => ((i.2+1).choose (s.1.val+1) : ℂ) * binomialProduct D w s.2

private theorem triangleCoefficient_sign (D : LatticeData) (w : List (Index D))
    (s : JetTuple D w) :
    triangleCoefficient D w s = (-1 : ℂ)^(wordWeight D w) * binomialProduct D w s := by
  induction w with
  | nil => simp [triangleCoefficient, binomialProduct, wordWeight]
  | cons i w ih =>
    rw [triangleCoefficient, binomialProduct, ih]
    change ((-1 : ℂ)^(i.2+1) * _) * _ = (-1 : ℂ)^(i.2+1+wordWeight D w) * _
    rw [pow_add]
    ring

private theorem sourceField_single (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) :
    sourceField D hu (Finsupp.single a p) = polynomialField D hu a p := by
  rw [sourceField, Finsupp.lsum_single]

private theorem source_scalar_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((sourceField D hu v).coeff e x) y =
      ∑ a ∈ v.support,
        ∑ m ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr (v a)).support,
          ((MvPolynomial.basisMonomials (Index D) ℂ).repr (v a) m) *
            actualForm D hu ((polynomialField D hu a (MvPolynomial.monomial m 1)).coeff e x) y := by
  rw [sourceField_coefficient]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro m hm
  rw [polynomialField_monomial_public, wordField_coefficient]

def sourceExponentWindow (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (x y : ActualTensor D hu) : Finset ℤ :=
  v.support.biUnion (fun a =>
    ((MvPolynomial.basisMonomials (Index D) ℂ).repr (v a)).support.biUnion
      (fun m => wordExponentWindow D hu a (occurrences D m) x y))

theorem actual_source_scalar_exponent_support (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (x y : ActualTensor D hu) :
    Function.support (fun e => actualForm D hu ((sourceField D hu v).coeff e x) y) ⊆
      sourceExponentWindow D hu v x y := by
  intro e he
  change _ ≠ (0 : ℂ) at he
  dsimp only at he
  by_contra outside
  apply he
  rw [source_scalar_expansion]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro m hm
  have hz : actualForm D hu
      ((polynomialField D hu a (MvPolynomial.monomial m 1)).coeff e x) y = 0 := by
    by_contra hn
    have hn' : actualForm D hu ((chargedWordField D hu a (occurrences D m)).coeff e x) y ≠ 0 := by
      simpa only [polynomialField_monomial_public, chargedWordField] using hn
    exact outside (Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_biUnion.mpr ⟨m, hm, actual_word_scalar_exponent_support D hu a _ x y hn'⟩⟩)
  rw [hz, mul_zero]

/- Exact finite all-source NORMAL coefficient law. The separately owned Corr
   covariance is not a premise. Every RHS source is in the original Carrier,
   and is evaluated by the original sourceField in the right slot. -/
theorem actual_source_scalar_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((sourceField D hu v).coeff e x) y =
      ∑ a ∈ v.support,
        ∑ m ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr (v a)).support,
          ((MvPolynomial.basisMonomials (Index D) ℂ).repr (v a) m) *
            (paritySign (bilinear D a a / 2) *
              (-1 : ℂ)^(Finsupp.weight (sourceWeight D) m) *
                ∑ s : JetTuple D (occurrences D m),
                  binomialProduct D (occurrences D m) s *
                    actualForm D hu x ((sourceField D hu
                      (Finsupp.single a (wordPolynomial D (lowerWord D (occurrences D m) s)))).coeff
                        (-e-2*chargeNorm D a-4*(Finsupp.weight (sourceWeight D) m : ℤ)+
                          2*(weightLoss D (occurrences D m) s : ℤ)) y)) := by
  rw [source_scalar_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  rw [actual_polynomial_monomial_transpose]
  have hw : wordWeight D (occurrences D m) = Finsupp.weight (sourceWeight D) m := by
    exact LatticeHalfFockFiniteCorrection.wordWeight_occurrences D m
  simp_rw [triangleCoefficient_sign, transposeExponent_loss, hw, sourceField_single]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

private theorem polynomial_scalar_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((polynomialField D hu a p).coeff e x) y =
      ∑ m ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr p).support,
        ((MvPolynomial.basisMonomials (Index D) ℂ).repr p m) *
          (paritySign (bilinear D a a / 2) * (-1 : ℂ)^(Finsupp.weight (sourceWeight D) m) *
            ∑ s : JetTuple D (occurrences D m),
              binomialProduct D (occurrences D m) s *
                actualForm D hu x ((sourceField D hu
                  (Finsupp.single a (wordPolynomial D (lowerWord D (occurrences D m) s)))).coeff
                    (-e-2*chargeNorm D a-4*(Finsupp.weight (sourceWeight D) m : ℤ)+
                      2*(weightLoss D (occurrences D m) s : ℤ)) y)) := by
  classical
  by_cases hp : p = 0
  · subst p; simp
  · simpa only [sourceField_single, Finsupp.support_single _ hp, Finset.sum_singleton,
      Finsupp.single_eq_same] using actual_source_scalar_transpose D hu (Finsupp.single a p) e x y

/- A scalar evaluation map lets the existing finite field sums be used without
   pretending that a mode sum is finite in Module.End. -/
private def scalarLeftAt (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y : ActualTensor D hu) : NativeField D hu →ₗ[ℂ] ℂ where
  toFun F := actualForm D hu (F.coeff e x) y
  map_add' F G := by simp only [map_add, Pi.add_apply, LinearMap.add_apply]
  map_smul' c F := by
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]

private theorem corrected_scalar_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((correctedField D hu v).coeff e x) y =
      ∑ a ∈ v.support, ∑ c ∈ (Corr D a (v a)).support,
        actualForm D hu ((polynomialField D hu a ((Corr D a (v a)) c)).coeff
          (e+2*(c : ℤ)) x) y := by
  change scalarLeftAt D hu e x y (correctedField D hu v) = _
  simp only [correctedField, Finsupp.lsum_apply, Finsupp.sum, correctedPolynomial,
    LinearMap.comp_apply, correctedSum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  change actualForm D hu ((shiftField D hu c
    (polynomialField D hu a ((Corr D a (v a)) c))).coeff e x) y = _
  rw [shiftField_coefficient_public]

def correctedExponentWindow (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (x y : ActualTensor D hu) : Finset ℤ :=
  v.support.biUnion (fun a => (Corr D a (v a)).support.biUnion (fun c =>
    (sourceExponentWindow D hu (Finsupp.single a ((Corr D a (v a)) c)) x y).image
      (fun q => q-2*(c : ℤ))))

theorem actual_corrected_scalar_exponent_support (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (x y : ActualTensor D hu) :
    Function.support (fun e => actualForm D hu ((correctedField D hu v).coeff e x) y) ⊆
      correctedExponentWindow D hu v x y := by
  intro e he
  change _ ≠ (0 : ℂ) at he
  dsimp only at he
  by_contra outside
  apply he
  rw [corrected_scalar_expansion]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro c hc
  by_contra hn
  have hn' : actualForm D hu ((sourceField D hu
      (Finsupp.single a ((Corr D a (v a)) c))).coeff (e+2*(c : ℤ)) x) y ≠ 0 := by
    simpa only [sourceField_single] using hn
  exact outside (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr ⟨c, hc,
    Finset.mem_image.mpr ⟨e+2*(c : ℤ),
      actual_source_scalar_exponent_support D hu _ x y hn', by ring⟩⟩⟩)

/- This finite readout is unconditional on Corr covariance and source L1.
   It still has the actual Corr coefficients on the left source expansion.
   Replacing it by a homogeneous exp(L1) formula is a subsequent assembly. -/
theorem actual_corrected_scalar_normal_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((correctedField D hu v).coeff e x) y =
      ∑ a ∈ v.support, ∑ c ∈ (Corr D a (v a)).support,
        ∑ m ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr ((Corr D a (v a)) c)).support,
          ((MvPolynomial.basisMonomials (Index D) ℂ).repr ((Corr D a (v a)) c) m) *
            (paritySign (bilinear D a a / 2) * (-1 : ℂ)^(Finsupp.weight (sourceWeight D) m) *
              ∑ s : JetTuple D (occurrences D m),
                binomialProduct D (occurrences D m) s *
                  actualForm D hu x ((sourceField D hu
                    (Finsupp.single a (wordPolynomial D (lowerWord D (occurrences D m) s)))).coeff
                      (-(e+2*(c : ℤ))-2*chargeNorm D a-
                        4*(Finsupp.weight (sourceWeight D) m : ℤ)+
                        2*(weightLoss D (occurrences D m) s : ℤ)) y)) := by
  rw [corrected_scalar_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  exact polynomial_scalar_transpose D hu a ((Corr D a (v a)) c) (e+2*(c : ℤ)) x y

end D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose

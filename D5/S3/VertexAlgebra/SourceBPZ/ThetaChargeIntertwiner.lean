/- GID: D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeIntertwiner
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit paired-residue reconstruction classifies zero-neutral dihedral intertwiners. -/

import D5.S3.VertexAlgebra.SourceBPZ.ThetaChargeRotation
import Mathlib.RepresentationTheory.Intertwining

/-! # Explicit reconstruction of paired charge-residue intertwiners -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.SourceBPZ.ThetaChargeIntertwiner

open D5.S3.VertexAlgebra.SourceBPZ
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open ThetaGradeTraceSplit ThetaGradeRepresentation ThetaChargeRotation

/-- Coefficient filtering onto one actual charge-residue subspace. -/
def gradeChargeResidueProjection (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (k : ℤ) (r : ZMod 3) : grade D k →ₗ[ℂ] gradeChargeResidue D ell k r := by
  classical
  let S : Set (EnergyFiber D k) := {a | ell a.1.1 = r}
  let p : Module.End ℂ (grade D k) :=
    (gradeCoeffEquiv D k).symm.toLinearMap.comp
      ((Finsupp.supported ℂ ℂ S).subtype.comp
        ((Finsupp.restrictDom ℂ ℂ S).comp (gradeCoeffEquiv D k).toLinearMap))
  exact p.codRestrict (gradeChargeResidue D ell k r) (fun x => by
    change gradeCoeffEquiv D k (p x) ∈ Finsupp.supported ℂ ℂ S
    simpa [p] using ((Finsupp.restrictDom ℂ ℂ S) (gradeCoeffEquiv D k x)).property)

private theorem projection_coeff (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (k : ℤ) (r : ZMod 3) (x : grade D k) (a : EnergyFiber D k) :
    gradeCoeffEquiv D k (gradeChargeResidueProjection D ell k r x).val a =
      if ell a.1.1 = r then gradeCoeffEquiv D k x a else 0 := by
  classical
  simp [gradeChargeResidueProjection, Finsupp.filter_apply]

private theorem projection_on_residue (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (k : ℤ) (r s : ZMod 3)
    (x : grade D k) (hx : x ∈ gradeChargeResidue D ell k s) :
    (gradeChargeResidueProjection D ell k r x).val =
      if s = r then x else 0 := by
  classical
  have hc : ∀ a : EnergyFiber D k, ell a.1.1 ≠ s →
      gradeCoeffEquiv D k x a = 0 :=
    (Finsupp.mem_supported' ℂ (gradeCoeffEquiv D k x)).mp hx
  apply (gradeCoeffEquiv D k).injective
  ext a
  rw [projection_coeff]
  by_cases hsr : s = r
  · subst s
    by_cases ha : ell a.1.1 = r
    · simp [ha]
    · simp [ha, hc a ha]
  · by_cases ha : ell a.1.1 = r
    · have has : ell a.1.1 ≠ s := by
        intro has
        exact hsr (has.symm.trans ha)
      simp [hsr, ha, hc a has]
    · simp [hsr, ha]

private theorem residue_decomposition (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (k : ℤ) (x : grade D k) :
    (gradeChargeResidueProjection D ell k 0 x).val +
        (gradeChargeResidueProjection D ell k 1 x).val +
        (gradeChargeResidueProjection D ell k 2 x).val = x := by
  apply (gradeCoeffEquiv D k).injective
  ext a
  simp only [map_add, Finsupp.add_apply, projection_coeff]
  generalize ell a.1.1 = r
  fin_cases r <;> norm_num [show (0 : ZMod 3) ≠ 2 by decide,
    show (1 : ZMod 3) ≠ 2 by decide, show (2 : ZMod 3) ≠ 0 by decide,
    show (2 : ZMod 3) ≠ 1 by decide]

private theorem projection_theta (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (k : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (r : ZMod 3) (x : grade D k) :
    (gradeChargeResidueProjection D ell k r (gradeTheta D k x)).val =
      gradeTheta D k (gradeChargeResidueProjection D ell k (-r) x).val := by
  have hsector (s : ZMod 3) := gradeTheta_mem_gradeChargeResidue_neg D ell k s hD
    (gradeChargeResidueProjection D ell k s x).val
    (gradeChargeResidueProjection D ell k s x).property
  have h := congrArg (fun y : grade D k =>
    (gradeChargeResidueProjection D ell k r (gradeTheta D k y)).val)
    (residue_decomposition D ell k x)
  simp only [map_add, Submodule.coe_add] at h
  rw [projection_on_residue D ell k r (-0) _ (hsector 0),
    projection_on_residue D ell k r (-1) _ (hsector 1),
    projection_on_residue D ell k r (-2) _ (hsector 2)] at h
  have hr : r = 0 ∨ r = 1 ∨ r = 2 :=
    (show ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2 from by decide) r
  rcases hr with rfl | rfl | rfl
  · rw [show (-(0 : ZMod 3)) = 0 by decide]
    simpa [show (-1 : ZMod 3) = 2 by decide,
      show (-2 : ZMod 3) = 1 by decide, show (2 : ZMod 3) ≠ 0 by decide]
      using h.symm
  · rw [show (-1 : ZMod 3) = 2 by decide]
    simpa [show (-1 : ZMod 3) = 2 by decide,
      show (-2 : ZMod 3) = 1 by decide, show (2 : ZMod 3) ≠ 1 by decide]
      using h.symm
  · rw [show (-2 : ZMod 3) = 1 by decide]
    simpa [show (-1 : ZMod 3) = 2 by decide,
      show (-2 : ZMod 3) = 1 by decide, show (0 : ZMod 3) ≠ 2 by decide,
      show (1 : ZMod 3) ≠ 2 by decide] using h.symm

private theorem rotation_on_residue (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (k : ℤ)
    (i r : ZMod 3) (x : grade D k) (hx : x ∈ gradeChargeResidue D ell k r) :
    gradeChargeRotation D ell phase k (Multiplicative.ofAdd i) x =
      chargePhaseScalar phase (i * r) • x := by
  have hc : ∀ a : EnergyFiber D k, ell a.1.1 ≠ r →
      gradeCoeffEquiv D k x a = 0 :=
    (Finsupp.mem_supported' ℂ (gradeCoeffEquiv D k x)).mp hx
  apply (gradeCoeffEquiv D k).injective
  ext a
  rw [gradeChargeRotation_coeff]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases ha : ell a.1.1 = r
  · simp [ha]
  · simp [hc a ha]

private theorem projection_rotation (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (k : ℤ)
    (r i : ZMod 3) (x : grade D k) :
    gradeChargeResidueProjection D ell k r
        (gradeChargeRotation D ell phase k (Multiplicative.ofAdd i) x) =
      chargePhaseScalar phase (i * r) • gradeChargeResidueProjection D ell k r x := by
  classical
  apply Subtype.ext
  apply (gradeCoeffEquiv D k).injective
  ext a
  rw [projection_coeff, gradeChargeRotation_coeff]
  simp only [Submodule.coe_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [projection_coeff]
  by_cases ha : ell a.1.1 = r <;> simp [ha]

private theorem phase_injective (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1) :
    Function.Injective (chargePhaseScalar phase) := by
  intro r s h
  have hz : chargePhaseScalar phase (r - s) = 1 := by
    rw [sub_eq_add_neg, chargePhaseScalar_add, h, ← chargePhaseScalar_add,
      add_neg_cancel, chargePhaseScalar_zero]
  exact sub_eq_zero.mp ((chargePhaseScalar_eq_one_iff phase hphase (r - s)).mp hz)

private theorem intertwiner_preserves_residue (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1)
    (m n : ℤ)
    (T : Representation.IntertwiningMap
      (gradeChargeDihedralRepresentation D ellD phase m)
      (gradeChargeDihedralRepresentation E ellE phase n))
    (r : ZMod 3) (x : grade D m) (hx : x ∈ gradeChargeResidue D ellD m r) :
    T x ∈ gradeChargeResidue E ellE n r := by
  change gradeCoeffEquiv E n (T x) ∈ Finsupp.supported ℂ ℂ
    {a : EnergyFiber E n | ellE a.1.1 = r}
  rw [Finsupp.mem_supported']
  intro a ha
  have ht := LinearMap.congr_fun (T.isIntertwining' (DihedralGroup.r 1)) x
  change T (gradeChargeRotation D ellD phase m (Multiplicative.ofAdd 1) x) =
    gradeChargeRotation E ellE phase n (Multiplicative.ofAdd 1) (T x) at ht
  rw [rotation_on_residue D ellD phase m 1 r x hx, map_smul] at ht
  have hc := congrArg (fun y : grade E n => gradeCoeffEquiv E n y a) ht
  rw [gradeChargeRotation_coeff] at hc
  simp only [toAdd_ofAdd, one_mul, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at hc
  have hne : chargePhaseScalar phase r ≠ chargePhaseScalar phase (ellE a.1.1) := by
    intro heq
    exact ha ((phase_injective phase hphase heq).symm)
  have hz : (chargePhaseScalar phase r - chargePhaseScalar phase (ellE a.1.1)) *
      gradeCoeffEquiv E n (T x) a = 0 := by
    rw [sub_mul, hc, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

private theorem intertwiner_theta (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase) (m n : ℤ)
    (T : Representation.IntertwiningMap
      (gradeChargeDihedralRepresentation D ellD phase m)
      (gradeChargeDihedralRepresentation E ellE phase n)) (x : grade D m) :
    T (gradeTheta D m x) = gradeTheta E n (T x) := by
  have ht := LinearMap.congr_fun (T.isIntertwining' (DihedralGroup.sr 0)) x
  change T (gradeChargeRotation D ellD phase m (Multiplicative.ofAdd (-0))
      (gradeTheta D m x)) =
    gradeChargeRotation E ellE phase n (Multiplicative.ofAdd (-0))
      (gradeTheta E n (T x)) at ht
  have hzD : gradeChargeRotation D ellD phase m (Multiplicative.ofAdd 0) =
      LinearMap.id := (gradeChargeRotationRepresentation D ellD phase m).map_one
  have hzE : gradeChargeRotation E ellE phase n (Multiplicative.ofAdd 0) =
      LinearMap.id := (gradeChargeRotationRepresentation E ellE phase n).map_one
  simpa only [neg_zero, hzD, hzE, LinearMap.id_apply] using ht

/-- The actual submodule of dihedral intertwiners which kill the neutral residue. -/
def gradeChargeIntertwinerH0 (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase) (m n : ℤ) :
    Submodule ℂ (Representation.IntertwiningMap
      (gradeChargeDihedralRepresentation D ellD phase m)
      (gradeChargeDihedralRepresentation E ellE phase n)) where
  carrier := {T | ∀ x : gradeChargeResidue D ellD m 0, T x.val = 0}
  zero_mem' := by intro x; rfl
  add_mem' := by
    intro T U hT hU x
    change T x.val + U x.val = 0
    rw [hT x, hU x, add_zero]
  smul_mem' := by
    intro c T hT x
    change c • T x.val = 0
    rw [hT x, smul_zero]

/-- Actual restriction of an intertwiner to source residue one; rotation forces
its values to lie in target residue one. -/
def gradeChargeIntertwinerRestrict (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1) (m n : ℤ) :
    gradeChargeIntertwinerH0 D E ellD ellE phase m n →ₗ[ℂ]
      (gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1) where
  toFun T :=
    { toFun := fun x => ⟨T.val x.val,
        intertwiner_preserves_residue D E ellD ellE phase hphase m n T.val
          1 x.val x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add T.val x.val y.val
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact map_smul T.val c x.val }
  map_add' T U := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_smul' c T := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

private def pairedMap (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3) (m n : ℤ)
    (B : gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1) :
    grade D m →ₗ[ℂ] grade E n where
  toFun x :=
    (B (gradeChargeResidueProjection D ellD m 1 x)).val +
      gradeTheta E n (B (gradeChargeResidueProjection D ellD m 1 (gradeTheta D m x))).val
  map_add' := by
    intro x y
    simp only [map_add, Submodule.coe_add]
    abel
  map_smul' := by
    intro c x
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply, smul_add]

private theorem pairedMap_theta (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3) (m n : ℤ)
    (B : gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1)
    (x : grade D m) :
    pairedMap D E ellD ellE m n B (gradeTheta D m x) =
      gradeTheta E n (pairedMap D E ellD ellE m n B x) := by
  change
    (B (gradeChargeResidueProjection D ellD m 1 (gradeTheta D m x))).val +
        gradeTheta E n (B (gradeChargeResidueProjection D ellD m 1
          (gradeTheta D m (gradeTheta D m x)))).val =
      gradeTheta E n ((B (gradeChargeResidueProjection D ellD m 1 x)).val +
        gradeTheta E n (B (gradeChargeResidueProjection D ellD m 1
          (gradeTheta D m x))).val)
  rw [gradeTheta_sq, map_add, gradeTheta_sq, add_comm]

private theorem pairedMap_rotation (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase) (m n : ℤ)
    (hE : Matrix.PosDef (E.G.map (Int.cast : ℤ → ℝ)))
    (B : gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1)
    (i : ZMod 3) (x : grade D m) :
    pairedMap D E ellD ellE m n B
        (gradeChargeRotation D ellD phase m (Multiplicative.ofAdd i) x) =
      gradeChargeRotation E ellE phase n (Multiplicative.ofAdd i)
        (pairedMap D E ellD ellE m n B x) := by
  have hmove : gradeTheta D m
      (gradeChargeRotation D ellD phase m (Multiplicative.ofAdd i) x) =
      gradeChargeRotation D ellD phase m (Multiplicative.ofAdd (-i))
        (gradeTheta D m x) := by
    have h := congrArg (fun f : Module.End ℂ (grade D m) => f (gradeTheta D m x))
      (gradeChargeRotation_theta_conj D ellD phase m (Multiplicative.ofAdd i))
    simpa [LinearMap.comp_apply, gradeTheta_sq] using h
  have htarget := gradeTheta_mem_gradeChargeResidue_neg E ellE n 1 hE
    (B (gradeChargeResidueProjection D ellD m 1 (gradeTheta D m x))).val
    (B (gradeChargeResidueProjection D ellD m 1 (gradeTheta D m x))).property
  change
    (B (gradeChargeResidueProjection D ellD m 1
      (gradeChargeRotation D ellD phase m (Multiplicative.ofAdd i) x))).val +
        gradeTheta E n (B (gradeChargeResidueProjection D ellD m 1
          (gradeTheta D m
            (gradeChargeRotation D ellD phase m (Multiplicative.ofAdd i) x)))).val =
      gradeChargeRotation E ellE phase n (Multiplicative.ofAdd i)
        ((B (gradeChargeResidueProjection D ellD m 1 x)).val +
          gradeTheta E n (B (gradeChargeResidueProjection D ellD m 1
            (gradeTheta D m x))).val)
  rw [hmove, projection_rotation D ellD phase m 1 i x,
    projection_rotation D ellD phase m 1 (-i) (gradeTheta D m x), map_add,
    rotation_on_residue E ellE phase n i 1 _
      (B (gradeChargeResidueProjection D ellD m 1 x)).property,
    rotation_on_residue E ellE phase n i (-1) _ htarget]
  simp only [mul_one, mul_neg, map_smul, Submodule.coe_smul]

private theorem pairedMap_zero (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (B : gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1)
    (x : gradeChargeResidue D ellD m 0) :
    pairedMap D E ellD ellE m n B x.val = 0 := by
  have hp : gradeChargeResidueProjection D ellD m 1 x.val = 0 := by
    apply Subtype.ext
    simpa using projection_on_residue D ellD m 1 0 x.val x.property
  have ht := gradeTheta_mem_gradeChargeResidue_neg D ellD m 0 hD x.val x.property
  have hq : gradeChargeResidueProjection D ellD m 1 (gradeTheta D m x.val) = 0 := by
    apply Subtype.ext
    simpa using projection_on_residue D ellD m 1 (-0) (gradeTheta D m x.val) ht
  simp [pairedMap, hp, hq]

/-- Extend a residue-one linear map by zero on residue zero and by theta B theta
on residue two, as a genuine map intertwining all six dihedral elements. -/
def gradeChargeIntertwinerFromResidue (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hE : Matrix.PosDef (E.G.map (Int.cast : ℤ → ℝ))) :
    (gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1) →ₗ[ℂ]
      gradeChargeIntertwinerH0 D E ellD ellE phase m n where
  toFun B :=
    ⟨{ toLinearMap := pairedMap D E ellD ellE m n B
       isIntertwining' := by
         intro g
         apply LinearMap.ext
         intro x
         cases g with
         | r i => exact pairedMap_rotation D E ellD ellE phase m n hE B i x
         | sr i =>
           change pairedMap D E ellD ellE m n B
               (gradeChargeRotation D ellD phase m (Multiplicative.ofAdd (-i))
                 (gradeTheta D m x)) =
             gradeChargeRotation E ellE phase n (Multiplicative.ofAdd (-i))
               (gradeTheta E n (pairedMap D E ellD ellE m n B x))
           rw [pairedMap_rotation D E ellD ellE phase m n hE B (-i),
             pairedMap_theta] },
      pairedMap_zero D E ellD ellE m n hD B⟩
  map_add' B C := by
    apply Subtype.ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change pairedMap D E ellD ellE m n (B + C) x =
      pairedMap D E ellD ellE m n B x + pairedMap D E ellD ellE m n C x
    simp only [pairedMap, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply, Submodule.coe_add, map_add]
    abel
  map_smul' c B := by
    apply Subtype.ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change pairedMap D E ellD ellE m n (c • B) x =
      c • pairedMap D E ellD ellE m n B x
    simp only [pairedMap, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, Submodule.coe_smul, map_smul, smul_add]

/-- The inverse uses the actual residue-one projection and the two lattice thetas. -/
theorem gradeChargeIntertwinerFromResidue_apply (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hE : Matrix.PosDef (E.G.map (Int.cast : ℤ → ℝ)))
    (B : gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1)
    (x : grade D m) :
    (gradeChargeIntertwinerFromResidue D E ellD ellE phase m n hD hE B).val x =
      (B (gradeChargeResidueProjection D ellD m 1 x)).val +
        gradeTheta E n (B (gradeChargeResidueProjection D ellD m 1
          (gradeTheta D m x))).val := rfl

theorem gradeChargeIntertwinerRestrict_fromResidue (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hE : Matrix.PosDef (E.G.map (Int.cast : ℤ → ℝ)))
    (B : gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1) :
    gradeChargeIntertwinerRestrict D E ellD ellE phase hphase m n
        (gradeChargeIntertwinerFromResidue D E ellD ellE phase m n hD hE B) = B := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (gradeChargeIntertwinerFromResidue D E ellD ellE phase m n hD hE B).val
    x.val = (B x).val
  rw [gradeChargeIntertwinerFromResidue_apply]
  have hp : gradeChargeResidueProjection D ellD m 1 x.val = x := by
    apply Subtype.ext
    simpa using projection_on_residue D ellD m 1 1 x.val x.property
  have ht := gradeTheta_mem_gradeChargeResidue_neg D ellD m 1 hD x.val x.property
  have hq : gradeChargeResidueProjection D ellD m 1 (gradeTheta D m x.val) = 0 := by
    apply Subtype.ext
    simpa [show (-1 : ZMod 3) ≠ 1 by decide] using
      projection_on_residue D ellD m 1 (-1) (gradeTheta D m x.val) ht
  rw [hp, hq]
  simp

theorem gradeChargeIntertwinerFromResidue_restrict (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hE : Matrix.PosDef (E.G.map (Int.cast : ℤ → ℝ)))
    (T : gradeChargeIntertwinerH0 D E ellD ellE phase m n) :
    gradeChargeIntertwinerFromResidue D E ellD ellE phase m n hD hE
        (gradeChargeIntertwinerRestrict D E ellD ellE phase hphase m n T) = T := by
  apply Subtype.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (gradeChargeIntertwinerFromResidue D E ellD ellE phase m n hD hE
    (gradeChargeIntertwinerRestrict D E ellD ellE phase hphase m n T)).val x = T.val x
  rw [gradeChargeIntertwinerFromResidue_apply]
  change T.val (gradeChargeResidueProjection D ellD m 1 x).val +
    gradeTheta E n (T.val (gradeChargeResidueProjection D ellD m 1
      (gradeTheta D m x)).val) = T.val x
  rw [← intertwiner_theta D E ellD ellE phase m n T.val]
  have hp : gradeTheta D m (gradeChargeResidueProjection D ellD m 1
      (gradeTheta D m x)).val = (gradeChargeResidueProjection D ellD m 2 x).val := by
    rw [projection_theta D ellD m hD 1 x, gradeTheta_sq,
      show (-1 : ZMod 3) = 2 by decide]
  rw [hp]
  have h := congrArg T.val (residue_decomposition D ellD m x)
  rw [map_add, map_add, T.property (gradeChargeResidueProjection D ellD m 0 x),
    zero_add] at h
  exact h

/-- Specified restriction/reconstruction equivalence for the paired nonzero
residues, across independent lattices and arbitrary signed energy grades. -/
def gradeChargeIntertwinerEquiv (D E : LatticeData)
    (ellD : Charge D →+ ZMod 3) (ellE : Charge E →+ ZMod 3)
    (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hE : Matrix.PosDef (E.G.map (Int.cast : ℤ → ℝ))) :
    gradeChargeIntertwinerH0 D E ellD ellE phase m n ≃ₗ[ℂ]
      (gradeChargeResidue D ellD m 1 →ₗ[ℂ] gradeChargeResidue E ellE n 1) :=
  LinearEquiv.ofLinearMap
    (gradeChargeIntertwinerRestrict D E ellD ellE phase hphase m n)
    (gradeChargeIntertwinerFromResidue D E ellD ellE phase m n hD hE)
    (by
      apply LinearMap.ext
      intro B
      exact gradeChargeIntertwinerRestrict_fromResidue D E ellD ellE phase
        hphase m n hD hE B)
    (by
      apply LinearMap.ext
      intro T
      exact gradeChargeIntertwinerFromResidue_restrict D E ellD ellE phase
        hphase m n hD hE T)

end D5.S3.VertexAlgebra.SourceBPZ.ThetaChargeIntertwiner

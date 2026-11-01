/- GID: D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors
   mirror-E: none(waiver:no-experimental-evidence)
   anchors: []
   utility: none
   digest: Real incidence sectors of an arbitrary finite projective plane. -/

import D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Configuration

namespace D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors

variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L]
  [ProjectivePlane P L]

/-- The order of the actual plane, regarded as a real number. -/
abbrev orderR : ℝ := (ProjectivePlaneIntegerLattice.q (P := P) (L := L) : ℝ)

/-- The original incidence matrix: point rows and line columns. -/
def incidenceMatrix : Matrix P L ℝ := fun x l => (ProjectivePlaneIntegerLattice.row l x : ℝ)

/-- The original incidence map from line coordinates to point coordinates. -/
def toPoints : (L → ℝ) →ₗ[ℝ] (P → ℝ) :=
  (incidenceMatrix (P := P) (L := L)).mulVecLin

/-- Its transpose, from original points to original lines. -/
def toLines : (P → ℝ) →ₗ[ℝ] (L → ℝ) :=
  (incidenceMatrix (P := P) (L := L))ᵀ.mulVecLin

private lemma row_sum (l : L) :
    ∑ x : P, incidenceMatrix x l = orderR (P := P) (L := L) + 1 := by
  exact_mod_cast ProjectivePlaneIntegerLattice.row_total (P := P) l

private lemma col_sum (x : P) :
    ∑ l : L, incidenceMatrix x l = orderR (P := P) (L := L) + 1 := by
  exact_mod_cast ProjectivePlaneIntegerLattice.column_total (L := L) x

private lemma points_gram (x y : P) :
    ∑ l : L, incidenceMatrix x l * incidenceMatrix y l =
      if x = y then orderR (P := P) (L := L) + 1 else 1 := by
  exact_mod_cast ProjectivePlaneIntegerLattice.column_gram (L := L) x y

private lemma lines_gram (l k : L) :
    ∑ x : P, incidenceMatrix x l * incidenceMatrix x k =
      if l = k then orderR (P := P) (L := L) + 1 else 1 := by
  exact_mod_cast ProjectivePlaneIntegerLattice.row_gram (P := P) l k

private lemma sum_toPoints (y : L → ℝ) :
    ∑ x, toPoints y x = (orderR (P := P) (L := L) + 1) * ∑ l, y l := by
  simp only [toPoints, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, row_sum]
  rw [Finset.mul_sum]

private lemma sum_toLines (x : P → ℝ) :
    ∑ l, toLines x l = (orderR (P := P) (L := L) + 1) * ∑ p, x p := by
  simp only [toLines, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, col_sum]
  rw [Finset.mul_sum]

private lemma toPoints_toLines (x : P → ℝ) (p : P) :
    toPoints (toLines (L := L) x) p = orderR (P := P) (L := L) * x p + ∑ r, x r := by
  simp only [toPoints, toLines, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, points_gram]
  calc
    _ = ∑ r : P, ((if r = p then orderR (P := P) (L := L) * x p else 0) + x r) := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : r = p
      · subst r; simp; ring
      · simp [h, Ne.symm h]
    _ = _ := by classical simp [Finset.sum_add_distrib]

private lemma toLines_toPoints (y : L → ℝ) (l : L) :
    toLines (toPoints (P := P) y) l = orderR (P := P) (L := L) * y l + ∑ k, y k := by
  simp only [toPoints, toLines, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, lines_gram]
  calc
    _ = ∑ k : L, ((if k = l then orderR (P := P) (L := L) * y l else 0) + y k) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = l
      · subst k; simp; ring
      · simp [h, Ne.symm h]
    _ = _ := by classical simp [Finset.sum_add_distrib]

/-- The zero-sum coordinate subspace, with no choice of a distinguished label. -/
def zeroSum (I : Type*) [Fintype I] : Submodule ℝ (I → ℝ) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all [Finset.sum_add_distrib]
  smul_mem' := by intro a x hx; simp_all [← Finset.smul_sum]

private lemma orderR_pos : 0 < orderR (P := P) (L := L) := by
  have h := ProjectivePlaneIntegerLattice.q_ge_two (P := P) (L := L)
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2) h)

/-- The positive singular value on the nonconstant incidence sectors. -/
def rootOrder : ℝ := Real.sqrt (orderR (P := P) (L := L))

private lemma rootOrder_pos : 0 < rootOrder (P := P) (L := L) :=
  Real.sqrt_pos.2 orderR_pos

private lemma rootOrder_sq : rootOrder (P := P) (L := L) ^ 2 = orderR (P := P) (L := L) :=
  Real.sq_sqrt (le_of_lt orderR_pos)

/-- Normalized transposed incidence on zero-sum coordinates. -/
def normalizedToLines : zeroSum P →ₗ[ℝ] zeroSum L where
  toFun x := ⟨(rootOrder (P := P) (L := L))⁻¹ • toLines x, by
    change ∑ l, (rootOrder (P := P) (L := L))⁻¹ * toLines x l = 0
    rw [← Finset.mul_sum, sum_toLines, x.property, mul_zero, mul_zero]⟩
  map_add' x y := by apply Subtype.ext; simp [map_add, smul_add]
  map_smul' a x := by apply Subtype.ext; simp [map_smul, smul_smul, mul_comm]

/-- Normalized incidence in the opposite direction. -/
def normalizedToPoints : zeroSum L →ₗ[ℝ] zeroSum P where
  toFun y := ⟨(rootOrder (P := P) (L := L))⁻¹ • toPoints y, by
    change ∑ p, (rootOrder (P := P) (L := L))⁻¹ * toPoints y p = 0
    rw [← Finset.mul_sum, sum_toPoints, y.property, mul_zero, mul_zero]⟩
  map_add' x y := by apply Subtype.ext; simp [map_add, smul_add]
  map_smul' a x := by apply Subtype.ext; simp [map_smul, smul_smul, mul_comm]

/-- Incidence divided by the positive square root of the plane order identifies
its original point and line zero-sum spaces. -/
def balancedEquiv : zeroSum P ≃ₗ[ℝ] zeroSum L where
  toLinearMap := normalizedToLines
  invFun := normalizedToPoints
  left_inv x := by
    apply Subtype.ext
    funext p
    change (rootOrder (P := P) (L := L))⁻¹ *
      toPoints ((rootOrder (P := P) (L := L))⁻¹ • toLines x) p = x p
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [toPoints_toLines, x.property, add_zero, ← rootOrder_sq]
    have hs := ne_of_gt (rootOrder_pos (P := P) (L := L))
    field_simp [hs] <;> ring
  right_inv y := by
    apply Subtype.ext
    funext l
    change (rootOrder (P := P) (L := L))⁻¹ *
      toLines ((rootOrder (P := P) (L := L))⁻¹ • toPoints y) l = y l
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [toLines_toPoints, y.property, add_zero, ← rootOrder_sq]
    have hs := ne_of_gt (rootOrder_pos (P := P) (L := L))
    field_simp [hs] <;> ring

/-- Arithmetic mean of a finite coordinate vector, with inverse-zero convention. -/
def mean {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * ∑ i, x i

private lemma mean_add {I : Type*} [Fintype I] (x y : I → ℝ) :
    mean (x + y) = mean x + mean y := by
  simp [mean, Finset.sum_add_distrib, mul_add]

private lemma mean_smul {I : Type*} [Fintype I] (a : ℝ) (x : I → ℝ) :
    mean (a • x) = a * mean x := by
  simp [mean, ← Finset.mul_sum, mul_left_comm]

private lemma mean_const {I : Type*} [Fintype I] (hn : Fintype.card I ≠ 0) (a : ℝ) :
    mean (fun _ : I => a) = a := by
  simp [mean, Nat.cast_ne_zero.mpr hn, ← mul_assoc]

private lemma mean_zeroSum {I : Type*} [Fintype I] (x : zeroSum I) : mean (x : I → ℝ) = 0 := by
  rw [mean, x.property, mul_zero]

/-- Separating the constant coordinate from a vector on a nonempty finite set. -/
def splitConstant (I : Type*) [Fintype I] (hn : Fintype.card I ≠ 0) :
    (I → ℝ) ≃ₗ[ℝ] ℝ × zeroSum I where
  toFun x := (mean x, ⟨x - fun _ => mean x, by
    change ∑ i, (x i - mean x) = 0
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [mean, Nat.cast_ne_zero.mpr hn]⟩)
  invFun z := (fun _ => z.1) + z.2
  left_inv x := by ext i; change mean x + (x i - mean x) = x i; ring
  right_inv z := by
    have hm : mean ((fun _ : I => z.1) + (z.2 : I → ℝ)) = z.1 := by
      rw [mean_add, mean_const hn, mean_zeroSum, add_zero]
    apply Prod.ext
    · exact hm
    · apply Subtype.ext; funext i; simp [hm]
  map_add' x y := by
    apply Prod.ext
    · exact mean_add x y
    · apply Subtype.ext; funext i; simp [mean_add]; ring
  map_smul' a x := by
    apply Prod.ext
    · exact mean_smul a x
    · apply Subtype.ext; funext i; simp [mean_smul]; ring

private lemma card_points_ne_zero : Fintype.card P ≠ 0 := by
  rw [ProjectivePlane.card_points P L]
  omega

private lemma card_lines_ne_zero : Fintype.card L ≠ 0 := by
  rw [ProjectivePlane.card_lines P L]
  omega

private def sumDiff (A : Type*) [AddCommGroup A] [Module ℝ A] : (A × A) ≃ₗ[ℝ] A × A where
  toFun z := (z.1 + z.2, z.1 - z.2)
  invFun z := ((1 / 2 : ℝ) • (z.1 + z.2), (1 / 2 : ℝ) • (z.1 - z.2))
  left_inv z := by ext <;> dsimp <;> module
  right_inv z := by ext <;> dsimp <;> module
  map_add' z w := by ext <;> dsimp <;> module
  map_smul' a z := by ext <;> dsimp <;> module

/-- All coordinates in the four original-incidence sectors. The first two
coordinates give the constant and bipartition lines; the last two give the
positive and negative nonconstant incidence sectors. -/
def sectorEquiv : ((ℝ × ℝ) × (zeroSum P × zeroSum P)) ≃ₗ[ℝ]
    ((P → ℝ) × (L → ℝ)) :=
  ((sumDiff ℝ).prodCongr (sumDiff (zeroSum P))) |>.trans
    (LinearEquiv.prodProdProdComm ℝ ℝ ℝ (zeroSum P) (zeroSum P)) |>.trans
    ((LinearEquiv.refl ℝ (ℝ × zeroSum P)).prodCongr
      ((LinearEquiv.refl ℝ ℝ).prodCongr (balancedEquiv (P := P) (L := L)))) |>.trans
    ((splitConstant P card_points_ne_zero).symm.prodCongr
      (splitConstant L card_lines_ne_zero).symm)

private lemma sectorEquiv_apply (z : (ℝ × ℝ) × (zeroSum P × zeroSum P)) :
    sectorEquiv (L := L) z =
      ((fun p => z.1.1 + z.1.2 + (z.2.1 p + z.2.2 p)),
       (fun l => z.1.1 - z.1.2 +
         balancedEquiv (P := P) (L := L) (z.2.1 - z.2.2) l)) := rfl

/-- Original-label constant and bipartition directions, followed by the two
nonconstant incidence sectors. -/
def sectorConstant : ℝ →ₗ[ℝ] ((P → ℝ) × (L → ℝ)) :=
  (sectorEquiv (P := P) (L := L)).toLinearMap.comp
    { toFun := fun a => ((a, 0), (0, 0))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

def sectorBipartition : ℝ →ₗ[ℝ] ((P → ℝ) × (L → ℝ)) :=
  (sectorEquiv (P := P) (L := L)).toLinearMap.comp
    { toFun := fun b => ((0, b), (0, 0))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

def sectorPlus : zeroSum P →ₗ[ℝ] ((P → ℝ) × (L → ℝ)) :=
  (sectorEquiv (P := P) (L := L)).toLinearMap.comp
    { toFun := fun x => ((0, 0), (x, 0))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

def sectorMinus : zeroSum P →ₗ[ℝ] ((P → ℝ) × (L → ℝ)) :=
  (sectorEquiv (P := P) (L := L)).toLinearMap.comp
    { toFun := fun x => ((0, 0), (0, x))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- Every original point/line vector has unique coordinates in the four sectors. -/
theorem existsUnique_sector_coordinates (z : (P → ℝ) × (L → ℝ)) :
    ∃! c : (ℝ × ℝ) × (zeroSum P × zeroSum P),
      sectorEquiv (L := L) c = z :=
  (sectorEquiv (P := P) (L := L)).bijective.existsUnique z

private lemma finrank_zeroSum (I : Type*) [Fintype I] (hn : Fintype.card I ≠ 0) :
    Module.finrank ℝ (zeroSum I) = Fintype.card I - 1 := by
  have h := (splitConstant I hn).finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Module.finrank_prod,
    Module.finrank_self] at h
  omega

/-- The actual four sectors have dimensions 1, 1, v-1, v-1. -/
theorem sector_finranks :
    Module.finrank ℝ (LinearMap.range (sectorConstant (P := P) (L := L))) = 1 ∧
    Module.finrank ℝ (LinearMap.range (sectorBipartition (P := P) (L := L))) = 1 ∧
    Module.finrank ℝ (LinearMap.range (sectorPlus (P := P) (L := L))) = Fintype.card P - 1 ∧
    Module.finrank ℝ (LinearMap.range (sectorMinus (P := P) (L := L))) = Fintype.card P - 1 := by
  have hc : Function.Injective (sectorConstant (P := P) (L := L)) := by
    intro a b h
    exact congrArg (fun z => z.1.1) ((sectorEquiv (P := P) (L := L)).injective h)
  have hb : Function.Injective (sectorBipartition (P := P) (L := L)) := by
    intro a b h
    exact congrArg (fun z => z.1.2) ((sectorEquiv (P := P) (L := L)).injective h)
  have hp : Function.Injective (sectorPlus (P := P) (L := L)) := by
    intro a b h
    exact congrArg (fun z => z.2.1) ((sectorEquiv (P := P) (L := L)).injective h)
  have hm : Function.Injective (sectorMinus (P := P) (L := L)) := by
    intro a b h
    exact congrArg (fun z => z.2.2) ((sectorEquiv (P := P) (L := L)).injective h)
  simp only [LinearMap.finrank_range_of_inj hc, LinearMap.finrank_range_of_inj hb,
    LinearMap.finrank_range_of_inj hp, LinearMap.finrank_range_of_inj hm,
    Module.finrank_self, finrank_zeroSum P card_points_ne_zero, and_self]

private lemma transpose_pairing (x : P → ℝ) (y : L → ℝ) :
    ∑ l, toLines x l * y l = ∑ p, x p * toPoints y p := by
  simp only [toLines, toPoints, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro l _
  ring

private lemma balancedEquiv_dot (x y : zeroSum P) :
    ∑ l : L, balancedEquiv (L := L) x l * balancedEquiv (L := L) y l =
      ∑ p : P, x p * y p := by
  change (∑ l : L, (rootOrder (P := P) (L := L))⁻¹ * toLines x l *
    ((rootOrder (P := P) (L := L))⁻¹ * toLines y l)) = _
  calc
    _ = (rootOrder (P := P) (L := L))⁻¹ ^ 2 *
        ∑ l : L, toLines x l * toLines y l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = (rootOrder (P := P) (L := L))⁻¹ ^ 2 *
        (orderR (P := P) (L := L) * ∑ p : P, x p * y p) := by
      rw [transpose_pairing]
      simp_rw [toPoints_toLines, y.property, add_zero]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [← rootOrder_sq]
      have hs := ne_of_gt (rootOrder_pos (P := P) (L := L))
      field_simp [hs] <;> ring

/-- Euclidean dot product on the original disjoint point/line coordinates. -/
def vertexDot (z w : (P → ℝ) × (L → ℝ)) : ℝ :=
  (∑ p, z.1 p * w.1 p) + ∑ l, z.2 l * w.2 l

/-- The four-sector coordinates are orthogonal, with constant-sector weight
2v and nonconstant-sector weight 2. -/
theorem sectorEquiv_dot (z w : (ℝ × ℝ) × (zeroSum P × zeroSum P)) :
    vertexDot (sectorEquiv (L := L) z) (sectorEquiv (L := L) w) =
      2 * (Fintype.card P : ℝ) * (z.1.1 * w.1.1 + z.1.2 * w.1.2) +
      2 * ((∑ p : P, z.2.1 p * w.2.1 p) + ∑ p : P, z.2.2 p * w.2.2 p) := by
  rw [vertexDot, sectorEquiv_apply, sectorEquiv_apply]
  have expand (I : Type*) [Fintype I] (a b : ℝ) (x y : zeroSum I) :
      (∑ i, (a + x i) * (b + y i)) =
        (Fintype.card I : ℝ) * a * b + ∑ i, x i * y i := by
    calc
      _ = ∑ i, (a*b + a*y i + b*x i + x i*y i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, ← Finset.mul_sum, x.property, y.property]
  change (∑ p : P, (z.1.1 + z.1.2 + (z.2.1 + z.2.2) p) *
      (w.1.1 + w.1.2 + (w.2.1 + w.2.2) p)) +
      (∑ l : L, (z.1.1 - z.1.2 + balancedEquiv (L := L) (z.2.1 - z.2.2) l) *
      (w.1.1 - w.1.2 + balancedEquiv (L := L) (w.2.1 - w.2.2) l)) = _
  rw [expand P, expand L, balancedEquiv_dot,
    ← ProjectivePlane.card_points_eq_card_lines P L]
  simp only [Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply]
  simp_rw [add_mul, sub_mul, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

private lemma toPoints_const (a : ℝ) :
    toPoints (fun _ : L => a) = fun _ : P => (orderR (P := P) (L := L) + 1) * a := by
  funext p
  change (∑ l : L, incidenceMatrix p l * a) = _
  rw [← Finset.sum_mul, col_sum]

private lemma toLines_const (a : ℝ) :
    toLines (fun _ : P => a) = fun _ : L => (orderR (P := P) (L := L) + 1) * a := by
  funext l
  change (∑ p : P, incidenceMatrix p l * a) = _
  rw [← Finset.sum_mul, row_sum]

private lemma toPoints_balanced (x : zeroSum P) :
    toPoints (balancedEquiv (P := P) (L := L) x) =
      rootOrder (P := P) (L := L) • (x : P → ℝ) := by
  funext p
  change toPoints ((rootOrder (P := P) (L := L))⁻¹ • toLines x) p = _
  rw [map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, toPoints_toLines, x.property, add_zero]
  rw [← rootOrder_sq]
  have hs := ne_of_gt (rootOrder_pos (P := P) (L := L))
  field_simp

private lemma toLines_balanced (x : zeroSum P) :
    toLines x = rootOrder (P := P) (L := L) •
      (balancedEquiv (P := P) (L := L) x : L → ℝ) := by
  funext l
  change toLines x l = rootOrder (P := P) (L := L) *
    ((rootOrder (P := P) (L := L))⁻¹ * toLines x l)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt rootOrder_pos), one_mul]

/-- Adjacency of the original projective-plane incidence graph, on its two
original coordinate spaces. -/
def adjacency : ((P → ℝ) × (L → ℝ)) →ₗ[ℝ] ((P → ℝ) × (L → ℝ)) where
  toFun z := (toPoints z.2, toLines z.1)
  map_add' z w := by simp
  map_smul' a z := by simp

/-- Orthogonal centering across all original vertices. The two sides have
identical cardinality, so the common mean is the average of their means. -/
def center : ((P → ℝ) × (L → ℝ)) →ₗ[ℝ] ((P → ℝ) × (L → ℝ)) where
  toFun z :=
    (z.1 - fun _ => (mean z.1 + mean z.2) / 2,
     z.2 - fun _ => (mean z.1 + mean z.2) / 2)
  map_add' z w := by
    ext i <;> simp [mean_add] <;> ring
  map_smul' a z := by
    ext i <;> simp [mean_smul] <;> ring

/-- The centered Gram operator of the squared-distance assignment with edge
value 1 and distinct nonedge value delta: delta H/2 + (delta-1) HAH/2. -/
def gramAction (delta : ℝ) : ((P → ℝ) × (L → ℝ)) →ₗ[ℝ] ((P → ℝ) × (L → ℝ)) :=
  (delta / 2) • center + ((delta - 1) / 2) • (center.comp (adjacency.comp center))

private lemma center_sector (z : (ℝ × ℝ) × (zeroSum P × zeroSum P)) :
    center (sectorEquiv (L := L) z) = sectorEquiv (L := L) ((0, z.1.2), z.2) := by
  rw [sectorEquiv_apply, sectorEquiv_apply]
  have hP : mean (fun p : P => z.1.1 + z.1.2 + (z.2.1 p + z.2.2 p)) =
      z.1.1 + z.1.2 := by
    change mean ((fun _ : P => z.1.1 + z.1.2) + ((z.2.1 + z.2.2 : zeroSum P) : P → ℝ)) = _
    rw [mean_add, mean_const card_points_ne_zero, mean_zeroSum, add_zero]
  have hL : mean (fun l : L => z.1.1 - z.1.2 +
      balancedEquiv (P := P) (L := L) (z.2.1 - z.2.2) l) = z.1.1 - z.1.2 := by
    change mean ((fun _ : L => z.1.1 - z.1.2) +
      ((balancedEquiv (L := L) (z.2.1 - z.2.2) : zeroSum L) : L → ℝ)) = _
    rw [mean_add, mean_const card_lines_ne_zero, mean_zeroSum, add_zero]
  ext i <;> simp [center, hP, hL] <;> ring

private lemma adjacency_sector (z : (ℝ × ℝ) × (zeroSum P × zeroSum P)) :
    adjacency (sectorEquiv (L := L) z) = sectorEquiv (L := L)
      (((orderR (P := P) (L := L) + 1) * z.1.1,
        -(orderR (P := P) (L := L) + 1) * z.1.2),
       (rootOrder (P := P) (L := L) • z.2.1,
        -rootOrder (P := P) (L := L) • z.2.2)) := by
  rw [sectorEquiv_apply, sectorEquiv_apply]
  change (toPoints ((fun _ : L => z.1.1 - z.1.2) +
    (balancedEquiv (L := L) (z.2.1 - z.2.2) : L → ℝ)),
    toLines ((fun _ : P => z.1.1 + z.1.2) + (z.2.1 + z.2.2 : zeroSum P))) = _
  rw [map_add, map_add, toPoints_const, toPoints_balanced, toLines_const]
  simp only [Submodule.coe_add, map_add, toLines_balanced, Submodule.coe_smul,
    map_sub, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ext i <;> simp <;> ring

/-- Complete diagonal action of the centered Gram operator in the original
incidence sectors, including every singular parameter. -/
theorem gramAction_sector (delta : ℝ) (z : (ℝ × ℝ) × (zeroSum P × zeroSum P)) :
    gramAction delta (sectorEquiv (L := L) z) = sectorEquiv (L := L)
      ((0, ((orderR (P := P) (L := L) + 1 - orderR (P := P) (L := L) * delta) / 2) * z.1.2),
       ((((1 + rootOrder (P := P) (L := L)) * delta - rootOrder (P := P) (L := L)) / 2) • z.2.1,
        ((rootOrder (P := P) (L := L) + (1 - rootOrder (P := P) (L := L)) * delta) / 2) • z.2.2)) := by
  simp only [gramAction, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [center_sector, adjacency_sector, center_sector]
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext i <;> simp <;> ring

/-- The scalar of the bipartition sector. -/
def bipartitionScalar (delta : ℝ) : ℝ :=
  (orderR (P := P) (L := L) + 1 - orderR (P := P) (L := L) * delta) / 2

/-- The scalar of the positive nonconstant incidence sector. -/
def plusScalar (delta : ℝ) : ℝ :=
  ((1 + rootOrder (P := P) (L := L)) * delta - rootOrder (P := P) (L := L)) / 2

/-- The scalar of the negative nonconstant incidence sector. -/
def minusScalar (delta : ℝ) : ℝ :=
  (rootOrder (P := P) (L := L) + (1 - rootOrder (P := P) (L := L)) * delta) / 2

private lemma gramAction_quadratic (delta : ℝ)
    (z : (ℝ × ℝ) × (zeroSum P × zeroSum P)) :
    vertexDot (sectorEquiv (L := L) z) (gramAction delta (sectorEquiv (L := L) z)) =
      2 * (Fintype.card P : ℝ) * bipartitionScalar (P := P) (L := L) delta * z.1.2 ^ 2 +
      2 * plusScalar (P := P) (L := L) delta * (∑ p : P, z.2.1 p ^ 2) +
      2 * minusScalar (P := P) (L := L) delta * (∑ p : P, z.2.2 p ^ 2) := by
  rw [gramAction_sector, sectorEquiv_dot]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have scale (a : ℝ) (x : zeroSum P) :
      (∑ p : P, x p * (a * x p)) = a * ∑ p : P, x p ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [scale, scale]
  dsimp [bipartitionScalar, plusScalar, minusScalar]
  ring

private lemma exists_nonzero_balanced : ∃ x : zeroSum P, x ≠ 0 := by
  have hv : 1 < Fintype.card P := by
    rw [ProjectivePlane.card_points P L]
    have hq := ProjectivePlane.one_lt_order P L
    nlinarith
  have hdim := (sector_finranks (P := P) (L := L)).2.2.1
  letI : Nontrivial (LinearMap.range (sectorPlus (P := P) (L := L))) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : LinearMap.range (sectorPlus (P := P) (L := L)))
  obtain ⟨x, hx⟩ := u.property
  refine ⟨x, ?_⟩
  intro hxzero
  apply hu
  apply Subtype.ext
  rw [← hx, hxzero, map_zero]
  rfl

/-- Nonnegativity on all actual original-label vectors is equivalent to the
three sector inequalities. -/
theorem gramAction_nonnegative_iff (delta : ℝ) :
    (∀ z : (P → ℝ) × (L → ℝ), 0 ≤ vertexDot z (gramAction delta z)) ↔
      0 ≤ bipartitionScalar (P := P) (L := L) delta ∧
      0 ≤ plusScalar (P := P) (L := L) delta ∧
      0 ≤ minusScalar (P := P) (L := L) delta := by
  have hv : (0 : ℝ) < Fintype.card P := by exact_mod_cast Nat.pos_of_ne_zero card_points_ne_zero
  constructor
  · intro h
    have hb := h (sectorEquiv (L := L) ((0, 1), (0, 0)))
    rw [gramAction_quadratic] at hb
    simp only [one_pow, mul_one, ZeroMemClass.coe_zero, Pi.zero_apply, zero_pow (by omega : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero, add_zero] at hb
    obtain ⟨x, hx⟩ := exists_nonzero_balanced (P := P) (L := L)
    have hx' : (x : P → ℝ) ≠ 0 := fun he => hx (Subtype.ext he)
    have hs : 0 < ∑ p : P, x p ^ 2 := by
      simpa only [dotProduct, Pi.star_apply, star_trivial, pow_two] using
        (Matrix.dotProduct_self_star_pos_iff.mpr hx')
    have hp := h (sectorEquiv (L := L) ((0, 0), (x, 0)))
    have hm := h (sectorEquiv (L := L) ((0, 0), (0, x)))
    rw [gramAction_quadratic] at hp hm
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, zero_pow (by omega : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero, zero_add, add_zero] at hp hm
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨hb, hp, hm⟩ z
    obtain ⟨w, hw, _⟩ := existsUnique_sector_coordinates (L := L) z
    rw [← hw, gramAction_quadratic]
    exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv.le) hb) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) hp) (Finset.sum_nonneg (fun p _ => sq_nonneg _))))
      (mul_nonneg (mul_nonneg (by norm_num) hm) (Finset.sum_nonneg (fun p _ => sq_nonneg _)))

/-- Exact nonnegative parameter interval for the original incidence centered
Gram form. No existence of a plane of any prescribed order is assumed. -/
theorem gramAction_nonnegative_interval (delta : ℝ) :
    (∀ z : (P → ℝ) × (L → ℝ), 0 ≤ vertexDot z (gramAction delta z)) ↔
      rootOrder (P := P) (L := L) / (1 + rootOrder (P := P) (L := L)) ≤ delta ∧
      delta ≤ (orderR (P := P) (L := L) + 1) / orderR (P := P) (L := L) := by
  rw [gramAction_nonnegative_iff]
  have hq := orderR_pos (P := P) (L := L)
  have hs := rootOrder_pos (P := P) (L := L)
  have hs2 := rootOrder_sq (P := P) (L := L)
  have hs1 : 1 < rootOrder (P := P) (L := L) := by
    have hq2 : 2 ≤ orderR (P := P) (L := L) := by
      exact_mod_cast ProjectivePlaneIntegerLattice.q_ge_two (P := P) (L := L)
    nlinarith
  have hden : 0 < 1 + rootOrder (P := P) (L := L) := by linarith
  simp only [bipartitionScalar, plusScalar, minusScalar]
  rw [le_div_iff₀ hq, div_le_iff₀ hden]
  constructor
  · rintro ⟨hb, hp, _⟩
    constructor <;> nlinarith
  · rintro ⟨ha, hb⟩
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    have haux : 0 ≤ (rootOrder (P := P) (L := L) - 1) *
        (orderR (P := P) (L := L) + 1 - orderR (P := P) (L := L) * delta) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hpositive : 0 < orderR (P := P) (L := L) + 1 - rootOrder (P := P) (L := L) := by
      nlinarith [sq_nonneg (rootOrder (P := P) (L := L) - 1 / 2)]
    have hmul : 0 ≤ orderR (P := P) (L := L) *
        (rootOrder (P := P) (L := L) + (1 - rootOrder (P := P) (L := L)) * delta) := by
      nlinarith only [haux, hpositive]
    exact div_nonneg (nonneg_of_mul_nonneg_right hmul hq) (by norm_num)

/-- The coordinate identification with the original disjoint vertex type. -/
def vertexEquiv : ((P ⊕ L) → ℝ) ≃ₗ[ℝ] ((P → ℝ) × (L → ℝ)) where
  toFun f := (f ∘ Sum.inl, f ∘ Sum.inr)
  invFun z := Sum.elim z.1 z.2
  left_inv f := by ext i; cases i <;> rfl
  right_inv z := rfl
  map_add' f g := rfl
  map_smul' a f := rfl

private def allOnes : Matrix (P ⊕ L) (P ⊕ L) ℝ := fun _ _ => 1

/-- The adjacency matrix of the original incidence graph. -/
def adjacencyMatrix : Matrix (P ⊕ L) (P ⊕ L) ℝ :=
  Matrix.fromBlocks 0 incidenceMatrix (incidenceMatrix (P := P) (L := L))ᵀ 0

/-- The squared-distance assignment: zero on the diagonal, one on original
point-line incidences, and delta on all distinct nonedges. -/
def distanceMatrix (delta : ℝ) : Matrix (P ⊕ L) (P ⊕ L) ℝ := by
  classical
  exact delta • (allOnes - 1) + (1 - delta) • adjacencyMatrix

/-- Uniform centering on the original disjoint vertex set. -/
def centeringMatrix : Matrix (P ⊕ L) (P ⊕ L) ℝ := by
  classical
  exact 1 - (Fintype.card (P ⊕ L) : ℝ)⁻¹ • allOnes

/-- The actual doubly centered squared-distance Gram matrix. -/
def centeredGram (delta : ℝ) : Matrix (P ⊕ L) (P ⊕ L) ℝ :=
  (-1 / 2 : ℝ) • (centeringMatrix * distanceMatrix delta * centeringMatrix)

private lemma adjacencyMatrix_action (f : (P ⊕ L) → ℝ) :
    vertexEquiv (adjacencyMatrix *ᵥ f) = adjacency (vertexEquiv f) := by
  rw [adjacencyMatrix, Matrix.fromBlocks_mulVec]
  simp [vertexEquiv, adjacency, toPoints, toLines]

private lemma allOnes_action (f : (P ⊕ L) → ℝ) :
    allOnes *ᵥ f = fun _ => ∑ i, f i := by
  ext i
  simp [allOnes, Matrix.mulVec, dotProduct]

private lemma centeringMatrix_action (f : (P ⊕ L) → ℝ) :
    vertexEquiv (centeringMatrix *ᵥ f) = center (vertexEquiv f) := by
  classical
  rw [centeringMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, allOnes_action]
  have hc := ProjectivePlane.card_points_eq_card_lines P L
  have hv : (Fintype.card P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr card_points_ne_zero
  ext i <;> simp [vertexEquiv, center, mean, Fintype.sum_sum_type,
    Fintype.card_sum, ← hc] <;> field_simp <;> ring

private lemma center_idempotent (z : (P → ℝ) × (L → ℝ)) : center (center z) = center z := by
  obtain ⟨w, rfl⟩ := (sectorEquiv (P := P) (L := L)).surjective z
  rw [center_sector, center_sector]

private lemma center_allOnes (f : (P ⊕ L) → ℝ) :
    center (vertexEquiv (allOnes *ᵥ f)) = 0 := by
  rw [allOnes_action]
  ext i <;> simp [vertexEquiv, center, mean_const card_points_ne_zero,
    mean_const card_lines_ne_zero]

/-- The four-sector operator is exactly the actual centered distance matrix,
under the original-label coordinate identification. -/
theorem centeredGram_action (delta : ℝ) (f : (P ⊕ L) → ℝ) :
    vertexEquiv (centeredGram delta *ᵥ f) = gramAction delta (vertexEquiv f) := by
  classical
  simp only [centeredGram, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, map_smul,
    centeringMatrix_action]
  simp only [distanceMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, map_add, map_smul, map_sub]
  rw [center_allOnes, adjacencyMatrix_action, centeringMatrix_action, center_idempotent]
  simp only [gramAction, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    zero_sub, smul_neg]
  module

private lemma centeredGram_hermitian (delta : ℝ) :
    (centeredGram (P := P) (L := L) delta).IsHermitian := by
  classical
  have hH : (centeringMatrix (P := P) (L := L)).IsHermitian := by
    change (centeringMatrix (P := P) (L := L))ᴴ = centeringMatrix
    ext i j
    simp [centeringMatrix, allOnes, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  have hD : (distanceMatrix (P := P) (L := L) delta).IsHermitian := by
    change (distanceMatrix delta)ᴴ = distanceMatrix (P := P) (L := L) delta
    ext i j
    cases i <;> cases j <;>
      simp [distanceMatrix, allOnes, adjacencyMatrix, Matrix.conjTranspose_apply,
        Matrix.one_apply, eq_comm]
  apply Matrix.IsHermitian.smul _ (show IsSelfAdjoint (-1 / 2 : ℝ) from by simp [isSelfAdjoint_iff])
  simpa only [hH.eq] using Matrix.isHermitian_conjTranspose_mul_mul
    (centeringMatrix (P := P) (L := L)) hD

private lemma dot_vertex (f g : (P ⊕ L) → ℝ) :
    dotProduct f g = vertexDot (vertexEquiv f) (vertexEquiv g) := by
  simp [dotProduct, Fintype.sum_sum_type, vertexDot, vertexEquiv]

/-- Exact PSD interval for the doubly centered matrix of the original
projective-plane incidence distance assignment. -/
theorem centeredGram_posSemidef_iff (delta : ℝ) :
    (centeredGram (P := P) (L := L) delta).PosSemidef ↔
      rootOrder (P := P) (L := L) / (1 + rootOrder (P := P) (L := L)) ≤ delta ∧
      delta ≤ (orderR (P := P) (L := L) + 1) / orderR (P := P) (L := L) := by
  rw [← gramAction_nonnegative_interval]
  constructor
  · intro h z
    obtain ⟨f, rfl⟩ := (vertexEquiv (P := P) (L := L)).surjective z
    have hh := h.dotProduct_mulVec_nonneg f
    simpa only [Pi.star_apply, star_trivial, dot_vertex, centeredGram_action] using hh
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (centeredGram_hermitian delta)
    intro f
    simpa only [Pi.star_apply, star_trivial, dot_vertex, centeredGram_action] using h (vertexEquiv f)

end D5.S3.Geometry.FiniteGeometry.ProjectivePlaneRealSectors

import OmegaBuild.Commands
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Omega original.

Determinant and trace on three cyclically composable square matrices. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix

namespace OmegaMath.CyclicMatrixCubic

variable {K : Type*} [Field K]

abbrev Square (K : Type*) := Matrix (Fin 3) (Fin 3) K
abbrev Triple (K : Type*) := Square K × Square K × Square K
abbrev Group (K : Type*) [Field K] :=
  SpecialLinearGroup (Fin 3) K × SpecialLinearGroup (Fin 3) K × SpecialLinearGroup (Fin 3) K

def cubic (A B C : Square K) : K := A.det + B.det + C.det - (A * B * C).trace

def changeBasis (g : Group K) (x : Triple K) : Triple K :=
  ((g.1 : Square K) * x.1 * (↑(g.2.1⁻¹) : Square K),
   (g.2.1 : Square K) * x.2.1 * (↑(g.2.2⁻¹) : Square K),
   (g.2.2 : Square K) * x.2.2 * (↑(g.1⁻¹) : Square K))

instance : MulAction (Group K) (Triple K) where
  smul := changeBasis
  one_smul x := by
    rcases x with ⟨A, B, C⟩
    change changeBasis 1 (A, B, C) = (A, B, C)
    simp [changeBasis]
  mul_smul g h x := by
    rcases g with ⟨a, b, c⟩
    rcases h with ⟨d, e, f⟩
    rcases x with ⟨A, B, C⟩
    change changeBasis ((a, b, c) * (d, e, f)) (A, B, C) =
      changeBasis (a, b, c) (changeBasis (d, e, f) (A, B, C))
    simp [changeBasis, _root_.mul_inv_rev, Matrix.mul_assoc]

def rotate (x : Triple K) : Triple K := (x.2.1, x.2.2, x.1)

def rotateGroup (g : Group K) : Group K := (g.2.1, g.2.2, g.1)

theorem rotation_intertwines (g : Group K) (x : Triple K) :
    rotate (g • x) = rotateGroup g • rotate x ∧ rotate (rotate (rotate x)) = x := by
  rcases x with ⟨A, B, C⟩
  exact ⟨rfl, rfl⟩

private theorem det_changeBasis (a b : SpecialLinearGroup (Fin 3) K) (A : Square K) :
    ((a : Square K) * A * (↑(b⁻¹) : Square K)).det = A.det := by
  rw [det_mul, det_mul, a.prop, (b⁻¹).prop, one_mul, mul_one]

private theorem mul_inverse_coe (a : SpecialLinearGroup (Fin 3) K) :
    (a : Square K) * (↑(a⁻¹) : Square K) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]

private theorem inverse_mul_coe (a : SpecialLinearGroup (Fin 3) K) :
    (↑(a⁻¹) : Square K) * (a : Square K) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]

private theorem trace_changeBasis (a b c : SpecialLinearGroup (Fin 3) K)
    (A B C : Square K) :
    (((a : Square K) * A * (↑(b⁻¹) : Square K)) *
      ((b : Square K) * B * (↑(c⁻¹) : Square K)) *
      ((c : Square K) * C * (↑(a⁻¹) : Square K))).trace = (A * B * C).trace := by
  have first :
      (a : Square K) * A * (↑(b⁻¹) : Square K) *
        ((b : Square K) * B * (↑(c⁻¹) : Square K)) =
      (a : Square K) * A * ((↑(b⁻¹) : Square K) * (b : Square K)) *
        B * (↑(c⁻¹) : Square K) := by simp [Matrix.mul_assoc]
  rw [first, inverse_mul_coe, mul_one]
  have second :
      (a : Square K) * A * B * (↑(c⁻¹) : Square K) *
        ((c : Square K) * C * (↑(a⁻¹) : Square K)) =
      (a : Square K) * A * B * ((↑(c⁻¹) : Square K) * (c : Square K)) *
        C * (↑(a⁻¹) : Square K) := by simp [Matrix.mul_assoc]
  rw [second, inverse_mul_coe, mul_one]
  rw [trace_mul_comm]
  have last : (↑(a⁻¹) : Square K) * ((a : Square K) * A * B * C) =
      ((↑(a⁻¹) : Square K) * (a : Square K)) * (A * B * C) := by
    simp [Matrix.mul_assoc]
  rw [last, inverse_mul_coe, one_mul]

theorem cubic_changeBasis (g : Group K) (x : Triple K) :
    cubic (g • x).1 (g • x).2.1 (g • x).2.2 = cubic x.1 x.2.1 x.2.2 := by
  change cubic (changeBasis g x).1 (changeBasis g x).2.1 (changeBasis g x).2.2 = _
  simp only [changeBasis, cubic, det_changeBasis, trace_changeBasis]

theorem cubic_rotate (A B C : Square K) : cubic B C A = cubic A B C := by
  unfold cubic
  rw [trace_mul_cycle B C A]
  ring

theorem cubic_scale (z : K) (A B C : Square K) :
    cubic (z • A) (z • B) (z • C) = z ^ 3 * cubic A B C := by
  simp [cubic, trace_smul, smul_eq_mul]
  ring

theorem cubic_plain_matrices (A B C a b c : Square K)
    (ha : a.det = 1) (hb : b.det = 1) (hc : c.det = 1) :
    cubic (a * A * b⁻¹) (b * B * c⁻¹) (c * C * a⁻¹) = cubic A B C := by
  let g : Group K := (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩)
  have h := cubic_changeBasis g (A, B, C)
  change cubic ((changeBasis g (A, B, C)).1) ((changeBasis g (A, B, C)).2.1)
    ((changeBasis g (A, B, C)).2.2) = cubic A B C at h
  change cubic (a * A * b.adjugate) (b * B * c.adjugate) (c * C * a.adjugate) = _ at h
  simpa [Matrix.inv_def, ha, hb, hc] using h

private def cubicOf (x : Triple K) : K := cubic x.1 x.2.1 x.2.2

def stabilizer : Subgroup (Triple K ≃ₗ[K] Triple K) where
  carrier := {g | ∀ x, cubicOf (g x) = cubicOf x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have h := (hg (g.symm x)).symm
    rwa [g.apply_symm_apply] at h

def linearAction (g : Group K) : Triple K ≃ₗ[K] Triple K where
  toFun := fun x => g • x
  invFun := fun x => g⁻¹ • x
  left_inv x := by
    change g⁻¹ • (g • x) = x
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv x := by
    change g • (g⁻¹ • x) = x
    rw [← mul_smul, mul_inv_cancel, one_smul]
  map_add' x y := by
    change changeBasis g (x + y) = changeBasis g x + changeBasis g y
    simp [changeBasis, Matrix.mul_add, Matrix.add_mul]
  map_smul' z x := by
    change changeBasis g (z • x) = z • changeBasis g x
    simp [changeBasis]

def toStabilizer : Group K →* (stabilizer : Subgroup (Triple K ≃ₗ[K] Triple K)) where
  toFun g := ⟨linearAction g, cubic_changeBasis g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact one_smul (Group K) x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact mul_smul g h x

def linearRotation : Triple K ≃ₗ[K] Triple K where
  toFun := rotate
  invFun x := rotate (rotate x)
  left_inv x := by rcases x with ⟨_, _, _⟩; rfl
  right_inv x := by rcases x with ⟨_, _, _⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rotationInStabilizer : (stabilizer : Subgroup (Triple K ≃ₗ[K] Triple K)) :=
  ⟨linearRotation, fun x => cubic_rotate x.1 x.2.1 x.2.2⟩

theorem stabilizer_rotation (g : Group K) :
    rotationInStabilizer * toStabilizer g =
      toStabilizer (rotateGroup g) * rotationInStabilizer ∧
    (rotationInStabilizer : (stabilizer : Subgroup (Triple K ≃ₗ[K] Triple K))) ^ 3 = 1 := by
  constructor <;> apply Subtype.ext <;> apply LinearEquiv.ext <;> intro x
  · exact (rotation_intertwines g x).1
  · exact (rotation_intertwines g x).2

theorem action_kernel (g : Group K) :
    (∀ x : Triple K, g • x = x) ↔
      ∃ z : K, z ^ 3 = 1 ∧ (g.1 : Square K) = Matrix.scalar (Fin 3) z ∧
        (g.2.1 : Square K) = Matrix.scalar (Fin 3) z ∧
        (g.2.2 : Square K) = Matrix.scalar (Fin 3) z := by
  rcases g with ⟨a, b, c⟩
  let A : Square K := a
  let B : Square K := b
  let C : Square K := c
  let Ai : Square K := ↑(a⁻¹)
  let Bi : Square K := ↑(b⁻¹)
  let Ci : Square K := ↑(c⁻¹)
  have hA : A * Ai = 1 := mul_inverse_coe a
  have hB : B * Bi = 1 := mul_inverse_coe b
  have hC : C * Ci = 1 := mul_inverse_coe c
  have cancel (X X' Y Y' : Square K) (hY : Y' * Y = 1) (agree : X * Y' = X') :
      X = X' * Y := by rw [← agree, Matrix.mul_assoc, hY, mul_one]
  constructor
  · intro h
    have he := h (1, 1, 1)
    change (A * 1 * Bi, B * 1 * Ci, C * 1 * Ai) = (1, 1, 1) at he
    have hab : A = B := by
      simpa using cancel A 1 B Bi (inverse_mul_coe b) (by simpa using congrArg Prod.fst he)
    have hbc : B = C := by
      simpa using cancel B 1 C Ci (inverse_mul_coe c)
        (by simpa using congrArg (fun x : Triple K => x.2.1) he)
    have comm (i j : Fin 3) :
        Commute A (Matrix.single i j (1 : K)) := by
      let X : Square K := Matrix.single i j 1
      have hx := congrArg Prod.fst (h (X, 0, 0))
      change A * X * Bi = X at hx
      unfold Commute SemiconjBy
      calc
        A * X = X * B := cancel (A * X) X B Bi (inverse_mul_coe b) hx
        _ = X * A := by rw [hab]
    obtain ⟨z, hz⟩ := Matrix.mem_range_scalar_iff_commute_single'.2 (fun i j => (comm i j).symm)
    have hd := a.prop
    change A.det = 1 at hd
    rw [← hz, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
    exact ⟨z, hd, hz.symm, hab.symm.trans hz.symm, (hab.trans hbc).symm.trans hz.symm⟩
  · rintro ⟨z, _, ha, hb, hc⟩ ⟨X, Y, Z⟩
    change (A * X * Bi, B * Y * Ci, C * Z * Ai) = (X, Y, Z)
    change A = Matrix.scalar (Fin 3) z at ha
    change B = Matrix.scalar (Fin 3) z at hb
    change C = Matrix.scalar (Fin 3) z at hc
    have scalarMove (W : Square K) : Matrix.scalar (Fin 3) z * W =
        W * Matrix.scalar (Fin 3) z := Matrix.scalar_commute _ (fun w => show z * w = w * z from mul_comm z w) _
    rw [ha, scalarMove, ← hb, Matrix.mul_assoc, hB, mul_one,
      hb, scalarMove, ← hc, Matrix.mul_assoc, hC, mul_one,
      hc, scalarMove, ← ha, Matrix.mul_assoc, hA, mul_one]

abbrev Entry := (Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3)

def differenceWeight {S : Type*} [Sub S] (a b c : Fin 3 → S) : Entry → S
  | .inl (i, j) => a i - b j
  | .inr (.inl (i, j)) => b i - c j
  | .inr (.inr (i, j)) => c i - a j

private theorem cube_difference_sum (a b : Fin 3 → K)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) :
    (∑ i, ∑ j, (a i - b j) ^ 3) =
      3 * ((∑ i, a i ^ 3) - ∑ j, b j ^ 3) := by
  simp only [Fin.sum_univ_three] at ha hb ⊢
  generalize a 0 = a₀ at *
  generalize a 1 = a₁ at *
  generalize a 2 = a₂ at *
  generalize b 0 = b₀ at *
  generalize b 1 = b₁ at *
  generalize b 2 = b₂ at *
  have ha₂ : a₂ = -(a₀ + a₁) := by linear_combination ha
  have hb₂ : b₂ = -(b₀ + b₁) := by linear_combination hb
  rw [ha₂, hb₂]
  ring

theorem total_cubic_trace (a b c : Fin 3 → K)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) (hc : ∑ i, c i = 0) :
    (∑ x : Entry, differenceWeight a b c x ^ 3) = 0 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, differenceWeight]
  rw [cube_difference_sum a b ha hb, cube_difference_sum b c hb hc,
    cube_difference_sum c a hc ha]
  ring

end OmegaMath.CyclicMatrixCubic

/- GID: D5/S3/Quantum/Algebra/PauliFixedProductFamily
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PauliFixedProductFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct, mathlib/module/Mathlib.Analysis.InnerProductSpace.TensorProduct]
   utility: none
   digest: Fixed spin products and the actual real parametric Pauli action. -/

import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped TensorProduct InnerProductSpace
open TensorProduct WithLp

namespace D5.S3.Quantum.Algebra.PauliFixedProductFamily

/-- The local Euclidean spin factor, in the order scalar, x, y, z. -/
abbrev J := EuclideanSpace ℝ (Fin 4)
/-- The actual joint carrier with its positive product inner product. -/
abbrev V := J ⊗[ℝ] J

/-- The fixed complete orthonormal local basis. -/
def e (i : Fin 4) : J := EuclideanSpace.single i 1
/-- The local spin product. -/
def spin (a b : J) : J := toLp 2
  ![a 0*b 0+a 1*b 1+a 2*b 2+a 3*b 3,
    a 0*b 1+b 0*a 1, a 0*b 2+b 0*a 2, a 0*b 3+b 0*a 3]
/-- The fixed cross-product channel. -/
def cross (a b : J) : J := toLp 2
  (Matrix.vecCons 0 (crossProduct ![a 1,a 2,a 3] ![b 1,b 2,b 3]))

private theorem spin_add_left (a b c : J) : spin (a+b) c = spin a c + spin b c := by
  ext i; fin_cases i <;> simp [spin] <;> ring
private theorem spin_smul_left (r : ℝ) (a b : J) : spin (r • a) b = r • spin a b := by
  ext i; fin_cases i <;> simp [spin] <;> ring
private theorem spin_add_right (a b c : J) : spin a (b+c) = spin a b + spin a c := by
  ext i; fin_cases i <;> simp [spin] <;> ring
private theorem spin_smul_right (r : ℝ) (a b : J) : spin a (r • b) = r • spin a b := by
  ext i; fin_cases i <;> simp [spin] <;> ring

/-- The fixed spin multiplication as a bilinear map. -/
def S : J →ₗ[ℝ] J →ₗ[ℝ] J :=
  LinearMap.mk₂ ℝ spin spin_add_left spin_smul_left spin_add_right
    (fun r a b => spin_smul_right r a b)

private theorem cross_add_left (a b c : J) : cross (a+b) c = cross a c + cross b c := by
  ext i; fin_cases i <;> simp [cross, cross_apply] <;> ring
private theorem cross_smul_left (r : ℝ) (a b : J) : cross (r • a) b = r • cross a b := by
  ext i; fin_cases i <;> simp [cross, cross_apply] <;> ring
private theorem cross_add_right (a b c : J) : cross a (b+c) = cross a b + cross a c := by
  ext i; fin_cases i <;> simp [cross, cross_apply] <;> ring
private theorem cross_smul_right (r : ℝ) (a b : J) : cross a (r • b) = r • cross a b := by
  ext i; fin_cases i <;> simp [cross, cross_apply] <;> ring

/-- The fixed cross product as a bilinear map. -/
def C : J →ₗ[ℝ] J →ₗ[ℝ] J :=
  LinearMap.mk₂ ℝ cross cross_add_left cross_smul_left cross_add_right
    (fun r a b => cross_smul_right r a b)

/-- Shift the z label by t times the scalar label; no product is changed. -/
def shift (t : ℝ) : J →ₗ[ℝ] J where
  toFun a := toLp 2 ![a 0,a 1,a 2,a 3+t*a 0]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r a := by ext i; fin_cases i <;> simp <;> ring

/-- The actual local label-linear derivation assignment. -/
def D (t : ℝ) : J →ₗ[ℝ] J →ₗ[ℝ] J := C.comp (shift t)

/-- The fixed joint product, with the fixed C channel. -/
def M : V →ₗ[ℝ] V →ₗ[ℝ] V := TensorProduct.lift
  (LinearMap.mk₂ ℝ (fun a b => TensorProduct.map (S a) (S b) - TensorProduct.map (C a) (C b))
    (by intros; simp [map_add, TensorProduct.map_add_left, add_sub_add_comm])
    (by intros; simp [map_smul, TensorProduct.map_smul_left, smul_sub])
    (by intros; simp [map_add, TensorProduct.map_add_right, add_sub_add_comm])
    (by intros; simp [map_smul, TensorProduct.map_smul_right, smul_sub]))

/-- The actual joint label-linear action. -/
def Gamma (t : ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] V := TensorProduct.lift
  (LinearMap.mk₂ ℝ (fun a b => TensorProduct.map (D t a) (S b) + TensorProduct.map (S a) (D t b))
    (by intros; simp [map_add, TensorProduct.map_add_left, add_add_add_comm])
    (by intros; simp [map_smul, TensorProduct.map_smul_left, smul_add])
    (by intros; simp [map_add, TensorProduct.map_add_right, add_add_add_comm])
    (by intros; simp [map_smul, TensorProduct.map_smul_right, smul_add]))

/-- The full actual trilinear derivation residual. -/
def E (t : ℝ) (H X Y : V) : V :=
  Gamma t H (M X Y) - M (Gamma t H X) Y - M X (Gamma t H Y)

private theorem m_tmul (a b c d : J) :
    M (a ⊗ₜ b) (c ⊗ₜ d) = S a c ⊗ₜ S b d - C a c ⊗ₜ C b d := by
  simp [M]
private theorem gamma_tmul (t : ℝ) (a b c d : J) :
    Gamma t (a ⊗ₜ b) (c ⊗ₜ d) = D t a c ⊗ₜ S b d + S a c ⊗ₜ D t b d := by
  simp [Gamma]

private theorem s_comm (a b : J) : S a b = S b a := by
  ext i; fin_cases i <;> simp [S, spin] <;> ring
private theorem s_unit (a : J) : S (e 0) a = a := by
  ext i; fin_cases i <;> simp [S, spin, e, EuclideanSpace.single_apply]
private theorem s_unit_right (a : J) : S a (e 0) = a := by
  rw [s_comm, s_unit]
private theorem c_anti (a b : J) : C a b = -(C b a) := by
  ext i; fin_cases i <;> simp [C, cross, cross_apply] <;> ring
private theorem c_unit (a : J) : C (e 0) a = 0 := by
  ext i; fin_cases i <;> simp [C, cross, cross_apply, e, EuclideanSpace.single_apply]
private theorem c_unit_right (a : J) : C a (e 0) = 0 := by
  rw [c_anti, c_unit, neg_zero]
private theorem d_unit (t : ℝ) (a : J) : D t a (e 0) = 0 := c_unit_right _

private theorem d_derivation (t : ℝ) (a b c : J) :
    D t a (S b c) = S (D t a b) c + S b (D t a c) := by
  ext i; fin_cases i <;> simp [D, shift, C, S, spin, cross, cross_apply] <;> ring

private theorem s_frob (a b c : J) : inner ℝ (S a b) c = inner ℝ a (S b c) := by
  simp [PiLp.inner_apply, S, spin, Fin.sum_univ_succ, RCLike.inner_apply]
  <;> ring
private theorem c_frob (a b c : J) : inner ℝ (C a b) c = inner ℝ a (C b c) := by
  simp [PiLp.inner_apply, C, cross, cross_apply, Fin.sum_univ_succ, RCLike.inner_apply]
  <;> ring

private theorem m_comm (X Y : V) : M X Y = M Y X := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction Y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      simp only [m_tmul]
      rw [s_comm c a, s_comm d b, c_anti c a, c_anti d b]
      simp
    | add X Y hx hy => simp [map_add, hx, hy]
  | add X Y hx hy => simp [map_add, hx, hy]

private theorem m_unit (X : V) : M (e 0 ⊗ₜ e 0) X = X := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [m_tmul, s_unit, c_unit]
  | add X Y hx hy => simp [hx, hy]

private theorem m_frob (X Y Z : V) : inner ℝ (M X Y) Z = inner ℝ X (M Y Z) := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction Y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      induction Z using TensorProduct.induction_on with
      | zero => simp
      | tmul f g => simp [m_tmul, inner_sub_left, inner_sub_right, s_frob, c_frob]
      | add X Y hx hy => simp [map_add, inner_add_left, inner_add_right, hx, hy]
    | add X Y hx hy => simp [map_add, inner_add_left, inner_add_right, hx, hy]
  | add X Y hx hy => simp [map_add, inner_add_left, inner_add_right, hx, hy]

/-- The two exact module actions and two preserving actions hold on all local inputs. -/
theorem all_input_contract (t : ℝ) (a b c d : J) :
    M (a ⊗ₜ e 0) (c ⊗ₜ d) = S a c ⊗ₜ d ∧
    M (e 0 ⊗ₜ b) (c ⊗ₜ d) = c ⊗ₜ S b d ∧
    Gamma t (a ⊗ₜ b) (c ⊗ₜ e 0) = D t a c ⊗ₜ b ∧
    Gamma t (a ⊗ₜ b) (e 0 ⊗ₜ d) = a ⊗ₜ D t b d := by
  simp [m_tmul, gamma_tmul, s_unit, s_unit_right, c_unit, c_unit_right, d_unit]

/-- The fixed joint product is commutative, unital and Frobenius for its product inner product. -/
theorem fixed_product_laws :
    (∀ X Y : V, M X Y = M Y X) ∧
    (∀ X : V, M (e 0 ⊗ₜ e 0) X = X) ∧
    (∀ X Y Z : V, inner ℝ (M X Y) Z = inner ℝ X (M Y Z)) :=
  ⟨m_comm, m_unit, m_frob⟩

end D5.S3.Quantum.Algebra.PauliFixedProductFamily

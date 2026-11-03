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
  ext i; fin_cases i <;> simp [S, spin, e, PiLp.single_apply]
private theorem s_unit_right (a : J) : S a (e 0) = a := by
  rw [s_comm, s_unit]
private theorem c_anti (a b : J) : C a b = -(C b a) := by
  ext i; fin_cases i <;> simp [C, cross, cross_apply] <;> ring
private theorem c_unit (a : J) : C (e 0) a = 0 := by
  ext i; fin_cases i <;> simp [C, cross, cross_apply, e, PiLp.single_apply]
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
  induction X using TensorProduct.inductionOn with
  | tmul a b =>
    induction Y using TensorProduct.inductionOn with
    | tmul c d =>
      simp only [m_tmul]
      rw [s_comm c a, s_comm d b, c_anti c a, c_anti d b]
      simp [TensorProduct.neg_tmul, TensorProduct.tmul_neg]
    | add X Y hx hy => simp [map_add, hx, hy]
  | add X Y hx hy => simp [map_add, hx, hy]

private theorem m_unit (X : V) : M (e 0 ⊗ₜ e 0) X = X := by
  induction X using TensorProduct.inductionOn with
  | tmul a b => simp [m_tmul, s_unit, c_unit]
  | add X Y hx hy => simp [hx, hy]

private theorem m_frob (X Y Z : V) : inner ℝ (M X Y) Z = inner ℝ X (M Y Z) := by
  induction X using TensorProduct.inductionOn with
  | tmul a b =>
    induction Y using TensorProduct.inductionOn with
    | tmul c d =>
      induction Z using TensorProduct.inductionOn with
      | tmul f g => simp [m_tmul, inner_sub_left, inner_sub_right, s_frob, c_frob]
      | add X Y hx hy => simp [map_add, inner_add_left, inner_add_right, hx, hy]
    | add X Y hx hy => simp [map_add, inner_add_left, inner_add_right, hx, hy]
  | add X Y hx hy => simp [map_add, inner_add_left, inner_add_right, hx, hy]

/-- The two exact module actions and two preserving actions hold on all local inputs. -/
private theorem all_input_contract (t : ℝ) (a b c d : J) :
    M (a ⊗ₜ e 0) (c ⊗ₜ d) = S a c ⊗ₜ d ∧
    M (e 0 ⊗ₜ b) (c ⊗ₜ d) = c ⊗ₜ S b d ∧
    Gamma t (a ⊗ₜ b) (c ⊗ₜ e 0) = D t a c ⊗ₜ b ∧
    Gamma t (a ⊗ₜ b) (e 0 ⊗ₜ d) = a ⊗ₜ D t b d := by
  simp [m_tmul, gamma_tmul, s_unit, s_unit_right, c_unit, c_unit_right, d_unit]

/-- The fixed joint product is commutative, unital and Frobenius for its product inner product. -/
private theorem fixed_product_laws :
    (∀ X Y : V, M X Y = M Y X) ∧
    (∀ X : V, M (e 0 ⊗ₜ e 0) X = X) ∧
    (∀ X Y Z : V, inner ℝ (M X Y) Z = inner ℝ X (M Y Z)) :=
  ⟨m_comm, m_unit, m_frob⟩


private theorem d_split (t : ℝ) (a b : J) :
    D t a b = C a b + (t*a 0) • C (e 3) b := by
  ext i; fin_cases i <;> simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply] <;> ring

private theorem s_basis (i j : Fin 4) :
    S (e i) (e j) = if i = 0 then e j else if j = 0 then e i
      else if i = j then e 0 else 0 := by
  fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
    norm_num [S, spin, e, PiLp.single_apply]

private theorem c_basis (i j : Fin 4) :
    C (e i) (e j) =
    if i = 1 ∧ j = 2 then e 3 else
    if i = 2 ∧ j = 3 then e 1 else
    if i = 3 ∧ j = 1 then e 2 else
    if i = 2 ∧ j = 1 then -(e 3) else
    if i = 3 ∧ j = 2 then -(e 1) else
    if i = 1 ∧ j = 3 then -(e 2) else 0 := by
  fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
    norm_num [C, cross, cross_apply, e, PiLp.single_apply]

private theorem e_apply (i j : Fin 4) : e i j = if i=j then 1 else 0 := by
  simp [e, PiLp.single_apply, eq_comm]

private theorem e_inner (i j : Fin 4) : inner ℝ (e i) (e j) = if i=j then 1 else 0 := by
  simp [e, EuclideanSpace.inner_single_left, PiLp.single_apply]

/-- The full unaveraged report, over all ordered complete product-basis labels. -/
def reportSquared (t : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
    ∑ m : Fin 4, ∑ n : Fin 4,
      ‖E t (e i ⊗ₜ e j) (e k ⊗ₜ e l) (e m ⊗ₜ e n)‖ ^ 2


private theorem d_affine (t : ℝ) (a b : J) :
    D t a b = D 0 a b + t • (D 1 a b-D 0 a b) := by
  ext i; fin_cases i <;> simp [D,C,cross,cross_apply,shift] <;> ring

private theorem d_affine_map (t : ℝ) (a : J) :
    D t a = D 0 a+t • (D 1 a-D 0 a) := by
  apply LinearMap.ext
  intro b
  exact d_affine t a b

private theorem map_sub_left (f g k : J →ₗ[ℝ] J) :
    TensorProduct.map (f-g) k=TensorProduct.map f k-TensorProduct.map g k := by
  apply LinearMap.ext
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul a b => simp [TensorProduct.sub_tmul]
  | add X Y hx hy => simp [map_add,hx,hy]

private theorem map_sub_right (f g k : J →ₗ[ℝ] J) :
    TensorProduct.map f (g-k)=TensorProduct.map f g-TensorProduct.map f k := by
  apply LinearMap.ext
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul a b => simp [TensorProduct.tmul_sub]
  | add X Y hx hy => simp [map_add,hx,hy]

private theorem gamma_affine (t : ℝ) (H X : V) :
    Gamma t H X = Gamma 0 H X + t • (Gamma 1 H X-Gamma 0 H X) := by
  have hmap : Gamma t H = Gamma 0 H+t • (Gamma 1 H-Gamma 0 H) := by
    induction H using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [Gamma,TensorProduct.lift.tmul,LinearMap.mk₂_apply]
      rw [d_affine_map t a,d_affine_map t b]
      simp only [TensorProduct.map_add_left,TensorProduct.map_add_right,
        map_sub_left,map_sub_right,
        TensorProduct.map_smul_left,TensorProduct.map_smul_right]
      module
    | add H K hh hk => simp only [map_add,hh,hk]; module
  exact LinearMap.congr_fun hmap X

private theorem e_affine (t : ℝ) (H X Y : V) :
    E t H X Y = E 0 H X Y + t • (E 1 H X Y-E 0 H X Y) := by
  simp only [E, gamma_affine t, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  module

set_option maxHeartbeats 2000000 in
private theorem report_row_z (k l : Fin 4) :
    (∑ m : Fin 4, ∑ n : Fin 4,
      ‖E 1 (e 0 ⊗ₜ e 3) (e k ⊗ₜ e l) (e m ⊗ₜ e n)‖ ^ 2) =
      (if (k=0 ∨ k=3) ∧ (l=0 ∨ l=3) then 0 else 4) := by
  fin_cases k <;> fin_cases l <;>
    norm_num [Fin.sum_univ_succ, E, m_tmul, gamma_tmul, d_split, s_basis, c_basis,
      e_apply, map_add, map_sub, map_smul, map_neg,
      TensorProduct.add_tmul, TensorProduct.sub_tmul,
      TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.neg_tmul,
      TensorProduct.tmul_neg]
  all_goals norm_num [e]


set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
private theorem e_zero_basis (i j k l m n : Fin 4) :
    E 0 (e i ⊗ₜ e j) (e k ⊗ₜ e l) (e m ⊗ₜ e n)=0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;>
    norm_num [E,m_tmul,gamma_tmul,d_split,s_basis,c_basis,e_apply,
      map_add,map_sub,map_neg,TensorProduct.add_tmul,TensorProduct.sub_tmul,
      TensorProduct.tmul_add,TensorProduct.tmul_sub,TensorProduct.neg_tmul,
      TensorProduct.tmul_neg]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
private theorem block_one (i j : Fin 4) :
    (∑ k : Fin 4, ∑ l : Fin 4, ∑ m : Fin 4, ∑ n : Fin 4,
      ‖E 1 (e i ⊗ₜ e j) (e k ⊗ₜ e l) (e m ⊗ₜ e n)‖^2)=
      if (i=0 ∧ j≠0) ∨ (i≠0 ∧ j=0) then 48 else 0 := by
  by_cases hz : i=0 ∧ j=3
  · rcases hz with ⟨rfl,rfl⟩
    simp_rw [report_row_z]
    norm_num [Fin.sum_univ_succ]
  · fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_succ,E,m_tmul,gamma_tmul,d_split,s_basis,c_basis,
        e_apply,map_add,map_sub,map_neg,TensorProduct.add_tmul,TensorProduct.sub_tmul,
        TensorProduct.tmul_add,TensorProduct.tmul_sub,TensorProduct.neg_tmul,
        TensorProduct.tmul_neg] at hz ⊢
    all_goals norm_num [e]

/-- The complete 16 by 16 by 16 actual residual, with all output coordinates, has this exact square. -/
theorem full_report (t : ℝ) : reportSquared t=288*t^2 := by
  have hone : reportSquared 1=288 := by
    unfold reportSquared
    simp_rw [block_one]
    norm_num [Fin.sum_univ_succ]
  have hscale : reportSquared t=t^2*reportSquared 1 := by
    unfold reportSquared
    simp_rw [e_affine t,e_zero_basis,sub_zero,zero_add,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs]
    simp_rw [← Finset.mul_sum]
  rw [hscale,hone]
  ring

/-- The complete local orthonormal basis. -/
def localBasis : OrthonormalBasis (Fin 4) ℝ J := EuclideanSpace.basisFun (Fin 4) ℝ
/-- The complete joint orthonormal basis with the product positive inner product. -/
def jointBasis : OrthonormalBasis (Fin 4 × Fin 4) ℝ V :=
  localBasis.tensorProduct localBasis

/-- The same fixed products satisfy the complete all-input realization contract. -/
theorem family_contract (t : ℝ) :
    Module.finrank ℝ J=4 ∧ Module.finrank ℝ V=16 ∧
    (∀ i : Fin 4, localBasis i=e i) ∧
    (∀ i j : Fin 4, jointBasis (i,j)=e i ⊗ₜ e j) ∧
    (∀ a b : J, S a b=S b a) ∧ (∀ a : J, S (e 0) a=a) ∧
    (∀ a b c : J, inner ℝ (S a b) c=inner ℝ a (S b c)) ∧
    (∀ a b c : J, D t a (S b c)=S (D t a b) c+S b (D t a c)) ∧
    D t (e 1) (e 2)=e 3 ∧
    (∀ X Y : V, M X Y=M Y X) ∧
    (∀ X : V, M (e 0 ⊗ₜ e 0) X=X) ∧
    (∀ X Y Z : V, inner ℝ (M X Y) Z=inner ℝ X (M Y Z)) ∧
    (∀ X : V, 0≤inner ℝ X X ∧ (inner ℝ X X=0 ↔ X=0)) ∧
    (∀ a b c d : J,
      M (a ⊗ₜ e 0) (c ⊗ₜ d)=S a c ⊗ₜ d ∧
      M (e 0 ⊗ₜ b) (c ⊗ₜ d)=c ⊗ₜ S b d ∧
      Gamma t (a ⊗ₜ b) (c ⊗ₜ e 0)=D t a c ⊗ₜ b ∧
      Gamma t (a ⊗ₜ b) (e 0 ⊗ₜ d)=a ⊗ₜ D t b d) ∧
    reportSquared t=288*t^2 := by
  refine ⟨by simp [J],?_,?_,?_,s_comm,s_unit,s_frob,d_derivation t,?_,
    fixed_product_laws.1,fixed_product_laws.2.1,fixed_product_laws.2.2,?_,
    all_input_contract t,full_report t⟩
  · simpa [V,J] using (Module.finrank_tensorProduct ℝ J J)
  · intro i
    rfl
  · intro i j
    exact OrthonormalBasis.tensorProduct_apply _ _ _ _
  · ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
  · intro X
    exact ⟨real_inner_self_nonneg,inner_self_eq_zero⟩

end D5.S3.Quantum.Algebra.PauliFixedProductFamily

/- GID: D5/S3/Quantum/Algebra/PauliFixedProductFamily
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PauliFixedProductFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct, mathlib/module/Mathlib.Analysis.InnerProductSpace.TensorProduct]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Algebra/PauliFixedProductLinear.actual_strict_improvement; premises=D5/S3/Quantum/Algebra/PauliFixedProductFamily.full_report
   digest: Fixed spin products and the actual real parametric Pauli action. -/

import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.InnerProductSpace.Adjoint

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

theorem s_comm (a b : J) : S a b = S b a := by
  ext i; fin_cases i <;> simp [S, spin] <;> ring
private theorem s_unit (a : J) : S (e 0) a = a := by
  ext i; fin_cases i <;> simp [S, spin, e, PiLp.single_apply]
private theorem s_unit_right (a : J) : S a (e 0) = a := by
  rw [s_comm, s_unit]
theorem c_anti (a b : J) : C a b = -(C b a) := by
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


/-- The complete local orthonormal basis. -/
def localBasis : OrthonormalBasis (Fin 4) ℝ J := EuclideanSpace.basisFun (Fin 4) ℝ
/-- The complete joint orthonormal basis with the product positive inner product. -/
def jointBasis : OrthonormalBasis (Fin 4 × Fin 4) ℝ V :=
  localBasis.tensorProduct localBasis

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
  have hswap (a b : V) : a+b-(b+a)=0 := by abel
  have hcancel (a b : V) : a-b+ -a= -b := by abel
  by_cases hz : i=0 ∧ j=3
  · rcases hz with ⟨rfl,rfl⟩
    simp_rw [report_row_z]
    norm_num [Fin.sum_univ_succ]
  · fin_cases i <;> fin_cases j
    all_goals norm_num at hz
    all_goals norm_num [Fin.sum_univ_succ,E,m_tmul,gamma_tmul,d_split,s_basis,c_basis,
        e_apply,map_add,map_sub,map_neg,TensorProduct.add_tmul,TensorProduct.sub_tmul,
        TensorProduct.tmul_add,TensorProduct.tmul_sub,TensorProduct.neg_tmul,
        TensorProduct.tmul_neg]
    all_goals norm_num [e]
    all_goals norm_num [hswap,hcancel,e]


private theorem e_add_h (t : ℝ) (H K X Y : V) :
    E t (H+K) X Y=E t H X Y+E t K X Y := by
  simp only [E,map_add,LinearMap.add_apply]
  abel
private theorem e_smul_h (t r : ℝ) (H X Y : V) :
    E t (r • H) X Y=r • E t H X Y := by
  simp only [E,map_smul,LinearMap.smul_apply,smul_sub]
private theorem e_add_x (t : ℝ) (H X X' Y : V) :
    E t H (X+X') Y=E t H X Y+E t H X' Y := by
  simp only [E,map_add,LinearMap.add_apply]
  abel
private theorem e_smul_x (t r : ℝ) (H X Y : V) :
    E t H (r • X) Y=r • E t H X Y := by
  simp only [E,map_smul,LinearMap.smul_apply,smul_sub]
private theorem e_add_y (t : ℝ) (H X Y Y' : V) :
    E t H X (Y+Y')=E t H X Y+E t H X Y' := by
  simp only [E,map_add,LinearMap.add_apply]
  abel
private theorem e_smul_y (t r : ℝ) (H X Y : V) :
    E t H X (r • Y)=r • E t H X Y := by
  simp only [E,map_smul,LinearMap.smul_apply,smul_sub]

private theorem e_zero_all (H X Y : V) : E 0 H X Y=0 := by
  have hspan (Z : V) : Z∈Submodule.span ℝ (Set.range jointBasis) := by
    rw [←jointBasis.coe_toBasis,jointBasis.toBasis.span_eq]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspan H)
  · rintro H ⟨p,rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspan X)
    · rintro X ⟨q,rfl⟩
      refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspan Y)
      · rintro Y ⟨r,rfl⟩
        simpa [jointBasis,localBasis,OrthonormalBasis.tensorProduct_apply',
          EuclideanSpace.basisFun_apply,e] using
          e_zero_basis p.1 p.2 q.1 q.2 r.1 r.2
      · simp [E]
      · intro a b _ _ ha hb
        rw [e_add_y,ha,hb,zero_add]
      · intro r a _ ha
        rw [e_smul_y,ha,smul_zero]
    · simp [E]
    · intro a b _ _ ha hb
      rw [e_add_x,ha,hb,zero_add]
    · intro r a _ ha
      rw [e_smul_x,ha,smul_zero]
  · simp [E]
  · intro a b _ _ ha hb
    rw [e_add_h,ha,hb,zero_add]
  · intro r a _ ha
    rw [e_smul_h,ha,smul_zero]

/-- The actual trilinear residual scales on every input of the actual joint carrier. -/
theorem residual_scaling (t : ℝ) (H X Y : V) : E t H X Y=t • E 1 H X Y := by
  rw [e_affine,e_zero_all]
  simp

/-- The complete 16 by 16 by 16 actual residual, with all output coordinates, has this exact square. -/
theorem full_report (t : ℝ) : reportSquared t=288*t^2 := by
  have hone : reportSquared 1=288 := by
    unfold reportSquared
    simp_rw [block_one]
    norm_num [Fin.sum_univ_succ]
  have hscale : reportSquared t=t^2*reportSquared 1 := by
    unfold reportSquared
    simp_rw [residual_scaling t,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs]
    simp_rw [← Finset.mul_sum]
  rw [hscale,hone]
  ring

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
    (∀ X : V, 0 ≤ inner ℝ X X ∧ (inner ℝ X X=0 ↔ X=0)) ∧
    (∀ a b c d : J,
      M (a ⊗ₜ e 0) (c ⊗ₜ d)=S a c ⊗ₜ d ∧
      M (e 0 ⊗ₜ b) (c ⊗ₜ d)=c ⊗ₜ S b d ∧
      Gamma t (a ⊗ₜ b) (c ⊗ₜ e 0)=D t a c ⊗ₜ b ∧
      Gamma t (a ⊗ₜ b) (e 0 ⊗ₜ d)=a ⊗ₜ D t b d) ∧
    reportSquared t=288*t^2 := by
  refine ⟨by simp [J],?_,?_,?_,s_comm,s_unit,s_frob,d_derivation t,?_,
    fixed_product_laws.1,fixed_product_laws.2.1,fixed_product_laws.2.2,?_,
    all_input_contract t,full_report t⟩
  · simp [V,J]
  · intro i
    simp [localBasis,e,EuclideanSpace.basisFun_apply]
  · intro i j
    simp [jointBasis,localBasis,e,OrthonormalBasis.tensorProduct_apply,
      EuclideanSpace.basisFun_apply]
  · ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
  · intro X
    exact ⟨real_inner_self_nonneg,inner_self_eq_zero⟩

private theorem sqrt_two_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
private theorem sqrt_two_four : (Real.sqrt 2)^4=4 := by
  calc
    (Real.sqrt 2)^4=((Real.sqrt 2)^2)^2 := by ring
    _=4 := by rw [sqrt_two_sq]; norm_num
private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- The common attaining direction for the spin product and diagonal defect. -/
def balanced : J := (Real.sqrt 2)⁻¹ • (e 0 + e 1)

private theorem balanced_norm : ‖balanced‖ = 1 := by
  have hn : ‖balanced‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [balanced, e, PiLp.single_apply, Fin.sum_univ_succ]
    field_simp
    nlinarith [sqrt_two_sq,sqrt_two_four]
  nlinarith [norm_nonneg balanced]

private theorem spin_bound (a b : J) : ‖S a b‖ ≤ Real.sqrt 2 * ‖a‖ * ‖b‖ := by
  have hid : ‖S a b‖^2 +
      (a 0*b 0-a 1*b 1-a 2*b 2-a 3*b 3)^2 +
      (a 0*b 1-b 0*a 1)^2 + (a 0*b 2-b 0*a 2)^2 + (a 0*b 3-b 0*a 3)^2 +
      2*((a 1*b 2-a 2*b 1)^2+(a 2*b 3-a 3*b 2)^2+(a 3*b 1-a 1*b 3)^2) =
      2 * ‖a‖^2 * ‖b‖^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, S, spin, Fin.sum_univ_succ]
    <;> ring
  have h : ‖S a b‖^2 ≤ 2*‖a‖^2*‖b‖^2 := by
    nlinarith [sq_nonneg (a 0*b 0-a 1*b 1-a 2*b 2-a 3*b 3),
      sq_nonneg (a 0*b 1-b 0*a 1), sq_nonneg (a 0*b 2-b 0*a 2),
      sq_nonneg (a 0*b 3-b 0*a 3), sq_nonneg (a 1*b 2-a 2*b 1),
      sq_nonneg (a 2*b 3-a 3*b 2), sq_nonneg (a 3*b 1-a 1*b 3)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa [mul_pow, sqrt_two_sq] using h

private theorem d_bound (t : ℝ) (a b : J) :
    ‖D t a b‖ ≤ Real.sqrt (1+t^2) * ‖a‖ * ‖b‖ := by
  let q := a 1^2+a 2^2+(a 3+t*a 0)^2
  have hid : ‖D t a b‖^2 +
      ((a 0-t*a 3)^2+t^2*(a 1^2+a 2^2))*‖b‖^2 +
      q*b 0^2 + (a 1*b 1+a 2*b 2+(a 3+t*a 0)*b 3)^2 =
      (1+t^2)*‖a‖^2*‖b‖^2 := by
    simp [q, EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift,
      Fin.sum_univ_succ]
    <;> ring
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp : 0 ≤ ((a 0-t*a 3)^2+t^2*(a 1^2+a 2^2))*‖b‖^2 := by positivity
  have h : ‖D t a b‖^2 ≤ (1+t^2)*‖a‖^2*‖b‖^2 := by
    nlinarith [mul_nonneg hq (sq_nonneg (b 0)),
      sq_nonneg (a 1*b 1+a 2*b 2+(a 3+t*a 0)*b 3)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa [mul_pow, Real.sq_sqrt (show 0 ≤ 1+t^2 by positivity)] using h

private theorem self_bound (t : ℝ) (a : J) : ‖D t a a‖ ≤ |t|/2*‖a‖^2 := by
  have hid : 4*‖D t a a‖^2 +
      t^2*(a 0^2-a 1^2-a 2^2-a 3^2)^2+4*t^2*a 0^2*a 3^2 =
      t^2*(‖a‖^2)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift,
      Fin.sum_univ_succ]
    <;> ring
  have h : 4*‖D t a a‖^2 ≤ t^2*(‖a‖^2)^2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (a 0^2-a 1^2-a 2^2-a 3^2)),
      mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg (a 0))) (sq_nonneg (a 3))]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have ht : |t|^2 = t^2 := sq_abs t
  nlinarith

private theorem unit_bound (t : ℝ) (b : J) : ‖D t (e 0) b‖ ≤ |t| *‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp [EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift, e,
    PiLp.single_apply, Fin.sum_univ_succ, mul_pow, sq_abs]
  nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (b 0)),
    mul_nonneg (sq_nonneg t) (sq_nonneg (b 3))]

private theorem self_attained (t : ℝ) : ‖D t balanced balanced‖ = |t|/2 := by
  have hsq : ‖D t balanced balanced‖^2 = t^2/4 := by
    simp [EuclideanSpace.real_norm_sq_eq, balanced, D, C, cross, cross_apply,
      shift, e, PiLp.single_apply, Fin.sum_univ_succ]
    field_simp
    nlinarith [sqrt_two_sq,sqrt_two_four]
  have ht : |t|^2 = t^2 := sq_abs t
  nlinarith [norm_nonneg (D t balanced balanced), abs_nonneg t]

private theorem unit_attained (t : ℝ) : ‖D t (e 0) (e 1)‖ = |t| := by
  have heq : D t (e 0) (e 1) = t • e 2 := by
    ext i; fin_cases i <;> simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply]
  rw [heq, norm_smul]
  simp [e]

/-- The actual unit generator as a continuous operator on the fixed Euclidean space. -/
def unitOperator (t : ℝ) : J →L[ℝ] J := (D t (e 0)).toContinuousLinearMap

private theorem unit_opnorm (t : ℝ) : ‖unitOperator t‖=|t| := by
  apply le_antisymm
  · exact (unitOperator t).opNorm_le_bound (abs_nonneg t) (unit_bound t)
  · have hh := (unitOperator t).le_opNorm (e 1)
    change ‖D t (e 0) (e 1)‖≤‖unitOperator t‖*‖e 1‖ at hh
    rw [unit_attained] at hh
    simpa [e] using hh

/-- The original local defect and unit-generator bounds are attained in the same family. -/
theorem exact_defects (t : ℝ) :
    IsGreatest {r : ℝ | ∃ a : J, ‖a‖=1 ∧ r=‖D t a a‖} (|t|/2) ∧
    IsGreatest {r : ℝ | ∃ b : J, ‖b‖=1 ∧ r=‖D t (e 0) b‖} |t| ∧
    (∀ a b : J, ‖S a b‖ ≤ Real.sqrt 2*‖a‖*‖b‖) ∧
    (∀ a b : J, ‖D t a b‖ ≤ Real.sqrt (1+t^2)*‖a‖*‖b‖) ∧
    ‖unitOperator t‖=|t| := by
  refine ⟨⟨⟨balanced, balanced_norm, (self_attained t).symm⟩, ?_⟩,
    ⟨⟨e 1, by simp [e], (unit_attained t).symm⟩, ?_⟩, spin_bound, d_bound t,unit_opnorm t⟩
  · rintro r ⟨a, ha, rfl⟩
    simpa [ha] using self_bound t a
  · rintro r ⟨b, hb, rfl⟩
    simpa [hb] using unit_bound t b


/-- The actual action Gram operator, using adjoints for the fixed Euclidean inner product. -/
def actionGram (t : ℝ) : J →ₗ[ℝ] J :=
  ∑ i : Fin 4, (LinearMap.adjoint (D t (e i))).comp (D t (e i))

private theorem d_adjoint (t : ℝ) (a : J) : LinearMap.adjoint (D t a) = -D t a := by
  apply LinearMap.ext
  intro b
  apply ext_inner_right ℝ
  intro c
  rw [LinearMap.adjoint_inner_left]
  simp [PiLp.inner_apply, D, C, cross, cross_apply, shift, Fin.sum_univ_succ,
    RCLike.inner_apply]
  <;> ring

private theorem gram_coordinates (t : ℝ) (a : J) :
    actionGram t a = toLp 2 ![0,(2+t^2)*a 1,(2+t^2)*a 2,2*a 3] := by
  simp only [actionGram, d_adjoint]
  ext i; fin_cases i <;>
    simp [Fin.sum_univ_succ, D, C, cross, cross_apply, shift, e, PiLp.single_apply] <;> ring

private theorem common_kernel (t : ℝ) (a : J) :
    (∀ i : Fin 4, D t (e i) a = 0) ↔ a 1=0 ∧ a 2=0 ∧ a 3=0 := by
  constructor
  · intro h
    have hx := h 1
    have hy := h 2
    have hx2 := congrArg (fun v : J => v 2) hx
    have hx3 := congrArg (fun v : J => v 3) hx
    have hy3 := congrArg (fun v : J => v 3) hy
    simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply] at hx2 hx3 hy3
    exact ⟨hy3, hx3, by linarith⟩
  · rintro ⟨h1,h2,h3⟩ i
    fin_cases i <;> ext k <;> fin_cases k <;>
      simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply, h1,h2,h3]

private theorem scalar_axis (a : J) :
    (a 1=0 ∧ a 2=0 ∧ a 3=0) ↔ ∃ r : ℝ, a = r • e 0 := by
  constructor
  · rintro ⟨h1,h2,h3⟩
    refine ⟨a 0, ?_⟩
    ext i; fin_cases i <;> simp [e, PiLp.single_apply, h1,h2,h3]
  · rintro ⟨r,rfl⟩
    simp [e, PiLp.single_apply]

private theorem label_kernel (t : ℝ) (a : J) :
    D t a = 0 ↔ ∃ r : ℝ, a = r • (e 0-t • e 3) := by
  constructor
  · intro h
    have hx := LinearMap.congr_fun h (e 1)
    have hy := LinearMap.congr_fun h (e 2)
    have hx2 := congrArg (fun v : J => v 2) hx
    have hx3 := congrArg (fun v : J => v 3) hx
    have hy3 := congrArg (fun v : J => v 3) hy
    simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply] at hx2 hx3 hy3
    refine ⟨a 0, ?_⟩
    ext i; fin_cases i <;> simp [e, PiLp.single_apply]
    · linarith
    · linarith
    · linarith
  · rintro ⟨r,rfl⟩
    ext b i; fin_cases i <;>
      simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply] <;> ring

/-- The span of all actual local table outputs. -/
def actionSupport (t : ℝ) : Submodule ℝ J :=
  Submodule.span ℝ (Set.range (fun p : Fin 4 × Fin 4 => D t (e p.1) (e p.2)))

private theorem support_coordinates (t : ℝ) (a : J) : a ∈ actionSupport t ↔ a 0=0 := by
  constructor
  · intro ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro v ⟨p,rfl⟩
      simp [D,C,cross,cross_apply]
    · rfl
    · intro a b ha hb
      simp_all
    · intro r a ha
      simp_all
  · intro ha
    have hx : e 1 ∈ actionSupport t := by
      have heq : D t (e 2) (e 3) = e 1 := by
        ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
      exact heq ▸ Submodule.subset_span (Set.mem_range_self (2,3))
    have hy : e 2 ∈ actionSupport t := by
      have heq : D t (e 3) (e 1) = e 2 := by
        ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
      exact heq ▸ Submodule.subset_span (Set.mem_range_self (3,1))
    have hz : e 3 ∈ actionSupport t := by
      have heq : D t (e 1) (e 2) = e 3 := by
        ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
      exact heq ▸ Submodule.subset_span (Set.mem_range_self (1,2))
    have heq : a = a 1 • e 1 + a 2 • e 2 + a 3 • e 3 := by
      ext i; fin_cases i <;> simp [e,PiLp.single_apply,ha]
    rw [heq]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)) (Submodule.smul_mem _ _ hz)

private theorem gram_eigenvalues (t lam : ℝ) :
    (∃ a : J, a ≠ 0 ∧ actionGram t a = lam • a) ↔
      lam=0 ∨ lam=2+t^2 ∨ lam=2 := by
  constructor
  · rintro ⟨a,ha,heq⟩
    by_cases h0 : lam=0
    · exact Or.inl h0
    by_cases hxy : lam=2+t^2
    · exact Or.inr (Or.inl hxy)
    by_cases hz : lam=2
    · exact Or.inr (Or.inr hz)
    exfalso
    apply ha
    ext i
    have h := congrArg (fun v : J => v i) heq
    fin_cases i
    · simp [gram_coordinates] at h
      exact h.resolve_left h0
    · simp [gram_coordinates] at h
      exact h.resolve_left (Ne.symm hxy)
    · simp [gram_coordinates] at h
      exact h.resolve_left (Ne.symm hxy)
    · simp [gram_coordinates] at h
      exact h.resolve_left (Ne.symm hz)
  · rintro (rfl|rfl|rfl)
    · refine ⟨e 0, ?_, ?_⟩
      · simp [e]
      · ext i; fin_cases i <;> simp [gram_coordinates,e,PiLp.single_apply]
    · refine ⟨e 1, ?_, ?_⟩
      · simp [e]
      · ext i; fin_cases i <;> simp [gram_coordinates,e,PiLp.single_apply]
    · refine ⟨e 3, ?_, ?_⟩
      · simp [e]
      · ext i; fin_cases i <;> simp [gram_coordinates,e,PiLp.single_apply]

/-- The same actual action has its exact Gram diagonal, fixed kernel, spatial support and spectrum. -/
theorem exact_action_data (t : ℝ) :
    (∀ a : J, actionGram t a = toLp 2 ![0,(2+t^2)*a 1,(2+t^2)*a 2,2*a 3]) ∧
    (∀ a : J, (∀ i : Fin 4, D t (e i) a=0) ↔ ∃ r : ℝ, a=r • e 0) ∧
    (∀ a : J, a ∈ actionSupport t ↔ a 0=0) ∧
    (∀ a : J, D t a=0 ↔ ∃ r : ℝ, a=r • (e 0-t • e 3)) ∧
    (∀ lam : ℝ, (∃ a : J, a≠0 ∧ actionGram t a=lam • a) ↔
      lam=0 ∨ lam=2+t^2 ∨ lam=2) := by
  refine ⟨gram_coordinates t, ?_, support_coordinates t, label_kernel t, gram_eigenvalues t⟩
  intro a
  exact (common_kernel t a).trans (scalar_axis a)


/-- A unit label attaining the exact bilinear action constant. -/
def extremalLabel (t : ℝ) : J :=
  (Real.sqrt (1+t^2))⁻¹ • (t • e 0+e 3)

private theorem extremal_norm (t : ℝ) : ‖extremalLabel t‖=1 := by
  have hp : 0<Real.sqrt (1+t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0≤1+t^2 by positivity)
  have hn : ‖extremalLabel t‖^2=1 := by
    simp [EuclideanSpace.real_norm_sq_eq,extremalLabel,e,PiLp.single_apply,
      Fin.sum_univ_succ]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (extremalLabel t)]

private theorem d_attained (t : ℝ) :
    ‖D t (extremalLabel t) (e 1)‖=Real.sqrt (1+t^2) := by
  have hp : 0<Real.sqrt (1+t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0≤1+t^2 by positivity)
  have heq : D t (extremalLabel t) (e 1)=Real.sqrt (1+t^2) • e 2 := by
    ext i; fin_cases i <;>
      simp [extremalLabel,D,C,cross,cross_apply,shift,e,PiLp.single_apply]
    field_simp
    nlinarith
  rw [heq,norm_smul]
  simp [e,abs_of_pos hp]

private theorem spin_attained : ‖S balanced balanced‖=Real.sqrt 2 := by
  have hs := sqrt_two_sq
  have hn : ‖S balanced balanced‖^2=2 := by
    simp [EuclideanSpace.real_norm_sq_eq,S,spin,balanced,e,PiLp.single_apply,
      Fin.sum_univ_succ]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (S balanced balanced),sqrt_two_pos]

/-- The finite curvature entry uses the original complete basis and spin multiplication. -/
def curvature (i j k : Fin 4) : J := S (e i) (S (e j) (e k))-S (e j) (S (e i) (e k))

theorem spin_commutator (a b c : J) :
    S a (S b c)-S b (S a c) = -(C (C a b) c) := by
  have hv : ![(C a b) 1,(C a b) 2,(C a b) 3] =
      crossProduct ![a 1,a 2,a 3] ![b 1,b 2,b 3] := by
    ext i; fin_cases i <;> rfl
  change spin a (spin b c)-spin b (spin a c) =
    -(toLp 2 (Matrix.vecCons 0
      (crossProduct ![(C a b) 1,(C a b) 2,(C a b) 3] ![c 1,c 2,c 3])))
  rw [hv,cross_cross_eq_smul_sub_smul]
  ext i; fin_cases i <;> simp [spin] <;> ring

private theorem curvature_bound (i j k : Fin 4) : ‖curvature i j k‖≤1 := by
  have hc (a b : J) : ‖C a b‖≤‖a‖*‖b‖ := by
    have hs : shift 0 a=a := by
      ext l; fin_cases l <;> simp [shift]
    simpa [D,hs] using d_bound 0 a b
  have hbound (a b c : J) :
      ‖S a (S b c)-S b (S a c)‖≤‖a‖*‖b‖*‖c‖ := by
    rw [spin_commutator,norm_neg]
    exact (hc (C a b) c).trans
      (mul_le_mul_of_nonneg_right (hc a b) (norm_nonneg c))
  simpa [curvature,e] using hbound (e i) (e j) (e k)

private theorem curvature_attained : ‖curvature 1 2 2‖=1 := by
  rw [curvature,spin_commutator]
  have h : -(C (C (e 1) (e 2)) (e 2))=e 1 := by
    change -(toLp 2 (Matrix.vecCons 0
      (crossProduct ![(C (e 1) (e 2)) 1,(C (e 1) (e 2)) 2,
        (C (e 1) (e 2)) 3] ![(e 2) 1,(e 2) 2,(e 2) 3])))=e 1
    have hv : ![(C (e 1) (e 2)) 1,(C (e 1) (e 2)) 2,
        (C (e 1) (e 2)) 3] =
        crossProduct ![(e 1) 1,(e 1) 2,(e 1) 3]
          ![(e 2) 1,(e 2) 2,(e 2) 3] := by
      ext i; fin_cases i <;> rfl
    rw [hv,cross_cross_eq_smul_sub_smul]
    ext i; fin_cases i <;> norm_num [e,PiLp.single_apply,Matrix.vec3_dotProduct]
  rw [h]
  simp [e]

/-- Exact local constants, with attaining inputs rather than only upper bounds. -/
theorem exact_constants (t : ℝ) :
    ‖e 0‖=1 ∧
    IsGreatest {r : ℝ | ∃ a b : J, ‖a‖=1 ∧ ‖b‖=1 ∧ r=‖S a b‖} (Real.sqrt 2) ∧
    IsGreatest {r : ℝ | ∃ a b : J, ‖a‖=1 ∧ ‖b‖=1 ∧ r=‖D t a b‖}
      (Real.sqrt (1+t^2)) ∧
    IsGreatest {r : ℝ | ∃ i j k : Fin 4, r=‖curvature i j k‖} 1 := by
  refine ⟨by simp [e], ⟨⟨balanced,balanced,balanced_norm,balanced_norm,
    spin_attained.symm⟩,?_⟩,
    ⟨⟨extremalLabel t,e 1,extremal_norm t,by simp [e],(d_attained t).symm⟩,?_⟩,
    ⟨⟨1,2,2,curvature_attained.symm⟩,?_⟩⟩
  · rintro r ⟨a,b,ha,hb,rfl⟩
    simpa [ha,hb] using spin_bound a b
  · rintro r ⟨a,b,ha,hb,rfl⟩
    simpa [ha,hb] using d_bound t a b
  · rintro r ⟨i,j,k,rfl⟩
    exact curvature_bound i j k

/-- The actual label Gram, distinct from the action Gram. -/
def labelGram (t : ℝ) : J →ₗ[ℝ] J :=
  ∑ i : Fin 4, (LinearMap.adjoint ((LinearMap.flip (D t)) (e i))).comp
    ((LinearMap.flip (D t)) (e i))

private theorem label_gram_coordinates (t : ℝ) (a : J) :
    labelGram t a=toLp 2 ![2*t^2*a 0+2*t*a 3,2*a 1,2*a 2,2*t*a 0+2*a 3] := by
  apply ext_inner_right ℝ
  intro b
  simp only [labelGram,LinearMap.sum_apply,LinearMap.comp_apply,sum_inner,
    LinearMap.adjoint_inner_left]
  simp [PiLp.inner_apply,D,C,cross,cross_apply,shift,e,PiLp.single_apply,
    Fin.sum_univ_succ,RCLike.inner_apply]
  <;> ring

private theorem label_eigenvalues (t lam : ℝ) :
    (∃ a : J, a≠0 ∧ labelGram t a=lam • a) ↔
      lam=0 ∨ lam=2 ∨ lam=2*(1+t^2) := by
  constructor
  · rintro ⟨a,ha,heq⟩
    by_cases h0 : lam=0
    · exact Or.inl h0
    by_cases h2 : lam=2
    · exact Or.inr (Or.inl h2)
    by_cases hp : lam=2*(1+t^2)
    · exact Or.inr (Or.inr hp)
    exfalso
    have hx := congrArg (fun v : J => v 0) heq
    have hz := congrArg (fun v : J => v 3) heq
    simp [label_gram_coordinates] at hx hz
    have hc : lam*(lam-2*(1+t^2))≠0 :=
      mul_ne_zero h0 (sub_ne_zero.mpr hp)
    have ha0 : a 0=0 := by
      have hh : (lam*(lam-2*(1+t^2)))*a 0=0 := by
        linear_combination -(lam-2)*hx-2*t*hz
      exact (mul_eq_zero.mp hh).resolve_left hc
    have ha3 : a 3=0 := by
      have hh : (lam*(lam-2*(1+t^2)))*a 3=0 := by
        linear_combination -2*t*hx-(lam-2*t^2)*hz
      exact (mul_eq_zero.mp hh).resolve_left hc
    apply ha
    ext i; fin_cases i
    · exact ha0
    · have hh := congrArg (fun v : J => v 1) heq
      simp [label_gram_coordinates] at hh
      exact hh.resolve_left (Ne.symm h2)
    · have hh := congrArg (fun v : J => v 2) heq
      simp [label_gram_coordinates] at hh
      exact hh.resolve_left (Ne.symm h2)
    · exact ha3
  · rintro (rfl|rfl|rfl)
    · refine ⟨e 0-t • e 3,?_,?_⟩
      · intro h
        have hh := congrArg (fun a : J => a 0) h
        norm_num [e,PiLp.single_apply] at hh
      · ext i; fin_cases i <;> simp [label_gram_coordinates,e,PiLp.single_apply] <;> ring
    · refine ⟨e 1,by simp [e],?_⟩
      ext i; fin_cases i <;> simp [label_gram_coordinates,e,PiLp.single_apply]
    · refine ⟨t • e 0+e 3,?_,?_⟩
      · intro h
        have hh := congrArg (fun a : J => a 3) h
        norm_num [e,PiLp.single_apply] at hh
      · ext i; fin_cases i <;> simp [label_gram_coordinates,e,PiLp.single_apply] <;> ring

/-- The positive spectrum of the actual action Gram. -/
def positiveActionSpectrum (t : ℝ) : Set ℝ :=
  {lam : ℝ | 0<lam ∧ ∃ a : J, a≠0 ∧ actionGram t a=lam • a}
/-- The square root of the actual least positive action eigenvalue. -/
def actionGap (t : ℝ) : ℝ := Real.sqrt (sInf (positiveActionSpectrum t))

private theorem minimum_positive (t : ℝ) : IsLeast (positiveActionSpectrum t) 2 := by
  refine ⟨⟨by norm_num,?_⟩,?_⟩
  · exact (gram_eigenvalues t 2).2 (Or.inr (Or.inr rfl))
  · rintro lam ⟨hpos,heig⟩
    rcases (gram_eigenvalues t lam).1 heig with h|h|h
    · linarith
    · rw [h]; nlinarith [sq_nonneg t]
    · linarith

/-- Both exact spectra and the actual positive square-root gap belong to the same local action. -/
theorem exact_label_data (t : ℝ) :
    (∀ a : J, labelGram t a=toLp 2 ![2*t^2*a 0+2*t*a 3,2*a 1,2*a 2,2*t*a 0+2*a 3]) ∧
    (∀ lam : ℝ, (∃ a : J, a≠0 ∧ labelGram t a=lam • a) ↔
      lam=0 ∨ lam=2 ∨ lam=2*(1+t^2)) ∧
    IsLeast (positiveActionSpectrum t) 2 ∧ actionGap t=Real.sqrt 2 := by
  refine ⟨label_gram_coordinates t,label_eigenvalues t,minimum_positive t,?_⟩
  unfold actionGap
  rw [(minimum_positive t).csInf_eq]

/-- The common kernel of the actual complete action table. -/
def commonFixed (t : ℝ) : Submodule ℝ J := ⨅ i : Fin 4, (D t (e i)).ker

private theorem fixed_mem (t : ℝ) (a : J) :
    a∈commonFixed t ↔ ∃ r : ℝ, a=r • e 0 := by
  simp only [commonFixed,Submodule.mem_iInf,LinearMap.mem_ker]
  exact (common_kernel t a).trans (scalar_axis a)

private theorem support_orthogonal (t : ℝ) (a : J) :
    a∈(commonFixed t).orthogonal ↔ a 0=0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    have he0 : e 0∈commonFixed t := (fixed_mem t (e 0)).2 ⟨1,by simp⟩
    have hh := h (e 0) he0
    simpa [e,EuclideanSpace.inner_single_left] using hh
  · intro ha b hb
    rcases (fixed_mem t b).1 hb with ⟨r,rfl⟩
    simp [inner_smul_left,e,EuclideanSpace.inner_single_left,ha]

private theorem spectral_lower (t : ℝ) (a : J) (ha : a∈actionSupport t) :
    2*‖a‖^2≤ inner ℝ a (actionGram t a) := by
  have h0 := (support_coordinates t a).1 ha
  have heq : inner ℝ a (actionGram t a)=2*‖a‖^2+t^2*(a 1^2+a 2^2) := by
    simp [gram_coordinates,PiLp.inner_apply,EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succ,RCLike.inner_apply,h0]
    <;> ring
  rw [heq]
  nlinarith [mul_nonneg (sq_nonneg t) (add_nonneg (sq_nonneg (a 1)) (sq_nonneg (a 2)))]

/-- The positive support has an attained uniform gap, and the label and action kernels differ. -/
theorem exact_support_gap (t : ℝ) :
    actionSupport t=(commonFixed t).orthogonal ∧
    (∀ a : J, a∈actionSupport t → 2*‖a‖^2≤ inner ℝ a (actionGram t a)) ∧
    (e 3∈actionSupport t ∧ ‖e 3‖=1 ∧ actionGram t (e 3)=2 • e 3) ∧
    D t≠0 ∧
    (t≠0 → (∃ a : J, D t a a≠0) ∧ D t (e 0)≠0 ∧
      (D t).ker≠commonFixed t) ∧
    (∀ a : J, D 0 a a=0) ∧ D 0 (e 0)=0 := by
  refine ⟨?_,spectral_lower t,⟨?_,by simp [e],?_⟩,?_,?_,?_,?_⟩
  · ext a
    exact (support_coordinates t a).trans (support_orthogonal t a).symm
  · exact (support_coordinates t (e 3)).2 (by simp [e,PiLp.single_apply])
  · ext i; fin_cases i <;> simp [gram_coordinates,e,PiLp.single_apply]
  · intro h
    have he := congrArg (fun F : J →ₗ[ℝ] J →ₗ[ℝ] J => F (e 1) (e 2)) h
    have he3 : D t (e 1) (e 2)=e 3 := by
      ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
    rw [he3] at he
    have hh := congrArg (fun a : J => a 3) he
    norm_num [e,PiLp.single_apply] at hh
  · intro ht
    have hp : 0 < |t| := abs_pos.mpr ht
    have hself : D t balanced balanced≠0 := by
      intro h
      have hh := self_attained t
      rw [h,norm_zero] at hh
      linarith
    have hunit : D t (e 0)≠0 := by
      intro h
      have hh := unit_attained t
      rw [h,LinearMap.zero_apply,norm_zero] at hh
      linarith
    refine ⟨⟨balanced,hself⟩,hunit,?_⟩
    intro hk
    have hmem : e 0∈commonFixed t := (fixed_mem t (e 0)).2 ⟨1,by simp⟩
    rw [←hk] at hmem
    exact hunit hmem
  · intro a
    ext i; fin_cases i <;> simp [D,C,cross,cross_apply,shift] <;> ring
  · apply LinearMap.ext
    intro a
    ext i; fin_cases i <;> simp [D,C,cross,cross_apply,shift,e,PiLp.single_apply]

end D5.S3.Quantum.Algebra.PauliFixedProductFamily

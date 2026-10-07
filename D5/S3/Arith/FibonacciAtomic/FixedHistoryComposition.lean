/- GID: D5/S3/Arith/FibonacciAtomic/FixedHistoryComposition
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FixedHistoryComposition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual Clifford history and prescribed composition through directed capacities. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Group.Semiconj.Units
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Decomposition
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.FixedHistoryComposition
open GenealogicalFiberTransport (Source substitution composition)
open scoped BigOperators

def Q : QuadraticForm ℝ (ℝ × ℝ) :=
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ) +
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ) -
  QuadraticMap.linMulLin (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)
abbrev C := CliffordAlgebra Q
def A : C := CliffordAlgebra.ι Q (1,0)
def B : C := CliffordAlgebra.ι Q (0,1)
def AU : Cˣ := ⟨A,A,
  by simpa only [A,show Q (1,0)=1 by norm_num [Q],map_one] using CliffordAlgebra.ι_sq_scalar Q (1,0),
  by simpa only [A,show Q (1,0)=1 by norm_num [Q],map_one] using CliffordAlgebra.ι_sq_scalar Q (1,0)⟩
def BU : Cˣ := ⟨B,-B,
  by
    have h : B*B = -1 := by
      simpa only [B,show Q (0,1)= -1 by norm_num [Q],map_neg,map_one] using CliffordAlgebra.ι_sq_scalar Q (0,1)
    simpa [mul_neg,h],
  by
    have h : B*B = -1 := by
      simpa only [B,show Q (0,1)= -1 by norm_num [Q],map_neg,map_one] using CliffordAlgebra.ι_sq_scalar Q (0,1)
    simpa [neg_mul,h]⟩
def SU : Cˣ := BU*AU
def DU : Cˣ := SU^(2:ℤ)*AU
abbrev Tri := C × C × C
abbrev UTri := Cˣ × Cˣ × Cˣ
def value (x : UTri) : Tri := (x.1.val,x.2.1.val,x.2.2.val)
def L (u v w : ℤ) : UTri :=
  ((-1 : Cˣ)^v * SU^(2*u), (-1 : Cˣ)^w * SU^(2*v), (-1 : Cˣ)^u * SU^(2*w))
def g : UTri := (AU,BU,SU)
def h : UTri := (BU,SU,DU)
def R (p q : Bool) : UTri := if p then (if q then g*h else g) else (if q then h else 1)
def letter (b : Bool) : UTri := if b then g else h
def E : Source →ₙ* C := FreeMagma.lift fun b => if b then A else B
def W3 (t : Source) : Tri := (E t,E (substitution t),E (substitution (substitution t)))
def Omega (u v w : ℤ) (p q : Bool) : Tri := value (L u v w * R p q)
structure Params where
  u : ℤ
  v : ℤ
  w : ℤ
  p : Bool
  q : Bool
  deriving DecidableEq

abbrev State := Bool × Bool
abbrev Kind := State × Bool
def step (z : State) (b : Bool) : State := if b then (!z.1,z.2) else (z.1,!z.2)
def delta (z : State) (b : Bool) : ℤ × ℤ × ℤ :=
  if z.1 then
    if z.2 then (if b then (-1,-1,0) else (0,-1,0))
    else (if b then (0,0,1) else (0,0,0))
  else
    if z.2 then (if b then (1,1,-1) else (0,1,0))
    else (0,0,0)
def edgeCounts (u v w X Y : ℤ) (p q : Bool) : Kind → ℤ
  | ((false,false),true) => X+w-u+p.toNat
  | ((true,false),true) => X+w
  | ((false,true),true) => X
  | ((true,true),true) => X-u
  | ((false,false),false) => Y+u+q.toNat*(1-(p.toNat:ℤ))
  | ((false,true),false) => Y
  | ((true,false),false) => Y-v+p.toNat*q.toNat
  | ((true,true),false) => Y+u-v

def PositiveSupport (m : Kind → ℤ) := State
instance (m : Kind → ℤ) : Quiver (PositiveSupport m) :=
  ⟨fun i j => {b : Bool // step i b = j ∧ 0 < m (i,b)}⟩
def RootedSupport (m : Kind → ℤ) : Prop :=
  ∀ e : Kind, 0 < m e →
    Nonempty (@Quiver.Path (Quiver.Symmetrify (PositiveSupport m)) _ (false,false) e.1) ∧
    Nonempty (@Quiver.Path (Quiver.Symmetrify (PositiveSupport m)) _ (false,false) (step e.1 e.2))

instance : Quiver State := ⟨fun i j => {b : Bool // step i b = j}⟩
def pathCounts {s t : State} (P : Quiver.Path s t) : Kind → ℕ :=
  P.addWeight (fun {i j : State} (e : i ⟶ j) => fun k => if k = (i,e.val) then 1 else 0)
def pathWord {s t : State} (P : Quiver.Path s t) : List Bool :=
  (P.weight (fun {i j : State} (e : i ⟶ j) => (FreeMonoid.of e.val : FreeMonoid Bool))).toList
def divergence (m : Kind → ℤ) (z : State) : ℤ :=
  ∑ e : Kind, m e * ((if e.1 = z then 1 else 0) - (if step e.1 e.2 = z then 1 else 0))


set_option maxHeartbeats 2400000 in
theorem result (u v w : ℤ) (p q : Bool) (ac bc : ℕ) (hpositive : 1 ≤ ac+bc) :
    (∃ t : Source, W3 t=Omega u v w p q ∧ composition t=(ac,bc)) ↔
    ∃ X Y : ℤ,
      (X:ℚ)=((ac:ℚ)-(p.toNat:ℚ)-2*(w:ℚ)+2*(u:ℚ))/4 ∧
      (Y:ℚ)=((bc:ℚ)-(q.toNat:ℚ)-2*(u:ℚ)+2*(v:ℚ))/4 ∧
      (∀ e, 0 ≤ edgeCounts u v w X Y p q e) ∧
      RootedSupport (edgeCounts u v w X Y p q) := by
  classical
  let N (k : Params) : Tri := Omega k.u k.v k.w k.p k.q
  have Q_apply (x : ℝ × ℝ) : Q x=x.1*x.1+x.1*x.2-x.2*x.2 := rfl
  have a_sq : A*A=1 := by
    simpa [A,Q_apply] using CliffordAlgebra.ι_sq_scalar Q (1,0)
  have b_sq : B*B = -1 := by
    simpa [B,Q_apply] using CliffordAlgebra.ι_sq_scalar Q (0,1)
  have ab_swap : A*B+B*A=1 := by
    simpa [A,B,QuadraticMap.polar,Q_apply] using CliffordAlgebra.ι_mul_ι_add_swap (Q:=Q) (1,0) (0,1)
  have au_val : (AU : C)=A := rfl
  have bu_val : (BU : C)=B := rfl
  have su_val : (SU : C)=B*A := rfl
  have au_sq : AU*AU=1 := Units.ext a_sq
  have bu_sq : BU*BU = -1 := Units.ext b_sq
  have au_inv : AU⁻¹=AU := by apply inv_eq_of_mul_eq_one_left; exact au_sq
  have bu_inv : BU⁻¹ = -BU := by apply inv_eq_of_mul_eq_one_left; simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv]
  have su_sq : (SU : C)*(SU : C) = (SU : C)+1 := by
    change (B*A)*(B*A)=B*A+1
    have hab : A*B=1-B*A := eq_sub_of_add_eq ab_swap
    calc
      (B*A)*(B*A) = B*(A*B)*A := by noncomm_ring
      _ = B*(1-B*A)*A := by rw [hab]
      _ = B*A-(B*B)*(A*A) := by noncomm_ring
      _ = B*A+1 := by simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv]
  have su_inv_val : ((SU⁻¹ : Cˣ) : C) = (SU : C)-1 := by
    simp only [SU,mul_inv_rev,Units.val_mul,au_inv,bu_inv,Units.val_neg,au_val,bu_val]
    have hab : A*B=1-B*A := eq_sub_of_add_eq ab_swap
    change A*(-B)=B*A-1
    rw [mul_neg,hab]
    noncomm_ring
  have a_s : AU*SU = (-SU⁻¹)*AU := by
    apply Units.ext
    change A*(B*A)=(-((SU⁻¹ : Cˣ):C))*A
    rw [su_inv_val]
    calc
      A*(B*A) = (A*B)*A := _root_.mul_assoc _ _ _ |>.symm
      _ = (1-B*A)*A := by rw [eq_sub_of_add_eq ab_swap]
      _ = (-(B*A-1))*A := by noncomm_ring
  have sign_comm (x : Cˣ) : Commute (-1 : Cˣ) x := by
    apply Units.ext
    change (-1:C)*x.val=x.val*(-1:C)
    simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv]
  have a_signed_power (n : ℤ) :
    A*((SU^n : Cˣ):C) = (((-1:Cˣ)^n : Cˣ):C)*((SU^(-n):Cˣ):C)*A := by
    have h0 : SemiconjBy A (SU:C) ((-SU⁻¹:Cˣ):C) := by
      exact congrArg Units.val a_s
    have hn := h0.units_zpow_right n
    have hc : Commute (-1:Cˣ) SU⁻¹ := sign_comm _
    have hp : (-SU⁻¹:Cˣ)^n = (-1:Cˣ)^n * SU^(-n) := by
      rw [show (-SU⁻¹:Cˣ)=(-1:Cˣ)*SU⁻¹ by simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv], hc.mul_zpow, inv_zpow, zpow_neg]
    simpa only [SemiconjBy,hp,Units.val_mul,mul_assoc] using hn
  have d_eq : A+B=((SU^(2:ℤ):Cˣ):C)*A := by
    rw [zpow_ofNat,Units.val_pow_eq_pow_val,pow_two,su_sq]
    change A+B=(B*A+1)*A
    calc
      A+B = B*(A*A)+A := by simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv]; abel
      _ = (B*A+1)*A := by noncomm_ring
  have du_val : (DU:C)=A+B := by
    change ((SU^(2:ℤ):Cˣ):C)*A=A+B
    exact d_eq.symm
  have value_mul (x y : UTri) : value (x*y)=value x*value y := rfl
  have value_one : value (1:UTri)=(1:Tri) := rfl
  let WHom : Source →ₙ* Tri :=
    { toFun := W3
      map_mul' := by intro s t; simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,W3,E,map_mul] }
  have w3_leaf : W3 (.of true)=(A,B,(SU:C)) ∧ W3 (.of false)=(B,(SU:C),A+B) := by
    constructor
    · simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,W3,E,substitution,FreeMagma.lift_of,SU,BU,AU]
    · simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,W3,E,substitution,FreeMagma.lift_of,SU,BU,AU]
      change (B*A)*B=A+B
      rw [mul_assoc]
      have hab : A*B=1-B*A := eq_sub_of_add_eq ab_swap
      rw [hab]
      calc
        B*(1-B*A)=B-(B*B)*A := by noncomm_ring
        _ = A+B := by simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one]; abel
  have w3_hom : WHom = FreeMagma.lift (fun b => value (letter b)) := by
    apply FreeMagma.hom_ext
    funext b
    change W3 (.of b)=value (letter b)
    cases b
    · simpa [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,letter,g,h,value] using w3_leaf.2
    · simpa [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,letter,g,h,value] using w3_leaf.1
  have coord_add (a b c d : ℤ) :
    ((-1:Cˣ)^a*SU^(2*b))*((-1:Cˣ)^c*SU^(2*d))=
      (-1:Cˣ)^(a+c)*SU^(2*(b+d)) := by
    rw [((sign_comm SU).symm.zpow_zpow (2*b) c).mul_mul_mul_comm]
    rw [← zpow_add, ← zpow_add]
    rw [show 2*b+2*d=2*(b+d) by ring]
  have l_add (u v w u' v' w' : ℤ) :
    L u v w*L u' v' w'=L (u+u') (v+v') (w+w') := by
    apply Prod.ext
    · exact coord_add v u v' u'
    · apply Prod.ext
      · exact coord_add w v w' v'
      · exact coord_add u w u' w'
  have l_zero : L 0 0 0=1 := by simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,L]
  have a_power (n : ℤ) : AU*SU^n = ((-1:Cˣ)^n * SU^(-n))*AU := by
    apply Units.ext
    exact a_signed_power n
  have b_s_a : BU=SU*AU := by simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,SU,mul_assoc]
  have a_power_tail (n : ℤ) (x : Cˣ) : AU*(SU^n*x)=
    (-1:Cˣ)^n*(SU^(-n)*(AU*x)) := by rw [←mul_assoc,a_power]; simp only [mul_assoc]
  have a_s_tail (x : Cˣ) : AU*(SU*x)= -(SU⁻¹*(AU*x)) := by
    rw [←mul_assoc,a_s]
    simp only [neg_mul,mul_assoc]
  have a_natpow_tail (n : ℕ) (x : Cˣ) : AU*(SU^n*x)=
    (-1:Cˣ)^n*((SU^n)⁻¹*(AU*x)) := by
    simpa only [zpow_natCast,zpow_neg] using a_power_tail (n:ℤ) x
  have a_s_inv : AU*SU⁻¹ = -SU*AU := by
    simpa [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero] using a_power (-1)

  -- Every case is a direct small-exponent computation from the actual units.
  have right_table (p q b : Bool) : R p q*letter b =
    L (delta (p,q) b).1 (delta (p,q) b).2.1 (delta (p,q) b).2.2 *
      R ((step (p,q) b).1) ((step (p,q) b).2) := by
    cases p <;> cases q <;> cases b <;>
      simp only [R,letter,delta,step,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,↓reduceIte,L,g,h,DU,Prod.fst_mul,Prod.snd_mul,
        Prod.fst_one,Prod.snd_one] <;>
      apply Prod.ext
    all_goals try (apply Prod.ext)
    all_goals try dsimp only
    all_goals try simp only [zpow_zero,zpow_one,zpow_neg_one,one_mul,mul_one]
    all_goals try rfl
    all_goals try rw [b_s_a]
    all_goals try simp only [←zpow_ofNat,show (2:ℤ)*(1:ℤ)=2 by rfl,
      show (2:ℤ)*(-1:ℤ)= -2 by rfl]
    all_goals try simp only [mul_assoc,au_sq,mul_one]
    all_goals try rw [←mul_assoc,au_sq,one_mul]
    all_goals try rw [←mul_assoc,a_power]
    all_goals try rw [a_power_tail]
    all_goals try simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,mul_assoc,←zpow_add]
    all_goals try simp only [a_s_tail,a_natpow_tail,a_s,au_sq,mul_one,one_mul,
      neg_mul,mul_neg,neg_neg,mul_assoc]
    all_goals try norm_num
    all_goals try group
    all_goals try simp only [zpow_ofNat,pow_two]
    all_goals try rw [mul_assoc,a_s_inv]
    all_goals try simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,mul_assoc]
    all_goals try rw [a_s_inv]
    all_goals try simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,mul_assoc]
  let K : (ℝ × ℝ) →ₗ[ℝ] (Matrix (Fin 2) (Fin 2) ℝ) := {
    toFun x := !![0,x.1+x.2*Real.goldenRatio;x.1+x.2*Real.goldenConj,0]
    map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero] <;> ring
    map_smul' c x := by ext i j; fin_cases i <;> fin_cases j <;> simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero] <;> ring
  }
  have k_square (x : ℝ × ℝ) : K x*K x=algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (Q x) := by
    have hp : (x.1+x.2*Real.goldenRatio)*(x.1+x.2*Real.goldenConj)=Q x := by
      rw [Q_apply]
      calc
        (x.1+x.2*Real.goldenRatio)*(x.1+x.2*Real.goldenConj) =
          x.1*x.1+x.1*x.2*(Real.goldenRatio+Real.goldenConj)+x.2*x.2*(Real.goldenRatio*Real.goldenConj) := by ring
        _ = x.1*x.1+x.1*x.2-x.2*x.2 := by
          rw [Real.goldenRatio_add_goldenConj,Real.goldenRatio_mul_goldenConj]; ring
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,K,Matrix.mul_apply,Fin.sum_univ_two,Matrix.algebraMap_eq_diagonal,hp,mul_comm]
  let sep : C →ₐ[ℝ] (Matrix (Fin 2) (Fin 2) ℝ) := CliffordAlgebra.lift Q ⟨K,k_square⟩
  have sep_a : sep A=!![0,1;1,0] := by
    unfold sep A
    rw [CliffordAlgebra.lift_ι_apply]
    simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,K]
  have sep_b : sep B=!![0,Real.goldenRatio;Real.goldenConj,0] := by
    unfold sep B
    rw [CliffordAlgebra.lift_ι_apply]
    simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,K]
  have sep_s : sep (SU:C)=Matrix.diagonal ![Real.goldenRatio,Real.goldenConj] := by
    rw [su_val,map_mul,sep_b,sep_a]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal]
  let diagVector : (Fin 2 → ℝ)ˣ := {
    val := ![Real.goldenRatio,Real.goldenConj]
    inv := ![Real.goldenRatio⁻¹,Real.goldenConj⁻¹]
    val_inv := by
      ext i; fin_cases i
      · exact mul_inv_cancel₀ Real.goldenRatio_ne_zero
      · exact mul_inv_cancel₀ Real.goldenConj_ne_zero
    inv_val := by
      ext i; fin_cases i
      · exact inv_mul_cancel₀ Real.goldenRatio_ne_zero
      · exact inv_mul_cancel₀ Real.goldenConj_ne_zero
  }
  let sepU : Cˣ →* (Matrix (Fin 2) (Fin 2) ℝ)ˣ := Units.map sep.toMonoidHom
  let diagU : (Matrix (Fin 2) (Fin 2) ℝ)ˣ :=
    Units.map (Matrix.diagonalRingHom (Fin 2) ℝ).toMonoidHom diagVector
  have sep_s_unit : sepU SU=diagU := Units.ext sep_s
  have sep_s_power (n : ℤ) : sep ((SU^n:Cˣ):C)=Matrix.diagonal ![Real.goldenRatio^n,Real.goldenConj^n] := by
    change (sepU (SU^n)).val=_
    rw [map_zpow,sep_s_unit]
    change (Units.map (Matrix.diagonalRingHom (Fin 2) ℝ).toMonoidHom diagVector ^ n).val=_
    rw [←map_zpow]
    change Matrix.diagonal ((diagVector^n).val)=_
    congr 1
    ext i
    have hv : ∀ j : Fin 2, ((diagVector^n).val j) = ((![(Units.mk0 Real.goldenRatio Real.goldenRatio_ne_zero),(Units.mk0 Real.goldenConj Real.goldenConj_ne_zero)] j)^n).val := by
      intro j
      let ev : (Fin 2 → ℝ) →* ℝ := Pi.evalMonoidHom (fun _ : Fin 2 => ℝ) j
      change ((Units.map ev (diagVector^n)).val)=_
      rw [map_zpow]
      congr 1
      apply Units.ext
      fin_cases j <;> rfl
    rw [hv]
    fin_cases i <;> simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s]
  let detC : Cˣ →* ℝˣ := (Units.map (Matrix.detMonoidHom : (Matrix (Fin 2) (Fin 2) ℝ) →* ℝ)).comp sepU
  have detc_sign : detC (-1)=1 := by
    apply Units.ext
    change Matrix.det (sep (-1:C))=1
    simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,Matrix.det_fin_two]
  have detc_a : detC AU=(-1:ℝˣ) := by
    apply Units.ext
    change Matrix.det (sep A)=(-1:ℝ)
    simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,Matrix.det_fin_two]
  have detc_b : detC BU=1 := by
    apply Units.ext
    change Matrix.det (sep B)=1
    simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,detc_a,Matrix.det_fin_two,Real.goldenRatio_mul_goldenConj]
  have detc_s : detC SU=(-1:ℝˣ) := by simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,detc_a,detc_b,SU]
  have detc_d : detC DU=(-1:ℝˣ) := by simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,detc_a,detc_b,detc_s,DU]
  have detc_even (u : ℤ) : (-1:ℝˣ)^(2*u)=1 := by
    exact (even_two_mul u).neg_one_zpow
  have l_dets (u v w : ℤ) :
    detC (L u v w).1=1 ∧ detC (L u v w).2.1=1 ∧ detC (L u v w).2.2=1 := by
    simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,detc_a,detc_b,detc_s,detc_d,L,map_zpow,detc_even]
  have n_dets (k : Params) :
    detC (L k.u k.v k.w*R k.p k.q).1=(if k.p then -1 else 1) ∧
    detC (L k.u k.v k.w*R k.p k.q).2.1=(if k.q then -1 else 1) := by
    rcases l_dets k.u k.v k.w with ⟨h0,h1,h2⟩
    cases hp : k.p <;> cases hq : k.q <;>
      simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,detc_a,detc_b,detc_s,detc_d,R,g,h,hp,hq,map_mul,h0,h1]
  have value_injective : Function.Injective value := by
    intro x y h
    apply Prod.ext
    · exact Units.ext (congrArg Prod.fst h)
    · apply Prod.ext
      · exact Units.ext (congrArg (fun x : Tri => x.2.1) h)
      · exact Units.ext (congrArg (fun x : Tri => x.2.2) h)
  have same_states {k j : Params} (hn : N k=N j) : k.p=j.p ∧ k.q=j.q := by
    have hu := value_injective hn
    have hd0 := congrArg (fun x : UTri => detC x.1) hu
    have hd1 := congrArg (fun x : UTri => detC x.2.1) hu
    rw [(n_dets k).1,(n_dets j).1] at hd0
    rw [(n_dets k).2,(n_dets j).2] at hd1
    constructor
    · cases hp : k.p <;> cases hj : j.p <;> try rfl
      all_goals simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,detc_a,detc_b,detc_s,detc_d,hp,hj] at hd0
      all_goals have := congrArg Units.val hd0; norm_num at this
    · cases hq : k.q <;> cases hj : j.q <;> try rfl
      all_goals simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,detc_a,detc_b,detc_s,detc_d,hq,hj] at hd1
      all_goals have := congrArg Units.val hd1; norm_num at this
  have sep_sign_power (n : ℤ) : sep (((-1:Cˣ)^n:Cˣ):C)=
    Matrix.diagonal (fun _ : Fin 2 => (-1:ℝ)^n) := by
    let negVec : (Fin 2 → ℝ)ˣ := ⟨fun _ => -1,fun _ => -1,by ext i; norm_num,by ext i; norm_num⟩
    have he : sepU (-1)=Units.map (Matrix.diagonalRingHom (Fin 2) ℝ).toMonoidHom negVec := by
      apply Units.ext
      change sep (-1:C)=Matrix.diagonal (fun _ => -1)
      rw [map_neg,map_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Q_apply,a_sq,b_sq,au_val,bu_val,su_val,au_sq,bu_sq,au_inv,bu_inv,du_val,value_one,l_zero,sep_a,sep_b,sep_s,detc_sign,detc_a,detc_b,detc_s,detc_d,Matrix.diagonal,Matrix.one_apply]
    change (sepU ((-1:Cˣ)^n)).val=_
    rw [map_zpow,he,←map_zpow]
    change Matrix.diagonal ((negVec^n).val)=_
    congr 1
    ext i
    let ev : (Fin 2 → ℝ) →* ℝ := Pi.evalMonoidHom (fun _ : Fin 2 => ℝ) i
    change (Units.map ev (negVec^n)).val=_
    rw [map_zpow,Units.val_zpow_eq_zpow_val]
    rfl
  have coordinate_abs (a b : ℤ) :
    |sep (((-1:Cˣ)^a*SU^(2*b):Cˣ):C) 0 0|=Real.goldenRatio^(2*b) := by
    rw [Units.val_mul,map_mul,sep_sign_power,sep_s_power,Matrix.diagonal_mul_diagonal']
    simp only [Matrix.diagonal_apply_eq,Pi.mul_apply,Matrix.cons_val_zero,abs_mul]
    rw [abs_zpow,abs_neg,abs_one,_root_.one_zpow,one_mul,abs_of_pos (zpow_pos Real.goldenRatio_pos _)]
  have normal_injective : Function.Injective N := by
    intro k j hn
    rcases same_states hn with ⟨hp,hq⟩
    have hl : L k.u k.v k.w=L j.u j.v j.w := by
      have huu := value_injective hn
      change L k.u k.v k.w*R k.p k.q=L j.u j.v j.w*R j.p j.q at huu
      rw [←hp,←hq] at huu
      exact mul_right_cancel huu
    have h0 := congrArg (fun x : UTri => |sep x.1.val 0 0|) hl
    have h1 := congrArg (fun x : UTri => |sep x.2.1.val 0 0|) hl
    have h2 := congrArg (fun x : UTri => |sep x.2.2.val 0 0|) hl
    change |sep (((-1:Cˣ)^k.v*SU^(2*k.u):Cˣ):C) 0 0|=|sep (((-1:Cˣ)^j.v*SU^(2*j.u):Cˣ):C) 0 0| at h0
    change |sep (((-1:Cˣ)^k.w*SU^(2*k.v):Cˣ):C) 0 0|=|sep (((-1:Cˣ)^j.w*SU^(2*j.v):Cˣ):C) 0 0| at h1
    change |sep (((-1:Cˣ)^k.u*SU^(2*k.w):Cˣ):C) 0 0|=|sep (((-1:Cˣ)^j.u*SU^(2*j.w):Cˣ):C) 0 0| at h2
    rw [coordinate_abs,coordinate_abs] at h0 h1 h2
    have hi := zpow_right_injective₀ Real.goldenRatio_pos (ne_of_gt Real.one_lt_goldenRatio)
    have hu : k.u=j.u := by have := hi h0; omega
    have hv : k.v=j.v := by have := hi h1; omega
    have hw : k.w=j.w := by have := hi h2; omega
    cases k; cases j; simp_all
  classical
  have count_cons : ∀ {a b c : State} (P : Quiver.Path a b) (e : b ⟶ c) k,
      pathCounts (P.cons e) k = pathCounts P k + (if k=(b,e.val) then 1 else 0) := by
    intros; simp only [pathCounts,Quiver.Path.addWeight_cons,Pi.add_apply]
  have count_sum : ∀ {a b : State} (P : Quiver.Path a b), ∑ k, pathCounts P k = P.length := by
    intro a b P
    induction P with
    | nil => simp [pathCounts,Quiver.Path.addWeight]
    | @cons b c P e ih =>
      simp only [count_cons,Finset.sum_add_distrib,ih,Quiver.Path.length_cons]
      simp
  have count_balance : ∀ {a b : State} (P : Quiver.Path a b) z,
      divergence (fun k => (pathCounts P k : ℤ)) z =
        (if a=z then 1 else 0) - (if b=z then 1 else 0) := by
    intro a b P z
    induction P with
    | nil => simp [pathCounts,Quiver.Path.addWeight,divergence]
    | @cons b c P e ih =>
      simp only [divergence,count_cons,Nat.cast_add,add_mul,Finset.sum_add_distrib] at *
      rw [ih]
      have hs : (∑ k : Kind, ((if k=(b,e.val) then 1 else 0 : ℕ) : ℤ) *
          ((if k.1=z then 1 else 0) - (if step k.1 k.2=z then 1 else 0))) =
          (if b=z then 1 else 0) - (if c=z then 1 else 0) := by
        simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero,ite_mul,one_mul,zero_mul]
        simp [e.property]
      rw [hs]; ring
  have count_visited : ∀ {a b : State} (P : Quiver.Path a b) k, 0 < pathCounts P k →
      k.1 ∈ P.vertices ∧ step k.1 k.2 ∈ P.vertices := by
    intro a b P
    induction P with
    | nil => simp [pathCounts,Quiver.Path.addWeight]
    | @cons b c P e ih =>
      intro k hk
      rw [count_cons] at hk
      by_cases he : k=(b,e.val)
      · subst k
        exact ⟨(Quiver.Path.mem_vertices_cons _ _).2 (Or.inl P.end_mem_vertices),
          (Quiver.Path.mem_vertices_cons _ _).2 (Or.inr e.property)⟩
      · simp only [he,if_false,add_zero] at hk
        exact ⟨(Quiver.Path.mem_vertices_cons _ _).2 (Or.inl (ih k hk).1),
          (Quiver.Path.mem_vertices_cons _ _).2 (Or.inl (ih k hk).2)⟩
  have div_sub : ∀ f g : Kind → ℤ, ∀ z,
      divergence (fun e => f e-g e) z = divergence f z-divergence g z := by
    intros; simp [divergence,sub_mul,Finset.sum_sub_distrib]
  have out_in : ∀ f : Kind → ℕ, ∀ z,
      divergence (fun e => (f e : ℤ)) z =
        (∑ e : Kind, if e.1=z then (f e : ℤ) else 0) -
        (∑ e : Kind, if step e.1 e.2=z then (f e : ℤ) else 0) := by
    intros; simp [divergence,mul_sub,Finset.sum_sub_distrib,mul_ite]
  have outgoing : ∀ f : Kind → ℕ, ∀ z,
      0 < divergence (fun e => (f e : ℤ)) z ∨
        (divergence (fun e => (f e : ℤ)) z = 0 ∧
          ∃ e, 0 < f e ∧ (e.1=z ∨ step e.1 e.2=z)) →
      ∃ b, 0 < f (z,b) := by
    intro f z hz
    by_contra hn
    push_neg at hn
    have hzero : ∀ e : Kind, (if e.1=z then (f e : ℤ) else 0)=0 := by
      intro e; split_ifs with he
      · have h := hn e.2; rw [←he] at h
        simp only [Prod.eta] at h; omega
      · rfl
    have hout : (∑ e : Kind, if e.1=z then (f e : ℤ) else 0)=0 := by simp [hzero]
    have hin : 0 ≤ (∑ e : Kind, if step e.1 e.2=z then (f e : ℤ) else 0) := by
      exact Finset.sum_nonneg (by intro e _; split_ifs <;> positivity)
    rw [out_in,hout] at hz
    rcases hz with hz | ⟨hz,e,he,hend⟩
    · omega
    · rcases hend with hsrc | hdst
      · have h := hn e.2; rw [←hsrc] at h
        simp only [Prod.eta] at h; omega
      · have hpos : 0 < (∑ e : Kind, if step e.1 e.2=z then (f e : ℤ) else 0) := by
          apply (Finset.sum_pos_iff_of_nonneg (by intro e _; split_ifs <;> positivity)).2
          exact ⟨e,Finset.mem_univ _,by simp [hdst]; exact_mod_cast he⟩
        omega
  have euler (m : Kind → ℕ) (s t : State)
      (hb : ∀ z, divergence (fun e => (m e : ℤ)) z =
        (if s=z then 1 else 0) - (if t=z then 1 else 0))
      (hc : ∀ e, 0 < m e →
        Nonempty (@Quiver.Path (Quiver.Symmetrify (PositiveSupport (fun e => (m e : ℤ)))) _ s e.1) ∧
        Nonempty (@Quiver.Path (Quiver.Symmetrify (PositiveSupport (fun e => (m e : ℤ)))) _ s (step e.1 e.2))) :
      ∃ P : Quiver.Path s t, ∀ e, pathCounts P e = m e := by
    have maximal : ∀ f : Kind → ℕ, ∀ a : State,
        ∃ b, ∃ P : Quiver.Path a b, (∀ k, pathCounts P k ≤ f k) ∧
          ∀ c (Q : Quiver.Path a c), (∀ k, pathCounts Q k ≤ f k) → Q.length ≤ P.length := by
      intro f a
      let M := ∑ k, f k
      let attainable := fun n => ∃ b, ∃ P : Quiver.Path a b,
        (∀ k, pathCounts P k ≤ f k) ∧ P.length=n
      have hzero : attainable 0 := ⟨a,.nil,by simp [pathCounts,Quiver.Path.addWeight],rfl⟩
      have hmax := Nat.findGreatest_spec (Nat.zero_le M) hzero
      rcases hmax with ⟨b,P,hP,hlen⟩
      refine ⟨b,P,hP,?_⟩
      intro c Q hQ
      have hbound : Q.length ≤ M := by
        rw [←count_sum Q]; exact Finset.sum_le_sum (by intro k _; exact hQ k)
      have hle := Nat.le_findGreatest hbound (show attainable Q.length from ⟨c,Q,hQ,rfl⟩)
      simpa [hlen] using hle
    have endpoint : ∀ (f : Kind → ℕ) (a b c : State) (P : Quiver.Path a c),
        (∀ z, divergence (fun e => (f e : ℤ)) z =
          (if a=z then 1 else 0) - (if b=z then 1 else 0)) →
        (∀ e, pathCounts P e ≤ f e) →
        (∀ d (Q : Quiver.Path a d), (∀ e, pathCounts Q e ≤ f e) → Q.length ≤ P.length) → c=b := by
      intro f a b c P hbal hP hmax
      by_contra hcb
      let r := fun e => f e-pathCounts P e
      have hr : ∀ e, (r e : ℤ)=(f e : ℤ)-(pathCounts P e : ℤ) :=
        fun e => Nat.cast_sub (hP e)
      have hdiv : divergence (fun e => (r e : ℤ)) c = 1 := by
        simp_rw [hr]; rw [div_sub,hbal,count_balance]; simp [hcb,Ne.symm hcb]
      obtain ⟨b',hb'⟩ := outgoing r c (Or.inl (by omega))
      let e : c ⟶ step c b' := ⟨b',rfl⟩
      have hnew : ∀ k, pathCounts (P.cons e) k ≤ f k := by
        intro k; rw [count_cons]
        by_cases hk : k=(c,b')
        · subst k; dsimp [e]; simp only [ite_true]; dsimp [r] at hb'; omega
        · simpa [e,hk] using hP k
      have hh := hmax _ (P.cons e) hnew
      simp only [Quiver.Path.length_cons] at hh
      omega
    obtain ⟨z,P,hP,hmax⟩ := maximal m s
    have hzt := endpoint m s t z P hb hP hmax
    subst z
    let r := fun e => m e-pathCounts P e
    have hr : ∀ e, (r e : ℤ)=(m e : ℤ)-(pathCounts P e : ℤ) := fun e => Nat.cast_sub (hP e)
    have hrbal : ∀ z, divergence (fun e => (r e : ℤ)) z=0 := by
      intro z; simp_rw [hr]; rw [div_sub,hb,count_balance]; ring
    by_cases hall : ∀ e, pathCounts P e=m e
    · exact ⟨P,hall⟩
    push_neg at hall
    obtain ⟨k,hk⟩ := hall
    have hkr : 0 < r k := by dsimp [r]; have := hP k; omega
    let S : Set State := {v | v ∈ P.vertices}
    have incident : ∃ v, v ∈ S ∧ ∃ e, 0 < r e ∧ (e.1=v ∨ step e.1 e.2=v) := by
      by_cases hks : k.1 ∈ S
      · exact ⟨k.1,hks,k,hkr,Or.inl rfl⟩
      have hkm : 0 < m k := by dsimp [r] at hkr; omega
      obtain ⟨H⟩ := (hc k hkm).1
      let SS : Set (Quiver.Symmetrify (PositiveSupport (fun e => (m e : ℤ)))) := S
      have hs : s ∈ SS := P.start_mem_vertices
      obtain ⟨a,ha,b,hb',e,_,_,_⟩ :=
        Quiver.Path.exists_mem_notMem_hom_path_path_of_notMem_mem H SS hs hks
      change ({l : Bool // step a l=b ∧ 0 < (m (a,l):ℤ)}) ⊕
        {l : Bool // step b l=a ∧ 0 < (m (b,l):ℤ)} at e
      cases e with
      | inl e =>
        let j : Kind := (a,e.val)
        have hj0 : pathCounts P j=0 := by
          by_contra hj
          have hv := (count_visited P j (by omega)).2
          have ht : step j.1 j.2=b := e.property.1
          rw [ht] at hv; exact hb' hv
        have hjr : 0 < r j := by
          dsimp [r]; rw [hj0]; simp only [Nat.sub_zero]; exact_mod_cast e.property.2
        exact ⟨a,ha,j,hjr,Or.inl rfl⟩
      | inr e =>
        let j : Kind := (b,e.val)
        have hj0 : pathCounts P j=0 := by
          by_contra hj
          exact hb' (count_visited P j (by omega)).1
        have hjr : 0 < r j := by
          dsimp [r]; rw [hj0]; simp only [Nat.sub_zero]; exact_mod_cast e.property.2
        exact ⟨a,ha,j,hjr,Or.inr e.property.1⟩
    obtain ⟨v,hv,e,he,hev⟩ := incident
    obtain ⟨b',hb'⟩ := outgoing r v (Or.inr ⟨hrbal v,e,he,hev⟩)
    obtain ⟨z,Q,hQ,hQmax⟩ := maximal r v
    have hzv := endpoint r v v z Q (by intro z; rw [hrbal]; simp) hQ hQmax
    subst z
    have hQpos : 0 < Q.length := by
      let f : v ⟶ step v b' := ⟨b',rfl⟩
      have hf : ∀ k, pathCounts f.toPath k ≤ r k := by
        intro k
        by_cases hk : k=(v,b')
        · subst k
          simpa [pathCounts,Quiver.Hom.toPath,Quiver.Path.addWeight,f] using
            (Nat.succ_le_of_lt hb')
        · simp [pathCounts,Quiver.Hom.toPath,Quiver.Path.addWeight,f,hk]
      have hlen := hQmax _ f.toPath hf
      rw [Quiver.Path.length_toPath] at hlen
      omega
    obtain ⟨P₁,P₂,hcut⟩ := P.exists_eq_comp_of_mem_vertices hv
    let T := (P₁.comp Q).comp P₂
    have hT : ∀ e, pathCounts T e ≤ m e := by
      intro e
      have hadd : pathCounts T e = pathCounts P e + pathCounts Q e := by
        simp only [T,pathCounts,Quiver.Path.addWeight_comp,Pi.add_apply,hcut]
        omega
      rw [hadd]; have := hQ e; have := hP e; dsimp [r] at *; omega
    have hlen := hmax _ T hT
    simp only [T,Quiver.Path.length_comp,hcut] at hlen
    omega
  let leafWord := fun t : Source =>
    (FreeMagma.toFreeSemigroup t).head :: (FreeMagma.toFreeSemigroup t).tail
  let wordEval := fun l : List Bool => (l.map letter).prod
  let valueHom : UTri →* Tri :=
    { toFun := value, map_one' := rfl, map_mul' := value_mul }
  have w3_word (t : Source) : W3 t=value (wordEval (leafWord t)) := by
    have hw : WHom = (valueHom.toMulHom.comp (FreeSemigroup.lift letter)).comp
        FreeMagma.toFreeSemigroup := by
      apply FreeMagma.hom_ext
      funext b
      change W3 (.of b)=value (letter b)
      cases b
      · simpa [letter,h,value,du_val,au_val,bu_val,su_val] using w3_leaf.2
      · simpa [letter,g,value,au_val,bu_val,su_val] using w3_leaf.1
    have ht := DFunLike.congr_fun hw t
    change W3 t=value (FreeSemigroup.lift letter (FreeMagma.toFreeSemigroup t)) at ht
    rw [ht]
    congr 1
    rcases hfs : FreeMagma.toFreeSemigroup t with ⟨b,bs⟩
    simp [wordEval,leafWord,hfs,FreeSemigroup.lift_mk_eq_foldl,
      List.prod_eq_foldl,List.foldl_map]
  have leaf_mul (s t : Source) : leafWord (.mul s t)=leafWord s++leafWord t := by
    simp [leafWord,map_mul,List.cons_append]
  have source_counts (t : Source) : composition t=((leafWord t).count true,(leafWord t).count false) := by
    let f : Source →ₙ* Multiplicative (ℕ × ℕ) :=
      {toFun := fun t => Multiplicative.ofAdd (composition t), map_mul' := fun _ _ => rfl}
    let j : Source →ₙ* Multiplicative (ℕ × ℕ) :=
      {toFun := fun t => Multiplicative.ofAdd ((leafWord t).count true,(leafWord t).count false)
       map_mul' := by
         intro s t
         change Multiplicative.ofAdd ((leafWord (.mul s t)).count true,(leafWord (.mul s t)).count false)=
           Multiplicative.ofAdd (((leafWord s).count true,(leafWord s).count false)+
             ((leafWord t).count true,(leafWord t).count false))
         rw [leaf_mul]; simp only [List.count_append]; rfl}
    have hj : f=j := by apply FreeMagma.hom_ext; funext b; cases b <;> rfl
    exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hj t)
  have source_of_word (l : List Bool) (hl : l ≠ []) :
      ∃ t : Source, leafWord t=l := by
    cases l with
    | nil => contradiction
    | cons b bs =>
      let t := bs.foldl (fun t b => FreeMagma.mul t (.of b)) (.of b)
      refine ⟨t,?_⟩
      have hh := List.foldl_hom leafWord (l:=bs) (init:=FreeMagma.of b)
        (g₁:=fun t b => FreeMagma.mul t (.of b)) (g₂:=fun l b => l++[b])
        (by intro s b; change leafWord s++[b]=leafWord (.mul s (.of b)); rw [leaf_mul]; rfl)
      rw [←hh,List.foldl_append_eq_append]
      change [b]++(bs.flatMap fun b => [b])=b::bs
      simp
  have word_counts : ∀ {a b : State} (P : Quiver.Path a b) l,
      (pathWord P).count l=∑ z : State, pathCounts P (z,l) := by
    intro a b P l
    induction P with
    | nil => simp [pathWord,Quiver.Path.weight,pathCounts,Quiver.Path.addWeight]
    | @cons b c P e ih =>
      simp only [pathWord,Quiver.Path.weight_cons,FreeMonoid.toList_mul,FreeMonoid.toList_of,
        List.count_append,pathCounts,Quiver.Path.addWeight_cons,Pi.add_apply,
        Finset.sum_add_distrib] at *
      rw [ih]
      by_cases h : l=e.val
      · subst l; simp
      · simp [h,ne_comm]
  let charges := fun {a b : State} (P : Quiver.Path a b) =>
    P.addWeight (fun {i j : State} (e : i ⟶ j) => delta i e.val)
  have normal_path : ∀ {b : State} (P : Quiver.Path (false,false) b),
      wordEval (pathWord P) = L (charges P).1 (charges P).2.1 (charges P).2.2 * R b.1 b.2 := by
    intro b P
    induction P with
    | nil => simp [wordEval,pathWord,Quiver.Path.weight_nil,charges,Quiver.Path.addWeight_nil,L,R,FreeMonoid.toList_one] <;> rfl
    | @cons b c P e ih =>
      have he := e.property
      have hword : wordEval (pathWord (P.cons e))=wordEval (pathWord P)*letter e.val := by
        simp [wordEval,pathWord,Quiver.Path.weight_cons,FreeMonoid.toList_mul,FreeMonoid.toList_of]
      rw [hword,ih,mul_assoc,right_table]
      rw [←mul_assoc,l_add]
      simp only [charges,Quiver.Path.addWeight_cons,Prod.fst_add,Prod.snd_add,he]
  have charges_counts : ∀ {a b : State} (P : Quiver.Path a b),
      charges P =
        ((pathCounts P ((false,true),true):ℤ)-pathCounts P ((true,true),true),
         (pathCounts P ((false,true),true):ℤ)-pathCounts P ((true,true),true)+
          pathCounts P ((false,true),false)-pathCounts P ((true,true),false),
         (pathCounts P ((true,false),true):ℤ)-pathCounts P ((false,true),true)) := by
    intro a b P
    induction P with
    | nil => simp [charges,pathCounts,Quiver.Path.addWeight] <;> rfl
    | @cons b c P e ih =>
      rw [show charges (P.cons e)=charges P+delta b e.val by
        simp only [charges,Quiver.Path.addWeight_cons],ih]
      simp only [count_cons,Nat.cast_add]
      rcases b with ⟨p,q⟩
      cases p <;> cases q <;> cases he : e.val <;>
        simp [delta,he,Prod.mk.injEq] <;> omega
  have read_word (l : List Bool) :
      ∃ b, ∃ P : Quiver.Path (false,false) b, pathWord P=l := by
    have build : ∀ l : List Bool, ∀ a : State, ∃ b, ∃ P : Quiver.Path a b, pathWord P=l := by
      intro l
      induction l with
      | nil => intro a; exact ⟨a,.nil,by simp [pathWord,Quiver.Path.weight_nil]⟩
      | cons l ls ih =>
        intro a
        obtain ⟨b,P,hP⟩ := ih (step a l)
        let e : a ⟶ step a l := ⟨l,rfl⟩
        refine ⟨b,e.toPath.comp P,?_⟩
        simp only [pathWord] at hP
        simp [pathWord,Quiver.Path.weight_comp,Quiver.Hom.toPath,Quiver.Path.weight,e,hP,
          FreeMonoid.toList_mul,FreeMonoid.toList_of]
    exact build l (false,false)
  have support_from_path (f : Kind → ℤ) {a b : State} (P : Quiver.Path a b)
      (hf : ∀ e, 0 < pathCounts P e → 0 < f e) :
      ∀ v, v ∈ P.vertices →
        Nonempty (@Quiver.Path (Quiver.Symmetrify (PositiveSupport f)) _ a v) := by
    induction P with
    | nil => intro v hv; simp only [Quiver.Path.vertices_nil,List.mem_singleton] at hv; subst v; exact ⟨.nil⟩
    | @cons b c P e ih =>
      have hf' : ∀ k, 0 < pathCounts P k → 0 < f k := by
        intro k hk; apply hf k; rw [count_cons]; omega
      have hreach := ih hf'
      intro v hv
      rcases (Quiver.Path.mem_vertices_cons _ _).1 hv with hv | hv
      · exact hreach v hv
      · subst v
        obtain ⟨H⟩ := hreach b P.end_mem_vertices
        have hepos : 0 < f (b,e.val) := by
          apply hf; rw [count_cons]; simp
        let d : @Quiver.Hom (PositiveSupport f) _ b c := ⟨e.val,e.property,hepos⟩
        exact ⟨H.cons (Sum.inl d)⟩
  constructor
  · rintro ⟨t,hw,hc⟩
    obtain ⟨z,P,hword⟩ := read_word (leafWord t)
    let k : Params := ⟨(charges P).1,(charges P).2.1,(charges P).2.2,z.1,z.2⟩
    have hk : k=⟨u,v,w,p,q⟩ := by
      apply normal_injective
      change value (L (charges P).1 (charges P).2.1 (charges P).2.2 * R z.1 z.2)=Omega u v w p q
      rw [←normal_path P,hword,←w3_word]
      exact hw
    have hz : z=(p,q) := Prod.ext (congrArg Params.p hk) (congrArg Params.q hk)
    have hu : (charges P).1=u := congrArg Params.u hk
    have hv : (charges P).2.1=v := congrArg Params.v hk
    have hw : (charges P).2.2=w := congrArg Params.w hk
    subst z
    let f : Kind → ℤ := fun e => (pathCounts P e : ℤ)
    let X := f ((false,true),true)
    let Y := f ((false,true),false)
    have hch : (u,v,w)=
        ((pathCounts P ((false,true),true):ℤ)-pathCounts P ((true,true),true),
         (pathCounts P ((false,true),true):ℤ)-pathCounts P ((true,true),true)+
          pathCounts P ((false,true),false)-pathCounts P ((true,true),false),
         (pathCounts P ((true,false),true):ℤ)-pathCounts P ((false,true),true)) := by
      calc
        (u,v,w)=charges P := Prod.ext hu.symm (Prod.ext hv.symm hw.symm)
        _ = _ := charges_counts P
    have hbal10 := count_balance P (true,false)
    have hbal01 := count_balance P (false,true)
    have hbal11 := count_balance P (true,true)
    have hchu := congrArg Prod.fst hch
    have hchv := congrArg (fun x : ℤ × ℤ × ℤ => x.2.1) hch
    have hchw := congrArg (fun x : ℤ × ℤ × ℤ => x.2.2) hch
    dsimp only at hchu hchv hchw
    have hcounts : ∀ e, f e=edgeCounts u v w X Y p q e := by
      intro e
      rcases e with ⟨⟨a,b⟩,l⟩
      cases p <;> cases q <;> cases a <;> cases b <;> cases l <;>
        simp [divergence,Fintype.sum_prod_type,Fintype.univ_bool,step,f,X,Y,edgeCounts]
          at hbal10 hbal01 hbal11 hchu hchv hchw ⊢ <;> omega
    have hcasts : ∀ e, (pathCounts P e : ℤ)=edgeCounts u v w X Y p q e := hcounts
    have hcomp : ((pathWord P).count true,(pathWord P).count false)=(ac,bc) := by
      rw [hword,←source_counts]; exact hc
    have hac : (ac:ℤ)=4*X+2*w-2*u+p.toNat := by
      have hh := congrArg (fun x : ℕ × ℕ => (x.1:ℤ)) hcomp
      change ((pathWord P).count true : ℤ)=(ac:ℤ) at hh
      rw [word_counts] at hh
      simp [Fintype.sum_prod_type,Fintype.univ_bool] at hh
      simp_rw [hcasts] at hh
      cases p <;> cases q <;> simp [edgeCounts] at hh ⊢ <;> omega
    have hbc : (bc:ℤ)=4*Y+2*u-2*v+q.toNat := by
      have hh := congrArg (fun x : ℕ × ℕ => (x.2:ℤ)) hcomp
      change ((pathWord P).count false : ℤ)=(bc:ℤ) at hh
      rw [word_counts] at hh
      simp [Fintype.sum_prod_type,Fintype.univ_bool] at hh
      simp_rw [hcasts] at hh
      cases p <;> cases q <;> simp [edgeCounts] at hh ⊢ <;> omega
    refine ⟨X,Y,?_,?_,?_,?_⟩
    · have hh : (ac:ℚ)=4*(X:ℚ)+2*(w:ℚ)-2*(u:ℚ)+p.toNat := by exact_mod_cast hac
      linarith
    · have hh : (bc:ℚ)=4*(Y:ℚ)+2*(u:ℚ)-2*(v:ℚ)+q.toNat := by exact_mod_cast hbc
      linarith
    · intro e; rw [←hcounts]; exact Int.natCast_nonneg _
    · intro e he
      have hpos : 0 < pathCounts P e := by rw [←hcasts] at he; exact_mod_cast he
      have hvis := count_visited P e hpos
      have hreach := support_from_path (edgeCounts u v w X Y p q) P
        (by intro e he; rw [←hcasts]; exact_mod_cast he)
      exact ⟨hreach _ hvis.1,hreach _ hvis.2⟩
  · rintro ⟨X,Y,hX,hY,hnonneg,hconn⟩
    have hXi : (ac:ℤ)=4*X+2*w-2*u+p.toNat := by
      have hh : (ac:ℚ)=4*(X:ℚ)+2*(w:ℚ)-2*(u:ℚ)+p.toNat := by linarith
      exact_mod_cast hh
    have hYi : (bc:ℤ)=4*Y+2*u-2*v+q.toNat := by
      have hh : (bc:ℚ)=4*(Y:ℚ)+2*(u:ℚ)-2*(v:ℚ)+q.toNat := by linarith
      exact_mod_cast hh
    let f := edgeCounts u v w X Y p q
    let m := fun e => (f e).toNat
    have hm : ∀ e, (m e : ℤ)=f e := fun e => Int.toNat_of_nonneg (hnonneg e)
    have hmfun : (fun e => (m e : ℤ))=f := funext hm
    have hb : ∀ z, divergence (fun e => (m e : ℤ)) z =
        (if (false,false)=z then 1 else 0) - (if (p,q)=z then 1 else 0) := by
      intro ⟨a,b⟩; rw [hmfun]
      cases a <;> cases b <;> cases p <;> cases q <;>
        simp [divergence,f,edgeCounts,Fintype.sum_prod_type,Fintype.univ_bool,step] <;> ring
    have hc : ∀ e, 0 < m e →
        Nonempty (@Quiver.Path (Quiver.Symmetrify (PositiveSupport (fun e => (m e : ℤ)))) _ (false,false) e.1) ∧
        Nonempty (@Quiver.Path (Quiver.Symmetrify (PositiveSupport (fun e => (m e : ℤ)))) _ (false,false) (step e.1 e.2)) := by
      intro e he; rw [hmfun]
      have hh : (0:ℤ)<(m e:ℤ) := by exact_mod_cast he
      rw [hm] at hh
      exact hconn e hh
    obtain ⟨P,hP⟩ := euler m (false,false) (p,q) hb hc
    have hcharges : charges P=(u,v,w) := by
      rw [charges_counts]
      simp only [hP,hm]
      simp [f,edgeCounts]
      congr 1 <;> ring
    have hcounts : ((pathWord P).count true,(pathWord P).count false)=(ac,bc) := by
      apply Prod.ext
      · change (pathWord P).count true=ac
        rw [word_counts]
        apply Nat.cast_injective (R:=ℤ)
        simp [Fintype.sum_prod_type,Fintype.univ_bool,hP,hm,f,edgeCounts]
        cases p <;> cases q <;> simp at hXi ⊢ <;> omega
      · change (pathWord P).count false=bc
        rw [word_counts]
        apply Nat.cast_injective (R:=ℤ)
        simp [Fintype.sum_prod_type,Fintype.univ_bool,hP,hm,f,edgeCounts]
        cases p <;> cases q <;> simp at hYi ⊢ <;> omega
    have hl : pathWord P ≠ [] := by
      intro hh; rw [hh] at hcounts
      simp only [List.count_nil,Prod.mk.injEq] at hcounts
      omega
    obtain ⟨t,ht⟩ := source_of_word (pathWord P) hl
    refine ⟨t,?_,?_⟩
    · rw [w3_word,ht,normal_path,hcharges]
      rfl
    · rw [source_counts,ht]; exact hcounts


#print axioms result
end D5.S3.Arith.FibonacciAtomic.FixedHistoryComposition

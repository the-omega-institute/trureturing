/- GID: D5/S3/Quantum/Algebra/BalancedStarRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/BalancedStarRigidity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Both orientations of the balanced three-dimensional star have exact finite zero-probe rigidity at every real residual. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Tactic

noncomputable section
open Matrix Complex
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace D5.S3.Quantum.Algebra.BalancedStarRigidity

abbrev A := Matrix (Fin 3) (Fin 3) ℂ
abbrev Vec := Fin 3 → ℂ
def P : A := !![1,0,0; 0,1,0; 0,0,0]
def c : A := !![1,0,0; 0,2,0; 0,0,0]
def t : A := !![0,0,1; 0,0,(Real.sqrt 2 : ℂ); 1,(Real.sqrt 2 : ℂ),0]
def J (a b : A) : A := (1/2 : ℂ) • (a*b+b*a)
def K (σ : ℝ) (a b : A) : A := ((σ : ℂ)*I/2) • (a*b-b*a)
def s (ρ : ℝ) : A := (ρ : ℂ) • !![1,0,0; 0,-2,0; 0,0,0]
def g (σ ρ : ℝ) : A := K σ c t + s ρ
def h (σ : ℝ) (x : A) : A := K σ c x
def r (x : A) : A := J c x
def k : A := J c t
def Rp (σ : ℝ) (x : A) : A := x + (h σ x-k)
def Rm (σ : ℝ) (x : A) : A := x - (h σ x-k)
def Sp (σ ρ : ℝ) (x : A) : A := t + (r x+g σ ρ)
def Sm (σ ρ : ℝ) (x : A) : A := t - (r x+g σ ρ)
def L (σ ρ : ℝ) (x : A) : A :=
  (-2 : ℂ) • J x (h σ x-k) + (-2 : ℂ) • J t (r x+g σ ρ)
def CornerSA (x : A) : Prop := IsSelfAdjoint x ∧ P*x*P=x
def read (φ : A →ₚ[ℂ] ℂ) (a : A) : ℝ := (φ a).re
def B (φ : A →ₚ[ℂ] ℂ) (a b : A) : ℝ :=
  read φ (a*a)*read φ (b*b)-read φ (J a b)^2
def P2 (σ ρ : ℝ) (φ : A →ₚ[ℂ] ℂ) : Prop := read φ (g σ ρ)^2 ≤ B φ c t
def PB (σ ρ : ℝ) (x : A) (φ : A →ₚ[ℂ] ℂ) : Prop :=
  |read φ (L σ ρ x)| ≤ Real.sqrt (B φ (Rp σ x) (Sp σ ρ x)) +
    Real.sqrt (B φ (Rm σ x) (Sm σ ρ x))
def AllBudgets (σ ρ : ℝ) : Prop :=
  (∀ φ : A →ₚ[ℂ] ℂ, P2 σ ρ φ) ∧
    ∀ x : A, CornerSA x → ∀ φ : A →ₚ[ℂ] ℂ, PB σ ρ x φ
def ZeroBudget (σ ρ : ℝ) : Prop := ∀ φ : A →ₚ[ℂ] ℂ, PB σ ρ 0 φ

def u : Vec := ![2*(Real.sqrt 2 : ℂ)/3, -1/3, 0]
def e : Vec := ![1/3, 2*(Real.sqrt 2 : ℂ)/3, 0]
def f : Vec := ![0,0,1]
def theta (ρ : ℝ) : ℝ := 8/3*ρ
def dd (ρ : ℝ) : ℝ := (2+12*ρ^2)/9
def ee (ρ : ℝ) : ℝ := (2+4*ρ^2)/9
def amp (ρ : ℝ) : ℝ := 3*Real.sqrt (dd ρ+theta ρ^2*ee ρ)
def lam (ρ : ℝ) : ℝ := Real.sqrt 2*(1+64*ρ^2/9)
def bigM (ρ : ℝ) : ℝ := 3*(Real.sqrt 3+3/2+2*|ρ|)*(1+theta ρ^2)
def delta (ρ : ℝ) : ℝ := lam ρ-amp ρ
def epsilon (ρ : ℝ) : ℝ := delta ρ/(2*bigM ρ)
def eta (σ ρ : ℝ) : Vec := (I*(σ : ℂ)) • e + (theta ρ : ℂ) • f
def xi (σ ρ q : ℝ) : Vec := u+(q : ℂ) • eta σ ρ
def vectorLinear (v : Vec) : A →ₗ[ℂ] ℂ where
  toFun a := star v ⬝ᵥ (a *ᵥ v)
  map_add' a b := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' z a := by simp [Matrix.smul_mulVec, dotProduct_smul]
def vectorPhi (v : Vec) : A →ₚ[ℂ] ℂ where
  toLinearMap := vectorLinear v
  monotone' := by
    intro a b hab
    apply sub_nonneg.mp
    simpa [vectorLinear, Matrix.sub_mulVec, dotProduct_sub] using
      (Matrix.le_iff.mp hab).dotProduct_mulVec_nonneg v

private theorem vectorPhi_apply (v : Vec) (a : A) :
    vectorPhi v a = star v ⬝ᵥ (a *ᵥ v) := rfl

private theorem J_sa {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (J a b) := by
  change star (J a b) = J a b
  simp [J, star_smul, star_add, star_mul, ha.star_eq, hb.star_eq, add_comm]

private theorem K_sa (σ : ℝ) {a b : A} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) : IsSelfAdjoint (K σ a b) := by
  change star (K σ a b) = K σ a b
  simp only [K, star_smul, star_sub, star_mul, ha.star_eq, hb.star_eq]
  have hc : star (((σ : ℂ)*I/2)) = -((σ : ℂ)*I/2) := by
    simp
    ring
  rw [hc]
  module

private theorem ct_sa : IsSelfAdjoint c ∧ IsSelfAdjoint t := by
  constructor <;> change _ᴴ = _ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [c,t,Matrix.conjTranspose_apply]

private theorem s_sa (ρ : ℝ) : IsSelfAdjoint (s ρ) := by
  change (s ρ)ᴴ = s ρ
  ext i j; fin_cases i <;> fin_cases j <;> simp [s,Matrix.conjTranspose_apply]

private theorem labels_sa (σ ρ : ℝ) {x : A} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (g σ ρ) ∧ IsSelfAdjoint (Rp σ x) ∧ IsSelfAdjoint (Rm σ x) ∧
    IsSelfAdjoint (Sp σ ρ x) ∧ IsSelfAdjoint (Sm σ ρ x) ∧ IsSelfAdjoint (L σ ρ x) := by
  have hc := ct_sa.1
  have ht := ct_sa.2
  have hg : IsSelfAdjoint (g σ ρ) := (K_sa σ hc ht).add (s_sa ρ)
  have hh : IsSelfAdjoint (h σ x-k) := (K_sa σ hc hx).sub (J_sa hc ht)
  have hr : IsSelfAdjoint (r x+g σ ρ) := (J_sa hc hx).add hg
  exact ⟨hg, hx.add hh, hx.sub hh, ht.add hr, ht.sub hr,
    ((show IsSelfAdjoint (-2 : ℂ) by norm_num [IsSelfAdjoint]).smul (J_sa hx hh)).add
      ((show IsSelfAdjoint (-2 : ℂ) by norm_num [IsSelfAdjoint]).smul (J_sa ht hr))⟩

private theorem gram_commutator (σ : ℝ) (hs : σ=1 ∨ σ= -1)
    (φ : A →ₚ[ℂ] ℂ) {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    read φ (K σ a b)^2 ≤ B φ a b := by
  have hsymmetric : φ (b*a)=star (φ (a*b)) := by
    rw [← map_star φ, star_mul, ha.star_eq, hb.star_eq]
  have hj : read φ (J a b)=(φ (a*b)).re := by
    simp [read,J,map_smul,map_add,smul_eq_mul,hsymmetric,Complex.mul_re]
    <;> ring
  have hk : read φ (K σ a b)= -σ*(φ (a*b)).im := by
    simp [read,K,map_smul,map_sub,smul_eq_mul,hsymmetric,Complex.mul_re,
      Complex.mul_im,div_eq_mul_inv]
    <;> ring
  have hcs := PositiveLinearMap.norm_map_star_mul_sq_le φ a b
  have hna := φ.map_nonneg (star_mul_self_nonneg a)
  have hnb := φ.map_nonneg (star_mul_self_nonneg b)
  rw [ha.star_eq] at hna hcs
  rw [hb.star_eq] at hnb hcs
  have hnare : ‖φ (a*a)‖=(φ (a*a)).re := by
    exact congrArg Complex.re (Complex.norm_of_nonneg' hna)
  have hnbre : ‖φ (b*b)‖=(φ (b*b)).re := by
    exact congrArg Complex.re (Complex.norm_of_nonneg' hnb)
  rw [hnare,hnbre,Complex.sq_norm,Complex.normSq_apply] at hcs
  rw [B,hj,hk]
  rcases hs with rfl | rfl <;> dsimp [read] <;> nlinarith

private theorem gram_nonneg (φ : A →ₚ[ℂ] ℂ) {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) : 0 ≤ B φ a b :=
  (sq_nonneg _).trans (gram_commutator 1 (Or.inl rfl) φ ha hb)

private theorem pb_identity (σ : ℝ) (hs : σ=1 ∨ σ= -1) (x : A) :
    K σ (Rp σ x) (Sp σ 0 x)-K σ (Rm σ x) (Sm σ 0 x)=L σ 0 x := by
  rcases hs with rfl | rfl
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals simp [K,Rp,Rm,Sp,Sm,L,h,r,k,g,s,J,c,t,Matrix.mul_apply,
    Fin.sum_univ_succ,smul_eq_mul,Matrix.smul_apply,sub_eq_add_neg,
    Matrix.vecMul,Matrix.mulVec,dotProduct]
  all_goals ring_nf
  all_goals simp [Complex.I_sq] <;> ring

private theorem zero_forward (σ : ℝ) (hs : σ=1 ∨ σ= -1) : AllBudgets σ 0 := by
  constructor
  · intro φ
    simpa [P2,g,s] using gram_commutator σ hs φ ct_sa.1 ct_sa.2
  · intro x hx φ
    obtain ⟨_,hrp,hrm,hsp,hsm,_⟩ := labels_sa σ 0 hx.1
    have hp := Real.abs_le_sqrt (gram_commutator σ hs φ hrp hsp)
    have hm := Real.abs_le_sqrt (gram_commutator σ hs φ hrm hsm)
    have hid := congrArg (fun a => read φ a) (pb_identity σ hs x)
    have hidread : read φ (K σ (Rp σ x) (Sp σ 0 x)) -
        read φ (K σ (Rm σ x) (Sm σ 0 x)) = read φ (L σ 0 x) := by
      simpa only [read,map_sub,Complex.sub_re] using hid
    unfold PB
    rw [← hidread]
    apply le_trans ?_ (add_le_add hp hm)
    simpa only [Real.norm_eq_abs] using
      norm_sub_le (read φ (K σ (Rp σ x) (Sp σ 0 x)))
        (read φ (K σ (Rm σ x) (Sm σ 0 x)))

private def quartic (ρ : ℝ) : ℝ := (164096*ρ^4+69732*ρ^2+6561)/1296
private def cubic (ρ : ℝ) : ℝ :=
  Real.sqrt 2*(24576*ρ^4+24192*ρ^2+2916)/1296
private def base (ρ : ℝ) : ℝ := (9216*ρ^4+8496*ρ^2+648)/1296

private theorem scalar_constants (ρ : ℝ) :
    amp ρ^2=4*base ρ ∧
    lam ρ^2-amp ρ^2=20/9*ρ^2+5888/81*ρ^4 ∧
    0 ≤ amp ρ ∧ 0 < lam ρ ∧ 0 < bigM ρ ∧ 4*quartic ρ ≤ bigM ρ^2 := by
  have hrad : 0 ≤ dd ρ+theta ρ^2*ee ρ := by unfold dd ee; positivity
  have ha : amp ρ^2=4*base ρ := by
    rw [amp,mul_pow,Real.sq_sqrt hrad]
    unfold dd ee theta base
    ring
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hl : lam ρ^2-amp ρ^2=20/9*ρ^2+5888/81*ρ^4 := by
    rw [lam,mul_pow,hs2,ha]
    unfold base
    ring
  have hapos : 0 ≤ amp ρ := by unfold amp; positivity
  have hlpos : 0 < lam ρ := by unfold lam; positivity
  have hmpos : 0 < bigM ρ := by unfold bigM; positivity
  have hs3 : 3/2 ≤ Real.sqrt 3 := by
    have ht := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg (3:ℝ)]
  have hlo : 9+64*ρ^2 ≤ bigM ρ := by
    have hh : 0 ≤ Real.sqrt 3-3/2+2*|ρ| := by linarith [abs_nonneg ρ]
    have hp := mul_nonneg hh (show 0 ≤ 1+(8/3*ρ)^2 by positivity)
    unfold bigM theta
    nlinarith
  have hsq : (9+64*ρ^2)^2 ≤ bigM ρ^2 :=
    (sq_le_sq₀ (by positivity) hmpos.le).mpr hlo
  refine ⟨ha,hl,hapos,hlpos,hmpos,?_⟩
  unfold quartic
  nlinarith [sq_nonneg ρ, sq_nonneg (ρ^2)]

private theorem delta_pos (ρ : ℝ) (hρ : ρ≠0) : 0 < delta ρ := by
  obtain ⟨_,hd,ha,hl,_,_⟩ := scalar_constants ρ
  have hρ2 := sq_pos_of_ne_zero hρ
  unfold delta
  nlinarith [sq_nonneg (ρ^2)]

def FrameOrthonormal : Prop :=
  star u ⬝ᵥ u=1 ∧ star e ⬝ᵥ e=1 ∧ star f ⬝ᵥ f=1 ∧
    star u ⬝ᵥ e=0 ∧ star u ⬝ᵥ f=0 ∧ star e ⬝ᵥ f=0

private theorem frame_orthonormal : FrameOrthonormal := by
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  unfold FrameOrthonormal
  repeat' constructor
  all_goals apply Complex.ext
  all_goals norm_num [u,e,f,dotProduct,Fin.sum_univ_succ,Pi.star_apply,
    Complex.mul_re,Complex.mul_im,div_eq_mul_inv]
  all_goals nlinarith

set_option pp.all true in
private theorem finite_readings (σ ρ q : ℝ) (hs : σ=1 ∨ σ= -1) :
    vectorPhi (xi σ ρ q) 1 = ((1+q^2*(1+theta ρ^2) : ℝ) : ℂ) ∧
    read (vectorPhi (xi σ ρ q)) (L σ ρ 0) = -q*lam ρ ∧
    B (vectorPhi (xi σ ρ q)) (Rp σ 0) (Sp σ ρ 0) =
      q^2*(base ρ+q*cubic ρ+q^2*quartic ρ) ∧
    B (vectorPhi (xi σ ρ q)) (Rm σ 0) (Sm σ ρ 0) =
      q^2*(base ρ-q*cubic ρ+q^2*quartic ρ) := by
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hpow (n : ℕ) (_hn : 2 ≤ n) :
      (Real.sqrt 2)^n = (2 : ℝ)^(n/2)*(Real.sqrt 2)^(n%2) := by
    calc
      (Real.sqrt 2)^n = (Real.sqrt 2)^(n%2+2*(n/2)) :=
        congrArg (fun m : ℕ => (Real.sqrt 2)^m) (Nat.mod_add_div n 2).symm
      _ = (Real.sqrt 2)^(n%2)*((Real.sqrt 2)^2)^(n/2) := by
        rw [pow_add,pow_mul]
      _ = (2 : ℝ)^(n/2)*(Real.sqrt 2)^(n%2) := by
        rw [hs2]
        ring
  rcases hs with rfl | rfl
  all_goals refine ⟨?_,?_,?_,?_⟩
  all_goals simp only [B,read,vectorPhi_apply]
  all_goals try apply Complex.ext
  all_goals norm_num [xi,eta,u,e,f,theta,lam,base,cubic,
    quartic,Rp,Rm,Sp,Sm,L,h,r,k,g,s,J,K,c,t,Matrix.mul_apply,Matrix.mulVec,
    dotProduct,Fin.sum_univ_succ,Matrix.one_apply,Matrix.vecMul,Pi.star_apply,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,div_eq_mul_inv,
    map_div₀,map_mul,map_add,map_sub,map_neg,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  all_goals (try simp only [← Complex.ofReal_pow, ← Complex.ofReal_inv,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im])
  all_goals ring_nf
  all_goals (try simp only [← Complex.ofReal_pow, ← Complex.ofReal_inv,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im])
  all_goals (try simp (disch := norm_num) only [hpow])
  all_goals norm_num
  all_goals ring

private theorem finite_budget_bound (σ ρ q : ℝ) (hs : σ=1 ∨ σ= -1) (hq : 0 ≤ q) :
    Real.sqrt (B (vectorPhi (xi σ ρ q)) (Rp σ 0) (Sp σ ρ 0)) +
      Real.sqrt (B (vectorPhi (xi σ ρ q)) (Rm σ 0) (Sm σ ρ 0)) ≤
      q*amp ρ+q^2*bigM ρ := by
  obtain ⟨_,_,hp,hm⟩ := finite_readings σ ρ q hs
  obtain ⟨ha,_,hapos,_,hmpos,hM⟩ := scalar_constants ρ
  obtain ⟨_,hrp,hrm,hsp,hsm,_⟩ := labels_sa σ ρ (by simp : IsSelfAdjoint (0:A))
  have hbp := gram_nonneg (vectorPhi (xi σ ρ q)) hrp hsp
  have hbm := gram_nonneg (vectorPhi (xi σ ρ q)) hrm hsm
  have hsp2 := (Real.sq_sqrt hbp).trans hp
  have hsm2 := (Real.sq_sqrt hbm).trans hm
  have hqa := congrArg (fun z : ℝ => q^2*z) ha
  have hsump : (Real.sqrt (B (vectorPhi (xi σ ρ q)) (Rp σ 0) (Sp σ ρ 0)) +
      Real.sqrt (B (vectorPhi (xi σ ρ q)) (Rm σ 0) (Sm σ ρ 0)))^2 ≤
      q^2*amp ρ^2+4*q^4*quartic ρ := by
    have hn := sq_nonneg
      (Real.sqrt (B (vectorPhi (xi σ ρ q)) (Rp σ 0) (Sp σ ρ 0)) -
        Real.sqrt (B (vectorPhi (xi σ ρ q)) (Rm σ 0) (Sm σ ρ 0)))
    nlinarith [hqa]
  have hprod := mul_nonneg (pow_nonneg hq 4) (sub_nonneg.mpr hM)
  have hcross := mul_nonneg (pow_nonneg hq 3) (mul_nonneg hapos hmpos.le)
  have htarget : 0 ≤ q*amp ρ+q^2*bigM ρ := by positivity
  have hleft : 0 ≤ Real.sqrt (B (vectorPhi (xi σ ρ q)) (Rp σ 0) (Sp σ ρ 0)) +
      Real.sqrt (B (vectorPhi (xi σ ρ q)) (Rm σ 0) (Sm σ ρ 0)) := by positivity
  nlinarith

def ExactFiniteWitness (σ ρ : ℝ) : Prop :=
  FrameOrthonormal ∧ 0 < delta ρ ∧ 0 < epsilon ρ ∧
  vectorPhi (xi σ ρ (epsilon ρ)) 1 =
    ((1+epsilon ρ^2*(1+theta ρ^2) : ℝ) : ℂ) ∧
  0 < delta ρ^2/(4*bigM ρ) ∧
  delta ρ^2/(4*bigM ρ) ≤
    |read (vectorPhi (xi σ ρ (epsilon ρ))) (L σ ρ 0)| -
      Real.sqrt (B (vectorPhi (xi σ ρ (epsilon ρ))) (Rp σ 0) (Sp σ ρ 0)) -
      Real.sqrt (B (vectorPhi (xi σ ρ (epsilon ρ))) (Rm σ 0) (Sm σ ρ 0))

theorem exact_finite_witness (σ ρ : ℝ) (hs : σ=1 ∨ σ= -1) (hρ : ρ≠0) :
    ExactFiniteWitness σ ρ := by
  have hd := delta_pos ρ hρ
  obtain ⟨_,_,_,hl,hm,_⟩ := scalar_constants ρ
  have he : 0 < epsilon ρ := div_pos hd (mul_pos (by norm_num) hm)
  have hgap : 0 < delta ρ^2/(4*bigM ρ) := div_pos (sq_pos_of_pos hd) (by positivity)
  obtain ⟨hmass,hread,_,_⟩ := finite_readings σ ρ (epsilon ρ) hs
  have hb := finite_budget_bound σ ρ (epsilon ρ) hs he.le
  have habs : |read (vectorPhi (xi σ ρ (epsilon ρ))) (L σ ρ 0)| = epsilon ρ*lam ρ := by
    rw [hread,neg_mul,abs_neg,abs_of_nonneg (mul_nonneg he.le hl.le)]
  refine ⟨frame_orthonormal,hd,he,hmass,hgap,?_⟩
  rw [habs]
  have hid : epsilon ρ*lam ρ-(epsilon ρ*amp ρ+epsilon ρ^2*bigM ρ) =
      delta ρ^2/(4*bigM ρ) := by
    unfold epsilon delta
    field_simp [ne_of_gt hm]
    ring
  linarith

theorem zero_probe_forces_zero (σ ρ : ℝ) (hs : σ=1 ∨ σ= -1)
    (hb : ZeroBudget σ ρ) : ρ=0 := by
  by_contra hρ
  obtain ⟨_,_,_,_,hg,hv⟩ := exact_finite_witness σ ρ hs hρ
  have hp := hb (vectorPhi (xi σ ρ (epsilon ρ)))
  unfold PB at hp
  linarith

theorem full_equivalence (σ ρ : ℝ) (hs : σ=1 ∨ σ= -1) :
    (ρ=0 ↔ AllBudgets σ ρ) ∧ (AllBudgets σ ρ ↔ ZeroBudget σ ρ) := by
  have hz : CornerSA (0:A) := ⟨by simp, by simp⟩
  have hallzero : AllBudgets σ ρ → ZeroBudget σ ρ := fun hh => hh.2 0 hz
  constructor
  · exact ⟨fun hρ => hρ ▸ zero_forward σ hs,
      fun hh => zero_probe_forces_zero σ ρ hs (hallzero hh)⟩
  · exact ⟨hallzero, fun hh => (zero_probe_forces_zero σ ρ hs hh) ▸ zero_forward σ hs⟩

end D5.S3.Quantum.Algebra.BalancedStarRigidity

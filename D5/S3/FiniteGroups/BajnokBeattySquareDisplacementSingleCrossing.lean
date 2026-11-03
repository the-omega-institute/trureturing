/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementSingleCrossing
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementSingleCrossing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite exact quotient counts have a unique threshold for every odd square displacement. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open NearSquareLatticeRigidity BajnokBeattyFirstReturnDefect
open BajnokBeattyAsymmetricGrowth BajnokBeattyOddWrapReturnCounts
open BajnokBeattyOddWrapSingleCrossing BajnokBeattyOddWrapLateSign
open BajnokBeattyOddWrapGaussianUpperEnvelope BajnokBeattyOddWrapPositiveCone

/-- Signed coordinate-word returns in the complete two lattice quotients. -/
def square_return_pair (p q : ℤ) (t : ℕ) : ℕ × ℕ :=
  let m : ℤ := 2*q*(t : ℤ)-1
  let v1a : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v2a : Plane := ![p*(m-q^2)/2, -(p*(m+q^2)/2)]
  let v1q : Plane := ![p*(m-q)/2, p*(m+q)/2]
  let v2q : Plane := ![p*(m-q)/2, -(p*(m+q)/2)]
  let Ka := Submodule.span ℤ (Set.range ![v1a,v2a])
  let Kq := Submodule.span ℤ (Set.range ![v1q,v2q])
  let Fa : Plane →+ (Plane ⧸ Ka) := Ka.mkQ.toAddMonoidHom
  let Fq : Plane →+ (Plane ⧸ Kq) := Kq.mkQ.toAddMonoidHom
  let n : ℕ := (p*m).toNat
  (W Fa n, W Fq n)

-- This is the new free-factor algebra. The old factor-ten lemma is not used.
private theorem free_step (h c Q x y : ℚ) (hh : 0 < h) (hc : 1 < c)
    (hQ : c*h < Q) (hx : 0 < x) (hy : 0 < y) :
    let x' := x*Q/(Q-h)
    let y' := y*Q/(Q-c*h)
    0 < x'-x ∧ y/x < y'/x' ∧
      (2*x'-1-y')-(2*x-1-y) = (x'-x)*(2-c*(y'/x')) := by
  dsimp only
  have hch : h < c*h := by
    have hm := mul_pos hh (sub_pos.mpr hc)
    nlinarith only [hm]
  have hd : 0 < Q-h := by linarith
  have he : 0 < Q-c*h := by linarith
  have hQ0 : 0 < Q := by linarith
  have dx : x*Q/(Q-h)-x = x*h/(Q-h) := by
    field_simp [hd.ne']; ring
  have dy : y*Q/(Q-c*h)-y = y*(c*h)/(Q-c*h) := by
    field_simp [he.ne']; ring
  have hr : (y*Q/(Q-c*h))/(x*Q/(Q-h)) = (y/x)*((Q-h)/(Q-c*h)) := by
    field_simp [hx.ne', hQ0.ne', hd.ne', he.ne']
  have hf : 1 < (Q-h)/(Q-c*h) := (lt_div_iff₀ he).mpr (by linarith)
  have hs : y*Q/(Q-c*h)-y =
      c*((y*Q/(Q-c*h))/(x*Q/(Q-h)))*(x*Q/(Q-h)-x) := by
    rw [dx,dy,hr]
    field_simp [hx.ne', hd.ne', he.ne']
    <;> ring
  refine ⟨by rw [dx]; exact div_pos (mul_pos hx hh) hd, ?_, ?_⟩
  · rw [hr]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hf (div_pos hy hx)
  · nlinarith only [hs]

private theorem free_persistence (x y Q : ℕ → ℚ) (h c : ℚ)
    (hh : 0 < h) (hc : 1 < c) (hQ : ∀ z, c*h < Q z)
    (hx : ∀ z, 0 < x z) (hy : ∀ z, 0 < y z)
    (rx : ∀ z, x (z+1) = x z*Q z/(Q z-h))
    (ry : ∀ z, y (z+1) = y z*Q z/(Q z-c*h))
    (hco : ∀ z, ∃ k, z < k ∧ 0 < 2*x k-1-y k)
    {i j : ℕ} (hij : i < j) (hi : 0 ≤ 2*x i-1-y i) :
    0 < 2*x j-1-y j := by
  have localStep (z : ℕ) :
      0 < x (z+1)-x z ∧ y z/x z < y (z+1)/x (z+1) ∧
      (2*x (z+1)-1-y (z+1))-(2*x z-1-y z) =
        (x (z+1)-x z)*(2-c*(y (z+1)/x (z+1))) := by
    have hs := free_step h c (Q z) (x z) (y z) hh hc (hQ z) (hx z) (hy z)
    rwa [← rx z, ← ry z] at hs
  have hr : StrictMono (fun z => y z/x z) :=
    strictMono_nat_of_lt_succ (fun z => (localStep z).2.1)
  have hs : StrictMono (fun z => c*(y (z+1)/x (z+1))) := by
    intro a b hab
    exact mul_lt_mul_of_pos_left (hr (Nat.add_lt_add_right hab 1)) (by linarith)
  exact finite_sign_persistence (fun z => 2*x z-1-y z)
    (fun z => x (z+1)-x z) (fun z => c*(y (z+1)/x (z+1)))
    (fun z => (localStep z).1) hs (fun z => (localStep z).2.2) hco hij hi

-- New arbitrary block lengths, consuming the unchanged adjacent-drop suppliers.
private theorem block_bounds (n a p r s : ℕ) (hn : n+p = 2*a)
    (hfit : a+r+s ≤ n) :
    (Nat.choose n a : ℤ)*((a : ℤ)-(r : ℤ)*(p+r)) ≤
      (Nat.choose n (a+r) : ℤ)*a ∧
    (Nat.choose n (a+r+s) : ℤ)*
        ((a : ℤ)+r+s+(s : ℤ)*(p+2*r+s)) ≤
      (Nat.choose n (a+r) : ℤ)*((a : ℤ)+r+s) := by
  have hnZ : (n : ℤ)+p = 2*(a : ℤ) := by exact_mod_cast hn
  have first (i : ℕ) (hi : i < r) :
      ((Nat.choose n (a+i) : ℤ)-Nat.choose n (a+i+1))*(a : ℤ) ≤
        (Nat.choose n a : ℤ)*((p : ℤ)+2*i+1) := by
    have hk : a+i ≤ n := by omega
    have hstep := choose_step_noninc n (a+i) hk (by omega)
    have hz : (Nat.choose n (a+i+1) : ℤ) ≤ Nat.choose n (a+i) := by
      exact_mod_cast hstep
    have hu : (Nat.choose n (a+i) : ℤ) ≤ Nat.choose n a := by
      exact_mod_cast choose_right_le n a (a+i) (by omega) (by omega) hk
    have hid := choose_drop_identity n (a+i) hk
    change ((Nat.choose n (a+i) : ℤ)-Nat.choose n (a+i+1))*
      (((a+i : ℕ) : ℤ)+1) = (Nat.choose n (a+i) : ℤ)*
      (2*((a+i : ℕ) : ℤ)+1-n) at hid
    have hnum : 2*((a+i : ℕ) : ℤ)+1-n = (p : ℤ)+2*i+1 := by
      push_cast; omega
    rw [hnum] at hid
    calc
      _ ≤ ((Nat.choose n (a+i) : ℤ)-Nat.choose n (a+i+1))*
          (((a+i : ℕ) : ℤ)+1) :=
        mul_le_mul_of_nonneg_left (by push_cast; omega) (by omega)
      _ = _ := hid
      _ ≤ _ := mul_le_mul_of_nonneg_right hu (by positivity)
  have fs : ((Nat.choose n a : ℤ)-Nat.choose n (a+r))*(a : ℤ) ≤
      (Nat.choose n a : ℤ)*((r : ℤ)*p+(r : ℤ)^2) := by
    have hs := Finset.sum_le_sum (fun i hi => first i (Finset.mem_range.mp hi))
    rw [← Finset.sum_mul, ← Finset.mul_sum,
      sum_drops (fun k => (Nat.choose n k : ℤ)) a r,
      sum_linear_numerators] at hs
    push_cast at hs ⊢
    exact hs
  have second (i : ℕ) (hi : i < s) :
      (Nat.choose n (a+r+s) : ℤ)*(((p+2*r : ℕ) : ℤ)+2*i+1) ≤
        ((Nat.choose n (a+r+i) : ℤ)-Nat.choose n (a+r+i+1))*
          ((a : ℤ)+r+s) := by
    have hk : a+r+i ≤ n := by omega
    have hstep := choose_step_noninc n (a+r+i) hk (by omega)
    have hz : (Nat.choose n (a+r+i+1) : ℤ) ≤ Nat.choose n (a+r+i) := by
      exact_mod_cast hstep
    have hl : (Nat.choose n (a+r+s) : ℤ) ≤ Nat.choose n (a+r+i) := by
      exact_mod_cast choose_right_le n (a+r+i) (a+r+s) (by omega) (by omega) hfit
    have hid := choose_drop_identity n (a+r+i) hk
    change ((Nat.choose n (a+r+i) : ℤ)-Nat.choose n (a+r+i+1))*
      (((a+r+i : ℕ) : ℤ)+1) = (Nat.choose n (a+r+i) : ℤ)*
      (2*((a+r+i : ℕ) : ℤ)+1-n) at hid
    have hnum : 2*((a+r+i : ℕ) : ℤ)+1-n =
        ((p+2*r : ℕ) : ℤ)+2*i+1 := by push_cast; omega
    rw [hnum] at hid
    calc
      _ ≤ (Nat.choose n (a+r+i) : ℤ)*(((p+2*r : ℕ) : ℤ)+2*i+1) :=
        mul_le_mul_of_nonneg_right hl (by positivity)
      _ = _ := hid.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by push_cast; omega) (by omega)
  have ss : (Nat.choose n (a+r+s) : ℤ)*
      ((s : ℤ)*(p+2*r)+(s : ℤ)^2) ≤
      ((Nat.choose n (a+r) : ℤ)-Nat.choose n (a+r+s))*((a : ℤ)+r+s) := by
    have hs := Finset.sum_le_sum (fun i hi => second i (Finset.mem_range.mp hi))
    rw [← Finset.mul_sum, ← Finset.sum_mul,
      sum_drops (fun k => (Nat.choose n k : ℤ)) (a+r) s,
      sum_linear_numerators] at hs
    push_cast at hs ⊢
    exact hs
  push_cast at fs ss ⊢
  constructor <;> nlinarith only [fs,ss]

-- The tiny product induction is consumed only by the initial-sign proof.
private theorem prod_lower (u : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) (r : ℕ) :
    1+∑ i ∈ Finset.range r, u i ≤ ∏ i ∈ Finset.range r, (1+u i) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hs : 0 ≤ ∑ i ∈ Finset.range r, u i := Finset.sum_nonneg (fun i _ => hu i)
    have hm := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+u r by linarith [hu r])
    nlinarith [mul_nonneg hs (hu r)]

private theorem initial_binomial (n a p r : ℕ) (hp : 0 < p) (hr : 0 < r)
    (hn : n+p = 2*a) (hfit : a+r ≤ n)
    (hmass : (n : ℝ)+1 ≤ 2*(r : ℝ)*(p+r)) :
    2*Nat.choose n (a+r) < Nat.choose n a := by
  let R : ℝ := n+1
  let x : ℕ → ℝ := fun i => ((p : ℝ)+2*i+1)/R
  let u : ℕ → ℝ := fun i => 2*x i/(1-x i)
  have hR : 0 < R := by dsimp [R]; positivity
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hx (i : ℕ) (hi : i < r) : 0 < x i ∧ x i < 1 := by
    have hnR : (n : ℝ)+p = 2*(a : ℝ) := by exact_mod_cast hn
    have hiR : (a : ℝ)+(i : ℝ) < n := by exact_mod_cast (show a+i < n by omega)
    constructor
    · exact div_pos (by positivity) hR
    · apply (div_lt_iff₀ hR).mpr
      dsimp only [R]
      linarith
  have hu (i : ℕ) (hi : i < r) : 2*x i < u i := by
    have h := hx i hi
    apply (lt_div_iff₀ (show 0 < 1-x i by linarith)).mpr
    nlinarith [sq_pos_of_pos h.1]
  let u0 : ℕ → ℝ := fun i => if i < r then u i else 0
  have hu0 : ∀ i, 0 ≤ u0 i := by
    intro i
    dsimp [u0]
    split_ifs with hi
    · exact (lt_trans (mul_pos (by norm_num) (hx i hi).1) (hu i hi)).le
    · exact le_rfl
  have hs : (∑ i ∈ Finset.range r, 2*x i) < ∑ i ∈ Finset.range r, u i := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hu i (Finset.mem_range.mp hi)).le
    · exact ⟨0,Finset.mem_range.mpr hr,hu 0 hr⟩
  have hsum : (∑ i ∈ Finset.range r, 2*x i) = 2*(r : ℝ)*(p+r)/R := by
    simp only [x,div_eq_mul_inv]
    rw [← Finset.mul_sum, ← Finset.sum_mul, sum_linear]
    ring
  have hone : 1 ≤ ∑ i ∈ Finset.range r, 2*x i := by
    rw [hsum]
    exact (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hmass)
  have hp := prod_lower u0 hu0 r
  have heq : (∏ i ∈ Finset.range r, (1+u0 i)) =
      (Nat.choose n a : ℝ)/(Nat.choose n (a+r) : ℝ) := by
    rw [choose_ratio_centered_prod n a r p R hfit rfl (by
      have h : (n : ℝ)+p = 2*(a : ℝ) := by exact_mod_cast hn
      linarith)]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    dsimp only [u0]
    rw [if_pos hi']
    change 1+2*x i/(1-x i) = (1+x i)/(1-x i)
    field_simp [(show 0 < 1-x i by linarith [(hx i hi').2]).ne']
    <;> ring
  have hsum0 : (∑ i ∈ Finset.range r, u0 i) = ∑ i ∈ Finset.range r, u i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [u0, if_pos (Finset.mem_range.mp hi)]
  rw [heq,hsum0] at hp
  have hB : 0 < (Nat.choose n (a+r) : ℝ) := by exact_mod_cast Nat.choose_pos hfit
  have hratio : 2 < (Nat.choose n a : ℝ)/(Nat.choose n (a+r) : ℝ) := by linarith
  have hfinal := (lt_div_iff₀ hB).mp hratio
  exact_mod_cast hfinal

-- Odd natural coordinates make every half integral before nonlinear arithmetic.
private def P (u : ℕ) : ℕ := 2*u+1
private def Q (v : ℕ) : ℕ := 2*v+1
private def b (v : ℕ) : ℕ := 2*v*(v+1)
private def r (u v : ℕ) : ℕ := v*P u
private def l (u v : ℕ) : ℕ := (Q v+1)*r u v
private def j1 (u v : ℕ) : ℕ := u+r u v
private def j2 (u v : ℕ) : ℕ := u+l u v
private def H (u v : ℕ) : ℚ := (r u v : ℚ)*(P u+r u v)
private def C (v : ℕ) : ℚ := (Q v : ℚ)^2+1
private def row (u v z : ℕ) : ℕ := j2 u v+z
private def den (u v z : ℕ) : ℚ := S (row u v z)-lam u
private def X (u v z : ℕ) : ℚ := K (row u v z) (j1 u v)/K (row u v z) u
private def Y (u v z : ℕ) : ℚ := K (row u v z) (j2 u v)/K (row u v z) u
private def sample (u v t : ℕ) : ℕ := P u*(Q v*t-b v-1)
private def N (u v t : ℕ) : ℕ := P u*(2*(Q v*t)-1)
private def a (u v t : ℕ) : ℕ := P u*(Q v*t)
private def late (u v : ℕ) : ℕ := j1 u v+1

private theorem r_le_l (u v : ℕ) : r u v ≤ l u v := by
  dsimp [l]
  simpa only [one_mul] using
    Nat.mul_le_mul_right (r u v) (show 1 ≤ Q v+1 by omega)

private theorem param_id (u v : ℕ) :
    (Q v)^2 = 2*b v+1 ∧ l u v = b v*P u ∧
    2*j1 u v+1 = Q v*P u ∧ 2*j2 u v+1 = (Q v)^2*P u ∧
    lam (j1 u v)-lam u = H u v ∧
    lam (j2 u v)-lam u = C v*H u v := by
  dsimp [Q,b,l,r,P,j1,j2,lam,H,C]
  push_cast
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private theorem normalization (u v : ℕ) (hv : 1 ≤ v) :
    0 < H u v ∧ 1 < C v ∧ (∀ z, C v*H u v < den u v z) ∧
    (∀ z, 0 < X u v z) ∧ (∀ z, 0 < Y u v z) ∧
    (∀ z, X u v (z+1) = X u v z*den u v z/(den u v z-H u v)) ∧
    (∀ z, Y u v (z+1) = Y u v z*den u v z/(den u v z-C v*H u v)) := by
  have hj : u ≤ j1 u v ∧ j1 u v ≤ j2 u v := by
    have hh := r_le_l u v
    dsimp [j1,j2]; omega
  have hg1 := (param_id u v).2.2.2.2.1
  have hg2 := (param_id u v).2.2.2.2.2
  have hd1 (z : ℕ) : den u v z-H u v = S (row u v z)-lam (j1 u v) := by
    dsimp [den]; linarith only [hg1]
  have hd2 (z : ℕ) : den u v z-C v*H u v = S (row u v z)-lam (j2 u v) := by
    dsimp [den]; linarith only [hg2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [H,r,P]; positivity
  · have hq : (3 : ℚ) ≤ Q v := by dsimp [Q]; push_cast; exact_mod_cast (by omega : 3 ≤ 2*v+1)
    dsimp [C]; nlinarith
  · intro z
    have hh := denom_pos (row u v z) (j2 u v) (by dsimp [row]; omega)
    rw [← hd2 z] at hh
    linarith
  · intro z; exact div_pos (K_pos _ _) (K_pos _ _)
  · intro z; exact div_pos (K_pos _ _) (K_pos _ _)
  · intro z
    change K (row u v (z+1)) (j1 u v)/K (row u v (z+1)) u = _
    rw [show row u v (z+1) = row u v z+1 by dsimp [row]; omega]
    rw [ratio_step (row u v z) u (j1 u v) (by dsimp [row]; omega)
      (by dsimp [row]; omega), hd1 z]
    dsimp [X,den]; ring
  · intro z
    change K (row u v (z+1)) (j2 u v)/K (row u v (z+1)) u = _
    rw [show row u v (z+1) = row u v z+1 by dsimp [row]; omega]
    rw [ratio_step (row u v z) u (j2 u v) (by dsimp [row]; omega)
      (by dsimp [row]; omega), hd2 z]
    dsimp [Y,den]; ring

private theorem row_data (u v t : ℕ) (ht : v+1 ≤ t) :
    N u v t+P u = 2*a u v t ∧ a u v t+l u v ≤ N u v t ∧
    2*row u v (sample u v t)+1 = N u v t := by
  have hqt : b v+1 ≤ Q v*t := by
    have hh := Nat.mul_le_mul_left (Q v) ht
    have he : Q v*(v+1) = b v+v+1 := by dsimp [Q,b]; ring
    omega
  have he : Q v*t = (Q v*t-b v-1)+b v+1 := by omega
  have hn : 2*(Q v*t)-1 = 2*(Q v*t-b v-1)+2*b v+1 := by omega
  have hn' : (2*(Q v*t)-1)+1 = 2*(Q v*t) := by omega
  have hl := (param_id u v).2.1
  refine ⟨?_,?_,?_⟩
  · dsimp [N,a]
    calc
      P u*(2*(Q v*t)-1)+P u = P u*((2*(Q v*t)-1)+1) := by ring
      _ = 2*(P u*(Q v*t)) := by rw [hn']; ring
  · calc
      a u v t+l u v = P u*(Q v*t+b v) := by dsimp [a]; rw [hl]; ring
      _ ≤ P u*(2*(Q v*t)-1) := Nat.mul_le_mul_left _ (by omega)
      _ = N u v t := rfl
  · dsimp [row,j2,sample,N]
    rw [hl,hn]
    dsimp [P]
    ring

theorem actual_counts (u v t : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (ht : v+1 ≤ t) :
    (square_return_pair (P u) (Q v) t).1 =
        2*(Nat.choose (N u v t) (a u v t)+Nat.choose (N u v t) (a u v t+l u v)) ∧
    (square_return_pair (P u) (Q v) t).2 =
        4*Nat.choose (N u v t) (a u v t+r u v) := by
  let p : ℤ := P u
  let q : ℤ := Q v
  let m : ℤ := 2*q*t-1
  have hp : 0 < p := by dsimp [p,P]; positivity
  have hq : 3 ≤ q := by dsimp [q,Q]; push_cast; omega
  have hpo : Odd p := ⟨(u : ℤ),by simp [p,P]⟩
  have hqo : Odd q := ⟨(v : ℤ),by simp [q,Q]⟩
  have hmo : Odd m := ⟨q*t-1,by dsimp [m]; ring⟩
  have hq2o : Odd (q^2) := by simpa only [pow_two] using hqo.mul hqo
  have htime : q+1 ≤ 2*(t : ℤ) := by dsimp [q,Q]; push_cast; omega
  have hqm : q^2 < m := by
    have hh := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ 2*(t : ℤ)-q-1 by omega)
    dsimp [m]; nlinarith only [hh,hq]
  have hm1 : 1 < m := by nlinarith [sq_nonneg (q-3)]
  have hqm' : q < m := by nlinarith [sq_nonneg (q-1)]
  obtain ⟨_,ha1,ha2,_⟩ := asymmetric_rank_one_actual_data p m 1 (q^2)
    hp hpo hmo odd_one hq2o (by norm_num) hm1 (by positivity) hqm
  obtain ⟨_,hq1,hq2,_⟩ := asymmetric_rank_one_actual_data p m q q
    hp hpo hmo hqo hqo (by omega) hqm' (by omega) hqm'
  have ca := odd_boundary_count_of_sumDiff p m 1 (q^2)
    ![p*(m-1)/2,p*(m+1)/2] ![p*(m-q^2)/2,-(p*(m+q^2)/2)]
    hp hpo hmo odd_one hq2o (by norm_num) hm1 (by positivity) hqm ha1 ha2
  have cq := odd_boundary_count_of_sumDiff p m q q
    ![p*(m-q)/2,p*(m+q)/2] ![p*(m-q)/2,-(p*(m+q)/2)]
    hp hpo hmo hqo hqo (by omega) hqm' (by omega) hqm' hq1 hq2
  have hsmall : 1 ≤ 2*(Q v*t) := by
    have hqt0 := Nat.mul_pos (show 0 < Q v by dsimp [Q]; omega) (show 0 < t by omega)
    omega
  have hN : (p*m).toNat = N u v t := by
    have hh : p*m = (N u v t : ℤ) := by
      simp only [N,Nat.cast_mul,Nat.cast_sub hsmall,Nat.cast_ofNat,Nat.cast_one]
      dsimp [p,q,m]; ring
    rw [hh,Int.toNat_natCast]
  have hA : (p*(m+1)/2).toNat = a u v t := by
    have hh : p*(m+1) = 2*(a u v t : ℤ) := by
      dsimp [p,q,m,a]; push_cast; ring
    rw [show p*(m+1)/2 = (a u v t : ℤ) by omega,Int.toNat_natCast]
  have hB : (p*(m+q)/2).toNat = a u v t+r u v := by
    have hh : p*(m+q) = 2*((a u v t+r u v : ℕ) : ℤ) := by
      dsimp [p,q,m,a,r,Q]; push_cast; ring
    rw [show p*(m+q)/2 = ((a u v t+r u v : ℕ) : ℤ) by omega,Int.toNat_natCast]
  have hD : (p*(m+q^2)/2).toNat = a u v t+l u v := by
    have hh : p*(m+q^2) = 2*((a u v t+l u v : ℕ) : ℤ) := by
      dsimp [p,q,m,a,l,r,Q]; push_cast; ring
    rw [show p*(m+q^2)/2 = ((a u v t+l u v : ℕ) : ℤ) by omega,Int.toNat_natCast]
  dsimp only at ca cq
  rw [hN,hA,hD] at ca
  rw [hN,hB] at cq
  constructor
  · simpa only [square_return_pair,← hN] using ca
  · have cq' : (square_return_pair (P u) (Q v) t).2 =
      2*(Nat.choose (N u v t) (a u v t+r u v)+
        Nat.choose (N u v t) (a u v t+r u v)) := by
      simpa only [square_return_pair,← hN] using cq
    omega

private theorem sampled_gap (u v t : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (ht : v+1 ≤ t) :
    ((square_return_pair (P u) (Q v) t).2 : ℚ)-
        (square_return_pair (P u) (Q v) t).1 =
      2*K (row u v (sample u v t)) u*
        (2*X u v (sample u v t)-1-Y u v (sample u v t)) := by
  obtain ⟨hn,hfit,hrow⟩ := row_data u v t ht
  obtain ⟨hca,hcq⟩ := actual_counts u v t hu hv ht
  let M := row u v (sample u v t)
  have hs (d : ℕ) (hd : d ≤ l u v) :
      (Nat.choose (N u v t) (a u v t+d) : ℚ) = K M (u+d) := by
    have hp : P u = 2*u+1 := rfl
    have hle : a u v t+d ≤ N u v t := by omega
    have hcomp : N u v t-(a u v t+d) = M-(u+d) := by dsimp [M]; omega
    have hh := Nat.choose_symm hle
    rw [hcomp] at hh
    dsimp [K]
    rw [hrow]
    exact_mod_cast hh.symm
  have hrl := r_le_l u v
  have haK : (Nat.choose (N u v t) (a u v t) : ℚ) = K M u := by
    simpa only [Nat.add_zero] using hs 0 (Nat.zero_le _)
  have hbK := hs (r u v) hrl
  have hdK := hs (l u v) (le_refl _)
  have hcaQ : ((square_return_pair (P u) (Q v) t).1 : ℚ) =
      2*(K M u+K M (j2 u v)) := by
    have hh : ((square_return_pair (P u) (Q v) t).1 : ℚ) =
        2*((Nat.choose (N u v t) (a u v t) : ℚ)+
          Nat.choose (N u v t) (a u v t+l u v)) := by exact_mod_cast hca
    rw [haK,hdK] at hh
    exact hh
  have hcqQ : ((square_return_pair (P u) (Q v) t).2 : ℚ) =
      4*K M (j1 u v) := by
    have hh : ((square_return_pair (P u) (Q v) t).2 : ℚ) =
        4*(Nat.choose (N u v t) (a u v t+r u v) : ℚ) := by exact_mod_cast hcq
    rw [hbK] at hh
    exact hh
  rw [hcaQ,hcqQ]
  change 4*K M (j1 u v)-2*(K M u+K M (j2 u v)) =
    2*K M u*(2*(K M (j1 u v)/K M u)-1-K M (j2 u v)/K M u)
  field_simp [(K_pos M u).ne']
  <;> ring

private theorem late_binomial (u v t : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (ht : v+1 ≤ t) (hLate : late u v ≤ t) :
    Nat.choose (N u v t) (a u v t)+Nat.choose (N u v t) (a u v t+l u v) <
      2*Nat.choose (N u v t) (a u v t+r u v) := by
  obtain ⟨hn,hfit,_⟩ := row_data u v t ht
  let pp : ℤ := P u
  let qq : ℤ := Q v
  let rr : ℤ := r u v
  let ll : ℤ := l u v
  let aa : ℤ := a u v t
  let h : ℤ := rr*(pp+rr)
  let A : ℤ := Nat.choose (N u v t) (a u v t)
  let B : ℤ := Nat.choose (N u v t) (a u v t+r u v)
  let D : ℤ := Nat.choose (N u v t) (a u v t+l u v)
  let U : ℤ := aa-h
  let V : ℤ := aa+ll+qq^2*h
  have hp : 3 ≤ pp := by dsimp [pp,P]; push_cast; omega
  have hq : 3 ≤ qq := by dsimp [qq,Q]; push_cast; omega
  have hq0 : 0 < qq := by omega
  have hr : 0 < rr := by dsimp [rr,r,P]; positivity
  have hh : 0 < h := mul_pos hr (by omega)
  have h4 : 4*h = (qq^2-1)*pp^2 := by
    dsimp [h,rr,pp,qq,r,P,Q]; push_cast; ring
  have hl2 : 2*ll = (qq^2-1)*pp := by
    dsimp [ll,qq,pp,l,r,Q]; push_cast; ring
  have htime : qq*pp+1 ≤ 2*(t : ℤ) := by
    have he := (param_id u v).2.2.1
    have hz : ((late u v : ℕ) : ℤ) ≤ t := by exact_mod_cast hLate
    dsimp [late] at hz
    have heZ : 2*(j1 u v : ℤ)+1 = qq*pp := by
      dsimp only [qq,pp]
      exact_mod_cast he
    push_cast at hz
    omega
  have hcone : pp+qq^2*pp^2 < 2*aa := by
    have htime' := mul_le_mul_of_nonneg_left htime (show 0 ≤ qq by omega)
    have htime'' := mul_le_mul_of_nonneg_left htime' (show 0 ≤ pp by omega)
    have hid : 2*aa = pp*(2*qq*t) := by dsimp [aa,a,pp,qq]; push_cast; ring
    have hstrict : pp < pp*qq := by
      have hm := mul_pos (show 0 < pp by omega) (show 0 < qq-1 by omega)
      nlinarith only [hm]
    nlinarith only [htime'',hid,hstrict]
  have hU : 0 < U := by dsimp [U]; nlinarith [sq_nonneg pp]
  have hV : 0 < V := by dsimp [V,aa,ll]; positivity
  have hl : r u v+Q v*r u v = l u v := by dsimp [l]; ring
  have hs2 : ((Q v*r u v : ℕ) : ℤ)*
      ((P u : ℤ)+2*r u v+Q v*r u v) = qq^2*h := by
    dsimp [qq,h,rr,pp,Q,r,P]; push_cast; ring
  obtain ⟨hA,hD⟩ := block_bounds (N u v t) (a u v t) (P u) (r u v)
    (Q v*r u v) hn (by omega)
  rw [show a u v t+r u v+Q v*r u v = a u v t+l u v by omega] at hD
  have hlZ : (r u v : ℤ)+Q v*r u v = ll := by
    dsimp [ll]; exact_mod_cast hl
  push_cast at hA hD hs2 hlZ
  rw [hs2] at hD
  change A*U ≤ B*aa at hA
  have hD' : D*V ≤ B*(aa+ll) := by
    change D*(aa+(r u v : ℤ)+(Q v : ℤ)*(r u v : ℤ)+qq^2*h) ≤
      B*(aa+(r u v : ℤ)+(Q v : ℤ)*(r u v : ℤ)) at hD
    have hadd : aa+(r u v : ℤ)+(Q v : ℤ)*(r u v : ℤ) = aa+ll := by
      linarith only [hlZ]
    rw [hadd] at hD
    exact hD
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast Nat.choose_pos (show a u v t+r u v ≤ N u v t by
      have hrl := r_le_l u v
      omega)
  have hbr : 0 < (qq^2-1)*aa-ll-2*qq^2*h := by
    have hid : 2*((qq^2-1)*aa-ll-2*qq^2*h) =
        (qq^2-1)*(2*aa-pp-qq^2*pp^2) := by
      dsimp [h,rr,pp,qq,ll,r,l,P,Q]; push_cast; ring
    have hpos := mul_pos (show 0 < qq^2-1 by nlinarith) (show 0 < 2*aa-pp-qq^2*pp^2 by linarith)
    linarith only [hid,hpos]
  have hgap : aa*V+(aa+ll)*U < 2*U*V := by
    have hid : 2*U*V-aa*V-(aa+ll)*U = h*((qq^2-1)*aa-ll-2*qq^2*h) := by
      dsimp [U,V]; ring
    have hpos := mul_pos hh hbr
    linarith only [hid,hpos]
  have hweighted : (A+D)*(U*V) ≤ B*(aa*V+(aa+ll)*U) := by
    calc
      _ = (A*U)*V+(D*V)*U := by ring
      _ ≤ (B*aa)*V+(B*(aa+ll))*U :=
        add_le_add (mul_le_mul_of_nonneg_right hA hV.le)
          (mul_le_mul_of_nonneg_right hD' hU.le)
      _ = _ := by ring
  have hscaled : (A+D)*(U*V) < (2*B)*(U*V) := by
    calc
      _ ≤ B*(aa*V+(aa+ll)*U) := hweighted
      _ < B*(2*U*V) := mul_lt_mul_of_pos_left hgap hB
      _ = _ := by ring
  have hfinal := (mul_lt_mul_iff_left₀ (mul_pos hU hV)).mp hscaled
  dsimp [A,B,D] at hfinal
  exact_mod_cast hfinal

private theorem initial_sign (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (square_return_pair (P u) (Q v) (v+1)).2 <
      (square_return_pair (P u) (Q v) (v+1)).1 := by
  let pp : ℝ := P u
  let qq : ℝ := Q v
  let rr : ℝ := r u v
  have hp : 3 ≤ pp := by dsimp [pp,P]; push_cast; exact_mod_cast (by omega : 3 ≤ 2*u+1)
  have hq : 3 ≤ qq := by dsimp [qq,Q]; push_cast; exact_mod_cast (by omega : 3 ≤ 2*v+1)
  have hnR : (N u v (v+1) : ℝ) = pp*(qq^2+qq-1) := by
    simp only [N,Nat.cast_mul,Nat.cast_sub (by dsimp [Q]; nlinarith : 1 ≤ 2*(Q v*(v+1))),
      Nat.cast_ofNat,Nat.cast_one]
    dsimp [pp,qq,Q]; push_cast; ring
  have h4 : 4*rr*(pp+rr) = (qq^2-1)*pp^2 := by
    dsimp [rr,pp,qq,r,Q]; push_cast; ring
  have hq2 : 8 ≤ qq^2-1 := by nlinarith
  have hinner : 0 ≤ (pp+1)*(qq^2-1)-2*qq := by
    have hm := mul_nonneg (show 0 ≤ pp-3 by linarith) (show 0 ≤ qq^2-1 by linarith)
    nlinarith
  have hF : 0 ≤ (pp-3)*((pp+1)*(qq^2-1)-2*qq) :=
    mul_nonneg (by linarith) hinner
  have hcert : (qq^2-1)*pp^2-2*pp*(qq^2+qq-1)-2 =
      (pp-3)*((pp+1)*(qq^2-1)-2*qq)+3*(qq-1)^2-8 := by ring
  have hmass : (N u v (v+1) : ℝ)+1 ≤ 2*(r u v : ℝ)*(P u+r u v) := by
    change (N u v (v+1) : ℝ)+1 ≤ 2*rr*(pp+rr)
    rw [hnR]
    nlinarith [sq_nonneg (qq-3)]
  obtain ⟨hn,hfit,_⟩ := row_data u v (v+1) (le_refl _)
  have hrl := r_le_l u v
  have hbin := initial_binomial (N u v (v+1)) (a u v (v+1)) (P u) (r u v)
    (by dsimp [P]; omega) (by dsimp [r,P]; positivity) hn (by omega) hmass
  obtain ⟨ha,hq⟩ := actual_counts u v (v+1) hu hv (le_refl _)
  rw [ha,hq]
  omega

private theorem late_sign (u v t : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (ht : v+1 ≤ t) (hLate : late u v ≤ t) :
    (square_return_pair (P u) (Q v) t).1 < (square_return_pair (P u) (Q v) t).2 := by
  obtain ⟨ha,hq⟩ := actual_counts u v t hu hv ht
  have hb := late_binomial u v t hu hv ht hLate
  rw [ha,hq]
  omega

private theorem cofinal (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ∀ z, ∃ k, z < k ∧ 0 < 2*X u v k-1-Y u v k := by
  intro z
  let t := z+late u v+b v+v+3
  have ht : v+1 ≤ t := by dsimp [t]; omega
  have hl : late u v ≤ t := by dsimp [t]; omega
  have hs : z < sample u v t := by
    have hq : 1 ≤ Q v := by dsimp [Q]; omega
    have hqt := Nat.mul_le_mul_right t hq
    simp only [one_mul] at hqt
    have htbound : z+b v+2 ≤ t := by dsimp [t]; omega
    have hcoef : z+1 ≤ Q v*t-b v-1 := by omega
    have hp := Nat.mul_le_mul_right (Q v*t-b v-1) (show 1 ≤ P u by dsimp [P]; omega)
    simp only [one_mul] at hp
    dsimp [sample]; omega
  have hw := late_sign u v t hu hv ht hl
  have hwQ : ((square_return_pair (P u) (Q v) t).1 : ℚ) <
      (square_return_pair (P u) (Q v) t).2 := by exact_mod_cast hw
  have hg := sampled_gap u v t hu hv ht
  have hf : 0 < 2*K (row u v (sample u v t)) u := mul_pos (by norm_num) (K_pos _ _)
  refine ⟨sample u v t,hs,?_⟩
  have hm : 0 < 2*K (row u v (sample u v t)) u*
      (2*X u v (sample u v t)-1-Y u v (sample u v t)) := by
    rw [← hg]; linarith only [hwQ]
  have hscaled : (2*K (row u v (sample u v t)) u)*0 <
      (2*K (row u v (sample u v t)) u)*
        (2*X u v (sample u v t)-1-Y u v (sample u v t)) := by
    simpa only [mul_zero] using hm
  exact (mul_lt_mul_iff_right₀ hf).mp hscaled

private theorem actual_persistence (u v s t : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hs : v+1 ≤ s) (hst : s < t)
    (hbefore : (square_return_pair (P u) (Q v) s).1 ≤
      (square_return_pair (P u) (Q v) s).2) :
    (square_return_pair (P u) (Q v) t).1 < (square_return_pair (P u) (Q v) t).2 := by
  have ht : v+1 ≤ t := by omega
  have horder : sample u v s < sample u v t := by
    have hq : 0 < Q v := by dsimp [Q]; omega
    have hqs := Nat.mul_le_mul_left (Q v) hs
    have he : Q v*(v+1) = b v+v+1 := by dsimp [Q,b]; ring
    have hst' := Nat.mul_lt_mul_of_pos_left hst hq
    have hcoef : Q v*s-b v-1 < Q v*t-b v-1 := by omega
    exact Nat.mul_lt_mul_of_pos_left hcoef (by dsimp [P]; omega)
  have hgS := sampled_gap u v s hu hv hs
  have hgT := sampled_gap u v t hu hv ht
  have hfS : 0 < 2*K (row u v (sample u v s)) u := mul_pos (by norm_num) (K_pos _ _)
  have hfT : 0 < 2*K (row u v (sample u v t)) u := mul_pos (by norm_num) (K_pos _ _)
  have hbQ : ((square_return_pair (P u) (Q v) s).1 : ℚ) ≤
      (square_return_pair (P u) (Q v) s).2 := by exact_mod_cast hbefore
  have hn : 0 ≤ 2*X u v (sample u v s)-1-Y u v (sample u v s) := by
    have hm : (2*K (row u v (sample u v s)) u)*0 ≤
        (2*K (row u v (sample u v s)) u)*
          (2*X u v (sample u v s)-1-Y u v (sample u v s)) := by
      rw [mul_zero,← hgS]; linarith only [hbQ]
    exact (mul_le_mul_iff_right₀ hfS).mp hm
  obtain ⟨hh,hc,hQ,hX,hY,rx,ry⟩ := normalization u v hv
  have hpos := free_persistence (X u v) (Y u v) (den u v) (H u v) (C v)
    hh hc hQ hX hY rx ry (cofinal u v hu hv) horder hn
  have hm := mul_pos hfT hpos
  rw [← hgT] at hm
  have hfinal : ((square_return_pair (P u) (Q v) t).1 : ℚ) <
      (square_return_pair (P u) (Q v) t).2 := by linarith only [hm]
  exact_mod_cast hfinal

-- The baseline is now arbitrary; the upper endpoint is included in the predicate.
private theorem first_threshold (A B : ℕ → ℕ) (base last : ℕ)
    (hbase : base ≤ last) (hi : B base < A base) (hl : A last < B last)
    (hp : ∀ s t, base ≤ s → s < t → A s ≤ B s → A t < B t) :
    ∃! T : ℕ, base < T ∧
      (∀ t, base ≤ t → t < T → B t < A t) ∧ A T ≤ B T ∧
      (∀ t, T < t → A t < B t) ∧ T ≤ last := by
  classical
  let P : ℕ → Prop := fun t => base ≤ t ∧ A t ≤ B t
  have hex : ∃ t, P t := ⟨last,hbase,hl.le⟩
  let T := Nat.find hex
  have hT : base ≤ T ∧ A T ≤ B T := Nat.find_spec hex
  have hgt : base < T := by
    have hne : T ≠ base := by intro he; rw [he] at hT; omega
    omega
  have hbefore (t : ℕ) (ht : base ≤ t) (hlt : t < T) : B t < A t := by
    by_contra h
    have hmin : T ≤ t := Nat.find_min' hex ⟨ht,by omega⟩
    omega
  have hafter (t : ℕ) (ht : T < t) : A t < B t := hp T t hT.1 ht hT.2
  have hlast : T ≤ last := Nat.find_min' hex ⟨hbase,hl.le⟩
  refine ⟨T,⟨hgt,hbefore,hT.2,hafter,hlast⟩,?_⟩
  intro U hU
  rcases hU with ⟨hUg,hUb,hUa,hUf,hUl⟩
  apply Nat.le_antisymm
  · by_contra h
    have hh := hUb T (by omega) (by omega)
    omega
  · by_contra h
    have hh := hbefore U (by omega) (by omega)
    omega

/-- For every odd p,q >= 3, including odd composites, the exact actual
quotient counts have a unique first threshold on the entire valid t-domain.
The comparison at the threshold is non-strict; equality is not asserted. -/
theorem actual_square_displacement_single_crossing (p q : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q) :
    let tmin : ℕ := ((q+1)/2).toNat
    let tlate : ℕ := ((q*p+1)/2).toNat
    ∃! T : ℕ, tmin < T ∧
      (∀ t : ℕ, tmin ≤ t → t < T →
        (square_return_pair p q t).2 < (square_return_pair p q t).1) ∧
      (square_return_pair p q T).1 ≤ (square_return_pair p q T).2 ∧
      (∀ t : ℕ, T < t →
        (square_return_pair p q t).1 < (square_return_pair p q t).2) ∧
      T ≤ tlate := by
  obtain ⟨k,hk⟩ := hpo
  obtain ⟨e,he⟩ := hqo
  let u : ℕ := k.toNat
  let v : ℕ := e.toNat
  have huZ : (u : ℤ) = k := Int.toNat_of_nonneg (by omega)
  have hvZ : (v : ℤ) = e := Int.toNat_of_nonneg (by omega)
  have hu : 1 ≤ u := by omega
  have hv : 1 ≤ v := by omega
  have hp : (P u : ℤ) = p := by dsimp [P]; push_cast; omega
  have hq : (Q v : ℤ) = q := by dsimp [Q]; push_cast; omega
  have hmin : ((q+1)/2).toNat = v+1 := by
    have hhalf : (q+1)/2 = ((v+1 : ℕ) : ℤ) := by push_cast; omega
    rw [hhalf,Int.toNat_natCast]
  have hlate : ((q*p+1)/2).toNat = late u v := by
    have hh := (param_id u v).2.2.1
    have hhZ : 2*(j1 u v : ℤ)+1 = q*p := by
      rw [← hp,← hq]; exact_mod_cast hh
    have hhalf : (q*p+1)/2 = (late u v : ℤ) := by dsimp [late]; push_cast; omega
    rw [hhalf,Int.toNat_natCast]
  have hbl : v+1 ≤ late u v := by
    have hvr := Nat.mul_le_mul_left v (show 1 ≤ P u by dsimp [P]; omega)
    simp only [mul_one] at hvr
    change v ≤ r u v at hvr
    dsimp [late,j1]; omega
  dsimp only
  rw [hmin,hlate,← hp,← hq]
  exact first_threshold
    (fun t => (square_return_pair (P u) (Q v) t).1)
    (fun t => (square_return_pair (P u) (Q v) t).2) (v+1) (late u v)
    hbl (initial_sign u v hu hv) (late_sign u v (late u v) hu hv hbl (le_refl _))
    (fun s t hs hst hb => actual_persistence u v s t hu hv hs hst hb)

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing

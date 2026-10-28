/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubReciprocal
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub reciprocal identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubOrientation
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
open FiolDoubleHubEndpoint
namespace FiolDoubleHub
private def Pal (p : Polynomial ℝ) (n : ℕ) : Prop :=
  p.natDegree ≤ n ∧ p.reflect n = p

private theorem pal_add {p q : Polynomial ℝ} {n : ℕ}
    (hp : Pal p n) (hq : Pal q n) : Pal (p+q) n := by
  exact ⟨(Polynomial.natDegree_add_le p q).trans (max_le hp.1 hq.1),
    by simpa only [Polynomial.reflect_add, hp.2, hq.2]⟩

private theorem pal_mul {p q : Polynomial ℝ} {n k : ℕ}
    (hp : Pal p n) (hq : Pal q k) : Pal (p*q) (n+k) := by
  exact ⟨(Polynomial.natDegree_mul_le (p:=p) (q:=q)).trans (Nat.add_le_add hp.1 hq.1),
    by rw [Polynomial.reflect_mul p q hp.1 hq.1, hp.2, hq.2]⟩

private theorem pal_C_mul {p : Polynomial ℝ} {n : ℕ} (a : ℝ)
    (hp : Pal p n) : Pal (Polynomial.C a*p) n := by
  exact ⟨(Polynomial.natDegree_C_mul_le a p).trans hp.1,
    by rw [Polynomial.reflect_C_mul, hp.2]⟩

private theorem pal_pow {p : Polynomial ℝ} {n : ℕ}
    (hp : Pal p n) (r : ℕ) : Pal (p^r) (n*r) := by
  induction r with
  | zero => simp [Pal]
  | succ r ih =>
    simpa only [pow_succ, Nat.mul_succ] using pal_mul ih hp

private theorem H_pal (r : ℕ) : Pal (H r) r := by
  constructor
  · unfold H
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  · simp [H, Polynomial.reflect_add, Polynomial.reflect_monomial,
      Polynomial.revAt_le, add_comm]

private theorem S_coeff (r i : ℕ) : (S r).coeff i = if i < r then 1 else 0 := by
  classical
  simp [S, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow, eq_comm]

private theorem S_pal (r : ℕ) (hr : 1 ≤ r) : Pal (S r) (r-1) := by
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    simp only [Finset.mem_range] at hj
    simpa only [Polynomial.natDegree_X_pow] using (show j ≤ r-1 by omega)
  · ext i
    rw [Polynomial.coeff_reflect, S_coeff, S_coeff]
    by_cases hi : i ≤ r-1
    · rw [Polynomial.revAt_le hi]
      simp only [show i < r by omega, show r-1-i < r by omega, ite_true]
    · rw [Polynomial.revAt_eq_self_of_lt (by omega : r-1 < i)]

def baseDegree (d : ℕ) : ℕ := if Odd d then d-1 else d

private theorem UVW_pal (d : ℕ) (hd : 2 ≤ d) :
    Pal (U d) (baseDegree d) ∧ Pal (V d) (baseDegree d+1) ∧
      Pal (W d) (baseDegree d+2) := by
  by_cases ho : Odd d
  · simp only [U,V,W,baseDegree,ho,ite_true]
    have h1 : d+1-1 = d-1+1 := by omega
    have h2 : d+2-1 = d-1+2 := by omega
    exact ⟨S_pal d (by omega), by simpa only [h1] using S_pal (d+1) (by omega),
      by simpa only [h2] using S_pal (d+2) (by omega)⟩
  · simp only [U,V,W,baseDegree,ho,ite_false]
    exact ⟨H_pal d,H_pal (d+1),H_pal (d+2)⟩

private theorem Q_pal (d : ℕ) (hd : 2 ≤ d) : Pal (Q d) (2*N d) := by
  obtain ⟨hu,hv,hw⟩ := UVW_pal d hd
  have hl : Pal (1+Polynomial.X : Polynomial ℝ) 1 := by simpa [H] using H_pal 1
  have hn : 2*N d = 2*baseDegree d+4 := by
    unfold N baseDegree; split_ifs <;> omega
  let x : ℝ := d
  have h1 : Pal (Polynomial.C (2*x^4)*V d^2) (2*baseDegree d+2) := by
    convert pal_C_mul (2*x^4) (pal_pow hv 2) using 1 <;> omega
  have h2 : Pal (Polynomial.C ((3/2:ℝ)*x^2*(x^2-1))*U d*W d)
      (2*baseDegree d+2) := by
    convert pal_C_mul ((3/2:ℝ)*x^2*(x^2-1)) (pal_mul hu hw) using 1 <;>
      first | ring | omega
  have h3 : Pal (Polynomial.C (4*x*(x-1)*(2*x-1))*(1+Polynomial.X)*U d*V d)
      (2*baseDegree d+2) := by
    convert pal_C_mul (4*x*(x-1)*(2*x-1)) (pal_mul (pal_mul hl hu) hv) using 1 <;>
      first | ring | omega
  have h4 : Pal (Polynomial.C (2*(x-1)*(2*x-3))*(1+Polynomial.X)^2*U d^2)
      (2*baseDegree d+2) := by
    convert pal_C_mul (2*(x-1)*(2*x-3)) (pal_mul (pal_pow hl 2) (pal_pow hu 2)) using 1 <;>
      first | ring | omega
  have h5 : Pal (Polynomial.C (8*x*(2*x-1))*U d*V d) (2*baseDegree d+1) := by
    convert pal_C_mul (8*x*(2*x-1)) (pal_mul hu hv) using 1 <;>
      first | ring | omega
  have h6 : Pal (Polynomial.C (16*(x-1))*(1+Polynomial.X)*U d^2)
      (2*baseDegree d+1) := by
    convert pal_C_mul (16*(x-1)) (pal_mul hl (pal_pow hu 2)) using 1 <;>
      first | ring | omega
  have h7 : Pal (Polynomial.C 9*H 4*U d^2) (2*baseDegree d+4) := by
    convert pal_C_mul 9 (pal_mul (H_pal 4) (pal_pow hu 2)) using 1 <;>
      first | ring | omega
  have ht1 := pal_mul (H_pal 2) (pal_add (pal_add (pal_add h1 h2) h3) h4)
  have ht2 := pal_mul (H_pal 3) (pal_add h5 h6)
  have ht1' : Pal (H 2*(Polynomial.C (2*x^4)*V d^2 +
      Polynomial.C ((3/2:ℝ)*x^2*(x^2-1))*U d*W d +
      Polynomial.C (4*x*(x-1)*(2*x-1))*(1+Polynomial.X)*U d*V d +
      Polynomial.C (2*(x-1)*(2*x-3))*(1+Polynomial.X)^2*U d^2))
      (2*baseDegree d+4) := by convert ht1 using 1 <;> omega
  have ht2' : Pal (H 3*(Polynomial.C (8*x*(2*x-1))*U d*V d +
      Polynomial.C (16*(x-1))*(1+Polynomial.X)*U d^2))
      (2*baseDegree d+4) := by convert ht2 using 1 <;> omega
  rw [hn]
  exact pal_add (pal_add ht1' ht2') h7

noncomputable def endpointCoefficient (d : ℕ) : ℝ :=
  let x : ℝ := d
  2*x^4 + (3/2:ℝ)*x^2*(x^2-1) + 4*x*(x-1)*(2*x-1) +
    2*(x-1)*(2*x-3) + 8*x*(2*x-1) + 16*(x-1) + 9

theorem Q_coeff_zero (d : ℕ) (hd : 2 ≤ d) :
    (Q d).coeff 0 = endpointCoefficient d := by
  have hu : (U d).coeff 0 = 1 := by
    unfold U; split_ifs
    · rw [S_coeff]; simp [show 0 < d by omega]
    · simp [H,show d ≠ 0 by omega,show 0 ≠ d by omega]
  have hv : (V d).coeff 0 = 1 := by
    unfold V; split_ifs
    · rw [S_coeff]; simp
    · simp [H]
  have hw : (W d).coeff 0 = 1 := by
    unfold W; split_ifs
    · rw [S_coeff]; simp
    · simp [H]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hu0 : (U d).eval 0 = 1 := by rw [← Polynomial.coeff_zero_eq_eval_zero,hu]
  have hv0 : (V d).eval 0 = 1 := by rw [← Polynomial.coeff_zero_eq_eval_zero,hv]
  have hw0 : (W d).eval 0 = 1 := by rw [← Polynomial.coeff_zero_eq_eval_zero,hw]
  simp only [Q,H,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_X,hu0,hv0,hw0]
  norm_num [endpointCoefficient]
  ring

theorem endpointCoefficient_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < endpointCoefficient d := by
  have hx : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d:ℝ)-1 := by linarith
  have hd2 : 0 < (d:ℝ)^2-1 := by nlinarith
  have hd3 : 0 < 2*(d:ℝ)-3 := by linarith
  have hd4 : 0 < 2*(d:ℝ)-1 := by linarith
  unfold endpointCoefficient
  positivity

theorem candidate_degree_reciprocity (d : ℕ) (hd : 2 ≤ d) :
    (Q d).natDegree = 2*N d ∧ (Q d).reverse = Q d ∧
    (Q d).leadingCoeff = endpointCoefficient d ∧
    (Q d).coeff 0 = endpointCoefficient d ∧ Q d ≠ 0 := by
  have hp := Q_pal d hd
  have hc := Q_coeff_zero d hd
  have hcpos := endpointCoefficient_pos d hd
  have htop : (Q d).coeff (2*N d) = endpointCoefficient d := by
    have he := congrArg (fun p : Polynomial ℝ => p.coeff 0) hp.2
    simpa only [Polynomial.coeff_reflect, Polynomial.revAt_zero, hc] using he
  have hn : (Q d).natDegree = 2*N d :=
    Nat.le_antisymm hp.1 (Polynomial.le_natDegree_of_ne_zero (by rw [htop]; positivity))
  have hz : Q d ≠ 0 := by intro hz; simpa [hz] using hc.trans_ne (ne_of_gt hcpos)
  refine ⟨hn, ?_, ?_, hc, hz⟩
  · change (Q d).reflect (Q d).natDegree = Q d
    rw [hn]; exact hp.2
  · rw [Polynomial.leadingCoeff,hn,htop]

theorem candidate_R_structure (m : ℕ) (hm : 1 ≤ m) :
    (R m).natDegree = 4*m+6 ∧ (R m).reverse = R m ∧
    (R m).leadingCoeff = endpointCoefficient (m+1) ∧
    (R m).coeff 0 = endpointCoefficient (m+1) ∧ R m ≠ 0 := by
  have hd : 2 ≤ m+1 := by omega
  obtain ⟨hqdeg,hqrev,hqlc,hq0,hqne⟩ := candidate_degree_reciprocity (m+1) hd
  have he : Even (h (m+1)) := by
    unfold h; split_ifs
    · exact even_two_mul _
    · exact ⟨m,by omega⟩
  have hfac : (1-Polynomial.X : Polynomial ℝ)^h (m+1) =
      (Polynomial.X-Polynomial.C 1)^h (m+1) := by
    rw [show (1-Polynomial.X : Polynomial ℝ) = -(Polynomial.X-Polynomial.C 1) by simp only [Polynomial.C_1]; ring]
    exact he.neg_pow _
  have hmono := (Polynomial.monic_X_sub_C (1:ℝ)).pow (h (m+1))
  have hne : R m ≠ 0 := by
    unfold R; rw [hfac]; exact mul_ne_zero hmono.ne_zero hqne
  have hdeg : (R m).natDegree = h (m+1)+2*N (m+1) := by
    unfold R; rw [hfac,Polynomial.natDegree_mul hmono.ne_zero hqne,
      (Polynomial.monic_X_sub_C (1:ℝ)).natDegree_pow,Polynomial.natDegree_X_sub_C,
      mul_one,hqdeg]
  have htotal : h (m+1)+2*N (m+1) = 4*m+6 := by
    unfold h N; split_ifs <;> omega
  have h0 : (R m).coeff 0 = endpointCoefficient (m+1) := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [R,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_X,sub_zero,one_pow,one_mul]
    rw [← Polynomial.coeff_zero_eq_eval_zero,hq0]
  have hlc : (R m).leadingCoeff = endpointCoefficient (m+1) := by
    unfold R; rw [hfac,Polynomial.leadingCoeff_mul,hmono.leadingCoeff,one_mul,hqlc]
  have hxp : Pal (Polynomial.X : Polynomial ℝ) 2 := by
    constructor
    · simp
    · simpa using Polynomial.reflect_monomial (R:=ℝ) 2 1
  have hsquare : Pal ((1-Polynomial.X : Polynomial ℝ)^2) 2 := by
    convert pal_add (H_pal 2) (pal_C_mul (-2) hxp) using 1 <;> simp [H,Polynomial.C_ofNat] <;> ring
  obtain ⟨k,hk⟩ := he
  have hp : Pal ((1-Polynomial.X : Polynomial ℝ)^h (m+1)) (h (m+1)) := by
    have hhk : h (m+1) = 2*k := by omega
    rw [hhk, pow_mul]
    exact pal_pow hsquare k
  have hrpal := pal_mul hp (Q_pal (m+1) hd)
  refine ⟨hdeg.trans htotal,?_,hlc,h0,hne⟩
  change (R m).reflect (R m).natDegree = R m
  rw [hdeg]
  exact hrpal.2

private theorem I_pow_mod_four (n : ℕ) : Complex.I^n = Complex.I^(n%4) := by
  conv_lhs => rw [← Nat.mod_add_div n 4]
  rw [pow_add,pow_mul]
  norm_num

private theorem S_eval_I (n : ℕ) :
    (S n).eval₂ Complex.ofRealHom Complex.I =
      (1-Complex.I^n)/(1-Complex.I) := by
  apply (eq_div_iff (by norm_num [Complex.ext_iff] : (1-Complex.I : ℂ) ≠ 0)).mpr
  simpa only [S,Polynomial.eval₂_finsetSum,Polynomial.eval₂_pow,Polynomial.eval₂_X] using geom_sum_mul_neg Complex.I n

private theorem S_I_cases (n : ℕ) :
    (S n).eval₂ Complex.ofRealHom Complex.I =
      if n%4=0 then 0 else if n%4=1 then 1 else if n%4=2 then 1+Complex.I else Complex.I := by
  rw [S_eval_I,I_pow_mod_four]
  have hn : n%4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases hn' : n%4
  · norm_num
  · norm_num [show (1-Complex.I:ℂ) ≠ 0 by norm_num [Complex.ext_iff]]
  · norm_num
    apply (div_eq_iff (by norm_num [Complex.ext_iff] : (1-Complex.I:ℂ) ≠ 0)).mpr
    ring_nf
    norm_num [Complex.I_sq]
  · norm_num
    apply (div_eq_iff (by norm_num [Complex.ext_iff] : (1-Complex.I:ℂ) ≠ 0)).mpr
    ring_nf
    norm_num [Complex.I_sq]
    ring

private theorem H_eval_I (n : ℕ) :
    (H n).eval₂ Complex.ofRealHom Complex.I = 1+Complex.I^(n%4) := by
  simp only [H,Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_pow,Polynomial.eval₂_X]
  rw [I_pow_mod_four]

theorem Q_eval_I (d : ℕ) :
    (Q d).eval₂ Complex.ofRealHom Complex.I =
      if d%4 = 0 then ((4*(8*(d:ℝ)*(2*d-1))+8*(16*((d:ℝ)-1))+72 : ℝ) : ℂ)
      else if d%4 = 1 then ((2*(8*(d:ℝ)*(2*d-1))+2*(16*((d:ℝ)-1))+18 : ℝ) : ℂ)
      else if d%4 = 2 then 0
      else ((-2*(16*((d:ℝ)-1))-18 : ℝ) : ℂ) := by
  have hm : d%4 < 4 := Nat.mod_lt d (by norm_num)
  interval_cases he : d%4
  all_goals
    have h1 : (d+1)%4 = (d%4+1)%4 := Nat.add_mod d 1 4
    have h2 : (d+2)%4 = (d%4+2)%4 := Nat.add_mod d 2 4
    norm_num [he] at h1 h2
    have ho : Odd d ↔ d%4=1 ∨ d%4=3 := by rw [Nat.odd_iff]; omega
    simp only [Q,Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_pow,
      Polynomial.eval₂_C,Polynomial.eval₂_one,Polynomial.eval₂_X]
    simp only [U,V,W,ho,he,ite_true,ite_false,or_false,false_or,or_true,
      H_eval_I,S_I_cases,h1,h2]
    norm_num
    norm_num [H_eval_I,S_I_cases,he,h1,h2,Nat.add_comm 1 d,Nat.add_comm 2 d] <;>
      push_cast <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

private theorem Q_I_iff (d : ℕ) (hd : 2 ≤ d) :
    (Q d).eval₂ Complex.ofRealHom Complex.I = 0 ↔ d%4 = 2 := by
  rw [Q_eval_I]
  have hx : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hE : 0 < 8*(d:ℝ)*(2*d-1) := by
    have hh : 0 < 2*(d:ℝ)-1 := by linarith
    positivity
  have hG : 0 < 16*((d:ℝ)-1) := by linarith
  split_ifs with h0 h1 h2
  · rw [Complex.ofReal_eq_zero]; constructor <;> intro h
    · exfalso; linarith
    · omega
  · rw [Complex.ofReal_eq_zero]; constructor <;> intro h
    · exfalso; linarith
    · omega
  · simp [h2]
  · rw [Complex.ofReal_eq_zero]; constructor <;> intro h
    · exfalso; linarith
    · contradiction

theorem candidate_I_iff (m : ℕ) (hm : 1 ≤ m) :
    ((R m).map Complex.ofRealHom).IsRoot Complex.I ↔ m%4 = 1 := by
  change ((R m).map Complex.ofRealHom).eval Complex.I = 0 ↔ _
  rw [Polynomial.eval_map]
  simp only [R,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_sub,
    Polynomial.eval₂_one,Polynomial.eval₂_X]
  rw [mul_eq_zero]
  have hf : (1-Complex.I : ℂ)^h (m+1) ≠ 0 := pow_ne_zero _ (by norm_num [Complex.ext_iff])
  simp only [hf,false_or,Q_I_iff (m+1) (by omega)]
  omega

theorem candidate_neg_I_iff (m : ℕ) (hm : 1 ≤ m) :
    ((R m).map Complex.ofRealHom).IsRoot (-Complex.I) ↔ m%4 = 1 := by
  have he : ((R m).map Complex.ofRealHom).IsRoot (-Complex.I) ↔
      ((R m).map Complex.ofRealHom).IsRoot Complex.I := by
    simp only [Polynomial.IsRoot,Polynomial.eval_map]
    change Polynomial.aeval (-Complex.I) (R m) = 0 ↔
      Polynomial.aeval Complex.I (R m) = 0
    have hh : Polynomial.aeval (-Complex.I) (R m) = star (Polynomial.aeval Complex.I (R m)) := by
      have h := Polynomial.aeval_conj (R m) Complex.I
      change Polynomial.aeval (star Complex.I) (R m) = star (Polynomial.aeval Complex.I (R m)) at h
      have hi : star Complex.I = -Complex.I := by apply Complex.ext <;> norm_num
      rw [hi] at h
      exact h
    rw [hh,star_eq_zero]

  exact he.trans (candidate_I_iff m hm)

private theorem H_derivative (r : ℕ) : (H r).derivative =
    Polynomial.C (r:ℝ)*Polynomial.X^(r-1) := by
  simp [H,Polynomial.derivative_X_pow]

theorem Q_derivative_I (d : ℕ) (hd : d%4 = 2) :
    (Q d).derivative.eval₂ Complex.ofRealHom Complex.I =
      ((8*(d:ℝ)^4+16*(d:ℝ)^2*(2*d-1):ℝ):ℂ) := by
  have ho : ¬ Odd d := by rw [Nat.odd_iff]; omega
  have hd1 : (d-1)%4 = 1 := by omega
  have hd2 : (d+1)%4 = 3 := by omega
  have hd3 : (d+2)%4 = 0 := by omega
  have hu : (U d).eval₂ Complex.ofRealHom Complex.I = 0 := by
    simp only [U,ho,ite_false,H,Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_pow,Polynomial.eval₂_X]
    rw [I_pow_mod_four d,hd]
    norm_num
  have hv : (V d).eval₂ Complex.ofRealHom Complex.I = 1-Complex.I := by
    simp only [V,ho,ite_false,H,Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_pow,Polynomial.eval₂_X]
    rw [I_pow_mod_four (d+1),hd2]
    norm_num [pow_succ,Complex.I_sq] <;> ring
  have hdu : (U d).derivative.eval₂ Complex.ofRealHom Complex.I = (d:ℂ)*Complex.I := by
    simp only [U,ho,ite_false,H_derivative,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,Polynomial.eval₂_X]
    rw [I_pow_mod_four (d-1),hd1]
    norm_num
  simp only [Q,Polynomial.derivative_add,Polynomial.derivative_mul,
    Polynomial.derivative_C,Polynomial.derivative_pow,
    Polynomial.derivative_one,Polynomial.derivative_X,
    Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_pow,
    Polynomial.eval₂_C,Polynomial.eval₂_zero,Polynomial.eval₂_one,
    Polynomial.eval₂_X,hu,hv,hdu,zero_mul,mul_zero,zero_add,add_zero,
    pow_one,pow_zero]
  norm_num [H,H_derivative]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]
  ring

private theorem Q_I_simple (d : ℕ) (hd : 2 ≤ d) (hi : d%4 = 2) :
    Polynomial.rootMultiplicity Complex.I ((Q d).map Complex.ofRealHom) = 1 := by
  have hq := candidate_degree_reciprocity d hd
  have hn : (Q d).map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_eq_zero_iff Complex.ofReal_injective).not.mpr hq.2.2.2.2
  have hr : ((Q d).map Complex.ofRealHom).IsRoot Complex.I := by
    rw [Polynomial.IsRoot,Polynomial.eval_map,Q_I_iff d hd]
    exact hi
  have hder : ¬ (((Q d).map Complex.ofRealHom).derivative).IsRoot Complex.I := by
    rw [Polynomial.IsRoot,Polynomial.derivative_map,Polynomial.eval_map,Q_derivative_I d hi,
      Complex.ofReal_eq_zero]
    have hx : (2:ℝ) ≤ d := by exact_mod_cast hd
    have hp : 0 < (d:ℝ) := by linarith
    have ht : 0 < 2*(d:ℝ)-1 := by linarith
    have hh : 0 < 8*(d:ℝ)^4+16*(d:ℝ)^2*(2*d-1) := by positivity
    exact ne_of_gt hh
  have hpos := (Polynomial.rootMultiplicity_pos hn).mpr hr
  have hle : Polynomial.rootMultiplicity Complex.I ((Q d).map Complex.ofRealHom) ≤ 1 := by
    by_contra h
    have hh := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hn).mp (by omega :
      1 < Polynomial.rootMultiplicity Complex.I ((Q d).map Complex.ofRealHom))
    exact hder hh.2
  omega

theorem candidate_I_simple (m : ℕ) (hm : 1 ≤ m) (hi : m%4 = 1) :
    Polynomial.rootMultiplicity Complex.I ((R m).map Complex.ofRealHom) = 1 := by
  have hne := (candidate_R_structure m hm).2.2.2.2
  have hmap : (R m).map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_eq_zero_iff Complex.ofReal_injective).not.mpr hne
  have hf : ¬ (((1-Polynomial.X : Polynomial ℝ)^h (m+1)).map
      Complex.ofRealHom).IsRoot Complex.I := by
    simp only [Polynomial.IsRoot,Polynomial.eval_map,Polynomial.eval₂_pow,
      Polynomial.eval₂_sub,Polynomial.eval₂_one,Polynomial.eval₂_X]
    exact pow_ne_zero _ (by norm_num [Complex.ext_iff])
  rw [R,Polynomial.map_mul]
  change Polynomial.rootMultiplicity Complex.I
    ((((1-Polynomial.X : Polynomial ℝ)^h (m+1)).map Complex.ofRealHom)*
      ((Q (m+1)).map Complex.ofRealHom)) = 1
  have hn : (((1-Polynomial.X : Polynomial ℝ)^h (m+1)).map Complex.ofRealHom)*
      ((Q (m+1)).map Complex.ofRealHom) ≠ 0 := by
    simpa only [R,Polynomial.map_mul] using hmap
  rw [Polynomial.rootMultiplicity_mul hn,Polynomial.rootMultiplicity_eq_zero hf,zero_add]
  exact Q_I_simple (m+1) (by omega) (by omega)

theorem candidate_neg_I_simple (m : ℕ) (hm : 1 ≤ m) (hi : m%4 = 1) :
    Polynomial.rootMultiplicity (-Complex.I) ((R m).map Complex.ofRealHom) = 1 := by
  have he : ((R m).map Complex.ofRealHom).map (starRingEnd ℂ) =
      (R m).map Complex.ofRealHom := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    simp
  have h := Polynomial.eq_rootMultiplicity_map (p:=(R m).map Complex.ofRealHom)
    (f:=starRingEnd ℂ) star_injective Complex.I
  rw [he,candidate_I_simple m hm hi] at h
  simpa using h.symm

noncomputable def phaseValue (d : ℕ) (theta : ℝ) : ℂ :=
  Complex.exp (-((N d:ℕ):ℂ)*(theta:ℂ)*Complex.I) *
    (Q d).eval₂ Complex.ofRealHom (Complex.exp ((theta:ℂ)*Complex.I))

theorem phaseValue_real (d : ℕ) (hd : 2 ≤ d) (theta : ℝ) :
    (phaseValue d theta).im = 0 := by
  let z := Complex.exp ((theta:ℂ)*Complex.I)
  let ph := Complex.exp (-((N d:ℕ):ℂ)*(theta:ℂ)*Complex.I)
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  letI : Invertible z := invertibleOfNonzero hz0
  have hz : star z = z⁻¹ := by
    dsimp [z]
    rw [← Complex.exp_conj,← Complex.exp_neg]
    congr 1
    simp
  have hc : (Q d).eval₂ Complex.ofRealHom (star z) =
      star ((Q d).eval₂ Complex.ofRealHom z) :=
    Polynomial.aeval_conj (Q d) z
  have hq : star ((Q d).eval₂ Complex.ofRealHom z)*z^(2*N d) =
      (Q d).eval₂ Complex.ofRealHom z := by
    have hp := Q_pal d hd
    have he := Polynomial.eval₂_reflect_mul_pow Complex.ofRealHom z (2*N d) (Q d) hp.1
    rw [hp.2] at he
    simpa only [invOf_eq_inv,← hz,hc] using he
  have he : ph*z^(2*N d) = star ph := by
    dsimp [ph,z]
    rw [← Complex.exp_nat_mul,← Complex.exp_add,← Complex.exp_conj]
    congr 1
    push_cast
    simp only [map_mul, map_neg, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [← Complex.conj_eq_iff_im]
  change star (ph*(Q d).eval₂ Complex.ofRealHom z) = ph*(Q d).eval₂ Complex.ofRealHom z
  rw [star_mul',← he]
  calc
    ph*z^(2*N d)*star ((Q d).eval₂ Complex.ofRealHom z) =
        ph*(star ((Q d).eval₂ Complex.ofRealHom z)*z^(2*N d)) := by ring
    _ = ph*(Q d).eval₂ Complex.ofRealHom z := by rw [hq]

theorem phaseValue_zero_iff (d : ℕ) (theta : ℝ) :
    phaseValue d theta = 0 ↔
      ((Q d).map Complex.ofRealHom).IsRoot (Complex.exp ((theta:ℂ)*Complex.I)) := by
  simp only [phaseValue,mul_eq_zero,Complex.exp_ne_zero,false_or,
    Polynomial.IsRoot,Polynomial.eval_map]

theorem phaseValue_continuous (d : ℕ) : Continuous (phaseValue d) := by
  unfold phaseValue
  fun_prop




end FiolDoubleHub

end D5.S3.Zeros.LeeYang

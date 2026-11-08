/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapLateSign
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapLateSign
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite binomial recurrence gives a late strict actual quotient return gap. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Mathematical continuation: weighted finite binomial recurrence.

Write n=2a-p, A=choose(n,a), B=choose(n,a+p), D=choose(n,a+4p).
All indices are on the decreasing half of the binomial row.  The exact
recurrence, with f(k)=choose(n,k), reads

  (f(k)-f(k+1))*(k+1) = f(k)*(2k+1-n).

For k=a+i, 0<=i<p, bound f(k) by A and k+1 from below by a.
Summing the numerators p+2i+1 gives 2p^2, hence
  A*(a-2p^2) <= B*a.
For k=a+p+i, 0<=i<3p, bound f(k) from below by D and k+1
from above by a+4p.  The numerators sum to 18p^2, hence
  D*(a+4p+18p^2) <= B*(a+4p).

Put u=a-2p^2 and v=a+4p+18p^2.  If 2a>9p^2+p then u,v>0 and
  2uv-a*v-(a+4p)*u = 8p^2*(2a-p-9p^2) > 0.
The two weighted bounds and B>0 therefore give (A+D)uv<2Buv,
so A+D<2B.  No asymptotic or finite numerical evidence is used.

In the actual odd-wrap formulas a=3pt, n=p(6t-1); the sufficient
condition becomes 6t>9p+1.  In particular t>=2p is sufficient for p>=3.
The original restrictions p>=3, p odd and t>=2 are retained in the
actual quotient conclusion below.  No claim is made outside this cone.

proof_shape: actual_late_odd_wrap_sign: content.
admission_basis: escape-witness.
escape_witness: two weighted finite sums of adjacent binomial drops yield
A*(a-2*p^2)<=B*a and D*(a+4*p+18*p^2)<=B*(a+4*p).
Their strict positive surplus is used on the live proof path of the actual
quotient comparison. Helpers have actual consumers. No count or sign
conclusion is assumed. All parameters range over an unbounded symbolic
domain, so utility none applies; no finite certified-instance is delivered.

Repository/library reuse checked:
* Nat.choose_succ_right_eq is the exact adjacent-index recurrence.
* Nat.choose_pos supplies B>0.
* The library has choose_le_succ_of_lt_half_left / choose_le_middle,
  but no matching additive three-index comparison was found.
* actual_odd_wrap_counts supplies the actual full-domain quotient counts.
-/


set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign

open NearSquareLatticeRigidity BajnokBeattyFirstReturnDefect
open BajnokBeattyOddWrapReturnCounts

private abbrev c (n k : ℕ) : ℤ := Nat.choose n k

theorem choose_step_noninc (n k : ℕ) (hk : k ≤ n)
    (hhalf : n ≤ 2*k+1) : Nat.choose n (k+1) ≤ Nat.choose n k := by
  have hfactor : n-k ≤ k+1 := by omega
  have h := Nat.mul_le_mul_left (Nat.choose n k) hfactor
  rw [← Nat.choose_succ_right_eq] at h
  exact Nat.le_of_mul_le_mul_right h (by omega)

theorem choose_right_le (n u v : ℕ) (hhalf : n ≤ 2*u+1)
    (huv : u ≤ v) (hv : v ≤ n) : Nat.choose n v ≤ Nat.choose n u := by
  have hshift : ∀ r : ℕ, u+r ≤ n → Nat.choose n (u+r) ≤ Nat.choose n u := by
    intro r
    induction r with
    | zero => intro hr; simp
    | succ r ih =>
      intro hr
      have hprev := ih (by omega)
      have hstep := choose_step_noninc n (u+r) (by omega) (by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hstep.trans hprev
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le huv
  exact hshift r hv

theorem choose_drop_identity (n k : ℕ) (hk : k ≤ n) :
    (c n k-c n (k+1))*((k : ℤ)+1) =
      c n k*(2*(k : ℤ)+1-(n : ℤ)) := by
  have hnat := Nat.choose_succ_right_eq n k
  have hcast : (Nat.choose n (k+1) : ℤ)*((k : ℤ)+1) =
      (Nat.choose n k : ℤ)*((n-k : ℕ) : ℤ) := by exact_mod_cast hnat
  rw [Nat.cast_sub hk] at hcast
  dsimp only [c]
  nlinarith only [hcast]

theorem sum_drops (f : ℕ → ℤ) (a r : ℕ) :
    (∑ i ∈ Finset.range r, (f (a+i)-f (a+i+1))) = f a-f (a+r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show a+(r+1) = a+r+1 by omega]
    ring

theorem sum_linear_numerators (b r : ℕ) :
    (∑ i ∈ Finset.range r, ((b : ℤ)+2*(i : ℤ)+1)) =
      (r : ℤ)*b+(r : ℤ)^2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem two_block_bounds (n a p : ℕ) (hp : 0 < p)
    (hn : n+p = 2*a) (ha : a+4*p ≤ n) :
    c n a*((a : ℤ)-2*(p : ℤ)^2) ≤ c n (a+p)*(a : ℤ) ∧
    c n (a+4*p)*((a : ℤ)+4*p+18*(p : ℤ)^2) ≤
      c n (a+p)*((a : ℤ)+4*p) := by
  have hnZ : (n : ℤ)+(p : ℤ) = 2*(a : ℤ) := by exact_mod_cast hn
  have hfirst (i : ℕ) (hi : i < p) :
      (c n (a+i)-c n (a+i+1))*(a : ℤ) ≤
        c n a*((p : ℤ)+2*(i : ℤ)+1) := by
    have hk : a+i ≤ n := by omega
    have hstep := choose_step_noninc n (a+i) hk (by omega)
    have hstepZ : c n (a+i+1) ≤ c n (a+i) := by exact_mod_cast hstep
    have hdrop : 0 ≤ c n (a+i)-c n (a+i+1) := by omega
    have hupper : c n (a+i) ≤ c n a := by
      exact_mod_cast (choose_right_le n a (a+i) (by omega) (by omega) hk)
    have hnum : 2*((a+i : ℕ) : ℤ)+1-(n : ℤ) =
        (p : ℤ)+2*(i : ℤ)+1 := by push_cast; omega
    have hid := choose_drop_identity n (a+i) hk
    rw [hnum] at hid
    calc
      (c n (a+i)-c n (a+i+1))*(a : ℤ) ≤
          (c n (a+i)-c n (a+i+1))*(((a+i : ℕ) : ℤ)+1) :=
        mul_le_mul_of_nonneg_left (by push_cast; omega) hdrop
      _ = c n (a+i)*((p : ℤ)+2*(i : ℤ)+1) := hid
      _ ≤ c n a*((p : ℤ)+2*(i : ℤ)+1) :=
        mul_le_mul_of_nonneg_right hupper (by positivity)
  have hfirstSum : (c n a-c n (a+p))*(a : ℤ) ≤ c n a*(2*(p : ℤ)^2) := by
    have hs := Finset.sum_le_sum (fun i hi => hfirst i (Finset.mem_range.mp hi))
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_drops,
      sum_linear_numerators] at hs
    nlinarith only [hs]
  have hsecond (i : ℕ) (hi : i < 3*p) :
      c n (a+4*p)*(((3*p : ℕ) : ℤ)+2*(i : ℤ)+1) ≤
        (c n (a+p+i)-c n (a+p+i+1))*((a : ℤ)+4*p) := by
    have hk : a+p+i ≤ n := by omega
    have hstep := choose_step_noninc n (a+p+i) hk (by omega)
    have hstepZ : c n (a+p+i+1) ≤ c n (a+p+i) := by exact_mod_cast hstep
    have hdrop : 0 ≤ c n (a+p+i)-c n (a+p+i+1) := by omega
    have hlower : c n (a+4*p) ≤ c n (a+p+i) := by
      exact_mod_cast (choose_right_le n (a+p+i) (a+4*p)
        (by omega) (by omega) ha)
    have hnum : 2*((a+p+i : ℕ) : ℤ)+1-(n : ℤ) =
        ((3*p : ℕ) : ℤ)+2*(i : ℤ)+1 := by push_cast; omega
    have hid := choose_drop_identity n (a+p+i) hk
    rw [hnum] at hid
    calc
      c n (a+4*p)*(((3*p : ℕ) : ℤ)+2*(i : ℤ)+1) ≤
          c n (a+p+i)*(((3*p : ℕ) : ℤ)+2*(i : ℤ)+1) :=
        mul_le_mul_of_nonneg_right hlower (by positivity)
      _ = (c n (a+p+i)-c n (a+p+i+1))*(((a+p+i : ℕ) : ℤ)+1) := hid.symm
      _ ≤ (c n (a+p+i)-c n (a+p+i+1))*((a : ℤ)+4*p) :=
        mul_le_mul_of_nonneg_left (by push_cast; omega) hdrop
  have hsecondSum : c n (a+4*p)*(18*(p : ℤ)^2) ≤
      (c n (a+p)-c n (a+4*p))*((a : ℤ)+4*p) := by
    have hs := Finset.sum_le_sum (fun i hi => hsecond i (Finset.mem_range.mp hi))
    rw [← Finset.mul_sum, ← Finset.sum_mul, sum_drops,
      sum_linear_numerators] at hs
    rw [show a+p+3*p = a+4*p by omega] at hs
    push_cast at hs
    nlinarith only [hs]
  constructor <;> nlinarith only [hfirstSum, hsecondSum]

private theorem weighted_block_comparison (n a p : ℕ) (hp : 0 < p)
    (hn : n+p = 2*a) (ha : a+4*p ≤ n)
    (hcone : (p : ℤ)+9*(p : ℤ)^2 < 2*(a : ℤ)) :
    Nat.choose n a+Nat.choose n (a+4*p) < 2*Nat.choose n (a+p) := by
  let A : ℤ := c n a
  let B : ℤ := c n (a+p)
  let D : ℤ := c n (a+4*p)
  let u : ℤ := (a : ℤ)-2*(p : ℤ)^2
  let v : ℤ := (a : ℤ)+4*p+18*(p : ℤ)^2
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  have hu : 0 < u := by dsimp [u]; nlinarith [sq_nonneg (p : ℤ)]
  have hv : 0 < v := by dsimp [v]; positivity
  have hB : 0 < B := by
    dsimp [B, c]
    exact_mod_cast (Nat.choose_pos (show a+p ≤ n by omega))
  obtain ⟨hA, hD⟩ := two_block_bounds n a p hp hn ha
  change A*u ≤ B*(a : ℤ) at hA
  change D*v ≤ B*((a : ℤ)+4*p) at hD
  have hgap : (a : ℤ)*v+((a : ℤ)+4*p)*u < 2*u*v := by
    have hid : 2*u*v-((a : ℤ)*v+((a : ℤ)+4*p)*u) =
        8*(p : ℤ)^2*(2*(a : ℤ)-(p : ℤ)-9*(p : ℤ)^2) := by
      dsimp [u, v]
      ring
    have hpos : 0 < 8*(p : ℤ)^2*(2*(a : ℤ)-(p : ℤ)-9*(p : ℤ)^2) := by
      apply mul_pos
      · positivity
      · linarith only [hcone]
    linarith only [hid, hpos]
  have hweighted : (A+D)*(u*v) ≤ B*((a : ℤ)*v+((a : ℤ)+4*p)*u) := by
    calc
      (A+D)*(u*v) = (A*u)*v+(D*v)*u := by ring
      _ ≤ (B*(a : ℤ))*v+(B*((a : ℤ)+4*p))*u :=
        add_le_add (mul_le_mul_of_nonneg_right hA hv.le)
          (mul_le_mul_of_nonneg_right hD hu.le)
      _ = B*((a : ℤ)*v+((a : ℤ)+4*p)*u) := by ring
  have hscaled : (A+D)*(u*v) < (2*B)*(u*v) := by
    calc
      (A+D)*(u*v) ≤ B*((a : ℤ)*v+((a : ℤ)+4*p)*u) := hweighted
      _ < B*(2*u*v) := mul_lt_mul_of_pos_left hgap hB
      _ = (2*B)*(u*v) := by ring
  have hfinal : A+D < 2*B := (mul_lt_mul_iff_left₀ (mul_pos hu hv)).mp hscaled
  dsimp [A, B, D, c] at hfinal
  exact_mod_cast hfinal

/-- A finite-recurrence sufficient cone for the exact odd-wrap binomials.
The p,t hypotheses are integers, matching the actual quotient theorem. -/
private theorem late_binomial_comparison (p t : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t)
    (hcone : 9*p+1 < 6*t) :
    let N : ℕ := (p*(6*t-1)).toNat
    Nat.choose N (p*(3*t)).toNat+Nat.choose N (p*(3*t+4)).toNat <
      2*Nat.choose N (p*(3*t+1)).toNat := by
  let N : ℕ := (p*(6*t-1)).toNat
  let a : ℕ := (3*p*t).toNat
  let P : ℕ := p.toNat
  have hp : 0 < p := by omega
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg hp.le
  have ha : (a : ℤ) = 3*p*t := Int.toNat_of_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hp.le) (by omega))
  have hN : (N : ℤ) = p*(6*t-1) := Int.toNat_of_nonneg
    (mul_nonneg hp.le (by omega))
  have hPpos : 0 < P := by exact_mod_cast (show 0 < (P : ℤ) by rw [hP]; exact hp)
  have hNa : N+P = 2*a := by
    have hh : (N : ℤ)+(P : ℤ) = 2*(a : ℤ) := by rw [hN, hP, ha]; ring
    exact_mod_cast hh
  have haN : a+4*P ≤ N := by
    have htail := mul_nonneg hp.le (show 0 ≤ 3*t-5 by omega)
    have hh : (a : ℤ)+4*(P : ℤ) ≤ (N : ℤ) := by
      rw [ha, hP, hN]
      nlinarith only [htail]
    exact_mod_cast hh
  have hquad : (P : ℤ)+9*(P : ℤ)^2 < 2*(a : ℤ) := by
    have hh := mul_lt_mul_of_pos_left hcone hp
    rw [hP, ha]
    nlinarith only [hh]
  have hmain := weighted_block_comparison N a P hPpos hNa haN hquad
  have h0 : a = (p*(3*t)).toNat := by dsimp [a]; congr 1; ring
  have h1 : a+P = (p*(3*t+1)).toNat := by
    have hh : ((a+P : ℕ) : ℤ) = ((p*(3*t+1)).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (mul_nonneg hp.le (show 0 ≤ 3*t+1 by omega))]
      push_cast
      rw [ha, hP]
      ring
    exact_mod_cast hh
  have h4 : a+4*P = (p*(3*t+4)).toNat := by
    have hh : ((a+4*P : ℕ) : ℤ) = ((p*(3*t+4)).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (mul_nonneg hp.le (show 0 ≤ 3*t+4 by omega))]
      push_cast
      rw [ha, hP]
      ring
    exact_mod_cast hh
  change Nat.choose N (p*(3*t)).toNat+Nat.choose N (p*(3*t+4)).toNat <
    2*Nat.choose N (p*(3*t+1)).toNat
  rw [h4, h1, h0] at hmain
  exact hmain

/-- A late positive gap for the same full actual quotient maps. -/
theorem actual_late_odd_wrap_sign (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) (hcone : 9*p+1 < 6*t) :
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let L : ℕ := (p*m).toNat
    W F19 L < W F33 L := by
  have hc := actual_odd_wrap_counts p t hp3 hpo ht
  have hb := late_binomial_comparison p t hp3 ht hcone
  have h1 : p*((6*t-1)+1)/2 = p*(3*t) := by
    have he : p*((6*t-1)+1) = 2*(p*(3*t)) := by ring
    omega
  have h3 : p*((6*t-1)+3)/2 = p*(3*t+1) := by
    have he : p*((6*t-1)+3) = 2*(p*(3*t+1)) := by ring
    omega
  have h9 : p*((6*t-1)+9)/2 = p*(3*t+4) := by
    have he : p*((6*t-1)+9) = 2*(p*(3*t+4)) := by ring
    omega
  dsimp only at hc hb ⊢
  rw [hc.1, hc.2, h1, h3, h9]
  omega

end D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign

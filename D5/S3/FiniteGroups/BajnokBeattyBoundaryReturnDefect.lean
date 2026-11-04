/- GID: D5/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact first reversal and full pre-wrap quotient return counts. -/

import D5.S3.FiniteGroups.BajnokBeattyShortReturnBand
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
proof_shape: first_return_reversal: content; prewrap_return_reversal: content.
admission_basis: escape-witness.
escape_witness: an exact disjoint decomposition of the two actual quotient
return fibers at their first competing lattice relation, a strict product and
Vandermonde comparison, and an exhaustive parity split of all earlier lengths.
The pre-wrap estimate follows from a strict two-step binomial-ratio comparison
using a polynomial factorization and induction.
The existing endpoint and short-relation suppliers are consumed directly.
No kernel classification, endpoint count or sign comparison is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect
open NearSquareLatticeRigidity BajnokBeattyAsymmetricGrowth
open BajnokBeattyFirstReturnDefect

private theorem factor_le (M p i : ℕ) (hp : 2 ≤ p) (hM : 5*p ≤ M)
    (hi : i < p) :
    (2*p-i)*(M+5*p-i) ≤ (M-p-i)*(M-i) := by
  have h1 : ((M-p-i : ℕ) : ℤ) = (M:ℤ)-p-i := by omega
  have h2 : ((M-i : ℕ) : ℤ) = (M:ℤ)-i := by omega
  have h3 : ((2*p-i : ℕ) : ℤ) = 2*(p:ℤ)-i := by omega
  have h4 : ((M+5*p-i : ℕ) : ℤ) = (M:ℤ)+5*p-i := by omega
  have hprod : 0 ≤ ((M:ℤ)-5*p)*((M:ℤ)+2*p-i) :=
    mul_nonneg (by omega) (by omega)
  have hpi : 0 ≤ (3:ℤ)*p*i := by positivity
  apply Int.ofNat_le.mp
  push_cast
  rw [h1,h2,h3,h4]
  nlinarith

private theorem factor_one_lt (M p : ℕ) (hp : 2 ≤ p) (hM : 5*p ≤ M) :
    (2*p-1)*(M+5*p-1) < (M-p-1)*(M-1) := by
  have h1 : ((M-p-1 : ℕ) : ℤ) = (M:ℤ)-p-1 := by omega
  have h2 : ((M-1 : ℕ) : ℤ) = (M:ℤ)-1 := by omega
  have h3 : ((2*p-1 : ℕ) : ℤ) = 2*(p:ℤ)-1 := by omega
  have h4 : ((M+5*p-1 : ℕ) : ℤ) = (M:ℤ)+5*p-1 := by omega
  have hprod : 0 ≤ ((M:ℤ)-5*p)*((M:ℤ)+2*p-1) :=
    mul_nonneg (by omega) (by omega)
  apply Int.ofNat_lt.mp
  push_cast
  rw [h1,h2,h3,h4]
  nlinarith

private theorem shifted_choose_lt (M p : ℕ) (hp : 2 ≤ p) (hM : 5*p ≤ M) :
    (M+5*p).choose p < M.choose (2*p) := by
  have hprod :
      (∏ i ∈ Finset.range p, (2*p-i)*(M+5*p-i)) <
        ∏ i ∈ Finset.range p, (M-p-i)*(M-i) := by
    apply Finset.prod_lt_prod₀
    · intro i hi
      apply Nat.mul_pos <;> have := Finset.mem_range.mp hi <;> omega
    · intro i hi
      exact factor_le M p i hp hM (Finset.mem_range.mp hi)
    · exact ⟨1, Finset.mem_range.mpr (by omega), factor_one_lt M p hp hM⟩
  have hleft : (∏ i ∈ Finset.range p, (M-p-i)*(M-i)) =
      (2*p).factorial * M.choose (2*p) := by
    rw [Finset.prod_mul_distrib,
      ← Nat.descFactorial_eq_prod_range (M-p) p,
      ← Nat.descFactorial_eq_prod_range M p]
    have hs := Nat.descFactorial_mul_descFactorial
      (n := M) (k := p) (m := 2*p) (by omega)
    rw [show 2*p-p = p by omega] at hs
    rw [hs, Nat.descFactorial_eq_factorial_mul_choose]
  have hright : (∏ i ∈ Finset.range p, (2*p-i)*(M+5*p-i)) =
      (2*p).factorial * (M+5*p).choose p := by
    rw [Finset.prod_mul_distrib,
      ← Nat.descFactorial_eq_prod_range (2*p) p,
      ← Nat.descFactorial_eq_prod_range (M+5*p) p,
      Nat.descFactorial_eq_factorial_mul_choose (M+5*p) p]
    have hf := Nat.factorial_mul_descFactorial (n := 2*p) (k := p) (by omega)
    rw [show 2*p-p = p by omega] at hf
    calc
      _ = (p.factorial * (2*p).descFactorial p) * (M+5*p).choose p := by ring
      _ = _ := by rw [hf]
  rw [hleft,hright] at hprod
  by_contra h
  exact Nat.not_lt_of_ge (Nat.mul_le_mul_left ((2*p).factorial)
    (Nat.le_of_not_gt h)) hprod

/-- The consumed binomial comparison needs no parity or primality hypothesis. -/
private theorem quartic_choose_dominates_square (N p : ℕ) (hp : 2 ≤ p)
    (hN : 10*p ≤ N) : N.choose p ^ 2 < N.choose (4*p) := by
  let M := N-5*p
  have hM : 5*p ≤ M := by dsimp [M]; omega
  have hN' : M+5*p = N := by dsimp [M]; omega
  have hshift : N.choose p < M.choose (2*p) := by
    simpa only [hN'] using shifted_choose_lt M p hp hM
  have hterm : (4*p).choose p * M.choose (2*p) ≤
      (N-p).choose (3*p) := by
    have hmem : (p,2*p) ∈ Finset.antidiagonal (3*p) := by
      exact Finset.mem_antidiagonal.mpr (by omega)
    have hs := Finset.single_le_sum
      (fun ij (_ : ij ∈ Finset.antidiagonal (3*p)) =>
        Nat.zero_le ((4*p).choose ij.1 * M.choose ij.2)) hmem
    rw [← Nat.add_choose_eq] at hs
    simpa only [show 4*p+M = N-p by omega] using hs
  have hcomb := Nat.choose_mul (n := N) (k := 4*p) (s := p) (by omega)
  rw [show 4*p-p = 3*p by omega] at hcomb
  have hpos : 0 < N.choose p := Nat.choose_pos (by omega)
  have hpos' : 0 < (4*p).choose p := Nat.choose_pos (by omega)
  have hstrict := Nat.mul_lt_mul_of_pos_left hshift (Nat.mul_pos hpos hpos')
  have hbound := Nat.mul_le_mul_left (N.choose p) hterm
  have hfinal : (N.choose p ^ 2) * (4*p).choose p <
      N.choose (4*p) * (4*p).choose p := by
    nlinarith [hcomb]
  by_contra h
  exact Nat.not_lt_of_ge (Nat.mul_le_mul_right ((4*p).choose p)
    (Nat.le_of_not_gt h)) hfinal


private theorem choose_two_step_nat (N k : ℕ) :
    Nat.choose (N+2) (k+1) * (k+1) * (N+1-k) =
      Nat.choose N k * ((N+1)*(N+2)) := by
  have hfirst := Nat.add_one_mul_choose_eq (N+1) k
  have hsecond := Nat.choose_mul_succ_eq N k
  calc
    Nat.choose (N+2) (k+1) * (k+1) * (N+1-k) =
        ((N+2) * Nat.choose (N+1) k) * (N+1-k) := by
      rw [← hfirst]
    _ = (N+2) * (Nat.choose N k * (N+1)) := by
      rw [mul_assoc, ← hsecond]
    _ = Nat.choose N k * ((N+1)*(N+2)) := by ring

theorem choose_two_step_rat (N k : ℕ) (hk : k ≤ N) :
    (Nat.choose (N+2) (k+1) : ℚ) * ((k : ℚ)+1) * ((N : ℚ)+1-k) =
      (Nat.choose N k : ℚ) * (((N : ℚ)+1)*((N : ℚ)+2)) := by
  have hcast :
      (Nat.choose (N+2) (k+1) : ℚ) * ((k+1 : ℕ) : ℚ) *
          ((N+1-k : ℕ) : ℚ) =
        (Nat.choose N k : ℚ) * (((N+1)*(N+2) : ℕ) : ℚ) := by
    exact_mod_cast choose_two_step_nat N k
  rw [Nat.cast_sub (show k ≤ N+1 by omega)] at hcast
  push_cast at hcast
  exact hcast

private theorem band_step (L s a : ℕ) (ha : a ≤ L) :
    (Nat.choose (L+2*(s+1)) (a+s+1) : ℚ) *
        ((a : ℚ)+s+1) * ((L : ℚ)+s+1-a) =
      (Nat.choose (L+2*s) (a+s) : ℚ) *
        (((L : ℚ)+2*s+1)*((L : ℚ)+2*s+2)) := by
  have h := choose_two_step_rat (L+2*s) (a+s) (by omega)
  rw [show L+2*s+2 = L+2*(s+1) by omega] at h
  push_cast at h
  convert h using 1 <;> ring

-- A strict polynomial comparison controls the two-step binomial ratio.
private theorem ratio_factor_strict (p x u : ℚ)
    (hp : 0 < p) (hx : 7*p ≤ x) (hu : 0 ≤ u) (hu2 : 2*u ≤ p) :
    let B := u*(x+u)
    B*(B+4*p*(x-4*p)) < (B+p*(x-p))^2 := by
  dsimp only
  have hb : 0 ≤ p*(2*x+p)-4*(u*(x+u)) := by
    have h := mul_nonneg (show 0 ≤ p-2*u by linarith)
      (show 0 ≤ 2*x+p+2*u by linarith)
    nlinarith only [h]
  have hnonneg :
      0 ≤ 2*p*(x-7*p)*(p*(2*x+p)-4*(u*(x+u))) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) hb
  have hpos : 0 < 18*p^3*(x+p) := by
    have hxp : 0 < x+p := by linarith
    positivity
  have hid :
      4*((u*(x+u)+p*(x-p))^2-
        (u*(x+u))*(u*(x+u)+4*p*(x-4*p))) =
      2*p*(x-7*p)*(p*(2*x+p)-4*(u*(x+u)))+18*p^3*(x+p) := by
    ring
  nlinarith only [hid, hnonneg, hpos]

private theorem cross_of_rescaled_steps
    (x y z x' y' z' T A B C : ℚ)
    (hT : 0 < T) (hx' : 0 < x') (hy' : 0 < y') (hz' : 0 < z')
    (hx : x'*A = T*x) (hy : y'*C = T*y) (hz : z'*B = T*z)
    (hfactor : B*C < A^2) :
    (y*z)*x'^2 < (y'*z')*x^2 := by
  have hmiddle : x'^2*A^2 = T^2*x^2 := by
    calc
      x'^2*A^2 = (x'*A)^2 := by ring
      _ = (T*x)^2 := by rw [hx]
      _ = T^2*x^2 := by ring
  have houter : (y'*z')*(B*C) = T^2*(y*z) := by
    calc
      (y'*z')*(B*C) = (y'*C)*(z'*B) := by ring
      _ = (T*y)*(T*z) := by rw [hy,hz]
      _ = T^2*(y*z) := by ring
  have hscale : 0 < x'^2*(y'*z') := by positivity
  have hscaled := mul_lt_mul_of_pos_left hfactor hscale
  have hweighted : T^2*((y*z)*x'^2) < T^2*((y'*z')*x^2) := by
    calc
      T^2*((y*z)*x'^2) = x'^2*((y'*z')*(B*C)) := by
        rw [houter]
        ring
      _ < (y'*z')*(x'^2*A^2) := by
        convert hscaled using 1 <;> ring
      _ = T^2*((y'*z')*x^2) := by
        rw [hmiddle]
        ring
  exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos hT)).mp hweighted

-- This is R_(s+1)>R_s with no division and no hidden denominator premise.
private theorem shifted_binomial_cross_step (p L s : ℕ)
    (hp : 2 ≤ p) (hL : 10*p ≤ L) (hs : 2*(s+1) ≤ p) :
    ((Nat.choose (L+2*s) (4*p+s) : ℚ) *
        (Nat.choose (L+2*s) s : ℚ)) *
        (Nat.choose (L+2*(s+1)) (p+s+1) : ℚ)^2 <
      ((Nat.choose (L+2*(s+1)) (4*p+s+1) : ℚ) *
        (Nat.choose (L+2*(s+1)) (s+1) : ℚ)) *
        (Nat.choose (L+2*s) (p+s) : ℚ)^2 := by
  let u : ℚ := (s : ℚ)+1
  let B : ℚ := u*((L : ℚ)+u)
  let A : ℚ := B+(p : ℚ)*((L : ℚ)-p)
  let C : ℚ := B+4*(p : ℚ)*((L : ℚ)-4*p)
  let T : ℚ := ((L : ℚ)+2*s+1)*((L : ℚ)+2*s+2)
  have hpQ : 0 < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  have hLQ : 7*(p : ℚ) ≤ (L : ℚ) := by
    exact_mod_cast (show 7*p ≤ L by omega)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu2 : 2*u ≤ (p : ℚ) := by
    dsimp [u]
    exact_mod_cast hs
  have hfactor : B*C < A^2 := by
    exact ratio_factor_strict (p : ℚ) (L : ℚ) u hpQ hLQ hu hu2
  have hmid :
      (Nat.choose (L+2*(s+1)) (p+s+1) : ℚ)*A =
        T*(Nat.choose (L+2*s) (p+s) : ℚ) := by
    have h := band_step L s p (by omega)
    convert h using 1 <;> dsimp [A,B,T,u] <;> ring
  have hfour :
      (Nat.choose (L+2*(s+1)) (4*p+s+1) : ℚ)*C =
        T*(Nat.choose (L+2*s) (4*p+s) : ℚ) := by
    have h := band_step L s (4*p) (by omega)
    push_cast at h
    convert h using 1 <;> dsimp [C,B,T,u] <;> ring
  have hzero :
      (Nat.choose (L+2*(s+1)) (s+1) : ℚ)*B =
        T*(Nat.choose (L+2*s) s : ℚ) := by
    have h := band_step L s 0 (by omega)
    simp only [Nat.zero_add, Nat.cast_zero, zero_add, sub_zero] at h
    convert h using 1 <;> dsimp [B,T,u] <;> ring
  have hT : 0 < T := by dsimp [T]; positivity
  have hmidPos : 0 < (Nat.choose (L+2*(s+1)) (p+s+1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (show p+s+1 ≤ L+2*(s+1) by omega)
  have hfourPos : 0 < (Nat.choose (L+2*(s+1)) (4*p+s+1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (show 4*p+s+1 ≤ L+2*(s+1) by omega)
  have hzeroPos : 0 < (Nat.choose (L+2*(s+1)) (s+1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (show s+1 ≤ L+2*(s+1) by omega)
  exact cross_of_rescaled_steps _ _ _ _ _ _ T A B C
    hT hmidPos hfourPos hzeroPos hmid hfour hzero hfactor

private theorem prewrap_binomial_comparison (p L : ℕ)
    (hp : 2 ≤ p) (hL : 10*p ≤ L) :
    ∀ s : ℕ, 2*s < p →
      (Nat.choose (L+2*s) (p+s))^2 <
        Nat.choose (L+2*s) (4*p+s) * Nat.choose (L+2*s) s := by
  have hbase := quartic_choose_dominates_square L p hp hL
  intro s
  induction s with
  | zero =>
      intro hs
      simpa using hbase
  | succ s ih =>
      intro hs
      have hprev := ih (by omega)
      have hprevQ : (Nat.choose (L+2*s) (p+s) : ℚ)^2 <
          (Nat.choose (L+2*s) (4*p+s) : ℚ) *
            (Nat.choose (L+2*s) s : ℚ) := by
        exact_mod_cast hprev
      have hcross := shifted_binomial_cross_step p L s hp hL (by omega)
      have hq : 0 < (Nat.choose (L+2*s) (p+s) : ℚ)^2 := by
        have hc : 0 < (Nat.choose (L+2*s) (p+s) : ℚ) := by
          exact_mod_cast Nat.choose_pos (show p+s ≤ L+2*s by omega)
        positivity
      have hqnext : 0 < (Nat.choose (L+2*(s+1)) (p+s+1) : ℚ)^2 := by
        have hc : 0 < (Nat.choose (L+2*(s+1)) (p+s+1) : ℚ) := by
          exact_mod_cast Nat.choose_pos (show p+s+1 ≤ L+2*(s+1) by omega)
        positivity
      have hchain := lt_trans (mul_lt_mul_of_pos_right hprevQ hqnext) hcross
      have hnextQ : (Nat.choose (L+2*(s+1)) (p+s+1) : ℚ)^2 <
          (Nat.choose (L+2*(s+1)) (4*p+s+1) : ℚ) *
            (Nat.choose (L+2*(s+1)) (s+1) : ℚ) := by
        apply (mul_lt_mul_iff_left₀ hq).mp
        convert hchain using 1 <;> ring
      exact_mod_cast hnextQ


private theorem short_kernels (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6*t-1
    let n : ℤ := p*(m-3)
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    (∀ z : Plane, z ∈ K19 → |z 0|+|z 1| < p*m →
      z = 0 ∨ z = ![p*(m-5),-4*p] ∨ z = ![-(p*(m-5)),4*p]) ∧
    (∀ z : Plane, z ∈ K33 → |z 0|+|z 1| < p*m →
      z = 0 ∨ z = ![n,0] ∨ z = ![-n,0]) ∧
    (![n,0] : Plane) ∈ K33 ∧ (![-n,0] : Plane) ∈ K33 ∧
    (![p*(m-5),-4*p] : Plane) ∈ K19 ∧ (![-(p*(m-5)),4*p] : Plane) ∈ K19 := by
  let m : ℤ := 6*t-1
  let n : ℤ := p*(m-3)
  let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
  let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
  let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
  let K19 := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 := Submodule.span ℤ (Set.range ![v133, v233])
  change (∀ z : Plane, z ∈ K19 → |z 0|+|z 1| < p*m →
      z = 0 ∨ z = ![p*(m-5),-4*p] ∨ z = ![-(p*(m-5)),4*p]) ∧
    (∀ z : Plane, z ∈ K33 → |z 0|+|z 1| < p*m →
      z = 0 ∨ z = ![n,0] ∨ z = ![-n,0]) ∧
    (![n,0] : Plane) ∈ K33 ∧ (![-n,0] : Plane) ∈ K33 ∧
    (![p*(m-5),-4*p] : Plane) ∈ K19 ∧ (![-(p*(m-5)),4*p] : Plane) ∈ K19
  have hp : 0 < p := by omega
  have hm11 : 11 ≤ m := by dsimp [m]; omega
  have hmo : Odd m := by
    exact ⟨3*t-1, by dsimp [m]; ring⟩
  have h119 : 2*(p*(m-1)/2) = p*(m-1) := by
    have hd := ((hmo.sub_odd odd_one).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have h219 : 2*(p*(m+1)/2) = p*(m+1) := by
    have hd := ((hmo.add_odd odd_one).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have h319 : 2*(p*(m-9)/2) = p*(m-9) := by
    have hd := ((hmo.sub_odd (by decide : Odd (9:ℤ))).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have h419 : 2*(p*(m+9)/2) = p*(m+9) := by
    have hd := ((hmo.add_odd (by decide : Odd (9:ℤ))).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have h133 : 2*(p*(m-3)/2) = p*(m-3) := by
    have hd := ((hmo.sub_odd (by decide : Odd (3:ℤ))).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have hsum19 : v119+v219 = (![p*(m-5),-4*p] : Plane) := by
    ext i
    fin_cases i <;> dsimp [v119,v219] <;>
      nlinarith only [h119,h219,h319,h419]
  have hsum33 : v133+v233 = (![n,0] : Plane) := by
    ext i
    fin_cases i <;> dsimp [v133,v233,n] <;> omega
  have hn : 0 < n := by dsimp [n]; exact mul_pos hp (by omega)
  have hmin19 : 0 < p*(m-1) := mul_pos hp (by omega)
  have htwice : p*m < 2*n := by dsimp [n]; nlinarith
  have hposmem : (![n,0] : Plane) ∈ K33 := by
    rw [← hsum33]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  refine ⟨?_, ?_, hposmem, ?_, ?_, ?_⟩
  · intro z hz hnorm
    obtain ⟨k,hk⟩ := BajnokBeattyShortReturnBand.short_span p m 1 9 hp3 hpo hmo odd_one
      (by decide) (by norm_num) (by omega) (by norm_num) (by omega) z hz hnorm
    rw [hsum19] at hk
    have hzNorm : |z 0|+|z 1| = |k| * (p*(m-1)) := by
      rw [hk]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, abs_mul]
      norm_num [abs_of_pos hp, abs_of_nonneg (show 0 ≤ m-5 by omega)] <;> ring
    have hka : |k| < 2 := by nlinarith
    have hkcases : k=0 ∨ k=1 ∨ k= -1 := by
      have hkb := abs_lt.mp hka
      omega
    rcases hkcases with rfl | rfl | rfl
    · left; simpa using hk
    · right; left; simpa using hk
    · right; right
      rw [hk]
      ext i
      fin_cases i <;> simp
  · intro z hz hnorm
    obtain ⟨k,hk⟩ := BajnokBeattyShortReturnBand.short_span p m 3 3 hp3 hpo hmo (by decide)
      (by decide) (by norm_num) (by omega) (by norm_num) (by omega) z hz hnorm
    rw [hsum33] at hk
    have hzNorm : |z 0|+|z 1| = |k| * n := by
      rw [hk]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, abs_mul, abs_of_pos hn, mul_zero, abs_zero, add_zero]
    have hka : |k| < 2 := by nlinarith
    have hkcases : k=0 ∨ k=1 ∨ k= -1 := by
      have hkb := abs_lt.mp hka
      omega
    rcases hkcases with rfl | rfl | rfl
    · left; simpa using hk
    · right; left; simpa using hk
    · right; right
      rw [hk]
      ext i
      fin_cases i <;> simp
  · have hneg := K33.neg_mem hposmem
    simpa using hneg

  · rw [← hsum19]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  · have hpos : (![p*(m-5),-4*p] : Plane) ∈ K19 := by
      rw [← hsum19]
      apply Submodule.add_mem
      · exact Submodule.subset_span ⟨0, rfl⟩
      · exact Submodule.subset_span ⟨1, rfl⟩
    have hneg := K19.neg_mem hpos
    simpa using hneg

private theorem three_fiber_card (l : ℕ) (n y : ℤ) (hn : 0 < n) :
    Nat.card {w : Fin l → Fin 4 //
      endpoint w = 0 ∨ endpoint w = ![n,y] ∨ endpoint w = ![-n,-y]} =
    Nat.card {w : Fin l → Fin 4 // endpoint w = 0} +
      (Nat.card {w : Fin l → Fin 4 // endpoint w = ![n,y]} +
        Nat.card {w : Fin l → Fin 4 // endpoint w = ![-n,-y]}) := by
  classical
  have hzero : Disjoint (fun w : Fin l → Fin 4 => endpoint w = 0)
      (fun w => endpoint w = ![n,y] ∨ endpoint w = ![-n,-y]) := by
    apply Set.disjoint_left.mpr
    intro w hw hpm
    rcases hpm with hpm | hpm
    · have h := congrFun (hw.symm.trans hpm) 0
      simp only [Pi.zero_apply, Matrix.cons_val_zero] at h
      omega
    · have h := congrFun (hw.symm.trans hpm) 0
      simp only [Pi.zero_apply, Matrix.cons_val_zero] at h
      omega
  have hpm : Disjoint (fun w : Fin l → Fin 4 => endpoint w = ![n,y])
      (fun w => endpoint w = ![-n,-y]) := by
    apply Set.disjoint_left.mpr
    intro w hw hneg
    have h := congrFun (hw.symm.trans hneg) 0
    simp only [Matrix.cons_val_zero] at h
    omega
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_or_disjoint _ _ hzero,
    Fintype.card_subtype_or_disjoint _ _ hpm]


theorem prewrap_return_reversal (p t : ℤ) (s : ℕ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) (hs : 2*s < p.toNat) :
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let L : ℕ := (p*(m-1)).toNat
    let P : ℕ := p.toNat
    let l : ℕ := L+2*s
    W F19 l = (Nat.choose l (l/2))^2 + 2 * (Nat.choose l (4*P+s) * Nat.choose l s) ∧
    W F33 l = (Nat.choose l (l/2))^2 + 2 * (Nat.choose l (P+s))^2 ∧
    W F33 l + 2 * (Nat.choose l (4*P+s) * Nat.choose l s) =
      W F19 l + 2 * (Nat.choose l (P+s))^2 ∧ W F33 l < W F19 l := by
  classical
  let m : ℤ := 6*t-1
  let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
  let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
  let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
  let K19 := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 := Submodule.span ℤ (Set.range ![v133, v233])
  let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
  let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
  let L : ℕ := (p*(m-1)).toNat
  let P : ℕ := p.toNat
  let l : ℕ := L+2*s
  change W F19 l = (Nat.choose l (l/2))^2 + 2 * (Nat.choose l (4*P+s) * Nat.choose l s) ∧
    W F33 l = (Nat.choose l (l/2))^2 + 2 * (Nat.choose l (P+s))^2 ∧
    W F33 l + 2 * (Nat.choose l (4*P+s) * Nat.choose l s) =
      W F19 l + 2 * (Nat.choose l (P+s))^2 ∧ W F33 l < W F19 l
  have hp : 0 < p := by omega
  have hm : 11 ≤ m := by dsimp [m]; omega
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg (by omega)
  have hL : (L : ℤ) = p*(m-1) := Int.toNat_of_nonneg (mul_nonneg (by omega) (by omega))
  have hl : (l : ℤ) = p*(m-1)+2*(s : ℤ) := by
    dsimp only [l]
    push_cast
    rw [hL]
  have hsZ : 2*(s : ℤ) < p := by
    have h := Int.ofNat_lt.mpr hs
    change 2*(s : ℤ) < (P : ℤ) at h
    rwa [hP] at h
  have hLP : 10*P ≤ L := by
    apply Int.ofNat_le.mp
    push_cast
    rw [hP,hL]
    nlinarith
  have hpP : 2 ≤ P := by omega
  have h4 : 4*P ≤ L := by omega
  have h1 : P ≤ L := by omega
  let x : ℤ := p*(m-5)
  let y : ℤ := -4*p
  let n : ℤ := p*(m-3)
  have hx : 0 < x := mul_pos hp (by omega)
  have hn : 0 < n := mul_pos hp (by omega)
  obtain ⟨h19,h33,hp33,hn33,hp19,hn19⟩ := short_kernels p t hp3 hpo ht
  have hmem19 (w : Fin l → Fin 4) : F19 (endpoint w) = 0 ↔
      endpoint w = 0 ∨ endpoint w = ![x,y] ∨ endpoint w = ![-x,-y] := by
    constructor
    · intro hw
      have h := h19 (endpoint w) ((Submodule.Quotient.mk_eq_zero K19).mp hw)
        (by have he := endpoint_lee_bound w; rw [hl] at he; nlinarith)
      simpa [x,y] using h
    · intro hw
      apply (Submodule.Quotient.mk_eq_zero K19).mpr
      rcases hw with hw | hw | hw
      · rw [hw]; exact K19.zero_mem
      · rw [hw]; exact hp19
      · rw [hw]
        simpa only [x, y, neg_mul, neg_neg] using
          (show (![-(p*(m-5)),4*p] : Plane) ∈ K19 from hn19)
  have hmem33 (w : Fin l → Fin 4) : F33 (endpoint w) = 0 ↔
      endpoint w = 0 ∨ endpoint w = ![n,0] ∨ endpoint w = ![-n,0] := by
    constructor
    · intro hw
      exact h33 (endpoint w) ((Submodule.Quotient.mk_eq_zero K33).mp hw)
        (by have he := endpoint_lee_bound w; rw [hl] at he; nlinarith)
    · intro hw
      apply (Submodule.Quotient.mk_eq_zero K33).mpr
      rcases hw with hw | hw | hw
      · rw [hw]; exact K33.zero_mem
      · rw [hw]; exact hp33
      · rw [hw]; exact hn33
  have hc19 : W F19 l = Nat.card {w : Fin l → Fin 4 // endpoint w = 0} +
      (Nat.card {w : Fin l → Fin 4 // endpoint w = ![x,y]} +
        Nat.card {w : Fin l → Fin 4 // endpoint w = ![-x,-y]}) := by
    rw [show W F19 l = Nat.card {w : Fin l → Fin 4 //
      endpoint w = 0 ∨ endpoint w = ![x,y] ∨ endpoint w = ![-x,-y]} from
      Nat.card_congr (Equiv.subtypeEquivRight hmem19)]
    exact three_fiber_card l x y hx
  have hc33 : W F33 l = Nat.card {w : Fin l → Fin 4 // endpoint w = 0} +
      (Nat.card {w : Fin l → Fin 4 // endpoint w = ![n,0]} +
        Nat.card {w : Fin l → Fin 4 // endpoint w = ![-n,0]}) := by
    rw [show W F33 l = Nat.card {w : Fin l → Fin 4 //
      endpoint w = 0 ∨ endpoint w = ![n,0] ∨ endpoint w = ![-n,0]} from
      Nat.card_congr (Equiv.subtypeEquivRight hmem33)]
    simpa using three_fiber_card l n 0 hn
  have h4s : 4*P+s ≤ l := by dsimp only [l]; omega
  have hss : s ≤ l := by dsimp only [l]; omega
  have hps : P+s ≤ l := by dsimp only [l]; omega
  have hc19p : Nat.card {w : Fin l → Fin 4 // endpoint w = ![x,y]} =
      Nat.choose l (4*P+s) * Nat.choose l s := by
    exact PlaneWordEndpointCount.endpoint_card l (4*P+s) s x y
      (by push_cast; rw [hl,hP]; dsimp [x,y]; ring)
      (by push_cast; rw [hl]; dsimp [x,y]; ring)
  have hc19n : Nat.card {w : Fin l → Fin 4 // endpoint w = ![-x,-y]} =
      Nat.choose l (4*P+s) * Nat.choose l s := by
    rw [PlaneWordEndpointCount.endpoint_card l (l-(4*P+s)) (l-s) (-x) (-y)
      (by rw [Nat.cast_sub h4s]; push_cast; rw [hl,hP]; dsimp [x,y]; ring)
      (by rw [Nat.cast_sub hss]; push_cast; rw [hl]; dsimp [x,y]; ring)]
    rw [Nat.choose_symm h4s, Nat.choose_symm hss]
  have hc33p : Nat.card {w : Fin l → Fin 4 // endpoint w = ![n,0]} =
      (Nat.choose l (P+s))^2 := by
    rw [PlaneWordEndpointCount.endpoint_card l (P+s) (P+s) n 0
      (by push_cast; rw [hl,hP]; dsimp [n]; ring)
      (by push_cast; rw [hl,hP]; dsimp [n]; ring)]
    ring
  have hc33n : Nat.card {w : Fin l → Fin 4 // endpoint w = ![-n,0]} =
      (Nat.choose l (P+s))^2 := by
    rw [PlaneWordEndpointCount.endpoint_card l (l-(P+s)) (l-(P+s)) (-n) 0
      (by rw [Nat.cast_sub hps]; push_cast; rw [hl,hP]; dsimp [n]; ring)
      (by rw [Nat.cast_sub hps]; push_cast; rw [hl,hP]; dsimp [n]; ring)]
    rw [Nat.choose_symm hps]
    ring
  have hdouble : (l : ℤ) = 2*(p*(3*t-1)+(s : ℤ)) := by
    rw [hl]
    dsimp only [m]
    ring
  have hhalf : (l : ℤ) = 2*((l/2 : ℕ) : ℤ) := by omega
  have hc0 : Nat.card {w : Fin l → Fin 4 // endpoint w = 0} =
      (Nat.choose l (l/2))^2 := by
    have hz : (![0,0] : Plane) = 0 := by ext i; fin_cases i <;> rfl
    simpa only [hz, pow_two] using
      PlaneWordEndpointCount.endpoint_card l (l/2) (l/2) 0 0 (by omega) (by omega)
  rw [hc19p,hc19n,hc0] at hc19
  rw [hc33p,hc33n,hc0] at hc33
  have hstrict := prewrap_binomial_comparison P L hpP hLP s hs
  change (Nat.choose l (P+s))^2 <
    Nat.choose l (4*P+s) * Nat.choose l s at hstrict
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega


private theorem boundary_return_reversal (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let L : ℕ := (p*(m-1)).toNat
    let P : ℕ := p.toNat
    W F33 L + 2 * Nat.choose L (4*P) =
      W F19 L + 2 * (Nat.choose L P)^2 ∧ W F33 L < W F19 L := by
  have hs : 2*0 < p.toNat := by omega
  simpa using (prewrap_return_reversal p t 0 hp3 hpo ht hs).2.2

private theorem word_endpoint_even {l : ℕ} (w : Fin l → Fin 4) :
    Even ((l : ℤ) - endpoint w 0 - endpoint w 1) := by
  obtain ⟨hu, _⟩ := PlaneWordEndpointCount.rotated_endpoint w
  refine ⟨((l : ℤ) - endpoint w 0 - endpoint w 1) / 2, ?_⟩
  omega

private theorem odd_returns_zero (p m a b : ℤ)
    (hp : 0 < p) (hpo : Odd p) (hmo : Odd m) (hao : Odd a) (hbo : Odd b)
    (ha : 0 < a) (ham : a < m) (hb : 0 < b) (hbm : b < m)
    (l : ℕ) (hl : (l : ℤ) < p*m) (ho : Odd l) :
    let v1 : Plane := ![p*(m-a)/2, p*(m+a)/2]
    let v2 : Plane := ![p*(m-b)/2, -(p*(m+b)/2)]
    let K := Submodule.span ℤ (Set.range ![v1,v2])
    W K.mkQ.toAddMonoidHom l = 0 := by
  classical
  let v1 : Plane := ![p*(m-a)/2, p*(m+a)/2]
  let v2 : Plane := ![p*(m-b)/2, -(p*(m+b)/2)]
  let K := Submodule.span ℤ (Set.range ![v1,v2])
  let F : Plane →+ (Plane ⧸ K) := K.mkQ.toAddMonoidHom
  change W F l = 0
  obtain ⟨hs, _, _, hh, _, _, hshort⟩ :=
    asymmetric_rank_one_actual_data p m a b hp hpo hmo hao hbo ha ham hb hbm
  have hcoord : (v1+v2) 0 + (v1+v2) 1 = p*(m-b) := by
    simpa only [BajnokBeattyCayleyNecessity.sumDiff, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val_zero] using congrFun hh 0
  haveI : IsEmpty (ReturnWords F l) := ⟨by
    rintro ⟨w,hw⟩
    obtain ⟨k,hk⟩ := hshort ((p*m-1)/2) le_rfl (endpoint w)
      ((Submodule.Quotient.mk_eq_zero K).mp hw)
      (by have hlee := endpoint_lee_bound w; omega)
    have hsum : endpoint w 0 + endpoint w 1 = k * (p*(m-b)) := by
      rw [hk]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_add, hcoord]
    obtain ⟨c,hc⟩ := word_endpoint_even w
    obtain ⟨u,hu⟩ := hmo.sub_odd hbo
    have heven : Even (l : ℤ) := by
      refine ⟨c+k*p*u, ?_⟩
      calc
        (l : ℤ) = c+c+(endpoint w 0+endpoint w 1) := by omega
        _ = (c+k*p*u)+(c+k*p*u) := by rw [hsum,hu]; ring
    have hodd : Odd (l : ℤ) := by exact_mod_cast ho
    exact (Int.not_even_iff_odd.mpr hodd) heven⟩
  exact Nat.card_of_isEmpty

theorem first_return_reversal (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let L : ℕ := (p*(m-1)).toNat
    let P : ℕ := p.toNat
    (∀ l : ℕ, l < L → W F19 l ≤ W F33 l) ∧
      W F33 L + 2 * Nat.choose L (4*P) = W F19 L + 2 * (Nat.choose L P)^2 ∧
      W F33 L < W F19 L := by
  classical
  let m : ℤ := 6*t-1
  let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
  let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
  let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
  let K19 := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 := Submodule.span ℤ (Set.range ![v133, v233])
  let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
  let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
  let L : ℕ := (p*(m-1)).toNat
  let P : ℕ := p.toNat
  change (∀ l : ℕ, l < L → W F19 l ≤ W F33 l) ∧
    W F33 L + 2 * Nat.choose L (4*P) = W F19 L + 2 * (Nat.choose L P)^2 ∧
    W F33 L < W F19 L
  have hbdy := boundary_return_reversal p t hp3 hpo ht
  refine ⟨?_, hbdy⟩
  intro l hl
  let n : ℕ := (p*(m-3)).toNat
  have hp : 0 < p := by omega
  have hm : 11 ≤ m := by dsimp [m]; omega
  have hNz : (n : ℤ) = p*(m-3) := Int.toNat_of_nonneg (mul_nonneg (by omega) (by omega))
  have hLz : (L : ℤ) = p*(m-1) := Int.toNat_of_nonneg (mul_nonneg (by omega) (by omega))
  have hNz2 : (n : ℤ) = 2*(p*(3*t-2)) := by rw [hNz]; dsimp [m]; ring
  obtain ⟨_,_,_,_,hbefore,_⟩ := first_return_defect p t hp3 hpo ht
  by_cases hln : l < n
  · exact le_of_eq (hbefore l hln)
  rcases Nat.even_or_odd l with he | ho
  · obtain ⟨v,hv⟩ := he
    let r : ℕ := (l-n)/2
    have hlrep : l = n+2*r := by dsimp [r]; omega
    have hlrepZ : (l : ℤ) = (n : ℤ)+2*(r : ℤ) := by exact_mod_cast hlrep
    have hlZ : (l : ℤ) < (L : ℤ) := by exact_mod_cast hl
    have hr : (r : ℤ) < p := by nlinarith [hLz,hNz]
    have hband := BajnokBeattyShortReturnBand.short_return_band p t hp3 hpo ht r hr
    have heq : W F33 l = W F19 l + 2*(Nat.choose l r)^2 := by
      change W F33 (n+2*r) = W F19 (n+2*r) + 2*(Nat.choose (n+2*r) r)^2 at hband
      simpa only [← hlrep] using hband
    omega
  · have hmo : Odd m := ⟨3*t-1, by dsimp [m]; ring⟩
    have hlpm : (l : ℤ) < p*m := by
      have hlZ : (l : ℤ) < (L : ℤ) := by exact_mod_cast hl
      rw [hLz] at hlZ
      nlinarith
    have h19 : W F19 l = 0 := odd_returns_zero p m 1 9 hp hpo hmo odd_one
      (by decide) (by norm_num) (by omega) (by norm_num) (by omega) l hlpm ho
    have h33 : W F33 l = 0 := odd_returns_zero p m 3 3 hp hpo hmo (by decide)
      (by decide) (by norm_num) (by omega) (by norm_num) (by omega) l hlpm ho
    omega


end D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect

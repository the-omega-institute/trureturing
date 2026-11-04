/- GID: D5/S3/FiniteGroups/BajnokBeattyInitialOddWrapSign
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyInitialOddWrapSign
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Three binomial growth bounds prove the initial odd-wrap quotient sign. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
import Mathlib.Tactic

/-!
proof_shape: actual_initial_odd_wrap_sign: content.
admission_basis: escape-witness.
escape_witness: three adjacent binomial recurrence estimates give successive
growth factors at least 3/2,4/3,5/4. Positivity and their product5/2 give
a strict factor exceeding2; monotonic extension within the lower half-row
feeds the full actual-quotient comparison. Every helper is consumed.
This is an unbounded symbolic theorem in p, not a finite certified-instance;
all source declarations therefore have utility none.
Repository/library reuse: actual_odd_wrap_counts, Nat.choose_succ_right_eq,
Nat.choose_le_succ_of_lt_half_left, Nat.choose_pos and Nat.choose_symm.
No matching three-step comparison was found in the searched D5/Nat.Choose
sources. Provenance is repo-derived; no literature novelty is asserted.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign
open NearSquareLatticeRigidity BajnokBeattyFirstReturnDefect
open BajnokBeattyOddWrapReturnCounts

private theorem three_step_growth (p : ℕ) (hp : 3 ≤ p) :
    2 * Nat.choose (11*p) (4*p) < Nat.choose (11*p) (5*p) := by
  let f : ℕ → ℕ := fun k => Nat.choose (11*p) k
  have hratio (k u v : ℕ) (hk : k ≤ 11*p)
      (hcoeff : v*(k+1) ≤ u*(11*p-k)) :
      v*f k ≤ u*f (k+1) := by
    have h := Nat.choose_succ_right_eq (11*p) k
    have hbound := Nat.mul_le_mul_left (f k) hcoeff
    have heq : (f k * (u*(11*p-k))) = (u*f (k+1))*(k+1) := by
      dsimp [f]
      have hmul := congrArg (fun z : ℕ => u*z) h
      nlinarith only [hmul]
    have hh : (v*f k)*(k+1) ≤ (u*f (k+1))*(k+1) := by
      calc
        (v*f k)*(k+1) = f k*(v*(k+1)) := by ring
        _ ≤ f k*(u*(11*p-k)) := hbound
        _ = (u*f (k+1))*(k+1) := heq
    exact Nat.le_of_mul_le_mul_right hh (by omega)
  have h1 : 3*f (4*p) ≤ 2*f (4*p+1) :=
    hratio (4*p) 2 3 (by omega) (by omega)
  have h2 : 4*f (4*p+1) ≤ 3*f (4*p+2) := by
    simpa only [Nat.add_assoc] using hratio (4*p+1) 3 4 (by omega) (by omega)
  have h3 : 5*f (4*p+2) ≤ 4*f (4*p+3) := by
    simpa only [Nat.add_assoc] using hratio (4*p+2) 4 5 (by omega) (by omega)
  have hpos : 0 < f (4*p) := Nat.choose_pos (by omega)
  have hstrict : 2*f (4*p) < f (4*p+3) := by omega
  have hmono (r : ℕ) (hr : 4*p+3+r ≤ 5*p) : f (4*p+3) ≤ f (4*p+3+r) := by
    induction r with
    | zero => simp
    | succ r ih =>
      have hprev := ih (by omega)
      have hstep : f (4*p+3+r) ≤ f (4*p+3+r+1) :=
        Nat.choose_le_succ_of_lt_half_left (by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hprev.trans hstep
  have hm := hmono (p-3) (by omega)
  rw [show 4*p+3+(p-3) = 5*p by omega] at hm
  exact hstrict.trans_le hm

theorem actual_initial_odd_wrap_sign (p : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p) :
    let m : ℤ := 11
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    W F33 (11*p).toNat < W F19 (11*p).toNat := by
  have hc := actual_odd_wrap_counts p 2 hp3 hpo (by norm_num)
  let P := p.toNat
  have hp : 0 ≤ p := by omega
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg hp
  have hPn : 3 ≤ P := by omega
  have hbin := three_step_growth P hPn
  have h11 : (11*p).toNat = 11*P := by omega
  have h6 : (6*p).toNat = 6*P := by omega
  have h7 : (7*p).toNat = 7*P := by omega
  have h10 : (10*p).toNat = 10*P := by omega
  have hsymA : Nat.choose (11*P) (6*P) = Nat.choose (11*P) (5*P) := by
    have h := Nat.choose_symm (by omega : 6*P ≤ 11*P)
    simpa only [show 11*P-6*P=5*P by omega] using h.symm
  have hsymB : Nat.choose (11*P) (7*P) = Nat.choose (11*P) (4*P) := by
    have h := Nat.choose_symm (by omega : 7*P ≤ 11*P)
    simpa only [show 11*P-7*P=4*P by omega] using h.symm
  dsimp only at hc ⊢
  rw [show (6 : ℤ)*2-1=11 by norm_num] at hc
  norm_num only at hc ⊢
  rw [mul_comm 11 p]
  rw [hc.1,hc.2]
  have ha : p*12/2 = 6*p := by omega
  have hb : p*14/2 = 7*p := by omega
  have hd : p*20/2 = 10*p := by omega
  simp only [ha,hb,hd,show p*11 = 11*p by ring,h11,h6,h7,h10,hsymA,hsymB]
  omega

end D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign

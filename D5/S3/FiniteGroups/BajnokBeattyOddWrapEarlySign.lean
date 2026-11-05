/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapEarlySign
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapEarlySign
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact binomial increment weights prove a uniform early odd-wrap sign. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
import Mathlib.Tactic

/-!
A weighted finite-recurrence proof of the complete early-sign cone.

The consumed finite-recurrence helper proves 2*choose(N,b)<=choose(N,b+P)
when N=2b+3P and b+P<=2P^2.  Its induction keeps the exact partial weight
r(3P-r), hence gives 2P^2 at r=P; no sum helper is rebuilt here.

For integer p>=3,t>=2, take P=p.toNat, N=(p(6t-1)).toNat and
b=(p(3t-2)).toNat.  The cone 3t<=2p+1 gives b+P<=2P^2.
Binomial symmetry reflects the three actual odd-wrap indices to b+P,
b, and d=(p(3t-5)).toNat respectively.  The d fiber has positive count.
This yields a strict comparison, consumed by the only public theorem:
the actual original quotient maps satisfy W33(N)<W19(N).

proof_shape: actual_early_odd_wrap_sign: content.
admission_basis: escape-witness.
escape_witness: the live induction bounds each partial binomial increment
by the exact weight r(3p-r), giving 2p^2 at r=p. The full integer-domain
quotient comparison consumes this uniform bound and a positive outer fiber.
All helpers have consumers; no kernel, count or sign conclusion is assumed.
The source is an unbounded symbolic theorem, with utility none.
Reuse: actual_odd_wrap_counts and Mathlib choose_succ_right_eq,
choose_le_succ_of_lt_half_left, choose_pos and choose_symm. No matching
weighted block comparison was found in the searched D5/Nat.Choose scope.
Provenance is repo-derived; no optimal cone or literature novelty is claimed.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapEarlySign

open NearSquareLatticeRigidity BajnokBeattyFirstReturnDefect
open BajnokBeattyOddWrapReturnCounts

private abbrev f (n k : ℕ) : ℤ := Nat.choose n k

private theorem weighted_block_twofold (n b p : ℕ) (hp : 0 < p)
    (hn : n = 2*b+3*p) (hcone : b+p ≤ 2*p^2) :
    2*Nat.choose n b ≤ Nat.choose n (b+p) := by
  have hnZ : (n : ℤ) = 2*(b : ℤ)+3*(p : ℤ) := by exact_mod_cast hn
  have hmono : ∀ r : ℕ, r ≤ p → Nat.choose n b ≤ Nat.choose n (b+r) := by
    intro r
    induction r with
    | zero => intro hr; simp
    | succ r ih =>
      intro hr
      have hprev := ih (by omega)
      have hstep : Nat.choose n (b+r) ≤ Nat.choose n (b+r+1) :=
        Nat.choose_le_succ_of_lt_half_left (by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hprev.trans hstep
  have hterm (i : ℕ) (hi : i < p) :
      f n b*(((3*p : ℕ) : ℤ)-2*(i : ℤ)-1) ≤
        (f n (b+i+1)-f n (b+i))*((b+p : ℕ) : ℤ) := by
    have hk : b+i ≤ n := by omega
    have hstep : Nat.choose n (b+i) ≤ Nat.choose n (b+i+1) :=
      Nat.choose_le_succ_of_lt_half_left (by omega)
    have hstepZ : f n (b+i) ≤ f n (b+i+1) := by exact_mod_cast hstep
    have hdelta : 0 ≤ f n (b+i+1)-f n (b+i) := by omega
    have hlower : f n b ≤ f n (b+i) := by exact_mod_cast (hmono i (by omega))
    have hnumpos : 0 ≤ ((3*p : ℕ) : ℤ)-2*(i : ℤ)-1 := by
      push_cast
      omega
    have hnum : (n : ℤ)-2*((b+i : ℕ) : ℤ)-1 =
        ((3*p : ℕ) : ℤ)-2*(i : ℤ)-1 := by push_cast; omega
    have hnat := Nat.choose_succ_right_eq n (b+i)
    have hcast : f n (b+i+1)*(((b+i : ℕ) : ℤ)+1) =
        f n (b+i)*((n-(b+i) : ℕ) : ℤ) := by exact_mod_cast hnat
    rw [Nat.cast_sub hk] at hcast
    have hid : (f n (b+i+1)-f n (b+i))*(((b+i : ℕ) : ℤ)+1) =
        f n (b+i)*(((3*p : ℕ) : ℤ)-2*(i : ℤ)-1) := by
      rw [← hnum]
      nlinarith only [hcast]
    calc
      f n b*(((3*p : ℕ) : ℤ)-2*(i : ℤ)-1) ≤
          f n (b+i)*(((3*p : ℕ) : ℤ)-2*(i : ℤ)-1) :=
        mul_le_mul_of_nonneg_right hlower hnumpos
      _ = (f n (b+i+1)-f n (b+i))*(((b+i : ℕ) : ℤ)+1) := hid.symm
      _ ≤ (f n (b+i+1)-f n (b+i))*((b+p : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left (by push_cast; omega) hdelta
  have hsum : f n b*(2*(p : ℤ)^2) ≤
      (f n (b+p)-f n b)*((b+p : ℕ) : ℤ) := by
    have hweighted : ∀ r : ℕ, r ≤ p →
        f n b*((r : ℤ)*(3*(p : ℤ)-(r : ℤ))) ≤
          (f n (b+r)-f n b)*((b+p : ℕ) : ℤ) := by
      intro r
      induction r with
      | zero => intro hr; simp
      | succ r ih =>
        intro hr
        have hprev := ih (by omega)
        have hstep := hterm r (by omega)
        have hs := add_le_add hprev hstep
        rw [show b+(r+1) = b+r+1 by omega]
        push_cast at hs ⊢
        nlinarith only [hs]
    have hs := hweighted p le_rfl
    nlinarith only [hs]
  have hconeZ : ((b+p : ℕ) : ℤ) ≤ 2*(p : ℤ)^2 := by exact_mod_cast hcone
  have hnonneg : 0 ≤ f n b := by dsimp [f]; positivity
  have hleft := mul_le_mul_of_nonneg_left hconeZ hnonneg
  have hweighted : f n b*((b+p : ℕ) : ℤ) ≤
      (f n (b+p)-f n b)*((b+p : ℕ) : ℤ) := hleft.trans hsum
  have hpositive : 0 < ((b+p : ℕ) : ℤ) := by exact_mod_cast (show 0 < b+p by omega)
  have hcancel : f n b ≤ f n (b+p)-f n b :=
    (mul_le_mul_iff_left₀ hpositive).mp hweighted
  have hfinal : 2*f n b ≤ f n (b+p) := by linarith only [hcancel]
  dsimp [f] at hfinal
  exact_mod_cast hfinal

private theorem early_binomial_comparison (p t : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t)
    (hcone : 3*t ≤ 2*p+1) :
    let N : ℕ := (p*(6*t-1)).toNat
    2*Nat.choose N (p*(3*t+1)).toNat <
      Nat.choose N (p*(3*t)).toNat+Nat.choose N (p*(3*t+4)).toNat := by
  let N : ℕ := (p*(6*t-1)).toNat
  let b : ℕ := (p*(3*t-2)).toNat
  let P : ℕ := p.toNat
  let d : ℕ := (p*(3*t-5)).toNat
  let H0 : ℕ := (p*(3*t)).toNat
  let H1 : ℕ := (p*(3*t+1)).toNat
  let H4 : ℕ := (p*(3*t+4)).toNat
  change 2*Nat.choose N H1 < Nat.choose N H0+Nat.choose N H4
  have hp : 0 < p := by omega
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg hp.le
  have hN : (N : ℤ) = p*(6*t-1) := Int.toNat_of_nonneg
    (mul_nonneg hp.le (by omega))
  have hb : (b : ℤ) = p*(3*t-2) := Int.toNat_of_nonneg
    (mul_nonneg hp.le (by omega))
  have hd : (d : ℤ) = p*(3*t-5) := Int.toNat_of_nonneg
    (mul_nonneg hp.le (by omega))
  have hH0 : (H0 : ℤ) = p*(3*t) := Int.toNat_of_nonneg
    (mul_nonneg hp.le (by omega))
  have hH1 : (H1 : ℤ) = p*(3*t+1) := Int.toNat_of_nonneg
    (mul_nonneg hp.le (by omega))
  have hH4 : (H4 : ℤ) = p*(3*t+4) := Int.toNat_of_nonneg
    (mul_nonneg hp.le (by omega))
  have hPpos : 0 < P := by
    have hh : 0 < (P : ℤ) := by rw [hP]; exact hp
    exact_mod_cast hh
  have hn : N = 2*b+3*P := by
    have hh : (N : ℤ) = 2*(b : ℤ)+3*(P : ℤ) := by
      rw [hN, hb, hP]
      ring
    exact_mod_cast hh
  have hblockcone : b+P ≤ 2*P^2 := by
    have hm := mul_le_mul_of_nonneg_left (show 3*t-1 ≤ 2*p by omega) hp.le
    have hh : (b : ℤ)+(P : ℤ) ≤ 2*(P : ℤ)^2 := by
      rw [hb, hP]
      nlinarith only [hm]
    exact_mod_cast hh
  have htwo := weighted_block_twofold N b P hPpos hn hblockcone
  have hsum0 : H0+(b+P) = N := by
    have hh : (H0 : ℤ)+((b : ℤ)+(P : ℤ)) = (N : ℤ) := by
      rw [hH0, hb, hP, hN]
      ring
    exact_mod_cast hh
  have hsum1 : H1+b = N := by
    have hh : (H1 : ℤ)+(b : ℤ) = (N : ℤ) := by
      rw [hH1, hb, hN]
      ring
    exact_mod_cast hh
  have hsum4 : H4+d = N := by
    have hh : (H4 : ℤ)+(d : ℤ) = (N : ℤ) := by
      rw [hH4, hd, hN]
      ring
    exact_mod_cast hh
  have hsym0 : Nat.choose N H0 = Nat.choose N (b+P) := by
    have hh := Nat.choose_symm (show H0 ≤ N by omega)
    rw [show N-H0 = b+P by omega] at hh
    exact hh.symm
  have hsym1 : Nat.choose N H1 = Nat.choose N b := by
    have hh := Nat.choose_symm (show H1 ≤ N by omega)
    rw [show N-H1 = b by omega] at hh
    exact hh.symm
  have hsym4 : Nat.choose N H4 = Nat.choose N d := by
    have hh := Nat.choose_symm (show H4 ≤ N by omega)
    rw [show N-H4 = d by omega] at hh
    exact hh.symm
  have hpositive : 0 < Nat.choose N d := Nat.choose_pos (show d ≤ N by omega)
  rw [hsym1, hsym0, hsym4]
  omega

/-- The strengthened early negative cone for the complete original quotients. -/
theorem actual_early_odd_wrap_sign (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) (hcone : 3*t ≤ 2*p+1) :
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
    W F33 L < W F19 L := by
  have hc := actual_odd_wrap_counts p t hp3 hpo ht
  have hb := early_binomial_comparison p t hp3 ht hcone
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

end D5.S3.FiniteGroups.BajnokBeattyOddWrapEarlySign

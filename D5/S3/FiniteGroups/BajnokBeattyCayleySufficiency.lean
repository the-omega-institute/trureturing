/- GID: D5/S3/FiniteGroups/BajnokBeattyCayleySufficiency
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyCayleySufficiency
   mirror-E: none
   anchors: []
   utility: none
   digest: Uniform signed-radius construction for a partial direction of Bajnok--Beatty Conjecture 4.1. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/- Source admission: #25489, continuation 6567741241.
The new live mathematical mechanism is simultaneous skew-lattice remainder
descent. This is partial sufficiency, not a resolution of Conjecture 4.1.
All parameters are unbounded; no finite enumeration is mathematical content.
Direct frozen project dependencies: none. Pinned Mathlib supplies well-ordering,
integer arithmetic, additive homomorphisms, and modular casts.
-/

namespace D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem skew_remainder (A a b x y : ℤ) (hA : 0 < A)
    (ha : 0 ≤ a) (haA : a < A) (hb : 0 ≤ b) (hbA : b < A) :
    ∃ p q : ℤ, 0 ≤ x - p*A + q*a ∧ x - p*A + q*a < A ∧
      0 ≤ y + p*b - q*A ∧ y + p*b - q*A < A := by
  classical
  let P (n : ℕ) : Prop := ∃ p q : ℤ,
    0 ≤ x-p*A+q*a ∧ 0 ≤ y+p*b-q*A ∧
      (x-p*A+q*a)+(y+p*b-q*A) = (n : ℤ)
  have hex : ∃ n, P n := by
    let N := |x| + |y|
    have hN : 0 ≤ N := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hx : 0 ≤ x-(-N)*A+(-N)*a := by
      have := mul_nonneg hN (show 0 ≤ A-a-1 by omega)
      dsimp [N] at *
      nlinarith [neg_abs_le x, abs_nonneg y]
    have hy : 0 ≤ y+(-N)*b-(-N)*A := by
      have := mul_nonneg hN (show 0 ≤ A-b-1 by omega)
      dsimp [N] at *
      nlinarith [neg_abs_le y, abs_nonneg x]
    refine ⟨((x-(-N)*A+(-N)*a)+(y+(-N)*b-(-N)*A)).toNat,
      -N, -N, hx, hy, ?_⟩
    exact (Int.toNat_of_nonneg (add_nonneg hx hy)).symm
  obtain ⟨p,q,hx,hy,hsum⟩ := Nat.find_spec hex
  have hxmin : x-p*A+q*a < A := by
    by_contra hn
    have hx' : 0 ≤ x-(p+1)*A+q*a := by nlinarith
    have hy' : 0 ≤ y+(p+1)*b-q*A := by nlinarith
    have hm := Nat.find_min' hex (show P
      ((x-(p+1)*A+q*a)+(y+(p+1)*b-q*A)).toNat from
        ⟨p+1,q,hx',hy',(Int.toNat_of_nonneg (add_nonneg hx' hy')).symm⟩)
    have hc := Int.toNat_of_nonneg (add_nonneg hx' hy')
    have hm' : (Nat.find hex : ℤ) ≤
        (((x-(p+1)*A+q*a)+(y+(p+1)*b-q*A)).toNat : ℤ) := by
      exact_mod_cast hm
    rw [hc] at hm'
    nlinarith
  have hymin : y+p*b-q*A < A := by
    by_contra hn
    have hx' : 0 ≤ x-p*A+(q+1)*a := by nlinarith
    have hy' : 0 ≤ y+p*b-(q+1)*A := by nlinarith
    have hm := Nat.find_min' hex (show P
      ((x-p*A+(q+1)*a)+(y+p*b-(q+1)*A)).toNat from
        ⟨p,q+1,hx',hy',(Int.toNat_of_nonneg (add_nonneg hx' hy')).symm⟩)
    have hc := Int.toNat_of_nonneg (add_nonneg hx' hy')
    have hm' : (Nat.find hex : ℤ) ≤
        (((x-p*A+(q+1)*a)+(y+p*b-(q+1)*A)).toNat : ℤ) := by
      exact_mod_cast hm
    rw [hc] at hm'
    nlinarith
  exact ⟨p,q,hx,hxmin,hy,hymin⟩

private theorem integer_diamond_cover (t j x y : ℤ)
    (ht : 2 ≤ t) (hj : 0 ≤ j) (hjt : j < t) :
    ∃ p q : ℤ,
      |x-p*(2*(t-1))-q*(2*(t-j))| +
        |y-p*(2*(t+1))+q*(2*(t+j))| ≤ 2*t := by
  obtain ⟨p,q,hx,hxA,hy,hyA⟩ :=
    skew_remainder (4*t) (4*j) 4 (x+y+2*t) (x-y+2*t)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨p,q,?_⟩
  have he1 : (x-p*(2*(t-1))-q*(2*(t-j))) +
      (y-p*(2*(t+1))+q*(2*(t+j))) = x+y-p*(4*t)+q*(4*j) := by ring
  have he2 : (x-p*(2*(t-1))-q*(2*(t-j))) -
      (y-p*(2*(t+1))+q*(2*(t+j))) = x-y+p*4-q*(4*t) := by ring
  rcases le_total 0 (x-p*(2*(t-1))-q*(2*(t-j))) with h1 | h1 <;>
    rcases le_total 0 (y-p*(2*(t+1))+q*(2*(t+j))) with h2 | h2 <;>
    simp only [abs_of_nonneg, abs_of_nonpos, h1, h2] <;> omega

private theorem hom_diamond_cover {G : Type*} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) (t j : ℤ) (ht : 2 ≤ t) (hj : 0 ≤ j) (hjt : j < t)
    (hv : f (2*(t-j), -2*(t+j)) = 0)
    (hw : f (2*(t-1), 2*(t+1)) = 0)
    (hsur : Function.Surjective f) (g : G) :
    ∃ x y : ℤ, g = x • f (1,0) + y • f (0,1) ∧ |x|+|y| ≤ 2*t := by
  obtain ⟨⟨x,y⟩,rfl⟩ := hsur g
  obtain ⟨p,q,hbound⟩ := integer_diamond_cover t j x y ht hj hjt
  let r := x-p*(2*(t-1))-q*(2*(t-j))
  let s := y-p*(2*(t+1))+q*(2*(t+j))
  refine ⟨r,s,?_,hbound⟩
  have he : (r,s) = (x,y) - p • (2*(t-1),2*(t+1)) -
      q • (2*(t-j),-2*(t+j)) := by
    ext <;> simp [r,s,sub_eq_add_neg] <;> ring
  have hrep : f (r,s) = f (x,y) := by
    rw [he, map_sub, map_sub, map_zsmul, map_zsmul, hv, hw]
    simp
  rw [← hrep]
  have he' : (r,s) = r • (1,0) + s • (0,1) := by ext <;> simp
  rw [he', map_add, map_zsmul, map_zsmul]

end D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency

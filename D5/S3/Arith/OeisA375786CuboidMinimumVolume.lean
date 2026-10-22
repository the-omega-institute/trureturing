/- GID: D5/S3/Arith/OeisA375786CuboidMinimumVolume
   generality: G
   mirror-B: D5/B/S3/Arith/OeisA375786CuboidMinimumVolume
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The lexicographically smallest cuboid of surface 6n squared minimizes volume. -/

/-
Public theorem result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#18592; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19802.
Direct frozen dependencies: none (all declarations use pinned Mathlib and this module).
Private helpers (all proof_shape: bind-only; escape_witness: none):
mem_bounds -> result; same_first -> result; volume_bounds -> large_first, result;
large_first -> result; mem_of_edges -> odd_witness, even_witness;
first_one_small -> result; odd_witness -> result; even_witness -> result.
The public definitions reproduce the expressions fixed in issue #18592.
The surface equation bounds each positive edge by 3*n^2, so the intervals lose no cuboid.
The proof uses algebraic inequalities and parity for arbitrary n, with definitional reduction
only at the base case n=1; it is not an enumeration or a certified-instance refutation.
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace D5.S3.Arith.OeisA375786CuboidMinimumVolume

/-- The integer-sided cuboids `x ≤ y ≤ z` having the same surface as the cube with edge `n`:
`x*y + y*z + x*z = 3*n^2`. -/
def cuboids (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 (3 * n ^ 2) ×ˢ Finset.Icc 1 (3 * n ^ 2) ×ˢ Finset.Icc 1 (3 * n ^ 2)).filter
    fun p => p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.1 * p.2.1 + p.2.1 * p.2.2 + p.1 * p.2.2 = 3 * n ^ 2

/-- The volume of the cuboid with edges `x, y, z`. -/
def volume (p : ℕ × ℕ × ℕ) : ℕ := p.1 * p.2.1 * p.2.2

/-- The conjecture of A375786: the cuboid with the smallest edge length (ties broken by the
smallest second edge length) has the minimum volume. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p ∈ cuboids n,
    (∀ q ∈ cuboids n, p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2.1 ≤ q.2.1)) →
    ∀ q ∈ cuboids n, volume p ≤ volume q

private theorem mem_bounds {n x y z : ℕ} (h : (x,y,z) ∈ cuboids n) :
    1 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x*y+y*z+x*z = 3*n^2 := by
  simp only [cuboids, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
  exact ⟨h.1.1.1, h.2⟩

private theorem same_first {x y z a b S : ℕ} (hx : 1 ≤ x)
    (hy : y ≤ a) (hab : a ≤ b)
    (he : x*y+y*z+x*z = S) (he' : x*a+a*b+x*b = S) :
    x*y*z ≤ x*a*b := by
  have hprod : 0 ≤ ((a:ℤ)-y)*(b-y) := mul_nonneg (by omega) (by omega)
  have hez : (x:ℤ)*y+y*z+x*z = S := by exact_mod_cast he
  have hez' : (x:ℤ)*a+a*b+x*b = S := by exact_mod_cast he'
  have hsum : (a:ℤ)+b ≤ y+z := by
    nlinarith
  have hvol : (x:ℤ)*y*z ≤ x*a*b := by
    have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (x:ℤ) by omega)
    have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ (x:ℤ) by omega)
    nlinarith [hez, hez']
  exact_mod_cast hvol

private theorem volume_bounds {x y z S : ℕ} (hx : 1 ≤ x)
    (hxy : x ≤ y) (hyz : y ≤ z) (he : x*y+y*z+x*z = S) :
    3*x^2 ≤ S ∧ x*S ≤ 2*x*y*z+x^3 := by
  have h₁ := Nat.mul_le_mul_left x hxy
  have h₂ := Nat.mul_le_mul_left y (le_trans hxy hyz)
  have h₃ := Nat.mul_le_mul_left x (le_trans hxy hyz)
  have h₄ := Nat.mul_le_mul hxy hxy
  have hsmall : 3*x^2 ≤ S := by nlinarith
  have hi : 0 ≤ ((y:ℤ)-x)*((z:ℤ)-x) := mul_nonneg (by omega) (by omega)
  have him := mul_nonneg (show 0 ≤ (x:ℤ) by omega) hi
  have hez : (x:ℤ)*y+y*z+x*z = S := by exact_mod_cast he
  have hm := congrArg (fun t : ℤ => (x:ℤ)*t) hez
  have hv : (x:ℤ)*S ≤ 2*x*y*z+x^3 := by nlinarith [him, hm]
  exact ⟨hsmall, by exact_mod_cast hv⟩

private theorem large_first {x y z S : ℕ} (hx : 3 ≤ x)
    (hxy : x ≤ y) (hyz : y ≤ z) (he : x*y+y*z+x*z = S) : S ≤ x*y*z := by
  obtain ⟨hsmall, hv⟩ := volume_bounds (by omega) hxy hyz he
  have hmul := Nat.mul_le_mul_left x hsmall
  have hmul' := Nat.mul_le_mul_left S hx
  nlinarith


private theorem mem_of_edges {n x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hyz : y ≤ z) (he : x*y+y*z+x*z = 3*n^2) : (x,y,z) ∈ cuboids n := by
  have hy : 1 ≤ y := le_trans hx hxy
  have hz : 1 ≤ z := le_trans hy hyz
  have hxS : x ≤ 3*n^2 := by nlinarith [Nat.mul_le_mul_left x hy]
  have hyS : y ≤ 3*n^2 := by nlinarith [Nat.mul_le_mul_left y hx]
  have hzS : z ≤ 3*n^2 := by nlinarith [Nat.mul_le_mul_left z hx]
  simp only [cuboids, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨⟨hx,hxS⟩,⟨hy,hyS⟩,hz,hzS⟩,hxy,hyz,he⟩

private theorem first_one_small {y z S : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z)
    (hS : 12 ≤ S) (he : y+y*z+z = S) : y*z+4 < S := by
  have hsum : 4 < y+z := by
    by_contra h
    have hs : y+z ≤ 4 := Nat.le_of_not_lt h
    have hyt : y = 1 ∨ y = 2 := by omega
    rcases hyt with rfl | rfl <;> nlinarith
  omega

private theorem odd_witness {n : ℕ} (hn : n % 2 = 1) :
    ∃ y z, (1,y,z) ∈ cuboids n := by
  let m := n/2
  have he : n = 2*m+1 := by omega
  refine ⟨1,6*m^2+6*m+1,mem_of_edges (by omega) (by omega) (by omega) ?_⟩
  rw [he]
  ring

private theorem even_witness {n : ℕ} (hn : 2 ≤ n) (he : n % 2 = 0) :
    ∃ z, (2,2,z) ∈ cuboids n ∧ volume (2,2,z)+4 = 3*n^2 := by
  let m := n/2
  have hnm : n = 2*m := by omega
  have hm : 1 ≤ m := by omega
  have hm2 : 1 ≤ m^2 := Nat.one_le_pow 2 m hm
  have hz : 3*m^2-1+1 = 3*m^2 := by omega
  refine ⟨3*m^2-1,mem_of_edges (by omega) (by omega) (by omega) ?_,?_⟩
  · rw [hnm]
    nlinarith
  · simp only [volume]
    rw [hnm]
    nlinarith

theorem result : claim := by
  intro n hn p hp hlex q hq
  obtain ⟨x,y,z⟩ := p
  obtain ⟨a,b,c⟩ := q
  obtain ⟨hx,hxy,hyz,hep⟩ := mem_bounds hp
  obtain ⟨ha,hab,hbc,heq⟩ := mem_bounds hq
  change x*y*z ≤ a*b*c
  by_cases hn1 : n = 1
  · subst n
    have hset : cuboids 1 = {(1,1,1)} := Finset.val_eq_singleton_iff.mp rfl
    rw [hset,Finset.mem_singleton] at hp hq
    cases hp
    cases hq
    rfl
  have hn2 : 2 ≤ n := by omega
  have hS : 12 ≤ 3*n^2 := by nlinarith
  by_cases hex : ∃ y z, (1,y,z) ∈ cuboids n
  · obtain ⟨u,v,hw⟩ := hex
    have hxp := hlex (1,u,v) hw
    have hx1 : x = 1 := by simpa only [Prod.fst,Prod.snd] using (show x=1 by rcases hxp with h | ⟨h,_⟩ <;> omega)
    subst x
    have hsmall : y*z+4 < 3*n^2 := first_one_small (by omega) hyz hS (by simpa using hep)
    by_cases ha1 : a = 1
    · subst a
      have hle := hlex (1,b,c) hq
      have hyb : y ≤ b := by simpa using hle
      simpa using same_first (by omega : 1 ≤ 1) hyb hbc hep heq
    by_cases ha2 : a = 2
    · subst a
      have hv := (volume_bounds (by omega : 1 ≤ 2) hab hbc heq).2
      simp only [Nat.one_mul]
      nlinarith
    · have hbig := large_first (by omega : 3 ≤ a) hab hbc heq
      simp only [Nat.one_mul]
      omega
  · have heven : n % 2 = 0 := Nat.mod_two_ne_one.mp (fun h => hex (odd_witness h))
    obtain ⟨w,hw,hvw⟩ := even_witness hn2 heven
    have hxp := hlex (2,2,w) hw
    have hx2 : x = 2 := by
      have hxne : x ≠ 1 := by
        intro h
        subst x
        exact hex ⟨y,z,hp⟩
      rcases hxp with h | ⟨h,_⟩ <;> omega
    subst x
    by_cases ha2 : a = 2
    · subst a
      have hle := hlex (2,b,c) hq
      have hyb : y ≤ b := by simpa using hle
      exact same_first (by omega) hyb hbc hep heq
    · have hane : a ≠ 1 := by
        intro h
        subst a
        exact hex ⟨b,c,hq⟩
      have hbig := large_first (by omega : 3 ≤ a) hab hbc heq
      have hle := hlex (2,2,w) hw
      have hy2 : y ≤ 2 := by simpa using hle
      have hwb := mem_bounds hw
      have hv := same_first (by omega : 1 ≤ 2) hy2 (show 2 ≤ w from hwb.2.2.1) hep hwb.2.2.2
      simp only [volume] at hvw
      omega

end D5.S3.Arith.OeisA375786CuboidMinimumVolume

/- GID: D5/S3/FiniteGroups/BajnokBeattyCayleySufficiency
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyCayleySufficiency
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A uniform sufficient family of signed Cayley radius bounds. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/- Source admission: #25489, continuation 6567741241.
The new live mathematical mechanism is simultaneous skew lattice remainder
descent. This is partial sufficiency, not a resolution of Conjecture 4.1.
All parameters are unbounded; no finite enumeration is mathematical content.
Direct frozen project dependencies: none. Pinned Mathlib supplies well-ordering,
integer arithmetic, additive homomorphisms, and modular casts.
Admission basis: escape-witness (not open-problem-resolution).
Proof shapes and live consumers, with same-delivery helpers inlined:
  skew_remainder: content; witness is simultaneous least-sum descent;
    consumed by integer_diamond_cover.
  integer_diamond_cover: content; live descent plus rotated integer bounds;
    consumed by hom_diamond_cover.
  hom_diamond_cover: content; live descent transferred through the homomorphism;
    consumed by result.
  matrix_map: definition; consumed by the modular map helpers.
  matrix_map_zero, matrix_map_distinct: bind-only; consumed by even_family_map
    and odd_family_map.
  even_family_map, odd_family_map: bind-only coordinate constructions from
    modular lifts and IsCoprime.mul_left; consumed by result.
  result: content; skew_remainder remains on its live proof path.
The displayed family is a sufficient construction; its failure at other
parameters cannot establish a universal exclusion.
-/

namespace D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem skew_remainder (A a b x y : ℤ) (hA : 0 < A)
    (ha : 0 ≤ a) (haA : a < A) (hb : 0 ≤ b) (hbA : b < A) :
    ∃ p q : ℤ, 0 ≤ x - p * A + q * a ∧ x - p * A + q * a < A ∧
      0 ≤ y + p * b - q * A ∧ y + p * b - q * A < A := by
  classical
  let P (n : ℕ) : Prop := ∃ p q : ℤ,
    0 ≤ x - p * A + q * a ∧ 0 ≤ y + p * b - q * A ∧
      (x - p * A + q * a) + (y + p * b - q * A) = (n : ℤ)
  have hex : ∃ n, P n := by
    let N := |x| + |y|
    have hN : 0 ≤ N := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hx : 0 ≤ x - (-N) * A + (-N) * a := by
      have := mul_nonneg hN (show 0 ≤ A - a-1 by omega)
      dsimp [N] at *
      nlinarith [neg_abs_le x, abs_nonneg y]
    have hy : 0 ≤ y + (-N) * b - (-N) * A := by
      have := mul_nonneg hN (show 0 ≤ A - b-1 by omega)
      dsimp [N] at *
      nlinarith [neg_abs_le y, abs_nonneg x]
    refine ⟨((x - (-N) * A + (-N) * a) + (y + (-N) * b - (-N) * A)).toNat,
      -N, -N, hx, hy, ?_⟩
    exact (Int.toNat_of_nonneg (add_nonneg hx hy)).symm
  obtain ⟨p, q, hx, hy, hsum⟩ := Nat.find_spec hex
  have hxmin : x - p * A + q * a < A := by
    by_contra hn
    have hx' : 0 ≤ x - (p + 1) * A + q * a := by nlinarith
    have hy' : 0 ≤ y + (p + 1) * b - q * A := by nlinarith
    have hm := Nat.find_min' hex (show P
      ((x - (p + 1) * A + q * a) + (y + (p + 1) * b - q * A)).toNat from
        ⟨p + 1, q, hx', hy', (Int.toNat_of_nonneg (add_nonneg hx' hy')).symm⟩)
    have hc := Int.toNat_of_nonneg (add_nonneg hx' hy')
    have hm' : (Nat.find hex : ℤ) ≤
        (((x - (p + 1) * A + q * a) + (y + (p + 1) * b - q * A)).toNat : ℤ) := by
      exact_mod_cast hm
    rw [hc] at hm'
    nlinarith
  have hymin : y + p * b - q * A < A := by
    by_contra hn
    have hx' : 0 ≤ x - p * A + (q + 1) * a := by nlinarith
    have hy' : 0 ≤ y + p * b - (q + 1) * A := by nlinarith
    have hm := Nat.find_min' hex (show P
      ((x - p * A + (q + 1) * a) + (y + p * b - (q + 1) * A)).toNat from
        ⟨p, q + 1, hx', hy', (Int.toNat_of_nonneg (add_nonneg hx' hy')).symm⟩)
    have hc := Int.toNat_of_nonneg (add_nonneg hx' hy')
    have hm' : (Nat.find hex : ℤ) ≤
        (((x - p * A + (q + 1) * a) + (y + p * b - (q + 1) * A)).toNat : ℤ) := by
      exact_mod_cast hm
    rw [hc] at hm'
    nlinarith
  exact ⟨p, q, hx, hxmin, hy, hymin⟩

private theorem integer_diamond_cover (t j x y : ℤ)
    (ht : 1 ≤ t) (hj : 0 ≤ j) (hjt : j < t) :
    ∃ p q : ℤ,
      |x - p * (2 * (t - 1)) - q * (2 * (t - j))| +
        |y - p * (2 * (t + 1)) + q * (2 * (t + j))| ≤ 2 * t := by
  have hrem : ∃ p q : ℤ,
      0 ≤ x + y + 2 * t - p * (4 * t) + q * (4 * j) ∧
      x + y + 2 * t - p * (4 * t) + q * (4 * j) < 4 * t ∧
      0 ≤ x - y + 2 * t + p * 4 - q * (4 * t) ∧ x - y + 2 * t + p * 4 - q * (4 * t) < 4 * t := by
    by_cases ht1 : t = 1
    · have hj0 : j = 0 := by omega
      subst t
      subst j
      refine ⟨(x + y + 2)/4, (x - y + 2 + 4 * ((x + y + 2)/4))/4, ?_, ?_, ?_, ?_⟩ <;> omega
    · exact skew_remainder (4 * t) (4 * j) 4 (x + y + 2 * t) (x - y + 2 * t)
        (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨p, q, hx, hxA, hy, hyA⟩ := hrem
  refine ⟨p, q, ?_⟩
  have he1 : (x - p * (2 * (t - 1)) - q * (2 * (t - j))) +
      (y - p * (2 * (t + 1)) + q * (2 * (t + j))) = x + y - p * (4 * t) + q * (4 * j) := by ring
  have he2 : (x - p * (2 * (t - 1)) - q * (2 * (t - j))) -
      (y - p * (2 * (t + 1)) + q * (2 * (t + j))) = x - y + p * 4 - q * (4 * t) := by ring
  rcases le_total 0 (x - p * (2 * (t - 1)) - q * (2 * (t - j))) with h1 | h1 <;>
    rcases le_total 0 (y - p * (2 * (t + 1)) + q * (2 * (t + j))) with h2 | h2 <;>
    simp only [abs_of_nonneg, abs_of_nonpos, h1, h2] <;> omega

private theorem hom_diamond_cover {G : Type*} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) (t j : ℤ) (ht : 1 ≤ t) (hj : 0 ≤ j) (hjt : j < t)
    (hv : f (2 * (t - j), -2 * (t + j)) = 0)
    (hw : f (2 * (t - 1), 2 * (t + 1)) = 0)
    (hsur : Function.Surjective f) (g : G) :
    ∃ x y : ℤ, g = x • f (1, 0) + y • f (0, 1) ∧ |x| + |y| ≤ 2 * t := by
  obtain ⟨⟨x, y⟩, rfl⟩ := hsur g
  obtain ⟨p, q, hbound⟩ := integer_diamond_cover t j x y ht hj hjt
  let r := x - p * (2 * (t - 1)) - q * (2 * (t - j))
  let s := y - p * (2 * (t + 1)) + q * (2 * (t + j))
  refine ⟨r, s, ?_, hbound⟩
  have he : (r, s) = (x, y) - p • (2 * (t - 1), 2 * (t + 1)) -
      q • (2 * (t - j), -2 * (t + j)) := by
    ext <;> simp [r, s, sub_eq_add_neg] <;> ring
  have hrep : f (r, s) = f (x, y) := by
    rw [he, map_sub, map_sub, map_zsmul, map_zsmul, hv, hw]
    simp
  rw [← hrep]
  have he' : (r, s) = r • (1, 0) + s • (0, 1) := by ext <;> simp
  rw [he', map_add, map_zsmul, map_zsmul]

private def matrix_map (N : ℕ) (r s c d : ℤ) :
    (ℤ × ℤ) →+ (ZMod 2 × ZMod N) where
  toFun z := (↑(r * z.1 + s * z.2), ↑(c * z.1 + d * z.2))
  map_zero' := by simp
  map_add' z w := by
    apply Prod.ext
    · change (↑(r * (z.1 + w.1) + s * (z.2 + w.2)) : ZMod 2) =
        ↑(r * z.1 + s * z.2) + ↑(r * w.1 + s * w.2)
      push_cast
      ring
    · change (↑(c * (z.1 + w.1) + d * (z.2 + w.2)) : ZMod N) =
        ↑(c * z.1 + d * z.2) + ↑(c * w.1 + d * w.2)
      push_cast
      ring

private theorem matrix_map_zero (N : ℕ) (r s c d x y : ℤ)
    (h1 : (2 : ℤ) ∣ r * x + s * y) (h2 : (N : ℤ) ∣ c * x + d * y) :
    matrix_map N r s c d (x, y) = 0 := by
  apply Prod.ext
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2

private theorem matrix_map_distinct (N : ℕ) (r s c d : ℤ) (hrs : r + s = 1) :
    matrix_map N r s c d (1, 0) ≠ matrix_map N r s c d (0, 1) := by
  intro he
  have he1 : (r : ZMod 2) = (s : ZMod 2) := by
    simpa [matrix_map] using congrArg Prod.fst he
  have hsum : (r : ZMod 2) + (s : ZMod 2) = 1 := by
    rw [← Int.cast_add, hrs]
    norm_num
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [he1] at hsum
  have hzero : (s : ZMod 2) + (s : ZMod 2) = 0 := by
    calc _ = (2 : ZMod 2) * (s : ZMod 2) := by ring
         _ = 0 := by rw [htwo]; simp
  rw [hzero] at hsum
  exact zero_ne_one hsum

private theorem even_family_map (N : ℕ) (t j : ℤ) (ht : Even t)
    (hN : (N : ℤ) = 4 * (t ^ 2 - j)) :
    ∃ f : (ℤ × ℤ) →+ (ZMod 2 × ZMod N), Function.Surjective f ∧
      f (2 * (t - j), -2 * (t + j)) = 0 ∧ f (2 * (t - 1), 2 * (t + 1)) = 0 ∧
      f (1, 0) ≠ f (0, 1) := by
  obtain ⟨h, hh⟩ := ht
  have ht' : t = 2 * h := by omega
  let f := matrix_map N h (1 - h) (t + 1) (1 - t)
  refine ⟨f, ?_, ?_, ?_, matrix_map_distinct N h (1 - h) (t + 1) (1 - t) (by ring)⟩
  · rintro ⟨u, v⟩
    obtain ⟨p, rfl⟩ := ZMod.intCast_surjective u
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective v
    refine ⟨((t - 1) * p + (1 - h) * z, (t + 1) * p - h * z), ?_⟩
    apply Prod.ext
    · change (↑(h * ((t - 1) * p + (1 - h) * z) + (1 - h) * ((t + 1) * p - h * z)) : ZMod 2) = ↑p
      congr 1
      rw [ht']
      ring
    · change (↑((t + 1) * ((t - 1) * p + (1 - h) * z) +
          (1 - t) * ((t + 1) * p - h * z)) : ZMod N) = ↑z
      congr 1
      rw [ht']
      ring
  · apply matrix_map_zero
    · refine ⟨h * (t - j) - (1 - h) * (t + j), ?_⟩; ring
    · refine ⟨1, ?_⟩
      rw [hN]
      ring
  · apply matrix_map_zero
    · refine ⟨h * (t - 1) + (1 - h) * (t + 1), ?_⟩; ring
    · refine ⟨0, ?_⟩; ring

private theorem odd_family_map (N : ℕ) (t j : ℤ) (ht : Odd t) (hj : Even j)
    (hN : (N : ℤ) = 4 * (t ^ 2 - j)) :
    ∃ f : (ℤ × ℤ) →+ (ZMod 2 × ZMod N), Function.Surjective f ∧
      f (2 * (t - j), -2 * (t + j)) = 0 ∧ f (2 * (t - 1), 2 * (t + 1)) = 0 ∧
      f (1, 0) ≠ f (0, 1) := by
  obtain ⟨h, hh⟩ := ht
  obtain ⟨l, hl⟩ := hj
  have ht' : t = 2 * h + 1 := by omega
  have hj' : j = 2 * l := by omega
  let d := t ^ 2 - j
  have hd : Odd d := by
    refine ⟨2 * h * (h + 1) - l, ?_⟩
    dsimp [d]
    rw [ht', hj']
    ring
  obtain ⟨q, hq⟩ := hd
  have hcop : IsCoprime (2 : ℤ) d := ⟨-q, 1, by nlinarith⟩
  obtain ⟨R, S, hbez⟩ := hcop.mul_left hcop
  have hbez' : 4 * R + d * S = 1 := by nlinarith [hbez]
  let f := matrix_map N (h + 1) (-h) (2 * (h + 1) - d) (d - 2 * h)
  refine ⟨f, ?_, ?_, ?_, matrix_map_distinct N (h + 1) (-h) (2 * (h + 1) - d) (d - 2 * h) (by ring)⟩
  · rintro ⟨u, v⟩
    obtain ⟨p, rfl⟩ := ZMod.intCast_surjective u
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective v
    let X := p + 2 * (R * (z - 2 * p))
    let Y := S * (z - 2 * p)
    refine ⟨(X + h * Y, X + (h + 1) * Y), ?_⟩
    apply Prod.ext
    · change (↑((h + 1) * (X + h * Y) + (-h) * (X + (h + 1) * Y)) : ZMod 2) = ↑p
      rw [show (h + 1) * (X + h * Y) + (-h) * (X + (h + 1) * Y) =
          p + 2 * (R * (z - 2 * p)) by dsimp [X, Y]; ring]
      push_cast
      simp [show (2 : ZMod 2) = 0 by decide]
    · change (↑((2 * (h + 1) - d) * (X + h * Y) + (d - 2 * h) * (X + (h + 1) * Y)) : ZMod N) = ↑z
      congr 1
      calc
        _ = 2 * p + (4 * R + d * S) * (z - 2 * p) := by dsimp [X, Y]; ring
        _ = z := by rw [hbez']; ring
  · apply matrix_map_zero
    · refine ⟨(h + 1) * (t - j) + h * (t + j), ?_⟩; ring
    · refine ⟨1 - t, ?_⟩
      rw [hN]
      dsimp [d]
      rw [ht']
      ring
  · apply matrix_map_zero
    · refine ⟨(h + 1) * (t - 1) - h * (t + 1), ?_⟩; ring
    · refine ⟨1, ?_⟩
      rw [hN]
      dsimp [d]
      rw [ht']
      ring

/-- A uniform sufficiency family. In particular, `0 ≤ 2 * j < t` covers the
allowed even-radius top strip. No converse or exclusion is asserted. -/
theorem result (t j : ℕ) (ht : 1 ≤ t) (hjt : j < t)
    (hpar : Even t ∨ Even j) :
    ∃ a b : ZMod 2 × ZMod (4 * (t ^ 2 - j)), a ≠ b ∧
      ∀ g, ∃ x y : ℤ, g = x • a + y • b ∧ |x| + |y| ≤ 2 * (t : ℤ) := by
  have hj2 : j ≤ t ^ 2 := by nlinarith
  have hN : ((4 * (t ^ 2 - j) : ℕ) : ℤ) = 4 * ((t : ℤ) ^ 2 - (j : ℤ)) := by
    rw [Nat.cast_mul, Nat.cast_sub hj2, Nat.cast_pow]
    norm_num
  have hpar' : Even (t : ℤ) ∨ Even (j : ℤ) := by
    rcases hpar with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have hex : ∃ f : (ℤ × ℤ) →+ (ZMod 2 × ZMod (4 * (t ^ 2 - j))),
      Function.Surjective f ∧ f (2 * ((t : ℤ) - j), -2 * ((t : ℤ) + j)) = 0 ∧
      f (2 * ((t : ℤ) - 1), 2 * ((t : ℤ) + 1)) = 0 ∧ f (1, 0) ≠ f (0, 1) := by
    rcases Int.even_or_odd (t : ℤ) with he | ho
    · exact even_family_map _ _ _ he hN
    · have hj : Even (j : ℤ) := hpar'.resolve_left (Int.not_even_iff_odd.mpr ho)
      exact odd_family_map _ _ _ ho hj hN
  obtain ⟨f, hsur, hv, hw, hdiff⟩ := hex
  refine ⟨f (1, 0), f (0, 1), hdiff, ?_⟩
  exact hom_diamond_cover f t j (by exact_mod_cast ht)
    (by exact_mod_cast Nat.zero_le j) (by exact_mod_cast hjt) hv hw hsur

#print axioms result

end D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency

/- GID: D5/S3/FiniteGroups/BajnokBeattySharpMaximum
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySharpMaximum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact attained maximum for finite noncyclic abelian signed covers of radius at least three. -/

import D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The Bajnok--Beatty sharp maximum

The literal maximum of Bajnok--Beatty, arXiv:2406.04045v1, Conjecture 1.6,
for every radius s >= 3, every finite noncyclic abelian group in any universe,
and every distinct signed covering pair. The explicit lower constructions and
their reflection argument are the known lower direction of Theorem 1.7.
The universal upper direction is supplied by BajnokBeattyFiniteUpper.
No current literature novelty or publication priority is claimed.

proof_shape: sharp_maximum: content.
admission_basis: escape-witness.
escape_witness: reflection_cover_hom constructs a radius-s representative for
any coefficient pair from two diagonal relations with A+B <= 2s+1. This live
construction proves the actual signed covers in both attainment families.
The private known-lower, reflection and arithmetic helpers are consumed by
sharp_maximum; they do not constitute independent new literature results.
All subtractions in MaximumOrder are natural-number subtractions; the private
composite arithmetic proof verifies the exact nontruncating identities.
-/

set_option autoImplicit false

universe u

namespace D5.S3.FiniteGroups.BajnokBeattySharpMaximum

/-- The natural-number expression in Bajnok--Beatty, Conjecture 1.6. -/
def MaximumOrder (s : ℕ) : ℕ :=
  if Nat.Prime (2 * s + 1) then 2 * s^2
  else 2 * s^2 + 2 * s - (Nat.minFac (2 * s + 1)^2 - 1) / 2

/-- Integer coefficient map; no quotient or exact-kernel assertion. -/
private def coefficientHom {G : Type*} [AddCommGroup G] (a b : G) : (ℤ × ℤ) →+ G where
  toFun z := z.1 • a + z.2 • b
  map_zero' := by simp
  map_add' z w := by
    change (z.1 + w.1) • a + (z.2 + w.2) • b =
      (z.1 • a + z.2 • b) + (w.1 • a + w.2 • b)
    simp only [add_zsmul]
    abel

/-- Two diagonal relations give a radius bound for every coefficient pair.
The radius and all inequalities here are integers; the odd boundary 2s+1
is retained exactly. -/
private theorem reflection_cover_hom {G : Type*} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) (A B s : ℤ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hsum : A + B ≤ 2 * s + 1)
    (hplus : f (A, B) = 0) (hminus : f (A, -B) = 0)
    (x y : ℤ) :
    ∃ u v : ℤ, f (u, v) = f (x, y) ∧ |u| + |v| ≤ s := by
  have hvertical : f (0, 2 * B) = 0 := by
    have hv : ((0, 2 * B) : ℤ × ℤ) = (A, B) - (A, -B) := by
      apply Prod.ext <;> dsimp <;> ring
    rw [hv, map_sub, hplus, hminus, sub_self]
  have hmultiple (m u v : ℤ) : f (m * u, m * v) = m • f (u, v) := by
    simpa only [Prod.smul_mk, Int.zsmul_eq_mul] using f.map_zsmul m (u, v)
  let q : ℤ := x / A
  let r : ℤ := x % A
  let z : ℤ := y - q * B
  let k : ℤ := (z + B) / (2 * B)
  let w : ℤ := (z + B) % (2 * B) - B
  have hr0 : 0 ≤ r := Int.emod_nonneg x (by omega)
  have hrA : r < A := Int.emod_lt_of_pos x (by omega)
  have hw0 : -B ≤ w := by
    have hm := Int.emod_nonneg (z + B) (show 2 * B ≠ 0 by omega)
    dsimp [w]
    omega
  have hwB : w < B := by
    have hm := Int.emod_lt_of_pos (z + B) (show 0 < 2 * B by omega)
    dsimp [w]
    omega
  have hx : x = r + q * A := by
    dsimp [r, q]
    nlinarith [Int.emod_add_mul_ediv x A]
  have hz : z = w + k * (2 * B) := by
    dsimp [w, k]
    nlinarith [Int.emod_add_mul_ediv (z + B) (2 * B)]
  have hreduced : f (r, w) = f (x, y) := by
    have hp : ((r, w) : ℤ × ℤ) =
        (x, y) - (q * A, q * B) - (k * 0, k * (2 * B)) := by
      apply Prod.ext
      · change r = x - q * A - k * 0
        nlinarith [hx]
      · change w = y - q * B - k * (2 * B)
        have hzdef : z = y - q * B := rfl
        nlinarith [hz, hzdef]
    rw [hp, map_sub, map_sub, hmultiple, hmultiple,
      hplus, hvertical, smul_zero, smul_zero, sub_zero, sub_zero]
  by_cases hsmall : |r| + |w| ≤ s
  · exact ⟨r, w, hreduced, hsmall⟩
  · by_cases hw : 0 ≤ w
    · refine ⟨r - A, w - B, ?_, ?_⟩
      · have hp : ((r - A, w - B) : ℤ × ℤ) = (r, w) - (A, B) := rfl
        rw [hp, map_sub, hplus, sub_zero]
        exact hreduced
      · rw [abs_of_nonpos (show r - A ≤ 0 by omega),
          abs_of_nonpos (show w - B ≤ 0 by omega)]
        rw [abs_of_nonneg hr0, abs_of_nonneg hw] at hsmall
        omega
    · refine ⟨r - A, w + B, ?_, ?_⟩
      · have hp : ((r - A, w + B) : ℤ × ℤ) = (r, w) - (A, -B) := by
          apply Prod.ext <;> dsimp <;> ring
        rw [hp, map_sub, hminus, sub_zero]
        exact hreduced
      · rw [abs_of_nonpos (show r - A ≤ 0 by omega),
          abs_of_nonneg (show 0 ≤ w + B by omega)]
        rw [abs_of_nonneg hr0, abs_of_nonpos (show w ≤ 0 by omega)] at hsmall
        omega

private theorem signed_cover_of_relations {G : Type*} [AddCommGroup G]
    (s : ℕ) (a b : G) (A B : ℤ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hsum : A + B ≤ 2 * (s : ℤ) + 1)
    (hplus : A • a + B • b = 0) (hminus : A • a - B • b = 0)
    (hsurj : ∀ g : G, ∃ x y : ℤ, x • a + y • b = g) :
    ∀ g : G, ∃ x y : ℤ, |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g := by
  have hm : coefficientHom a b (A, -B) = 0 := by
    change A • a + (-B) • b = 0
    simpa only [neg_zsmul, sub_eq_add_neg] using hminus
  intro g
  obtain ⟨x, y, hxy⟩ := hsurj g
  obtain ⟨v, w, hvw, hnorm⟩ :=
    reflection_cover_hom (coefficientHom a b) A B s hA hB hsum hplus hm x y
  exact ⟨v, w, hnorm, hvw.trans hxy⟩

private theorem not_isAddCyclic_zmod_prod (m n d : ℕ)
    (hd : 2 ≤ d) (hm : d ∣ m) (hn : d ∣ n) :
    ¬ IsAddCyclic (ZMod m × ZMod n) := by
  intro hc
  have hcop := (AddGroup.isAddCyclic_prod_iff.mp hc).2.2
  rw [Nat.card_zmod, Nat.card_zmod] at hcop
  have hdd : Nat.Coprime d d := hcop.of_dvd hm hn
  have hd1 : d = 1 := by simpa [Nat.Coprime] using hdd
  omega

private theorem zmod_one_ne_zero (m : ℕ) (hm : 2 ≤ m) : (1 : ZMod m) ≠ 0 := by
  intro h
  have hd : m ∣ 1 := (ZMod.natCast_eq_zero_iff 1 m).mp (by simpa using h)
  have := Nat.le_of_dvd (by omega : 0 < (1 : ℕ)) hd
  omega

/-- The known baseline family, with its actual distinct pair. -/
private theorem baseline_attainment (s : ℕ) (hs : 3 ≤ s) :
    ∃ a b : ZMod s × ZMod (2 * s), a ≠ b ∧
      ¬ IsAddCyclic (ZMod s × ZMod (2 * s)) ∧
      (∀ g : ZMod s × ZMod (2 * s), ∃ x y : ℤ,
        |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) ∧
      Finite (ZMod s × ZMod (2 * s)) ∧
      Nat.card (ZMod s × ZMod (2 * s)) = 2 * s^2 := by
  letI : NeZero s := ⟨by omega⟩
  letI : NeZero (2 * s) := ⟨by omega⟩
  let a : ZMod s × ZMod (2 * s) := (1, 1)
  let b : ZMod s × ZMod (2 * s) := (0, 1)
  have hrels : (s : ℤ) • a + (s : ℤ) • b = 0 ∧
      (s : ℤ) • a - (s : ℤ) • b = 0 := by
    have hs0 : (s : ZMod s) = 0 := ZMod.natCast_self s
    have h2s : ((2 * s : ℕ) : ZMod (2 * s)) = 0 := ZMod.natCast_self (2 * s)
    constructor
    · apply Prod.ext
      · simpa [a, b, zsmul_eq_mul] using hs0
      · simpa [a, b, zsmul_eq_mul, Nat.cast_mul, two_mul] using h2s
    · apply Prod.ext
      · simpa [a, b, zsmul_eq_mul] using hs0
      · simp [a, b, zsmul_eq_mul]
  have hsurj (g : ZMod s × ZMod (2 * s)) :
      ∃ x y : ℤ, x • a + y • b = g := by
    obtain ⟨α, hα⟩ := ZMod.intCast_surjective g.1
    obtain ⟨β, hβ⟩ := ZMod.intCast_surjective g.2
    refine ⟨α, β - α, ?_⟩
    apply Prod.ext
    · simpa [a, b, zsmul_eq_mul] using hα
    · change α • (1 : ZMod (2 * s)) + (β - α) • (1 : ZMod (2 * s)) = g.2
      calc
        _ = (β : ZMod (2 * s)) := by
          simp only [zsmul_eq_mul, Int.cast_sub]
          ring
        _ = g.2 := hβ
  have hcover := signed_cover_of_relations s a b s s
    (by omega) (by omega) (by omega) hrels.1 hrels.2 hsurj
  refine ⟨a, b, ?_, ?_, hcover, inferInstance, ?_⟩
  · intro he
    have hfirst : (1 : ZMod s) = 0 := congrArg Prod.fst he
    exact zmod_one_ne_zero s (by omega) hfirst
  · apply not_isAddCyclic_zmod_prod s (2 * s) s (by omega) (dvd_refl s)
    exact ⟨2, by ring⟩
  · simp only [Nat.card_prod, Nat.card_zmod]
    ring

/-- The known composite family; the two relation vectors have diagonal
lengths summing to the exact odd boundary `2s+1`. -/
private theorem composite_attainment (p t s : ℕ) (hp : 3 ≤ p) (ht : 1 ≤ t)
    (hsize : p * (2 * t + 1) = 2 * s + 1) :
    ∃ a b : ZMod p × ZMod (2 * p * t * (t + 1)), a ≠ b ∧
      ¬ IsAddCyclic (ZMod p × ZMod (2 * p * t * (t + 1))) ∧
      (∀ g : ZMod p × ZMod (2 * p * t * (t + 1)), ∃ x y : ℤ,
        |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) ∧
      Finite (ZMod p × ZMod (2 * p * t * (t + 1))) ∧
      2 * Nat.card (ZMod p × ZMod (2 * p * t * (t + 1))) =
        (2 * s + 1)^2 - p^2 := by
  let N : ℕ := 2 * p * t * (t + 1)
  have hN : 2 ≤ N := by
    have hpt : 3 ≤ p * t := by simpa using Nat.mul_le_mul hp ht
    have hbig : 3 ≤ p * t * (t + 1) := by
      calc
        3 = 3 * 1 := by omega
        _ ≤ (p * t) * (t + 1) := Nat.mul_le_mul hpt (by omega)
    have heq : N = 2 * (p * t * (t + 1)) := by dsimp [N]; ring
    omega
  letI : NeZero p := ⟨by omega⟩
  letI : NeZero N := ⟨by omega⟩
  let a : ZMod p × ZMod N := (1, (t : ZMod N))
  let b : ZMod p × ZMod N := (1, ((t + 1 : ℕ) : ZMod N))
  have hrels : ((p * (t + 1) : ℕ) : ℤ) • a +
        ((p * t : ℕ) : ℤ) • b = 0 ∧
      ((p * (t + 1) : ℕ) : ℤ) • a -
        ((p * t : ℕ) : ℤ) • b = 0 := by
    have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
    have hM : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
    constructor
    · apply Prod.ext
      · simp [a, b, zsmul_eq_mul, Nat.cast_mul, Nat.cast_add, hp0]
      · change ((p * (t + 1) : ℕ) : ℤ) • (t : ZMod N) +
          ((p * t : ℕ) : ℤ) • ((t + 1 : ℕ) : ZMod N) = 0
        calc
          _ = ((N : ℕ) : ZMod N) := by
            simp only [zsmul_eq_mul, Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat, Nat.cast_mul, Nat.cast_add,
              Nat.cast_one, Nat.cast_ofNat, N]
            ring
          _ = 0 := hM
    · apply Prod.ext
      · simp [a, b, zsmul_eq_mul, Nat.cast_mul, Nat.cast_add, hp0]
      · change ((p * (t + 1) : ℕ) : ℤ) • (t : ZMod N) -
          ((p * t : ℕ) : ℤ) • ((t + 1 : ℕ) : ZMod N) = 0
        simp only [zsmul_eq_mul, Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
  have hsurj (g : ZMod p × ZMod N) : ∃ x y : ℤ, x • a + y • b = g := by
    obtain ⟨α, hα⟩ := ZMod.intCast_surjective g.1
    obtain ⟨β, hβ⟩ := ZMod.intCast_surjective g.2
    refine ⟨((t : ℤ) + 1) * α - β, β - (t : ℤ) * α, ?_⟩
    apply Prod.ext
    · change ((((t : ℤ) + 1) * α - β) • (1 : ZMod p) +
        (β - (t : ℤ) * α) • (1 : ZMod p)) = g.1
      calc
        _ = (α : ZMod p) := by
          simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one,
            Int.cast_natCast]
          ring
        _ = g.1 := hα
    · change ((((t : ℤ) + 1) * α - β) • (t : ZMod N) +
        (β - (t : ℤ) * α) • ((t + 1 : ℕ) : ZMod N)) = g.2
      calc
        _ = (β : ZMod N) := by
          simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one,
            Int.cast_natCast, Nat.cast_add, Nat.cast_one]
          ring
        _ = g.2 := hβ
  have hcover : ∀ g : ZMod p × ZMod N, ∃ x y : ℤ,
      |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g := by
    apply signed_cover_of_relations s a b
      ((p * (t + 1) : ℕ) : ℤ) ((p * t : ℕ) : ℤ) ?_ ?_ ?_ hrels.1 hrels.2 hsurj
    · have h : (1 : ℕ) ≤ p * (t + 1) :=
        Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
      exact_mod_cast h
    · have h : (1 : ℕ) ≤ p * t :=
        Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
      exact_mod_cast h
    · have hi : (p : ℤ) * (2 * (t : ℤ) + 1) = 2 * (s : ℤ) + 1 := by
        exact_mod_cast hsize
      push_cast
      nlinarith [hi]
  refine ⟨a, b, ?_, ?_, hcover, inferInstance, ?_⟩
  · intro he
    have he' : (t : ZMod N) = (t : ZMod N) + 1 := by
      simpa only [a, b, Nat.cast_add, Nat.cast_one] using congrArg Prod.snd he
    have hone : (1 : ZMod N) = 0 :=
      add_left_cancel (show (t : ZMod N) + 1 = (t : ZMod N) + 0 by
        simpa using he'.symm)
    exact zmod_one_ne_zero N hN hone
  · apply not_isAddCyclic_zmod_prod p N p (by omega) (dvd_refl p)
    exact ⟨2 * t * (t + 1), by dsimp [N]; ring⟩
  · have hcard : Nat.card (ZMod p × ZMod N) = 2 * p^2 * t * (t + 1) := by
      simp only [Nat.card_prod, Nat.card_zmod, N]
      ring
    change 2 * Nat.card (ZMod p × ZMod N) = (2 * s + 1)^2 - p^2
    rw [hcard]
    have hpoly : (p * (2 * t + 1))^2 =
        2 * (2 * p^2 * t * (t + 1)) + p^2 := by ring
    rw [hsize] at hpoly
    omega

/-- For composite 2s+1, its least prime factor and odd cofactor give t≥1.
Mathlib's minFac_le_div reuses its existing least-factor arithmetic; no new
factorization theorem or floor bound is needed. -/
theorem minFac_parameters (s : ℕ) (hs : 3 ≤ s)
    (hcomposite : ¬ Nat.Prime (2 * s + 1)) :
    Nat.Prime (Nat.minFac (2 * s + 1)) ∧
    3 ≤ Nat.minFac (2 * s + 1) ∧
    ∃ t : ℕ, 1 ≤ t ∧ Nat.minFac (2 * s + 1) * (2 * t + 1) = 2 * s + 1 := by
  let n : ℕ := 2 * s + 1
  let p : ℕ := Nat.minFac n
  let q : ℕ := n / p
  have hn1 : n ≠ 1 := by dsimp [n]; omega
  have hnpos : 0 < n := by dsimp [n]; omega
  have hpprime : Nat.Prime p := Nat.minFac_prime hn1
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  have hp3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hpprime.two_le
    have hpne : p ≠ 2 := by
      intro he
      have hd : 2 ∣ 2 * s + 1 := by simpa only [he, n] using hpdvd
      exact Nat.two_not_dvd_two_mul_add_one s hd
    omega
  have hprod : p * q = n := Nat.mul_div_cancel' hpdvd
  have hpq : p ≤ q := Nat.minFac_le_div hnpos hcomposite
  have hq3 : 3 ≤ q := hp3.trans hpq
  have hoddprod : Odd (p * q) := by
    rw [hprod]
    exact ⟨s, by dsimp [n]⟩
  have hqodd : Odd q := (Nat.odd_mul.mp hoddprod).2
  obtain ⟨t, htq⟩ := odd_iff_exists_bit1.mp hqodd
  refine ⟨hpprime, hp3, t, ?_, ?_⟩
  · omega
  · calc
      p * (2 * t + 1) = p * q := by rw [htq]
      _ = n := hprod

/-- Exact arithmetic for the composite expression: its two subtractions do
not truncate, and the odd square correction is an integer at least four. -/
theorem composite_arithmetic (s : ℕ) (hs : 3 ≤ s)
    (hcomposite : ¬ Nat.Prime (2 * s + 1)) :
    2 * (2 * s^2 + 2 * s - (Nat.minFac (2 * s + 1)^2 - 1) / 2) =
        (2 * s + 1)^2 - Nat.minFac (2 * s + 1)^2 ∧
      2 * s^2 + 2 * s - (Nat.minFac (2 * s + 1)^2 - 1) / 2 =
        ((2 * s + 1)^2 - Nat.minFac (2 * s + 1)^2) / 2 ∧
      2 * s^2 + 2 * s - (Nat.minFac (2 * s + 1)^2 - 1) / 2 ≤
        2 * s^2 + 2 * s - 4 := by
  let p : ℕ := Nat.minFac (2 * s + 1)
  let A : ℕ := 2 * s^2 + 2 * s
  obtain ⟨_, hp3, t, _, hsize⟩ := minFac_parameters s hs hcomposite
  change 3 ≤ p at hp3
  change p * (2 * t + 1) = 2 * s + 1 at hsize
  have hoddprod : Odd (p * (2 * t + 1)) := by
    rw [hsize]
    exact ⟨s, by omega⟩
  have hpodd : Odd p := (Nat.odd_mul.mp hoddprod).1
  obtain ⟨r, hr⟩ := odd_iff_exists_bit1.mp hpodd
  let q : ℕ := 2 * r * (r + 1)
  have hpsquare : p^2 = 2 * q + 1 := by rw [hr]; dsimp [q]; ring
  have hp9 : 9 ≤ p^2 := by nlinarith [hp3]
  have hq4 : 4 ≤ q := by omega
  have hcorrection : (p^2 - 1) / 2 = q := by omega
  have hpsmall : p^2 ≤ 2 * s + 1 :=
    Nat.minFac_sq_le_self (by omega) hcomposite
  have hexpand : (2 * s + 1)^2 = 2 * A + 1 := by dsimp [A]; ring
  have hnsmall : 2 * s + 1 ≤ (2 * s + 1)^2 := by nlinarith
  have hp_le_square : p^2 ≤ (2 * s + 1)^2 := hpsmall.trans hnsmall
  have hqA : q ≤ A := by omega
  have hinner : 1 ≤ p^2 := by omega
  have houter : (p^2 - 1) / 2 ≤ A := by rw [hcorrection]; exact hqA
  have hbalance : (A - q) + q = A := Nat.sub_add_cancel hqA
  have hdifference : (2 * s + 1)^2 - p^2 = 2 * (A - q) := by omega
  change 2 * (A - (p^2 - 1) / 2) = (2 * s + 1)^2 - p^2 ∧
    A - (p^2 - 1) / 2 = ((2 * s + 1)^2 - p^2) / 2 ∧
    A - (p^2 - 1) / 2 ≤ A - 4
  rw [hcorrection, hdifference]
  omega

/-- The literal original maximum, both as a universal bound and as an attained
order. The universal assertion ranges over every universe and every distinct
signed covering pair; the witness is an explicit finite product of residue groups.
The second bound is the “in particular” assertion of Conjecture 1.6. -/
theorem sharp_maximum (s : ℕ) (hs : 3 ≤ s) :
    (∀ (G : Type u) [AddCommGroup G] [Finite G],
      ¬ IsAddCyclic G → ∀ a b : G, a ≠ b →
        (∀ g : G, ∃ x y : ℤ,
          |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) →
        Nat.card G ≤ MaximumOrder s ∧ Nat.card G ≤ 2 * s^2 + 2 * s - 4) ∧
    (∃ c k : ℕ, 2 ≤ c ∧ 1 ≤ k ∧
      ∃ a b : ZMod c × ZMod (c * k), a ≠ b ∧
        ¬ IsAddCyclic (ZMod c × ZMod (c * k)) ∧
        (∀ g : ZMod c × ZMod (c * k), ∃ x y : ℤ,
          |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) ∧
        Finite (ZMod c × ZMod (c * k)) ∧
        Nat.card (ZMod c × ZMod (c * k)) = MaximumOrder s) := by
  classical
  have hupper : ∀ (G : Type u) [AddCommGroup G] [Finite G],
      ¬ IsAddCyclic G → ∀ a b : G,
        (∀ g : G, ∃ x y : ℤ,
          |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) →
        Nat.card G ≤ MaximumOrder s := by
    intro G _ _ hnoncyclic a b hcover
    have hu := BajnokBeattyFiniteUpper.finite_noncyclic_upper hs hnoncyclic a b hcover
    by_cases hp : Nat.Prime (2 * s + 1)
    · simpa only [MaximumOrder, if_pos hp] using hu
    · simp only [if_neg hp] at hu
      have heq := (composite_arithmetic s hs hp).1
      rw [MaximumOrder, if_neg hp]
      omega
  have huniform : MaximumOrder s ≤ 2 * s^2 + 2 * s - 4 := by
    by_cases hp : Nat.Prime (2 * s + 1)
    · rw [MaximumOrder, if_pos hp]
      omega
    · rw [MaximumOrder, if_neg hp]
      exact (composite_arithmetic s hs hp).2.2
  constructor
  · intro G _ _ hnoncyclic a b _ hcover
    have hu := hupper G hnoncyclic a b hcover
    exact ⟨hu, hu.trans huniform⟩
  · by_cases hp : Nat.Prime (2 * s + 1)
    · refine ⟨s, 2, by omega, by omega, ?_⟩
      rw [show s * 2 = 2 * s by omega]
      simpa only [MaximumOrder, if_pos hp] using baseline_attainment s hs
    · obtain ⟨_, hp3, t, ht, hsize⟩ := minFac_parameters s hs hp
      let p : ℕ := Nat.minFac (2 * s + 1)
      obtain ⟨a, b, hab, hnoncyclic, hcover, hfinite, htwice⟩ :=
        composite_attainment p t s hp3 ht hsize
      have hcard : Nat.card (ZMod p × ZMod (2 * p * t * (t + 1))) =
          MaximumOrder s := by
        rw [MaximumOrder, if_neg hp]
        have heq := (composite_arithmetic s hs hp).1
        have htwice' : 2 * Nat.card (ZMod p × ZMod (2 * p * t * (t + 1))) =
            2 * (2 * s^2 + 2 * s - (Nat.minFac (2 * s + 1)^2 - 1) / 2) :=
          htwice.trans heq.symm
        omega
      have hmod : p * (2 * t * (t + 1)) = 2 * p * t * (t + 1) := by ring
      have hk : 1 ≤ 2 * t * (t + 1) := by
        have hprod : 1 ≤ t * (t + 1) := by
          simpa using Nat.mul_le_mul ht (show 1 ≤ t + 1 by omega)
        nlinarith
      refine ⟨p, 2 * t * (t + 1), by omega, hk, ?_⟩
      rw [hmod]
      exact
        (show ∃ a b : ZMod p × ZMod (2 * p * t * (t + 1)), a ≠ b ∧
          ¬ IsAddCyclic (ZMod p × ZMod (2 * p * t * (t + 1))) ∧
          (∀ g : ZMod p × ZMod (2 * p * t * (t + 1)), ∃ x y : ℤ,
            |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) ∧
          Finite (ZMod p × ZMod (2 * p * t * (t + 1))) ∧
          Nat.card (ZMod p × ZMod (2 * p * t * (t + 1))) = MaximumOrder s from
          ⟨a, b, hab, hnoncyclic, hcover, hfinite, hcard⟩)

end D5.S3.FiniteGroups.BajnokBeattySharpMaximum

/- GID: D5/S3/Arith/Primes/LucasSquareClassification
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/LucasSquareClassification
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The only square Lucas numbers have indices one and three, and the only twice-square Lucas numbers have indices zero and six. -/

import D5.S1.Scale.LucasDoubling
import D5.S3.Arith.GoldenApparition
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.LucasSquareClassification

open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition

set_option maxHeartbeats 1200000 in
/-- Cohn's complete classification of Lucas squares and twice squares.
The dyadic Lucas modulus supplies the quadratic obstruction at each
remaining index. -/

theorem lucas_square_classifications (n : ℕ) :
    (IsSquare (goldenLucas n) ↔ n = 1 ∨ n = 3) ∧
      ((∃ x : ℤ, goldenLucas n = 2 * x ^ 2) ↔ n = 0 ∨ n = 6) := by
  have htrace (b m : ℕ) :
      (goldenLucas m : ZMod b) =
        2 * ((GoldenMod.phi : GoldenMod b) ^ m).a +
          ((GoldenMod.phi : GoldenMod b) ^ m).b := by
    have hy : GoldenMod.reduce b phi = (GoldenMod.phi : GoldenMod b) := by
      ext <;> norm_num [GoldenMod.reduce, phi, GoldenMod.phi]
    calc
      (goldenLucas m : ZMod b) =
          2 * (GoldenMod.reduce b (phi ^ m)).a +
            (GoldenMod.reduce b (phi ^ m)).b := by
              simp [goldenLucas, trace, GoldenMod.reduce]
      _ = _ := by rw [map_pow, hy]
  have hperiod (b d m : ℕ)
      (hd : (GoldenMod.phi : GoldenMod b) ^ d = 1) :
      (goldenLucas m : ZMod b) = (goldenLucas (m % d) : ZMod b) := by
    rw [htrace, htrace, pow_eq_pow_mod m hd]
  have hLmod (r : ℕ) : (goldenLucas (2 ^ (r + 1)) : ZMod 4) = 3 := by
    induction r with
    | zero => change (goldenLucas 2 : ZMod 4) = 3; decide
    | succ r ih =>
      have he : Even (2 ^ (r + 1)) :=
        (Nat.even_pow).2 ⟨by decide, by omega⟩
      have hi : 2 ^ (r + 1 + 1) = 2 * 2 ^ (r + 1) := by ring
      rw [hi, golden_lucas_two_mul, he.neg_one_pow]
      push_cast
      rw [ih]
      decide
  have hLthree (r : ℕ) :
      (goldenLucas (2 ^ (r + 2)) : ZMod 3) = 1 ∨
        (goldenLucas (2 ^ (r + 2)) : ZMod 3) = 2 := by
    induction r with
    | zero => left; change (goldenLucas 4 : ZMod 3) = 1; decide
    | succ r ih =>
      have he : Even (2 ^ (r + 2)) :=
        (Nat.even_pow).2 ⟨by decide, by omega⟩
      have hi : 2 ^ (r + 1 + 2) = 2 * 2 ^ (r + 2) := by ring
      rw [hi, golden_lucas_two_mul, he.neg_one_pow]
      push_cast
      rcases ih with ih | ih <;> rw [ih]
      · right; decide
      · right; decide
  have hmodulus (r : ℕ) : ∃ b : ℕ, b % 4 = 3 ∧
      (GoldenMod.phi : GoldenMod b) ^ (4 * 2 ^ r) = -1 ∧
      (0 < r → Nat.Coprime 6 b) := by
    let u : ℕ := 2 ^ r
    have hu : 0 < u := pow_pos (by decide) r
    let L : ℤ := goldenLucas (2 * u)
    have hLpos : 0 < L := by
      have hidx : 2 * u = (2 * u - 1) + 1 := by omega
      change 0 < goldenLucas (2 * u)
      rw [hidx, golden_lucas_succ_eq_fib_add_fib]
      have hpos : 0 < Nat.fib (2 * u - 1 + 2) := Nat.fib_pos.mpr (by omega)
      positivity
    let b : ℕ := L.toNat
    have hbcast : (b : ℤ) = L := Int.toNat_of_nonneg (le_of_lt hLpos)
    have hidx : 2 * u = 2 ^ (r + 1) := by dsimp [u]; ring
    have hb4 : b % 4 = 3 := by
      have hz : (b : ZMod 4) = 3 := by
        calc
          (b : ZMod 4) = (L : ZMod 4) := by rw [← hbcast]; simp
          _ = 3 := by dsimp [L]; rw [hidx]; exact hLmod r
      exact (ZMod.natCast_eq_natCast_iff' b 3 4).mp hz
    have hLzero : (L : ZMod b) = 0 := by rw [← hbcast]; simp
    have hchar : (phi ^ (2 * u)) ^ 2 + 1 =
        (L : GoldenInt) * phi ^ (2 * u) := by
      have hnorm : norm (phi ^ (2 * u)) = 1 := by
        rw [norm_phi_pow]
        exact (even_two_mul u).neg_one_pow
      have hnormGI : phi ^ (2 * u) * conj (phi ^ (2 * u)) = 1 := by
        rw [← norm_eq_mul_conj, hnorm]
        norm_num
      calc
        (phi ^ (2 * u)) ^ 2 + 1 =
            (phi ^ (2 * u) + conj (phi ^ (2 * u))) * phi ^ (2 * u) := by
              rw [pow_two]
              linear_combination -hnormGI
        _ = (L : GoldenInt) * phi ^ (2 * u) := by
          rw [add_conj_eq_trace]
          rfl
    let f := GoldenMod.reduce b
    let y : GoldenMod b := f phi
    have hanti : y ^ (4 * u) = -1 := by
      have h := congrArg f hchar
      have hscalar : f (L : GoldenInt) = 0 := by
        ext <;> simp [f, GoldenMod.reduce, hLzero]
      simp only [map_add, map_pow, map_one, map_mul,
        hscalar, zero_mul] at h
      have hi : 4 * u = (2 * u) * 2 := by omega
      rw [hi, pow_mul]
      dsimp [y]
      linear_combination h
    have hy : y = GoldenMod.phi := by
      ext <;> simp [y, f, GoldenMod.phi]
    refine ⟨b, hb4, ?_, ?_⟩
    · simpa only [hy, u] using hanti
    · intro hr
      have hthree : (b : ZMod 3) = 1 ∨ (b : ZMod 3) = 2 := by
        have hi : 2 * u = 2 ^ ((r - 1) + 2) := by
          rw [hidx]
          congr 1
          omega
        have hc := hLthree (r - 1)
        have hcast : (b : ZMod 3) = (L : ZMod 3) := by
          rw [← hbcast]
          simp
        rw [hcast]
        change (goldenLucas (2 * u) : ZMod 3) = 1 ∨
          (goldenLucas (2 * u) : ZMod 3) = 2
        rw [hi]
        exact hc
      have hb3 : ¬3 ∣ b := by
        intro hdiv
        have hz : (b : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff b 3).mpr hdiv
        rcases hthree with hthree | hthree
        · rw [hz] at hthree
          exact (by decide : (0 : ZMod 3) ≠ 1) hthree
        · rw [hz] at hthree
          exact (by decide : (0 : ZMod 3) ≠ 2) hthree
      have htwo : Nat.Coprime 2 b := Nat.coprime_two_left.mpr
        (Nat.odd_iff.mpr (by omega))
      have hthree : Nat.Coprime 3 b := Nat.prime_three.coprime_iff_not_dvd.mpr hb3
      change Nat.Coprime (2 * 3) b
      exact Nat.coprime_mul_iff_left.mpr ⟨htwo, hthree⟩
  have hplus (b r s j m : ℕ)
      (ha : (GoldenMod.phi : GoldenMod b) ^ (4 * 2 ^ r) = -1)
      (hs : Odd s) (hm : m = 4 * 2 ^ r * s + j) :
      (goldenLucas m : ZMod b) = -(goldenLucas j : ZMod b) := by
    have hp : (GoldenMod.phi : GoldenMod b) ^ m =
        -((GoldenMod.phi : GoldenMod b) ^ j) := by
      rw [hm, pow_add, pow_mul, ha, hs.neg_one_pow]
      simp
    have hc := congrArg (fun v : GoldenMod b => 2 * v.a + v.b) hp
    rw [htrace, htrace]
    simpa only [GoldenMod.a_neg, GoldenMod.b_neg, mul_neg, ← neg_add] using hc
  have hnonsquare (b a : ℕ) (hb4 : b % 4 = 3) (hab : Nat.Coprime a b) :
      ¬ IsSquare (- ((a : ZMod b) ^ 2)) := by
    have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
    have hgcd : (a : ℤ).gcd (b : ℤ) = 1 := by
      change Nat.gcd a b = 1 at hab
      simpa only [Int.gcd_natCast_natCast] using hab
    have hj : jacobiSym (-((a : ℤ) ^ 2)) b = -1 := by
      rw [neg_eq_neg_one_mul, jacobiSym.mul_left,
        jacobiSym.at_neg_one hbodd, ZMod.χ₄_nat_three_mod_four hb4,
        jacobiSym.sq_one' hgcd]
      norm_num
    simpa only [Int.cast_neg, Int.cast_pow, Int.cast_natCast] using
      ZMod.nonsquare_of_jacobiSym_eq_neg_one hj
  constructor
  · constructor
    · intro hsq
      by_cases hsmall : n = 1 ∨ n = 3
      · exact hsmall
      by_cases hnodd : n % 2 = 1
      · have hsplit : ∃ t : ℕ, 0 < t ∧
            (n = 4 * t + 1 ∨ n = 4 * t + 3) := by
          by_cases h4 : n % 4 = 1
          · refine ⟨n / 4, ?_, Or.inl ?_⟩ <;> omega
          · refine ⟨n / 4, ?_, Or.inr ?_⟩ <;> omega
        obtain ⟨t, ht, hi⟩ := hsplit
        obtain ⟨r, s, hs, hts⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt ht)
        obtain ⟨b, hb4, ha, _⟩ := hmodulus r
        have hsqb := hsq.map (Int.castRingHom (ZMod b))
        change IsSquare (goldenLucas n : ZMod b) at hsqb
        rcases hi with hi | hi
        · have hin : n = 4 * 2 ^ r * s + 1 := by rw [hts] at hi; nlinarith [hi]
          have hn := hplus b r s 1 n ha hs hin
          have hj : goldenLucas 1 = 1 := by decide
          rw [hn, hj] at hsqb
          exact False.elim ((hnonsquare b 1 hb4 (by simp)) (by simpa using hsqb))
        · have hin : n = 4 * 2 ^ r * s + 3 := by rw [hts] at hi; nlinarith [hi]
          have hn := hplus b r s 3 n ha hs hin
          have hj : goldenLucas 3 = 4 := by decide
          rw [hn, hj] at hsqb
          have hcop : Nat.Coprime 2 b := Nat.coprime_two_left.mpr
            (Nat.odd_iff.mpr (by omega))
          exact False.elim ((hnonsquare b 2 hb4 hcop)
            (by convert hsqb using 1 <;> norm_num))
      · have hperiod4 : (GoldenMod.phi : GoldenMod 4) ^ 6 = 1 := by decide
        have hfinite : ∀ i : Fin 6, i.val % 2 = 0 → ∀ z : ZMod 4,
            (goldenLucas i.val : ZMod 4) ≠ z * z := by decide
        obtain ⟨x, hx⟩ := hsq
        have hxmod : (goldenLucas n : ZMod 4) = (x : ZMod 4) * (x : ZMod 4) := by
          simpa only [Int.coe_castRingHom, Int.cast_mul] using
            congrArg (Int.castRingHom (ZMod 4)) hx
        have hm : (n % 6) % 2 = 0 := by omega
        have hbad := hfinite ⟨n % 6, Nat.mod_lt _ (by decide)⟩ hm (x : ZMod 4)
        apply False.elim
        apply hbad
        rw [← hperiod 4 6 n hperiod4]
        exact hxmod
    · rintro (rfl | rfl)
      · exact ⟨1, by decide⟩
      · exact ⟨2, by decide⟩
  · constructor
    · rintro ⟨x, hx⟩
      by_cases hn0 : n = 0
      · exact Or.inl hn0
      by_cases hn6 : n = 6
      · exact Or.inr hn6
      have hs2 : IsSquare (2 * goldenLucas n) := by
        refine ⟨2 * x, ?_⟩
        rw [hx]
        ring
      by_cases hnodd : n % 2 = 1
      · have hperiod8 : (GoldenMod.phi : GoldenMod 8) ^ 12 = 1 := by decide
        have hfinite : ∀ i : Fin 12, i.val % 2 = 1 → ∀ z : ZMod 8,
            (goldenLucas i.val : ZMod 8) ≠ 2 * z ^ 2 := by decide
        have hm : (n % 12) % 2 = 1 := by omega
        have hbad := hfinite ⟨n % 12, Nat.mod_lt _ (by decide)⟩ hm (x : ZMod 8)
        apply False.elim
        apply hbad
        rw [← hperiod 8 12 n hperiod8]
        simpa using congrArg (Int.castRingHom (ZMod 8)) hx
      by_cases hn4 : n % 4 = 0
      · let t := n / 4
        have ht : 0 < t := by dsimp [t]; omega
        have hi : n = 4 * t := by dsimp [t]; omega
        obtain ⟨r, s, hs, hts⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt ht)
        obtain ⟨b, hb4, ha, _⟩ := hmodulus r
        have hin : n = 4 * 2 ^ r * s + 0 := by rw [hts] at hi; nlinarith [hi]
        have hn := hplus b r s 0 n ha hs hin
        have hj : goldenLucas 0 = 2 := by decide
        rw [hj] at hn
        have hsqb := hs2.map (Int.castRingHom (ZMod b))
        simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_ofNat] at hsqb
        rw [hn] at hsqb
        simp only [Int.cast_ofNat] at hsqb
        have hscalar : (2 : ZMod b) * (-2) = -((2 : ZMod b) ^ 2) := by ring
        rw [hscalar] at hsqb
        have hcop : Nat.Coprime 2 b := Nat.coprime_two_left.mpr
          (Nat.odd_iff.mpr (by omega))
        exact False.elim ((hnonsquare b 2 hb4 hcop) hsqb)
      by_cases hn8 : n % 8 = 6
      · let t := n / 8
        have ht : 0 < t := by dsimp [t]; omega
        have hi : n = 8 * t + 6 := by dsimp [t]; omega
        obtain ⟨r, s, hs, hts⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt ht)
        obtain ⟨b, hb4, ha, hc⟩ := hmodulus (r + 1)
        have hin : n = 4 * 2 ^ (r + 1) * s + 6 := by
          rw [hts] at hi
          rw [pow_succ]
          nlinarith [hi]
        have hn := hplus b (r + 1) s 6 n ha hs hin
        have hj : goldenLucas 6 = 18 := by decide
        rw [hj] at hn
        have hsqb := hs2.map (Int.castRingHom (ZMod b))
        simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_ofNat] at hsqb
        rw [hn] at hsqb
        simp only [Int.cast_ofNat] at hsqb
        have hscalar : (2 : ZMod b) * (-18) = -((6 : ZMod b) ^ 2) := by ring
        rw [hscalar] at hsqb
        exact False.elim ((hnonsquare b 6 hb4 (hc (by omega))) hsqb)
      · let t := n / 8
        have hi : n + 6 = 8 * (t + 1) := by dsimp [t]; omega
        obtain ⟨r, s, hs, hts⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : t + 1 ≠ 0)
        obtain ⟨b, hb4, ha, hc⟩ := hmodulus (r + 1)
        have hin : n + 6 = 4 * 2 ^ (r + 1) * s := by
          rw [hts] at hi
          rw [pow_succ]
          nlinarith [hi]
        let y : GoldenMod b := GoldenMod.phi
        let q : GoldenMod b := GoldenMod.reduce b (conj (phi ^ 6))
        have hy : GoldenMod.reduce b phi = y := by
          ext <;> norm_num [GoldenMod.reduce, phi, y, GoldenMod.phi]
        have hnorm : norm (phi ^ 6) = 1 := by rw [norm_phi_pow]; norm_num
        have hnormGI : phi ^ 6 * conj (phi ^ 6) = 1 := by
          rw [← norm_eq_mul_conj, hnorm]
          norm_num
        have hq : y ^ 6 * q = 1 := by
          have h := congrArg (GoldenMod.reduce b) hnormGI
          simpa only [map_mul, map_pow, map_one, hy, q] using h
        have hp : y ^ n * y ^ 6 = -1 := by
          rw [← pow_add, hin, pow_mul]
          change ((GoldenMod.phi : GoldenMod b) ^ (4 * 2 ^ (r + 1))) ^ s = -1
          rw [ha, hs.neg_one_pow]
        have hp' : y ^ n = -q := by
          calc
            y ^ n = (y ^ n * y ^ 6) * q := by rw [mul_assoc, hq, mul_one]
            _ = (-1) * q := congrArg (fun z : GoldenMod b => z * q) hp
            _ = -q := by simp
        have h6 : phi ^ 6 = (⟨5, 8⟩ : GoldenInt) := by decide
        have hn : (goldenLucas n : ZMod b) = -18 := by
          have h := congrArg (fun z : GoldenMod b => 2 * z.a + z.b) hp'
          rw [htrace]
          change 2 * (y ^ n).a + (y ^ n).b = -18
          norm_num [q, GoldenMod.reduce, h6, conj] at h
          exact h
        have hsqb := hs2.map (Int.castRingHom (ZMod b))
        simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_ofNat] at hsqb
        rw [hn] at hsqb
        have hscalar : (2 : ZMod b) * (-18) = -((6 : ZMod b) ^ 2) := by ring
        rw [hscalar] at hsqb
        exact False.elim ((hnonsquare b 6 hb4 (hc (by omega))) hsqb)
    · rintro (rfl | rfl)
      · exact ⟨1, by decide⟩
      · exact ⟨3, by decide⟩

#print axioms lucas_square_classifications

end D5.S3.Arith.Primes.LucasSquareClassification

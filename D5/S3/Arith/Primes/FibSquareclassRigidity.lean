/- GID: D5/S3/Arith/Primes/FibSquareclassRigidity
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibSquareclassRigidity
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The only nonsingleton positive Fibonacci square classes have index sets one, two, twelve and three, six. -/

import D5.S3.Arith.Primes.LucasSquareClassification
import D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Arith.Primes.FibSquareclassRigidity
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition
open D5.S3.Arith.Primes.LucasSquareClassification

set_option maxHeartbeats 10000000 in
/-- The complete positive-index Fibonacci square classes are singleton
classes together with the exceptional classes `{1, 2, 12}` and `{3, 6}`.
Dynamic Lucas moduli exclude all nontrivial odd index multiples; the
Lucas square classifications settle the even index multiples. -/
theorem fibonacci_squareclass_pairs (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsSquare (Nat.fib m * Nat.fib n) ↔
      m = n ∨
      ((m = 1 ∨ m = 2 ∨ m = 12) ∧ (n = 1 ∨ n = 2 ∨ n = 12)) ∨
      ((m = 3 ∨ m = 6) ∧ (n = 3 ∨ n = 6)) := by
  constructor
  · intro hsq
    have hOddBase (m t : ℕ) (hm : 0 < m) (hmodd : Odd m)
        (ht : 1 < t) (htodd : Odd t) :
        ¬ IsSquare (Nat.fib m * Nat.fib (t * m)) := by
      have hB (c j : ℕ) :
          ((GoldenMod.reduce c phi) ^ j).b = (Nat.fib j : ZMod c) := by
        rw [← map_pow]
        change ((phi ^ j).b : ZMod c) = (Nat.fib j : ZMod c)
        rw [golden_phi_pow_b_eq_fib_index]
        simp
      have htrace (c j : ℕ) :
          (goldenLucas j : ZMod c) =
            2 * ((GoldenMod.phi : GoldenMod c) ^ j).a +
              ((GoldenMod.phi : GoldenMod c) ^ j).b := by
        have hy : GoldenMod.reduce c phi = (GoldenMod.phi : GoldenMod c) := by
          ext <;> norm_num [GoldenMod.reduce, phi, GoldenMod.phi]
        calc
          (goldenLucas j : ZMod c) =
              2 * (GoldenMod.reduce c (phi ^ j)).a +
                (GoldenMod.reduce c (phi ^ j)).b := by
                  simp [goldenLucas, trace, GoldenMod.reduce]
          _ = _ := by rw [map_pow, hy]
      have hperiod4 (j : ℕ) :
          (goldenLucas j : ZMod 4) = (goldenLucas (j % 6) : ZMod 4) := by
        have hper : (GoldenMod.phi : GoldenMod 4) ^ 6 = 1 := by decide
        rw [htrace, htrace, pow_eq_pow_mod j hper]
      have hsplit : ∃ h : ℕ, 0 < h ∧ (t = 4 * h + 1 ∨ t + 1 = 4 * h) := by
        have ho := Nat.odd_iff.mp htodd
        by_cases h4 : t % 4 = 1
        · refine ⟨t / 4, ?_, Or.inl ?_⟩ <;> omega
        · refine ⟨(t + 1) / 4, ?_, Or.inr ?_⟩ <;> omega
      obtain ⟨h, hh, htshape⟩ := hsplit
      obtain ⟨r, s, hsodd, hhs⟩ := Nat.exists_eq_two_pow_mul_odd hh.ne'
      obtain ⟨u, d, hd3, hmd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' 3 (by decide)
      have hdpos : 0 < d := by
        by_contra hn
        have hd0 : d = 0 := by omega
        rw [hd0, mul_zero] at hmd
        omega
      let k : ℕ := 2 * 2 ^ r * d
      have hkpos : 0 < k := by dsimp [k]; positivity
      have hkeven : Even k := ⟨2 ^ r * d, by dsimp [k]; ring⟩
      have hk3 : ¬3 ∣ k := by
        intro hdiv
        change 3 ∣ 2 * 2 ^ r * d at hdiv
        rcases Nat.prime_three.dvd_mul.mp hdiv with hdiv | hdiv
        · rcases Nat.prime_three.dvd_mul.mp hdiv with hdiv | hdiv
          · norm_num at hdiv
          · have hb := Nat.prime_three.dvd_of_dvd_pow hdiv
            norm_num at hb
        · exact hd3 hdiv
      have hk4 : (goldenLucas k : ZMod 4) = 3 := by
        have hk2 : k % 2 = 0 := Nat.even_iff.mp hkeven
        have hk30 : k % 3 ≠ 0 := by
          intro hz
          exact hk3 (Nat.dvd_of_mod_eq_zero hz)
        have h6 : k % 6 = 2 ∨ k % 6 = 4 := by omega
        rw [hperiod4]
        rcases h6 with h6 | h6 <;> rw [h6] <;> decide
      let L : ℤ := goldenLucas k
      have hLpos : 0 < L := by
        have hidx : k = (k - 1) + 1 := by omega
        change 0 < goldenLucas k
        rw [hidx, golden_lucas_succ_eq_fib_add_fib]
        have hpos : 0 < Nat.fib (k - 1 + 2) := Nat.fib_pos.mpr (by omega)
        positivity
      let b : ℕ := L.toNat
      have hbcast : (b : ℤ) = L := Int.toNat_of_nonneg hLpos.le
      have hb4 : b % 4 = 3 := by
        have hz : (b : ZMod 4) = 3 := by
          calc
            (b : ZMod 4) = (L : ZMod 4) := by rw [← hbcast]; simp
            _ = 3 := hk4
        exact (ZMod.natCast_eq_natCast_iff' b 3 4).mp hz
      have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
      have hchar : (phi ^ k) ^ 2 + 1 = (L : GoldenInt) * phi ^ k := by
        have hnorm : norm (phi ^ k) = 1 := by
          rw [norm_phi_pow]
          exact hkeven.neg_one_pow
        have hnormGI : phi ^ k * conj (phi ^ k) = 1 := by
          rw [← norm_eq_mul_conj, hnorm]
          norm_num
        calc
          (phi ^ k) ^ 2 + 1 = (phi ^ k + conj (phi ^ k)) * phi ^ k := by
            rw [pow_two]
            linear_combination -hnormGI
          _ = (L : GoldenInt) * phi ^ k := by rw [add_conj_eq_trace]; rfl
      have hanti (c : ℕ) (hcb : c ∣ b) :
          (GoldenMod.reduce c phi) ^ (2 * k) = -1 := by
        have hLzero : (L : ZMod c) = 0 := by
          rw [← hbcast, Int.cast_natCast]
          exact (ZMod.natCast_eq_zero_iff b c).mpr hcb
        let f := GoldenMod.reduce c
        have hscalar : f (L : GoldenInt) = 0 := by
          ext <;> simp [f, GoldenMod.reduce, hLzero]
        have heq := congrArg f hchar
        simp only [map_add, map_pow, map_one, map_mul, hscalar, zero_mul] at heq
        rw [mul_comm 2 k, pow_mul]
        linear_combination heq
      have hSodd : Odd (s * 3 ^ u) := hsodd.mul ((by decide : Odd (3 : ℕ)).pow)
      have hshift : 4 * h * m = (2 * k) * (s * 3 ^ u) := by
        rw [hhs, hmd]
        dsimp [k]
        ring
      have hshiftAnti (c : ℕ) (hcb : c ∣ b) :
          (GoldenMod.reduce c phi) ^ (4 * h * m) = -1 := by
        rw [hshift, pow_mul, hanti c hcb, hSodd.neg_one_pow]
      have hnormM : norm (phi ^ m) = -1 := by rw [norm_phi_pow, hmodd.neg_one_pow]
      have hnormMGI : phi ^ m * conj (phi ^ m) = -1 := by
        rw [← norm_eq_mul_conj, hnormM]
        norm_num
      have hcop : Nat.Coprime (Nat.fib m) b := by
        let g := Nat.gcd (Nat.fib m) b
        have hgf : g ∣ Nat.fib m := Nat.gcd_dvd_left _ _
        have hgb : g ∣ b := Nat.gcd_dvd_right _ _
        let z : GoldenMod g := GoldenMod.reduce g (phi ^ m)
        have hzb : z.b = 0 := by
          change ((phi ^ m).b : ZMod g) = 0
          rw [golden_phi_pow_b_eq_fib_index, Int.cast_natCast]
          exact (ZMod.natCast_eq_zero_iff (Nat.fib m) g).mpr hgf
        have hnormZ : z.a * z.a + z.a * z.b - z.b * z.b = -1 := by
          change ((phi ^ m).a : ZMod g) * ((phi ^ m).a : ZMod g) +
            ((phi ^ m).a : ZMod g) * ((phi ^ m).b : ZMod g) -
            ((phi ^ m).b : ZMod g) * ((phi ^ m).b : ZMod g) = -1
          have hc := congrArg (Int.castRingHom (ZMod g)) hnormM
          rw [D5.S0.Carrier.norm_def] at hc
          simpa only [Int.coe_castRingHom, Int.cast_add, Int.cast_mul,
            Int.cast_sub, Int.cast_neg, Int.cast_one] using hc
        have hza2 : z.a ^ 2 = -1 := by simpa [hzb, pow_two] using hnormZ
        have hzscalar : z = GoldenMod.scalar g z.a := by
          ext <;> simp [hzb, GoldenMod.scalar]
        have hza4 : z.a ^ 4 = 1 := by
          calc
            z.a ^ 4 = (z.a ^ 2) ^ 2 := by ring
            _ = 1 := by rw [hza2]; norm_num
        have hz4 : z ^ 4 = 1 := by
          rw [hzscalar, ← map_pow, hza4, map_one]
        have hyz : (GoldenMod.reduce g phi) ^ m = z := by dsimp [z]; rw [map_pow]
        have hfour : (GoldenMod.reduce g phi) ^ (4 * m) = 1 := by
          rw [mul_comm 4 m, pow_mul, hyz]
          exact hz4
        have hga := hshiftAnti g hgb
        have hi : 4 * h * m = (4 * m) * h := by ring
        rw [hi, pow_mul, hfour, one_pow] at hga
        have hc := congrArg GoldenMod.a hga
        simp only [GoldenMod.a_one, GoldenMod.a_neg] at hc
        have htwo : (2 : ZMod g) = 0 := by linear_combination hc
        have hg2 : g ∣ 2 := (ZMod.natCast_eq_zero_iff 2 g).mp htwo
        have hg1 : g = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with hg1 | hg2
          · exact hg1
          · have h2b : 2 ∣ b := hg2 ▸ hgb
            have hz := Nat.mod_eq_zero_of_dvd h2b
            omega
        change Nat.gcd (Nat.fib m) b = 1
        exact hg1
      have hresidue : (Nat.fib (t * m) : ZMod b) = -(Nat.fib m : ZMod b) := by
        let f := GoldenMod.reduce b
        let y : GoldenMod b := f phi
        have hantiB : y ^ (4 * h * m) = -1 := hshiftAnti b (dvd_refl b)
        rcases htshape with htshape | htshape
        · have hi : t * m = 4 * h * m + m := by rw [htshape]; ring
          have hp : y ^ (t * m) = -(y ^ m) := by rw [hi, pow_add, hantiB]; simp
          have hc := congrArg GoldenMod.b hp
          rw [hB b (t * m), GoldenMod.b_neg, hB b m] at hc
          exact hc
        · let q : GoldenMod b := f (conj (phi ^ m))
          have hq : y ^ m * q = -1 := by
            have hc := congrArg f hnormMGI
            simpa only [map_mul, map_pow, map_neg, map_one, y, q] using hc
          have hp : y ^ (t * m) * y ^ m = -1 := by
            rw [← pow_add]
            have hi : t * m + m = 4 * h * m := by nlinarith [htshape]
            rw [hi]
            exact hantiB
          have heq : y ^ (t * m) = q := by
            calc
              y ^ (t * m) = -((y ^ (t * m) * y ^ m) * q) := by
                rw [mul_assoc, hq]
                simp
              _ = q := by rw [hp]; simp
          have hc := congrArg GoldenMod.b heq
          rw [hB b (t * m)] at hc
          change (Nat.fib (t * m) : ZMod b) = ((-(phi ^ m).b : ℤ) : ZMod b) at hc
          rw [golden_phi_pow_b_eq_fib_index] at hc
          simpa using hc
      have hj : jacobiSym (-((Nat.fib m : ℤ) ^ 2)) b = -1 := by
        have hgcd : (Nat.fib m : ℤ).gcd (b : ℤ) = 1 := by
          change Nat.gcd (Nat.fib m) b = 1 at hcop
          simpa only [Int.gcd_natCast_natCast] using hcop
        rw [neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hbodd,
          ZMod.χ₄_nat_three_mod_four hb4, jacobiSym.sq_one' hgcd]
        norm_num
      have hbad : ¬ IsSquare (-((Nat.fib m : ZMod b) ^ 2)) := by
        simpa only [Int.cast_neg, Int.cast_pow, Int.cast_natCast] using
          ZMod.nonsquare_of_jacobiSym_eq_neg_one hj
      intro hsq
      have hc := hsq.map (Nat.castRingHom (ZMod b))
      simp only [Nat.coe_castRingHom, Nat.cast_mul] at hc
      rw [hresidue] at hc
      have heq : (Nat.fib m : ZMod b) * -(Nat.fib m : ZMod b) =
          -((Nat.fib m : ZMod b) ^ 2) := by ring
      rw [heq] at hc
      exact hbad hc
    have hEvenBase (m t : ℕ) (hm : 0 < m) (hmeven : Even m)
        (ht : 1 < t) (htodd : Odd t) :
        ¬ IsSquare (Nat.fib m * Nat.fib (t * m)) := by
      have hB (c j : ℕ) :
          ((GoldenMod.reduce c phi) ^ j).b = (Nat.fib j : ZMod c) := by
        rw [← map_pow]
        change ((phi ^ j).b : ZMod c) = (Nat.fib j : ZMod c)
        rw [golden_phi_pow_b_eq_fib_index]
        simp
      have htrace (c j : ℕ) :
          (goldenLucas j : ZMod c) =
            2 * ((GoldenMod.phi : GoldenMod c) ^ j).a +
              ((GoldenMod.phi : GoldenMod c) ^ j).b := by
        have hy : GoldenMod.reduce c phi = (GoldenMod.phi : GoldenMod c) := by
          ext <;> norm_num [GoldenMod.reduce, phi, GoldenMod.phi]
        calc
          (goldenLucas j : ZMod c) =
              2 * (GoldenMod.reduce c (phi ^ j)).a +
                (GoldenMod.reduce c (phi ^ j)).b := by
                  simp [goldenLucas, trace, GoldenMod.reduce]
          _ = _ := by rw [map_pow, hy]
      have hperiod4 (j : ℕ) :
          (goldenLucas j : ZMod 4) = (goldenLucas (j % 6) : ZMod 4) := by
        have hper : (GoldenMod.phi : GoldenMod 4) ^ 6 = 1 := by decide
        rw [htrace, htrace, pow_eq_pow_mod j hper]
      obtain ⟨h, htshape⟩ := htodd
      have hh : 0 < h := by omega
      obtain ⟨r, s, hsodd, hhs⟩ := Nat.exists_eq_two_pow_mul_odd hh.ne'
      obtain ⟨u, d, hd3, hmd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' 3 (by decide)
      have hdpos : 0 < d := by
        by_contra hn
        have hd0 : d = 0 := by omega
        rw [hd0, mul_zero] at hmd
        omega
      have hdeven : Even d := by
        have hprod : Even (3 ^ u * d) := hmd ▸ hmeven
        have h3odd : Odd (3 ^ u) := (by decide : Odd (3 : ℕ)).pow
        exact (Nat.even_mul.mp hprod).resolve_left (Nat.not_even_iff_odd.mpr h3odd)
      let k : ℕ := 2 ^ r * d
      have hkpos : 0 < k := by dsimp [k]; positivity
      have hkeven : Even k := by dsimp [k]; exact hdeven.mul_left (2 ^ r)
      have hk3 : ¬3 ∣ k := by
        intro hdiv
        change 3 ∣ 2 ^ r * d at hdiv
        rcases Nat.prime_three.dvd_mul.mp hdiv with hdiv | hdiv
        · have hb := Nat.prime_three.dvd_of_dvd_pow hdiv
          norm_num at hb
        · exact hd3 hdiv
      have hk4 : (goldenLucas k : ZMod 4) = 3 := by
        have hk2 : k % 2 = 0 := Nat.even_iff.mp hkeven
        have hk30 : k % 3 ≠ 0 := by
          intro hz
          exact hk3 (Nat.dvd_of_mod_eq_zero hz)
        have h6 : k % 6 = 2 ∨ k % 6 = 4 := by omega
        rw [hperiod4]
        rcases h6 with h6 | h6 <;> rw [h6] <;> decide
      let L : ℤ := goldenLucas k
      have hLpos : 0 < L := by
        have hidx : k = (k - 1) + 1 := by omega
        change 0 < goldenLucas k
        rw [hidx, golden_lucas_succ_eq_fib_add_fib]
        have hpos : 0 < Nat.fib (k - 1 + 2) := Nat.fib_pos.mpr (by omega)
        positivity
      let b : ℕ := L.toNat
      have hbcast : (b : ℤ) = L := Int.toNat_of_nonneg hLpos.le
      have hb4 : b % 4 = 3 := by
        have hz : (b : ZMod 4) = 3 := by
          calc
            (b : ZMod 4) = (L : ZMod 4) := by rw [← hbcast]; simp
            _ = 3 := hk4
        exact (ZMod.natCast_eq_natCast_iff' b 3 4).mp hz
      have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
      have hchar : (phi ^ k) ^ 2 + 1 = (L : GoldenInt) * phi ^ k := by
        have hnorm : norm (phi ^ k) = 1 := by
          rw [norm_phi_pow]
          exact hkeven.neg_one_pow
        have hnormGI : phi ^ k * conj (phi ^ k) = 1 := by
          rw [← norm_eq_mul_conj, hnorm]
          norm_num
        calc
          (phi ^ k) ^ 2 + 1 = (phi ^ k + conj (phi ^ k)) * phi ^ k := by
            rw [pow_two]
            linear_combination -hnormGI
          _ = (L : GoldenInt) * phi ^ k := by rw [add_conj_eq_trace]; rfl
      have hanti (c : ℕ) (hcb : c ∣ b) :
          (GoldenMod.reduce c phi) ^ (2 * k) = -1 := by
        have hLzero : (L : ZMod c) = 0 := by
          rw [← hbcast, Int.cast_natCast]
          exact (ZMod.natCast_eq_zero_iff b c).mpr hcb
        let f := GoldenMod.reduce c
        have hscalar : f (L : GoldenInt) = 0 := by
          ext <;> simp [f, GoldenMod.reduce, hLzero]
        have heq := congrArg f hchar
        simp only [map_add, map_pow, map_one, map_mul, hscalar, zero_mul] at heq
        rw [mul_comm 2 k, pow_mul]
        linear_combination heq
      have hSodd : Odd (s * 3 ^ u) := hsodd.mul ((by decide : Odd (3 : ℕ)).pow)
      have hshift : 2 * h * m = (2 * k) * (s * 3 ^ u) := by
        rw [hhs, hmd]
        dsimp [k]
        ring
      have hshiftAnti (c : ℕ) (hcb : c ∣ b) :
          (GoldenMod.reduce c phi) ^ (2 * h * m) = -1 := by
        rw [hshift, pow_mul, hanti c hcb, hSodd.neg_one_pow]
      have hnormM : norm (phi ^ m) = 1 := by rw [norm_phi_pow, hmeven.neg_one_pow]
      have hcop : Nat.Coprime (Nat.fib m) b := by
        let g := Nat.gcd (Nat.fib m) b
        have hgf : g ∣ Nat.fib m := Nat.gcd_dvd_left _ _
        have hgb : g ∣ b := Nat.gcd_dvd_right _ _
        let z : GoldenMod g := GoldenMod.reduce g (phi ^ m)
        have hzb : z.b = 0 := by
          change ((phi ^ m).b : ZMod g) = 0
          rw [golden_phi_pow_b_eq_fib_index, Int.cast_natCast]
          exact (ZMod.natCast_eq_zero_iff (Nat.fib m) g).mpr hgf
        have hnormZ : z.a * z.a + z.a * z.b - z.b * z.b = 1 := by
          change ((phi ^ m).a : ZMod g) * ((phi ^ m).a : ZMod g) +
            ((phi ^ m).a : ZMod g) * ((phi ^ m).b : ZMod g) -
            ((phi ^ m).b : ZMod g) * ((phi ^ m).b : ZMod g) = 1
          have hc := congrArg (Int.castRingHom (ZMod g)) hnormM
          rw [D5.S0.Carrier.norm_def] at hc
          simpa only [Int.coe_castRingHom, Int.cast_add, Int.cast_mul,
            Int.cast_sub, Int.cast_neg, Int.cast_one] using hc
        have hza2 : z.a ^ 2 = 1 := by simpa [hzb, pow_two] using hnormZ
        have hzscalar : z = GoldenMod.scalar g z.a := by
          ext <;> simp [hzb, GoldenMod.scalar]
        have hz2 : z ^ 2 = 1 := by
          rw [hzscalar, ← map_pow, hza2, map_one]
        have hyz : (GoldenMod.reduce g phi) ^ m = z := by dsimp [z]; rw [map_pow]
        have htwoPow : (GoldenMod.reduce g phi) ^ (2 * m) = 1 := by
          rw [mul_comm 2 m, pow_mul, hyz]
          exact hz2
        have hga := hshiftAnti g hgb
        have hi : 2 * h * m = (2 * m) * h := by ring
        rw [hi, pow_mul, htwoPow, one_pow] at hga
        have hc := congrArg GoldenMod.a hga
        simp only [GoldenMod.a_one, GoldenMod.a_neg] at hc
        have htwo : (2 : ZMod g) = 0 := by linear_combination hc
        have hg2 : g ∣ 2 := (ZMod.natCast_eq_zero_iff 2 g).mp htwo
        have hg1 : g = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with hg1 | hg2
          · exact hg1
          · have h2b : 2 ∣ b := hg2 ▸ hgb
            have hz := Nat.mod_eq_zero_of_dvd h2b
            omega
        change Nat.gcd (Nat.fib m) b = 1
        exact hg1
      have hresidue : (Nat.fib (t * m) : ZMod b) = -(Nat.fib m : ZMod b) := by
        let f := GoldenMod.reduce b
        let y : GoldenMod b := f phi
        have hantiB : y ^ (2 * h * m) = -1 := hshiftAnti b (dvd_refl b)
        have hi : t * m = 2 * h * m + m := by nlinarith [htshape]
        have hp : y ^ (t * m) = -(y ^ m) := by rw [hi, pow_add, hantiB]; simp
        have hc := congrArg GoldenMod.b hp
        rw [hB b (t * m), GoldenMod.b_neg, hB b m] at hc
        exact hc
      have hj : jacobiSym (-((Nat.fib m : ℤ) ^ 2)) b = -1 := by
        have hgcd : (Nat.fib m : ℤ).gcd (b : ℤ) = 1 := by
          change Nat.gcd (Nat.fib m) b = 1 at hcop
          simpa only [Int.gcd_natCast_natCast] using hcop
        rw [neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hbodd,
          ZMod.χ₄_nat_three_mod_four hb4, jacobiSym.sq_one' hgcd]
        norm_num
      have hbad : ¬ IsSquare (-((Nat.fib m : ZMod b) ^ 2)) := by
        simpa only [Int.cast_neg, Int.cast_pow, Int.cast_natCast] using
          ZMod.nonsquare_of_jacobiSym_eq_neg_one hj
      intro hsq
      have hc := hsq.map (Nat.castRingHom (ZMod b))
      simp only [Nat.coe_castRingHom, Nat.cast_mul] at hc
      rw [hresidue] at hc
      have heq : (Nat.fib m : ZMod b) * -(Nat.fib m : ZMod b) =
          -((Nat.fib m : ZMod b) ^ 2) := by ring
      rw [heq] at hc
      exact hbad hc
    have oddExclude (m t : ℕ) (hm : 0 < m) (ht : 1 < t) (htodd : Odd t) :
        ¬ IsSquare (Nat.fib m * Nat.fib (t * m)) := by
      rcases Nat.even_or_odd m with he | ho
      · exact hEvenBase m t hm he ht htodd
      · exact hOddBase m t hm ho ht htodd
    have evenClass (m t : ℕ) (hm : 2 < m) (ht : 1 < t) (hteven : Even t) :
        (IsSquare (Nat.fib m * Nat.fib (t * m)) ↔ m = 3 ∧ t = 2) := by
      constructor
      · intro hsq
        obtain ⟨q, htq⟩ := hteven
        have hqpos : 0 < q := by omega
        let j := q * m
        have hjpos : 0 < j := by dsimp [j]; positivity
        have hjlarge : 3 ≤ j := by dsimp [j]; nlinarith
        have hdouble (a : ℕ) :
            (Nat.fib (2 * a) : ℤ) = (Nat.fib a : ℤ) * goldenLucas a := by
          calc
            (Nat.fib (2 * a) : ℤ) = (phi ^ (2 * a)).b := (golden_phi_pow_b_eq_fib_index _).symm
            _ = ((phi ^ a) ^ 2).b := by rw [pow_mul']
            _ = (phi ^ a).b * trace (phi ^ a) := by simp only [pow_two, b_mul, trace]; ring
            _ = _ := by rw [golden_phi_pow_b_eq_fib_index]; rfl
        have hLpos : 0 < goldenLucas j := by
          have hi : j = (j - 1) + 1 := by omega
          rw [hi, golden_lucas_succ_eq_fib_add_fib]
          have hp := Nat.fib_pos.mpr (by omega : 0 < j - 1 + 2)
          positivity
        let C := (goldenLucas j).toNat
        let K := Nat.fib m * Nat.fib j
        have hCcast : (C : ℤ) = goldenLucas j := Int.toNat_of_nonneg hLpos.le
        have hCpos : 0 < C := by
          have hc : (0 : ℤ) < (C : ℤ) := by rw [hCcast]; exact hLpos
          exact_mod_cast hc
        have hKpos : 0 < K := by dsimp [K]; exact Nat.mul_pos (Nat.fib_pos.mpr (by omega)) (Nat.fib_pos.mpr hjpos)
        have htj : t * m = 2 * j := by dsimp [j]; nlinarith [htq]
        have htotal : IsSquare (K * C) := by
          have heq : Nat.fib m * Nat.fib (t * m) = K * C := by
            have hi := hdouble j
            rw [← hCcast] at hi
            have hiNat : Nat.fib (2 * j) = Nat.fib j * C := by exact_mod_cast hi
            rw [htj, hiNat]
            dsimp [K]
            ring
          rwa [heq] at hsq
        have hNoOddCommon (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
            (hpC : p ∣ C) : ¬ p ∣ K := by
          intro hpK
          have hpFj : p ∣ Nat.fib j := by
            rcases hp.dvd_mul.mp hpK with hpFm | hpFj
            · exact dvd_trans hpFm (Nat.fib_dvd m j ⟨q, by dsimp [j]; ring⟩)
            · exact hpFj
          have : Fact p.Prime := ⟨hp⟩
          have hF0 : (Nat.fib j : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpFj
          have hL0 : (goldenLucas j : ZMod p) = 0 := by
            rw [← hCcast, Int.cast_natCast]
            exact (ZMod.natCast_eq_zero_iff _ _).mpr hpC
          have hdisc := congrArg (Int.castRingHom (ZMod p)) (golden_lucas_discriminant j)
          simp only [Int.coe_castRingHom, Int.cast_sub, Int.cast_mul, Int.cast_pow,
            Int.cast_natCast, Int.cast_neg, Int.cast_one, Int.cast_ofNat, hF0, hL0,
            zero_pow (by decide : 2 ≠ 0), mul_zero, sub_self] at hdisc
          have hfour : (4 : ZMod p) ≠ 0 := by
            have htwo : (2 : ZMod p) ≠ 0 := by
              intro hz
              have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
              exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
            have hi : (4 : ZMod p) = (2 : ZMod p) ^ 2 := by ring
            rw [hi]
            exact pow_ne_zero _ htwo
          exact (mul_ne_zero hfour (pow_ne_zero j (neg_ne_zero.mpr one_ne_zero))) hdisc.symm
        have hCoddEven (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
            Even (padicValNat p C) := by
          have : Fact p.Prime := ⟨hp⟩
          by_cases hpC : p ∣ C
          · have hK0 := padicValNat.eq_zero_of_not_dvd (hNoOddCommon p hp hp2 hpC)
            obtain ⟨x, hx⟩ := htotal
            have hx2 : K * C = x ^ 2 := by simpa [pow_two] using hx
            have hv := congrArg (padicValNat p) hx2
            rw [padicValNat.mul hKpos.ne' hCpos.ne', padicValNat.pow, hK0, zero_add] at hv
            exact ⟨padicValNat p x, by omega⟩
          · rw [padicValNat.eq_zero_of_not_dvd hpC]
            exact ⟨0, by omega⟩
        have hAllEvenSquare (a : ℕ) (ha : 0 < a)
            (he : ∀ p : ℕ, p.Prime → Even (padicValNat p a)) : IsSquare a := by
          let s := ∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2)
          refine ⟨s, ?_⟩
          have hs : a = s ^ 2 := by
            rw [Nat.prod_primeFactors_pow_factorization ha.ne']
            dsimp only [s]
            rw [← Finset.prod_pow]
            apply Finset.prod_congr rfl
            intro p hp
            rw [← pow_mul]
            congr 1
            have he' : Even (a.factorization p) := by
              rw [Nat.factorization_def a (Nat.prime_of_mem_primeFactors hp)]
              exact he p (Nat.prime_of_mem_primeFactors hp)
            obtain ⟨z, hz⟩ := he'
            omega
          simpa [pow_two] using hs
        have hCclass : IsSquare C ∨ ∃ x : ℕ, C = 2 * x ^ 2 := by
          by_cases he2 : Even (padicValNat 2 C)
          · left
            apply hAllEvenSquare C hCpos
            intro p hp
            by_cases hp2 : p = 2
            · simpa [hp2] using he2
            · exact hCoddEven p hp hp2
          · right
            have ho2 : Odd (padicValNat 2 C) := Nat.not_even_iff_odd.mp he2
            have h2Csq : IsSquare (2 * C) := by
              apply hAllEvenSquare (2 * C) (by positivity)
              intro p hp
              have : Fact p.Prime := ⟨hp⟩
              rw [padicValNat.mul (by decide : (2 : ℕ) ≠ 0) hCpos.ne']
              by_cases hp2 : p = 2
              · subst p
                rw [padicValNat_self]
                obtain ⟨z, hz⟩ := ho2
                exact ⟨z + 1, by omega⟩
              · have hpd2 : ¬p ∣ 2 := by
                  intro h
                  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
                rw [padicValNat.eq_zero_of_not_dvd hpd2, zero_add]
                exact hCoddEven p hp hp2
            obtain ⟨y, hy⟩ := h2Csq
            have hy2 : 2 * C = y ^ 2 := by simpa [pow_two] using hy
            have h2y : 2 ∣ y := Nat.prime_two.dvd_of_dvd_pow (by rw [← hy2]; exact dvd_mul_right 2 C)
            obtain ⟨x, hx⟩ := h2y
            refine ⟨x, ?_⟩
            rw [hx] at hy2
            nlinarith [hy2]
        have hjcases : j = 3 ∨ j = 6 := by
          rcases hCclass with hCsq | ⟨x, hx⟩
          · have hLsq : IsSquare (goldenLucas j) := by
              rw [← hCcast]
              exact hCsq.map (Nat.castRingHom ℤ)
            have hc := (lucas_square_classifications j).1.mp hLsq
            omega
          · have hLtwo : ∃ x : ℤ, goldenLucas j = 2 * x ^ 2 := by
              refine ⟨x, ?_⟩
              rw [← hCcast]
              exact_mod_cast hx
            have hc := (lucas_square_classifications j).2.mp hLtwo
            omega
        have hsmall : (m = 3 ∧ t = 2) ∨ (m = 3 ∧ t = 4) ∨ (m = 6 ∧ t = 2) := by
          dsimp [j] at hjcases
          rcases hjcases with h3 | h6
          · have hq : q = 1 := by nlinarith
            left
            constructor <;> nlinarith
          · have hmle : m ≤ 6 := by nlinarith
            interval_cases m <;> omega
        rcases hsmall with hgood | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hgood
        · norm_num [Nat.fib] at hsq
        · norm_num [Nat.fib] at hsq
      · rintro ⟨rfl, rfl⟩
        norm_num [Nat.fib]
    have squareFib (n : ℕ) (hn : 0 < n) (hsq : IsSquare (Nat.fib n)) :
        n = 1 ∨ n = 2 ∨ n = 12 := by
      rcases Nat.even_or_odd n with heven | hodd
      · obtain ⟨j, hnshape⟩ := heven
        have hjpos : 0 < j := by omega
        have hdouble (a : ℕ) :
            (Nat.fib (2 * a) : ℤ) = (Nat.fib a : ℤ) * goldenLucas a := by
          calc
            (Nat.fib (2 * a) : ℤ) = (phi ^ (2 * a)).b := (golden_phi_pow_b_eq_fib_index _).symm
            _ = ((phi ^ a) ^ 2).b := by rw [pow_mul']
            _ = (phi ^ a).b * trace (phi ^ a) := by simp only [pow_two, b_mul, trace]; ring
            _ = _ := by rw [golden_phi_pow_b_eq_fib_index]; rfl
        have hLpos : 0 < goldenLucas j := by
          have hi : j = (j - 1) + 1 := by omega
          rw [hi, golden_lucas_succ_eq_fib_add_fib]
          have hp := Nat.fib_pos.mpr (by omega : 0 < j - 1 + 2)
          positivity
        let C := (goldenLucas j).toNat
        let K := Nat.fib j
        have hCcast : (C : ℤ) = goldenLucas j := Int.toNat_of_nonneg hLpos.le
        have hCpos : 0 < C := by
          have hc : (0 : ℤ) < (C : ℤ) := by rw [hCcast]; exact hLpos
          exact_mod_cast hc
        have hKpos : 0 < K := Nat.fib_pos.mpr hjpos
        have hn2j : n = 2 * j := by omega
        have htotal : IsSquare (K * C) := by
          have hi := hdouble j
          rw [← hCcast] at hi
          have hiNat : Nat.fib (2 * j) = Nat.fib j * C := by exact_mod_cast hi
          rwa [hn2j, hiNat] at hsq
        have hNoOddCommon (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
            (hpC : p ∣ C) : ¬ p ∣ K := by
          intro hpK
          have hpFj : p ∣ Nat.fib j := hpK
          have : Fact p.Prime := ⟨hp⟩
          have hF0 : (Nat.fib j : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpFj
          have hL0 : (goldenLucas j : ZMod p) = 0 := by
            rw [← hCcast, Int.cast_natCast]
            exact (ZMod.natCast_eq_zero_iff _ _).mpr hpC
          have hdisc := congrArg (Int.castRingHom (ZMod p)) (golden_lucas_discriminant j)
          simp only [Int.coe_castRingHom, Int.cast_sub, Int.cast_mul, Int.cast_pow,
            Int.cast_natCast, Int.cast_neg, Int.cast_one, Int.cast_ofNat, hF0, hL0,
            zero_pow (by decide : 2 ≠ 0), mul_zero, sub_self] at hdisc
          have hfour : (4 : ZMod p) ≠ 0 := by
            have htwo : (2 : ZMod p) ≠ 0 := by
              intro hz
              have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
              exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
            have hi : (4 : ZMod p) = (2 : ZMod p) ^ 2 := by ring
            rw [hi]
            exact pow_ne_zero _ htwo
          exact (mul_ne_zero hfour (pow_ne_zero j (neg_ne_zero.mpr one_ne_zero))) hdisc.symm
        have hCoddEven (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
            Even (padicValNat p C) := by
          have : Fact p.Prime := ⟨hp⟩
          by_cases hpC : p ∣ C
          · have hK0 := padicValNat.eq_zero_of_not_dvd (hNoOddCommon p hp hp2 hpC)
            obtain ⟨x, hx⟩ := htotal
            have hx2 : K * C = x ^ 2 := by simpa [pow_two] using hx
            have hv := congrArg (padicValNat p) hx2
            rw [padicValNat.mul hKpos.ne' hCpos.ne', padicValNat.pow, hK0, zero_add] at hv
            exact ⟨padicValNat p x, by omega⟩
          · rw [padicValNat.eq_zero_of_not_dvd hpC]
            exact ⟨0, by omega⟩
        have hAllEvenSquare (a : ℕ) (ha : 0 < a)
            (he : ∀ p : ℕ, p.Prime → Even (padicValNat p a)) : IsSquare a := by
          let s := ∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2)
          refine ⟨s, ?_⟩
          have hs : a = s ^ 2 := by
            rw [Nat.prod_primeFactors_pow_factorization ha.ne']
            dsimp only [s]
            rw [← Finset.prod_pow]
            apply Finset.prod_congr rfl
            intro p hp
            rw [← pow_mul]
            congr 1
            have he' : Even (a.factorization p) := by
              rw [Nat.factorization_def a (Nat.prime_of_mem_primeFactors hp)]
              exact he p (Nat.prime_of_mem_primeFactors hp)
            obtain ⟨z, hz⟩ := he'
            omega
          simpa [pow_two] using hs
        have hCclass : IsSquare C ∨ ∃ x : ℕ, C = 2 * x ^ 2 := by
          by_cases he2 : Even (padicValNat 2 C)
          · left
            apply hAllEvenSquare C hCpos
            intro p hp
            by_cases hp2 : p = 2
            · simpa [hp2] using he2
            · exact hCoddEven p hp hp2
          · right
            have ho2 : Odd (padicValNat 2 C) := Nat.not_even_iff_odd.mp he2
            have h2Csq : IsSquare (2 * C) := by
              apply hAllEvenSquare (2 * C) (by positivity)
              intro p hp
              have : Fact p.Prime := ⟨hp⟩
              rw [padicValNat.mul (by decide : (2 : ℕ) ≠ 0) hCpos.ne']
              by_cases hp2 : p = 2
              · subst p
                rw [padicValNat_self]
                obtain ⟨z, hz⟩ := ho2
                exact ⟨z + 1, by omega⟩
              · have hpd2 : ¬p ∣ 2 := by
                  intro h
                  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
                rw [padicValNat.eq_zero_of_not_dvd hpd2, zero_add]
                exact hCoddEven p hp hp2
            obtain ⟨y, hy⟩ := h2Csq
            have hy2 : 2 * C = y ^ 2 := by simpa [pow_two] using hy
            have h2y : 2 ∣ y := Nat.prime_two.dvd_of_dvd_pow (by rw [← hy2]; exact dvd_mul_right 2 C)
            obtain ⟨x, hx⟩ := h2y
            refine ⟨x, ?_⟩
            rw [hx] at hy2
            nlinarith [hy2]
        have hjcases : j = 1 ∨ j = 3 ∨ j = 6 := by
          rcases hCclass with hCsq | ⟨x, hx⟩
          · have hLsq : IsSquare (goldenLucas j) := by
              rw [← hCcast]
              exact hCsq.map (Nat.castRingHom ℤ)
            have hc := (lucas_square_classifications j).1.mp hLsq
            rcases hc with h1 | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h3)
          · have hLtwo : ∃ x : ℤ, goldenLucas j = 2 * x ^ 2 := by
              refine ⟨x, ?_⟩
              rw [← hCcast]
              exact_mod_cast hx
            have hc := (lucas_square_classifications j).2.mp hLtwo
            right; right
            omega
        rcases hjcases with hj1 | hj3 | hj6
        · right; left; omega
        · have hn6 : n = 6 := by omega
          rw [hn6] at hsq
          norm_num [Nat.fib] at hsq
        · right; right; omega
      · by_cases hn1 : n = 1
        · exact Or.inl hn1
        · have hn3 : 3 ≤ n := by
            have ho := Nat.odd_iff.mp hodd
            omega
          exact (D5.S3.Arith.Primes.FibonacciOddIndexNonsquare.fibonacci_odd_index_nonsquare
            n hn3 hodd hsq).elim
    let d := Nat.gcd m n
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left n hm
    have hdm : d ∣ m := Nat.gcd_dvd_left _ _
    have hdn : d ∣ n := Nat.gcd_dvd_right _ _
    have hDm : d * (m / d) = m := Nat.mul_div_cancel' hdm
    have hDn : d * (n / d) = n := Nat.mul_div_cancel' hdn
    let G := Nat.fib d
    have hGpos : 0 < G := Nat.fib_pos.mpr hdpos
    have hGM : G ∣ Nat.fib m := Nat.fib_dvd d m hdm
    have hGN : G ∣ Nat.fib n := Nat.fib_dvd d n hdn
    let M := Nat.fib m / G
    let N := Nat.fib n / G
    have hGm : G * M = Nat.fib m := Nat.mul_div_cancel' hGM
    have hGn : G * N = Nat.fib n := Nat.mul_div_cancel' hGN
    have hGgcd : Nat.gcd (Nat.fib m) (Nat.fib n) = G := (Nat.fib_gcd m n).symm
    have hcop : Nat.Coprime M N := by
      have h := Nat.coprime_div_gcd_div_gcd
        (Nat.gcd_pos_of_pos_left (Nat.fib n) (Nat.fib_pos.mpr hm))
      simpa only [hGgcd, M, N] using h
    obtain ⟨x, hx⟩ := hsq
    have hxpow : Nat.fib m * Nat.fib n = x ^ 2 := by simpa [pow_two] using hx
    have hG2 : G ^ 2 ∣ x ^ 2 := by
      rw [← hxpow, pow_two]
      exact mul_dvd_mul hGM hGN
    have hGx : G ∣ x := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hG2
    let X := x / G
    have hGxx : G * X = x := Nat.mul_div_cancel' hGx
    have hMN : M * N = X ^ 2 := by
      apply Nat.mul_left_cancel (pow_pos hGpos 2)
      calc
        G ^ 2 * (M * N) = (G * M) * (G * N) := by ring
        _ = Nat.fib m * Nat.fib n := by rw [hGm, hGn]
        _ = x ^ 2 := hxpow
        _ = (G * X) ^ 2 := by rw [hGxx]
        _ = G ^ 2 * X ^ 2 := by ring
    have hunit : IsUnit (GCDMonoid.gcd M N) := by
      rw [gcd_eq_nat_gcd, hcop.gcd_eq_one]
      exact isUnit_one
    obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hunit hMN
    obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow
      (by rw [gcd_eq_nat_gcd, hcop.symm.gcd_eq_one]; exact isUnit_one)
      (by simpa only [Nat.mul_comm] using hMN)
    have hDmSq : IsSquare (Nat.fib d * Nat.fib m) := by
      refine ⟨G * a, ?_⟩
      change G * Nat.fib m = _
      rw [← hGm, ha]
      ring
    have hDnSq : IsSquare (Nat.fib d * Nat.fib n) := by
      refine ⟨G * b, ?_⟩
      change G * Nat.fib n = _
      rw [← hGn, hb]
      ring
    by_cases hdlarge : 2 < d
    · have hClass (k : ℕ) (hk : 0 < k) (hdk : d ∣ k)
          (hprod : IsSquare (Nat.fib d * Nat.fib k)) :
          k = d ∨ (d = 3 ∧ k = 6) := by
        have hmul : d * (k / d) = k := Nat.mul_div_cancel' hdk
        have hquotpos : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hk hdk) hdpos
        by_cases hquot1 : k / d = 1
        · left
          simpa [hquot1] using hmul.symm
        · have hquotgt : 1 < k / d := by omega
          have hidx : k / d * d = k := by simpa [Nat.mul_comm] using hmul
          rcases Nat.even_or_odd (k / d) with he | ho
          · have hc := (evenClass d (k / d) hdlarge hquotgt he).mp
              (by rw [hidx]; exact hprod)
            right
            refine ⟨hc.1, ?_⟩
            rw [hc.2, hc.1] at hmul
            norm_num at hmul
            exact hmul.symm
          · have hc := oddExclude d (k / d) hdpos hquotgt ho
            rw [hidx] at hc
            exact (hc hprod).elim
      have hcm := hClass m hm hdm hDmSq
      have hcn := hClass n hn hdn hDnSq
      rcases hcm with hmd | ⟨hd3, hm6⟩
      · rcases hcn with hnd | ⟨hd3, hn6⟩
        · left
          exact hmd.trans hnd.symm
        · right; right
          exact ⟨Or.inl (hmd.trans hd3), Or.inr hn6⟩
      · rcases hcn with hnd | ⟨_, hn6⟩
        · right; right
          exact ⟨Or.inr hm6, Or.inl (hnd.trans hd3)⟩
        · left
          exact hm6.trans hn6.symm
    · have hdsmall : d = 1 ∨ d = 2 := by omega
      have hG1 : G = 1 := by
        rcases hdsmall with hd1 | hd2
        · simp [G, hd1]
        · simp [G, hd2]
      have hFmSquare : IsSquare (Nat.fib m) := by
        change IsSquare (G * Nat.fib m) at hDmSq
        simpa [hG1] using hDmSq
      have hFnSquare : IsSquare (Nat.fib n) := by
        change IsSquare (G * Nat.fib n) at hDnSq
        simpa [hG1] using hDnSq
      exact Or.inr (Or.inl ⟨squareFib m hm hFmSquare, squareFib n hn hFnSquare⟩)
  · rintro (heq | ⟨hmclass, hnclass⟩ | ⟨hmclass, hnclass⟩)
    · subst n
      exact ⟨Nat.fib m, rfl⟩
    · rcases hmclass with rfl | rfl | rfl <;>
        rcases hnclass with rfl | rfl | rfl <;> norm_num [Nat.fib]
    · rcases hmclass with rfl | rfl <;>
        rcases hnclass with rfl | rfl <;> norm_num [Nat.fib]

#print axioms fibonacci_squareclass_pairs
end D5.S3.Arith.Primes.FibSquareclassRigidity

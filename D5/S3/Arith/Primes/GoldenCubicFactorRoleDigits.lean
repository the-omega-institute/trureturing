/- GID: D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicFactorRoleDigits
   mirror-E: none(waiver:exact-native-factor-role-arithmetic)
   anchors: []
   utility: none
   digest: Exact ternary and dyadic constraints for a square-times-cube factorization of a native Lucas block. -/

import D5.S3.Arith.Primes.GoldenCubicBlockRanks
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicFactorRoleDigits
open D5.S1.Scale
open D5.S3.Arith.Primes.GoldenCubicBlockRanks
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure

/-- The unmodified native cubic Lucas block. -/
def nativeBlock (j : ℕ) : ℤ := goldenLucas (3^j)^2+3

private theorem nativeBlock_lucas_step (j : ℕ) :
    goldenLucas (3^(j+1)) = goldenLucas (3^j)*nativeBlock j := by
  by_cases hj : 1 ≤ j
  · exact (golden_cubic_lucas_block j hj).2.2.2.2.2
  · have he : j = 0 := by omega
    subst j
    open D5.S0.Carrier in norm_num [nativeBlock,goldenLucas,trace,phi,pow_succ]

private theorem nativeBlock_fixed_point_step (j : ℕ) :
    nativeBlock (j+1)-1 = (nativeBlock j-1)*((nativeBlock j-1)^2-3) := by
  have h := nativeBlock_lucas_step j
  unfold nativeBlock at h ⊢
  rw [h]
  ring

private theorem nativeBlock_mod128 (j : ℕ) (hj : 1 ≤ j) :
    nativeBlock j ≡ 19 [ZMOD 128] := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h0 : j = 0
    · subst j
      have hL : goldenLucas 3 = 4 := by
        open D5.S0.Carrier in norm_num [goldenLucas,trace,phi,pow_succ]
      have he : nativeBlock 1 = 19 := by norm_num [nativeBlock,hL]
      change nativeBlock 1 ≡ 19 [ZMOD 128]
      rw [he]
    · have hm := ih (by omega)
      have hstep : nativeBlock (j+1) = 3+(nativeBlock j-3)*(nativeBlock j)^2 := by
        nlinarith only [nativeBlock_fixed_point_step j]
      change nativeBlock (j+1) ≡ 19 [ZMOD 128]
      rw [hstep]
      exact (((hm.sub_right 3).mul (hm.pow 2)).add_left 3).trans (by decide)

/-- Only the square-role factor contributes to the first surviving
ternary digit of a square-times-cube product. -/
theorem square_role_ternary_digit (R a b u : ℤ) (hR : R ≠ 0)
    (h3 : (3:ℤ) ∣ R)
    (hfac : (1+R*a)^2*(1+R*b)^3-1 = R*u) :
    (a : ZMod 3) = 2*(u : ZMod 3) := by
  let v := a*(2+R*a)*(1+R*b)^3+b*(3+3*R*b+R^2*b^2)
  have he : (1+R*a)^2*(1+R*b)^3-1 = R*v := by dsimp [v]; ring
  have hu := mul_left_cancel₀ hR (hfac.symm.trans he)
  have hzR : (R : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3
  have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hu
  simp only [v, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_one] at hz
  rw [hzR] at hz
  have hzero : (3 : ZMod 3) = 0 := by decide
  rw [hzero] at hz
  simp at hz
  rw [hz]
  have htwo : (2:ZMod 3)*2 = 1 := by decide
  calc
    (a : ZMod 3) = (a : ZMod 3)*(2*2) := by rw [htwo,mul_one]
    _ = 2*((a : ZMod 3)*2) := by ring

/-- The first unit of the native block minus one alternates at every
level, including the level-zero base case. -/
theorem native_block_ternary_unit (j : ℕ) :
    ∃ u : ℤ, nativeBlock j-1 = (3:ℤ)^(j+1)*u ∧ (u : ZMod 3) = (-1)^j := by
  induction j with
  | zero =>
      refine ⟨1,?_,by norm_num⟩
      open D5.S0.Carrier in norm_num [nativeBlock, goldenLucas, trace, phi]
  | succ j ih =>
      obtain ⟨u,hu,hmod⟩ := ih
      let v : ℤ := 3*((3:ℤ)^j*u)^2-1
      refine ⟨u*v, ?_, ?_⟩
      · rw [nativeBlock_fixed_point_step, hu]
        simp only [pow_succ]
        dsimp only [v]
        ring
      · simp only [Int.cast_mul, hmod, pow_succ]
        congr 1
        dsimp [v]
        push_cast
        rw [show (3:ZMod 3)=0 by decide]
        ring

private theorem block_prime_ne_two_five (j p : ℕ) (hj : 1 ≤ j)
    (hd : (p:ℤ) ∣ nativeBlock j) : p ≠ 2 ∧ p ≠ 5 := by
  have hodd : ¬ (2:ℤ) ∣ nativeBlock j := by
    have hc : nativeBlock j ≡ 19 [ZMOD 2] :=
      (nativeBlock_mod128 j hj).of_dvd (by decide)
    intro hh
    have hz := Int.emod_eq_zero_of_dvd hh
    change nativeBlock j % 2 = 19 % 2 at hc
    omega
  have hfive : ¬ (5:ℤ) ∣ nativeBlock j := by
    have hxSq : (goldenLucas (3^j) : ZMod 5)^2 = 1 := by
      simpa only [Int.cast_pow] using (golden_cubic_lucas_block j hj).2.2.2.1
    intro hh
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hh
    simp only [nativeBlock, Int.cast_add, Int.cast_pow, Int.cast_ofNat, hxSq] at hz
    exact (by decide : (1+3 : ZMod 5) ≠ 0) hz
  constructor
  · intro he
    subst p
    exact hodd hd
  · intro he
    subst p
    exact hfive hd

/-- The native primitive-rank restriction gives the stronger modulus
twice the next ternary power for both prime roles. -/
theorem block_prime_twice_ternary_dvd_pred (j p : ℕ) (hj : 1 ≤ j) (hp : p.Prime)
    (hd : (p:ℤ) ∣ nativeBlock j) :
    2*3^(j+1) ∣ p-1 := by
  obtain ⟨hp2,hp5⟩ := block_prime_ne_two_five j p hj hd
  obtain ⟨hr,hs,_⟩ := cubic_block_b_prime_rank j p hj hp hd
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrec : legendreSym p 5 = legendreSym 5 p :=
    legendreSym.quadratic_reciprocity_one_mod_four
      (p := 5) (q := p) (by norm_num) hp2
  have hsym : legendreSym 5 p = 1 := hrec.symm.trans hs
  have hw := (rankWitness p hp).property
  have h := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound hp hp5 hw.1 hw.2.1 hw.2.2
  rw [ite_eq_left hsym] at h
  rwa [show (rankWitness p hp).val = fibonacciRank p by simp [fibonacciRank,hp], hr] at h

/-- Necessary native square-role arithmetic, obtained from the actual
square-times-cube identity. The second formula uses the full doubled
modulus forced by the primitive Fibonacci rank. -/
theorem native_square_role_digits (j P Q : ℕ) (hj : 1 ≤ j)
    (hP : P.Prime) (hQ : Q.Prime)
    (hfac : nativeBlock j = (P:ℤ)^2*(Q:ℤ)^3) :
    let R := (3:ℤ)^(j+1)
    (((((P:ℤ)-1)/R : ℤ) : ZMod 3) = 2*(-1)^j) ∧
    (((((P:ℤ)-1)/(2*R) : ℤ) : ZMod 3) = (-1)^j) := by
  let R := (3:ℤ)^(j+1)
  have hR : R ≠ 0 := by dsimp [R]; positivity
  have hR3 : (3:ℤ) ∣ R := by dsimp [R]; exact dvd_pow_self 3 (by omega)
  have hPd : (P:ℤ) ∣ nativeBlock j := by
    rw [hfac]
    exact ⟨(P:ℤ)*(Q:ℤ)^3, by ring⟩
  have hQd : (Q:ℤ) ∣ nativeBlock j := by
    rw [hfac]
    exact ⟨(P:ℤ)^2*(Q:ℤ)^2, by ring⟩
  have hPd' := block_prime_twice_ternary_dvd_pred j P hj hP hPd
  have hQd' := block_prime_twice_ternary_dvd_pred j Q hj hQ hQd
  have castPred (p : ℕ) (hp : p.Prime) (h : 2*3^(j+1) ∣ p-1) : 2*R ∣ (p:ℤ)-1 := by
    have hh : ((2*3^(j+1):ℕ):ℤ) ∣ ((p-1:ℕ):ℤ) := by exact_mod_cast h
    simpa [R, Int.ofNat_sub hp.one_le] using hh
  obtain ⟨a,ha⟩ := castPred P hP hPd'
  obtain ⟨b,hb⟩ := castPred Q hQ hQd'
  obtain ⟨u,hu,hunit⟩ := native_block_ternary_unit j
  have hPa : (P:ℤ) = 1+R*(2*a) := by linear_combination ha
  have hQb : (Q:ℤ) = 1+R*(2*b) := by linear_combination hb
  have he : (1+R*(2*a))^2*(1+R*(2*b))^3-1 = R*u := by
    rw [← hPa, ← hQb, ← hfac]
    exact hu
  have hmod := square_role_ternary_digit R (2*a) (2*b) u hR hR3 he
  have hquot1 : ((P:ℤ)-1)/R = 2*a := by
    rw [ha,show 2*R*a=R*(2*a) by ring,Int.mul_ediv_cancel_left _ hR]
  have hquot2 : ((P:ℤ)-1)/(2*R) = a := by
    rw [ha,Int.mul_ediv_cancel_left _ (by positivity)]
  change (((((P:ℤ)-1)/R : ℤ) : ZMod 3) = 2*(-1)^j) ∧
    (((((P:ℤ)-1)/(2*R) : ℤ) : ZMod 3) = (-1)^j)
  rw [hquot1,hquot2]
  rw [hunit] at hmod
  refine ⟨hmod,?_⟩
  simp only [Int.cast_mul, Int.cast_ofNat] at hmod
  exact mul_left_cancel₀ (by decide : (2:ZMod 3) ≠ 0) hmod

/-- The first square-role ternary digit really is nonzero: the
three-adic valuation of the prime minus one is exactly the next level. -/
theorem square_role_pred_valuation (j P Q : ℕ) (hj : 1 ≤ j)
    (hP : P.Prime) (hQ : Q.Prime)
    (hfac : nativeBlock j = (P:ℤ)^2*(Q:ℤ)^3) :
    padicValInt 3 ((P:ℤ)-1) = j+1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let R := (3:ℤ)^(j+1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hPd : (P:ℤ) ∣ nativeBlock j := by
    rw [hfac]
    exact ⟨(P:ℤ)*(Q:ℤ)^3, by ring⟩
  have hPd' := block_prime_twice_ternary_dvd_pred j P hj hP hPd
  have hh : ((2*3^(j+1):ℕ):ℤ) ∣ ((P-1:ℕ):ℤ) := by exact_mod_cast hPd'
  have hdiv : R ∣ (P:ℤ)-1 := by
    apply dvd_trans (dvd_mul_left R (2:ℤ))
    simpa [R, Int.ofNat_sub hP.one_le] using hh
  obtain ⟨a,ha⟩ := hdiv
  have hu := (native_square_role_digits j P Q hj hP hQ hfac).1
  change (((((P:ℤ)-1)/R : ℤ) : ZMod 3) = 2*(-1)^j) at hu
  rw [ha, Int.mul_ediv_cancel_left _ hR.ne'] at hu
  have ha3 : ¬(3:ℤ) ∣ a := by
    intro h
    have hz : (a : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    rw [hu] at hz
    exact (mul_ne_zero (by decide) (pow_ne_zero j (by decide))) hz
  have ha0 : a ≠ 0 := fun h => ha3 (h ▸ dvd_zero _)
  rw [ha, padicValInt.mul hR.ne' ha0, padicValInt.eq_zero_of_not_dvd ha3, add_zero]
  change padicValInt 3 (((3:ℕ)^(j+1):ℕ):ℤ) = j+1
  rw [padicValInt.of_nat, padicValNat.prime_pow]

/-- The cube-role prime is 19 modulo 24. The dyadic assumption is
native, not an independent premise of this arithmetic statement. -/
theorem cube_role_mod24 (j P Q : ℕ) (hj : 1 ≤ j) (hQ : Q.Prime)
    (hfac : nativeBlock j = (P:ℤ)^2*(Q:ℤ)^3) :
    (Q:ℤ) ≡ 19 [ZMOD 24] := by
  have hB8 : nativeBlock j ≡ 3 [ZMOD 8] :=
    ((nativeBlock_mod128 j hj).of_dvd (by decide : (8:ℤ) ∣ 128)).trans
      (by decide : (19:ℤ) ≡ 3 [ZMOD 8])
  have hz := (ZMod.intCast_eq_intCast_iff _ _ 8).mpr hB8
  rw [hfac] at hz
  push_cast at hz
  have hf : ∀ a b : ZMod 8, a^2*b^3 = 3 → b = 3 := by decide
  have hQ8 : (Q:ℤ) ≡ 3 [ZMOD 8] :=
    (ZMod.intCast_eq_intCast_iff _ _ 8).mp (hf _ _ hz)
  have hQd : (Q:ℤ) ∣ nativeBlock j := by
    rw [hfac]
    exact ⟨(P:ℤ)^2*(Q:ℤ)^2, by ring⟩
  have hd := block_prime_twice_ternary_dvd_pred j Q hj hQ hQd
  have h3d : 3 ∣ (Q-1) :=
    (dvd_pow_self 3 (by omega : j+1 ≠ 0)).trans ((dvd_mul_left _ _).trans hd)
  have hd' : (3:ℤ) ∣ (Q:ℤ)-1 := by
    have hh : ((3:ℕ):ℤ) ∣ ((Q-1:ℕ):ℤ) := by exact_mod_cast h3d
    rw [Int.ofNat_sub hQ.one_le] at hh
    norm_num at hh
    exact hh
  have hQ3 : (1:ℤ) ≡ (Q:ℤ) [ZMOD 3] := (Int.modEq_iff_dvd).mpr hd'
  change (Q:ℤ)%8 = 3%8 at hQ8
  change (1:ℤ)%3 = (Q:ℤ)%3 at hQ3
  change (Q:ℤ)%24 = 19%24
  omega

private theorem square_lift (x M : ℤ) (hM : (2:ℤ) ∣ M)
    (hx : x ≡ 1 [ZMOD M]) : x^2 ≡ 1 [ZMOD 2*M] := by
  obtain ⟨a,ha⟩ := Int.modEq_iff_dvd.mp hx.symm
  obtain ⟨t,ht⟩ := hM
  have he : x = 1+M*a := by linarith
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-a-t*a^2, ?_⟩
  rw [he,ht]
  ring

private theorem odd_power_thirty_two (x : ℤ) (hx : x ≡ 1 [ZMOD 2]) :
    x^32 ≡ 1 [ZMOD 128] := by
  let k := x/4
  have h4 : x=4*k+1 ∨ x=4*k+3 := by
    change x%2 = 1%2 at hx
    dsimp [k]
    omega
  have h2 : x^2 ≡ 1 [ZMOD 8] := by
    apply Int.modEq_iff_dvd.mpr
    rcases h4 with he|he
    · refine ⟨-2*k^2-k, ?_⟩
      rw [he]
      ring
    · refine ⟨-2*k^2-3*k-1, ?_⟩
      rw [he]
      ring
  have h4' : x^4 ≡ 1 [ZMOD 16] := by
    have hh := square_lift (x^2) 8 (by decide) h2
    rw [← pow_mul, show (2:ℕ)*2=4 by decide, show (2:ℤ)*8=16 by decide] at hh
    exact hh
  have h8 : x^8 ≡ 1 [ZMOD 32] := by
    have hh := square_lift (x^4) 16 (by decide) h4'
    rw [← pow_mul, show (4:ℕ)*2=8 by decide, show (2:ℤ)*16=32 by decide] at hh
    exact hh
  have h16 : x^16 ≡ 1 [ZMOD 64] := by
    have hh := square_lift (x^8) 32 (by decide) h8
    rw [← pow_mul, show (8:ℕ)*2=16 by decide, show (2:ℤ)*32=64 by decide] at hh
    exact hh
  have hh := square_lift (x^16) 64 (by decide) h16
  rw [← pow_mul, show (16:ℕ)*2=32 by decide, show (2:ℤ)*64=128 by decide] at hh
  exact hh

/-- The native dyadic reading determines the cube-role prime modulo
128 from the square-role prime, rather than just fixing its mod-eight class. -/
theorem cube_role_mod128_coupling (j P Q : ℕ) (hj : 1 ≤ j)
    (hfac : nativeBlock j = (P:ℤ)^2*(Q:ℤ)^3) :
    (Q:ℤ) ≡ 43*(P:ℤ)^10 [ZMOD 128] := by
  have hB128 : nativeBlock j ≡ 19 [ZMOD 128] := nativeBlock_mod128 j hj
  have hz := (ZMod.intCast_eq_intCast_iff _ _ 128).mpr hB128
  rw [hfac] at hz
  push_cast at hz
  let red : ZMod 128 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 128) (ZMod 2)
  have h2 : (red (P : ZMod 128))^2 * (red (Q : ZMod 128))^3 = 1 := by
    have h := congrArg red hz
    simpa only [map_mul,map_pow,map_ofNat,show (19:ZMod 2)=1 by decide] using h
  have hs : ∀ a b : ZMod 2, a^2*b^3 = 1 → a = 1 ∧ b = 1 := by decide
  obtain ⟨hP2,hQ2⟩ := hs _ _ h2
  have hpOdd : (P:ℤ) ≡ 1 [ZMOD 2] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    simpa only [map_natCast,Int.cast_natCast,Int.cast_one] using hP2
  have hqOdd : (Q:ℤ) ≡ 1 [ZMOD 2] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    simpa only [map_natCast,Int.cast_natCast,Int.cast_one] using hQ2
  have hP32 : (P:ZMod 128)^32 = 1 := by
    simpa only [Int.cast_pow,Int.cast_natCast,Int.cast_one] using
      (ZMod.intCast_eq_intCast_iff _ _ 128).mpr (odd_power_thirty_two _ hpOdd)
  have hQ32 : (Q:ZMod 128)^32 = 1 := by
    simpa only [Int.cast_pow,Int.cast_natCast,Int.cast_one] using
      (ZMod.intCast_eq_intCast_iff _ _ 128).mpr (odd_power_thirty_two _ hqOdd)
  have hpow := congrArg (fun z : ZMod 128 => z^11) hz
  change (((P : ZMod 128)^2)*((Q : ZMod 128)^3))^11 = (19:ZMod 128)^11 at hpow
  rw [mul_pow, ← pow_mul, ← pow_mul,show 2*11=22 by decide,
    show 3*11=32+1 by decide,pow_add,hQ32,one_mul,pow_one,
    show (19 : ZMod 128)^11 = 43 by decide] at hpow
  apply (ZMod.intCast_eq_intCast_iff _ _ 128).mp
  push_cast
  calc
    (Q : ZMod 128) = (P : ZMod 128)^32*(Q:ZMod 128) := by rw [hP32,one_mul]
    _ = (P : ZMod 128)^10*((P:ZMod 128)^22*(Q:ZMod 128)) := by
      rw [← mul_assoc,← pow_add]
    _ = 43*(P : ZMod 128)^10 := by rw [hpow,mul_comm]

end D5.S3.Arith.Primes.GoldenCubicFactorRoleDigits

/- GID: D5/S3/Arith/Primes/GoldenCubicNormalizedZeroDigit
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicNormalizedZeroDigit
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The normalized later zero-branch digit recovers the earlier native cubic unit up to an explicit unit cube. -/

import D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth

set_option autoImplicit false

/-! # The normalized digit of the marked zero root

The native recurrence controls the divided Lucas parameter. The marked cubic
then determines the next root digit by its linear terms. The earlier equation
L² + 3 = 0 modulo p supplies the explicit unit cube relating this digit to the
earlier normalized block divided by twelve.
-/

namespace D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit
open D5.S1.Scale (goldenLucas golden_cubic_lucas_block)

private def eval (x t : ℤ) : ℤ := t^3 - 3*(x^2+3)*t + 2*(x^2+3)*x

private theorem cast_pow_vanishes (p h : ℕ) (hh : 1 ≤ h) :
    (((p:ℤ)^h : ℤ) : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_pow_self (p:ℤ) (by omega)

private theorem linearized (p h : ℕ) (hh : 1 ≤ h) (hp : p.Prime) (hp3 : 3 < p)
    (v w : ℤ) (hF : (p:ℤ)^(h+1) ∣ eval ((p:ℤ)^h*w) ((p:ℤ)^h*v)) :
    (3 : ZMod p) * v = 2 * w := by
  let q : ℤ := (p:ℤ)^h
  let E := -9*v+6*w+q^2*(v^3-3*w^2*v+2*w^3)
  have hf : eval (q*w) (q*v) = q*E := by unfold eval E; ring
  change (p:ℤ)^(h+1) ∣ eval (q*w) (q*v) at hF
  rw [hf,pow_succ] at hF
  have hpq : q ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hdiv : (p:ℤ) ∣ E := (mul_dvd_mul_iff_left hpq).mp hF
  have hsmall := (ZMod.intCast_zmod_eq_zero_iff_dvd E p).mpr hdiv
  have hq : (q : ZMod p) = 0 := cast_pow_vanishes p h hh
  dsimp only [E] at hsmall
  push_cast at hsmall
  rw [hq,zero_pow (by decide : 2 ≠ 0),zero_mul,add_zero] at hsmall
  have hu3 : IsUnit (3:ZMod p) := ZMod.isUnit_prime_of_not_dvd (by decide : Nat.Prime 3)
    (fun h => (not_le_of_gt hp3) ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp h).symm.le)
  have he : (3:ZMod p) * (3 * v) = 3 * (2*w) := by
    calc
      (3:ZMod p) * (3 * v) = -(-9 * v + 6 * w) + 3 * (2*w) := by ring
      _ = 3 * (2*w) := by rw [hsmall,neg_zero,zero_add]
  have he' := congrArg (fun z : ZMod p => (3:ZMod p)⁻¹*z) he
  simpa only [← mul_assoc, ZMod.inv_mul_of_unit _ hu3, one_mul] using he'

private theorem normalized_native_tail (p i h : ℕ) (u : ℤ) (hi : 1 ≤ i) (hh : 1 ≤ h)
    (hB : goldenLucas (3^i)^2+3 = (p:ℤ)^h*u) (k : ℕ) :
    ∃ w : ℤ, goldenLucas (3^(i+1+k)) = (p:ℤ)^h*w ∧
      (w:ZMod p) = 3^k * (goldenLucas (3^i) : ℤ) * u := by
  let x (j : ℕ) := goldenLucas (3^j)
  have step (n : ℕ) (hn : 1 ≤ n) : x (n+1) = x n * (x n^2+3) :=
    (golden_cubic_lucas_block n hn).2.2.2.2.2
  change x i^2+3 = (p:ℤ)^h*u at hB
  change ∃ w : ℤ, x (i+1+k) = (p:ℤ)^h*w ∧ (w:ZMod p) = 3^k * (x i:ℤ) * u
  induction k with
  | zero =>
    refine ⟨x i*u, ?_, ?_⟩
    · rw [Nat.add_zero,step i hi,hB]; ring
    · push_cast; ring
  | succ k ih =>
    obtain ⟨w,hw,hwr⟩ := ih
    refine ⟨w*(x (i+1+k)^2+3), ?_, ?_⟩
    · rw [show i+1+(k+1)=(i+1+k)+1 by omega,step _ (by omega)]
      calc
        x (i+1+k)*(x (i+1+k)^2+3) = ((p:ℤ)^h*w)*(x (i+1+k)^2+3) := by nth_rw 1 [hw]
        _ = (p:ℤ)^h*(w*(x (i+1+k)^2+3)) := by ring
    · have hx0 : (x (i+1+k):ZMod p) = 0 := by
        rw [hw, Int.cast_mul, cast_pow_vanishes p h hh, zero_mul]
      push_cast
      rw [hx0,hwr,pow_succ]
      ring
end D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit

namespace D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit
open D5.S1.Scale (goldenLucas)

private theorem coprime_six (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    IsCoprime (p:ℤ) 6 := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  change p.Coprime 6
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have he : p ∣ 2*3 := hd
  rcases hp.dvd_mul.mp he with h | h
  · have := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 3) h
    omega

/-- Integer representatives of an actual marked zero root at precision h+1
admit exact normalization, and the digit recovers the earlier normalized block. -/
private theorem normalized_native_zero_digit (p i k h : ℕ) (u t : ℤ)
    (hp : p.Prime) (hp3 : 3 < p) (hi : 1 ≤ i) (hh : 1 ≤ h)
    (hB : goldenLucas (3^i)^2+3 = (p:ℤ)^h*u)
    (ht : (p:ℤ) ∣ t)
    (hroot : (p:ℤ)^(h+1) ∣ eval (goldenLucas (3^(i+1+k))) t) :
    ∃ v : ℤ, t = (p:ℤ)^h*v ∧
      (-(3:ZMod p) * ((3:ZMod p)^k)⁻¹ * (v:ZMod p) =
        -2 * (goldenLucas (3^i) : ℤ) * u) := by
  obtain ⟨w,hw,hwmod⟩ := normalized_native_tail p i h u hi hh hB k
  have hx : (p:ℤ) ∣ goldenLucas (3^(i+1+k)) := by
    rw [hw]
    exact dvd_mul_of_dvd_left (dvd_pow_self (p:ℤ) (by omega)) _
  have hroot' : (p:ℤ)^h ∣ eval (goldenLucas (3^(i+1+k))) t :=
    (pow_dvd_pow (p:ℤ) (Nat.le_succ h)).trans hroot
  have htail : (p:ℤ)^h ∣ goldenLucas (3^(i+1+k)) := by rw [hw]; exact dvd_mul_right _ _
  let X := goldenLucas (3^(i+1+k))
  let Q := t^2-3*(X^2+3)
  have hxt : (p:ℤ)^h ∣ 2*(X^2+3)*X := dvd_mul_of_dvd_right htail _
  have hresp : eval X t - 2*(X^2+3)*X = t*Q := by
    unfold eval Q
    ring
  have hT := dvd_sub hroot' hxt
  change (p:ℤ)^h ∣ eval X t - 2*(X^2+3)*X at hT
  rw [hresp] at hT
  have hu3 : IsCoprime (p:ℤ) 3 := IsCoprime.of_mul_right_right
    (show IsCoprime (p:ℤ) ((2:ℤ)*3) from coprime_six p hp hp3)
  have hu9 : IsCoprime (p:ℤ) (-9) := by convert (hu3.mul_right hu3).neg_right using 1; decide
  have huQ : IsCoprime (p:ℤ) Q := by
    obtain ⟨a,ha⟩ := ht
    obtain ⟨z,hz⟩ : (p:ℤ) ∣ X := hx
    unfold Q
    rw [ha,hz]
    convert hu9.add_mul_left_right ((p:ℤ)*(a^2-3*z^2)) using 1
    ring
  obtain ⟨v,hv⟩ : (p:ℤ)^h ∣ t := (huQ.pow_left (m:=h)).dvd_of_dvd_mul_right hT
  have hlin := linearized p h hh hp hp3 v w (by simpa only [← hw, ← hv] using hroot)
  rw [hwmod] at hlin
  refine ⟨v,hv,?_⟩
  have hu3 : IsUnit (3:ZMod p) := ZMod.isUnit_prime_of_not_dvd (by decide : Nat.Prime 3)
    (fun h => (not_le_of_gt hp3) ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp h).symm.le)
  calc
    -(3:ZMod p) * ((3:ZMod p)^k)⁻¹ * (v:ZMod p) =
        -((3:ZMod p)^k)⁻¹ * (3 * (v:ZMod p)) := by ring
    _ = -((3:ZMod p)^k)⁻¹ * (2 * ((3:ZMod p)^k *
          (goldenLucas (3^i) : ℤ) * u)) := by rw [hlin]
    _ = -2 * (goldenLucas (3^i) : ℤ) * u := by
      calc
        _ = -2 * (((3:ZMod p)^k)⁻¹ * (3:ZMod p)^k) *
              (goldenLucas (3^i) : ℤ) * u := by ring
        _ = _ := by rw [ZMod.inv_mul_of_unit _ (hu3.pow k),mul_one]

end D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit

namespace D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit
open D5.S1.Scale (goldenLucas)
open D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth
  (evalMod fibonacci_marked_residue)

private theorem cast_eval (n : ℕ) (x t : ℤ) :
    ((eval x t : ℤ) : ZMod n) = evalMod n x t := by
  unfold eval evalMod
  push_cast
  rfl

/-- The actual unique finite zero branch supplied by the native theorem has
a normalized digit that reads the earlier block unit. Both the finite root
and its digit are in the actual residue rings. -/
private theorem native_residue_has_normalized_digit (p i k h : ℕ) (u : ℤ)
    (hp : p.Prime) (hp3 : 3 < p) (hi : 1 ≤ i) (hh : 1 ≤ h)
    (hB : goldenLucas (3^i)^2+3 = (p:ℤ)^h*u) :
    ∃ r : ZMod (p^(h+1)),
      evalMod (p^(h+1)) (goldenLucas (3^(i+1+k))) r = 0 ∧
      ZMod.castHom (dvd_pow_self p (by omega : h+1 ≠ 0)) (ZMod p) r = 0 ∧
      (∀ s : ZMod (p^(h+1)), evalMod (p^(h+1)) (goldenLucas (3^(i+1+k))) s = 0 →
        ZMod.castHom (dvd_pow_self p (by omega : h+1 ≠ 0)) (ZMod p) s = 0 →
        s=r) ∧
      ∃ v : ℤ, r = (((p:ℤ)^h*v : ℤ) : ZMod (p^(h+1))) ∧
        (-(3:ZMod p) * ((3:ZMod p)^k)⁻¹ * (v:ZMod p) =
          -2 * (goldenLucas (3^i) : ℤ) * u) := by
  have hpi : (p:ℤ) ∣ goldenLucas (3^i)^2+3 := by
    rw [hB]
    exact dvd_mul_of_dvd_left (dvd_pow_self (p:ℤ) (by omega)) _
  obtain ⟨r,hr,hm,_,hu⟩ :=
    fibonacci_marked_residue p i (i+1+k) h 0 hp hp3 hi (by omega) hpi (Or.inl rfl)
  have hm' : ZMod.castHom (dvd_pow_self p (by omega : h+1 ≠ 0)) (ZMod p) r = 0 := by
    simpa only [Int.cast_zero] using hm
  have hu' (s : ZMod (p^(h+1))) (hs : evalMod (p^(h+1)) (goldenLucas (3^(i+1+k))) s = 0)
      (hsm : ZMod.castHom (dvd_pow_self p (by omega : h+1 ≠ 0)) (ZMod p) s = 0) : s=r :=
    hu s hs (by simpa only [Int.cast_zero] using hsm)
  refine ⟨r,hr,hm',hu',?_⟩
  obtain ⟨t,rfl⟩ := ZMod.intCast_surjective r
  have ht : (p:ℤ) ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp
    (by simpa only [map_intCast] using hm')
  have htf : (p:ℤ)^(h+1) ∣ eval (goldenLucas (3^(i+1+k))) t := by
    rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, cast_eval]
    exact hr
  obtain ⟨v,hv,hD⟩ := normalized_native_zero_digit p i k h u t hp hp3 hi hh hB ht htf
  exact ⟨v,congrArg (fun z : ℤ => (z : ZMod (p^(h+1)))) hv,hD⟩

end D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit

namespace D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit
open D5.S1.Scale (goldenLucas)
open D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth (evalMod)

private theorem unit_twelve (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    IsUnit (12 : ZMod p) := by
  apply (ZMod.isUnit_iff_coprime 12 p).mpr
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have h : p ∣ 3*(2*2) := hd
  rcases hp.dvd_mul.mp h with h3|h4
  · exact (not_le_of_gt hp3) (Nat.le_of_dvd (by decide) h3)
  · obtain h2 | h2 := hp.dvd_mul.mp h4
    · exact (not_le_of_gt (show 2 < p by omega)) (Nat.le_of_dvd (by decide) h2)
    · exact (not_le_of_gt (show 2 < p by omega)) (Nat.le_of_dvd (by decide) h2)

/-- Multiplication by the native factor -2x changes u/12 by an explicit unit cube. -/
private theorem unit_cube_readout (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) (x u : ZMod p)
    (hx : x^2+3=0) :
    IsUnit (2*x) ∧ (-2*x*u) = (2*x)^3*(u*(12:ZMod p)⁻¹) ∧
    ((∃ y : ZMod p, y^3 = -2*x*u) ↔
      ∃ z : ZMod p, z^3 = u*(12:ZMod p)⁻¹) := by
  have h12 := unit_twelve p hp hp3
  have hx' : x^2 = -3 := eq_neg_of_add_eq_zero_left hx
  let c := 2*x
  have hc2 : c^2 = -12 := by
    calc
      c^2 = 4*x^2 := by unfold c; ring
      _ = -12 := by rw [hx']; ring
  have hc : IsUnit c := (isUnit_pow_iff (by decide : (2:ℕ) ≠ 0)).mp (hc2 ▸ h12.neg)
  have he : -2*x*u = c^3*(u*(12:ZMod p)⁻¹) := by
    symm
    calc
      c^3*(u*(12:ZMod p)⁻¹) = (c^2*c)*(u*(12:ZMod p)⁻¹) := by rw [pow_succ]
      _ = -c*u*(12*(12:ZMod p)⁻¹) := by rw [hc2]; ring
      _ = -2*x*u := by rw [ZMod.mul_inv_of_unit _ h12,mul_one]; unfold c; ring
  refine ⟨hc,he,?_⟩
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨c⁻¹*y,?_⟩
    calc
      (c⁻¹*y)^3 = (c⁻¹)^3*y^3 := mul_pow _ _ _
      _ = (c⁻¹*c)^3*(u*(12:ZMod p)⁻¹) := by rw [hy,he,mul_pow]; ring
      _ = _ := by rw [ZMod.inv_mul_of_unit _ hc,one_pow,one_mul]
  · rintro ⟨z,hz⟩
    exact ⟨c*z, by rw [mul_pow,hz,← he]⟩

private theorem normalized_representative_eq (p h : ℕ) (hp : p.Prime) (w v : ℤ)
    (H : (((p:ℤ)^h*w : ℤ) : ZMod (p^(h+1))) = (((p:ℤ)^h*v : ℤ) : ZMod (p^(h+1)))) :
    (w : ZMod p) = (v : ZMod p) := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub ((p:ℤ)^h*v) ((p:ℤ)^h*w) (p^(h+1))).mp H.symm
  rw [Int.natCast_pow,pow_succ, ← mul_sub] at hd
  have hpq : (p:ℤ)^h ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hi : (p:ℤ) ∣ w-v := (mul_dvd_mul_iff_left hpq).mp hd
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub v w p).mpr hi |>.symm

/-- The actual normalized marked-root observation gives the cube class of the
native unit divided by twelve, via the explicit unit multiplier (2L)^3. -/
theorem native_residue_cube_readout (p i k h : ℕ) (u : ℤ)
    (hp : p.Prime) (hp3 : 3 < p) (hi : 1 ≤ i) (hh : 1 ≤ h)
    (hB : goldenLucas (3^i)^2+3 = (p:ℤ)^h*u) :
    ∃ (r : ZMod (p^(h+1))) (v : ℤ),
      evalMod (p^(h+1)) (goldenLucas (3^(i+1+k))) r = 0 ∧
      ZMod.castHom (dvd_pow_self p (by omega : h+1 ≠ 0)) (ZMod p) r = 0 ∧
      (∀ s : ZMod (p^(h+1)), evalMod (p^(h+1)) (goldenLucas (3^(i+1+k))) s = 0 →
        ZMod.castHom (dvd_pow_self p (by omega : h+1 ≠ 0)) (ZMod p) s = 0 → s=r) ∧
      r = (((p:ℤ)^h*v : ℤ) : ZMod (p^(h+1))) ∧
      (∀ w : ℤ, r = (((p:ℤ)^h*w : ℤ) : ZMod (p^(h+1))) → (w:ZMod p) = (v:ZMod p)) ∧
      IsUnit (2*(goldenLucas (3^i):ℤ) : ZMod p) ∧
      -(3:ZMod p) * ((3:ZMod p)^k)⁻¹ * (v:ZMod p) =
        (2*(goldenLucas (3^i):ℤ) : ZMod p)^3*((u:ZMod p)*(12:ZMod p)⁻¹) ∧
      ((∃ y : ZMod p, y^3 = -(3:ZMod p) * ((3:ZMod p)^k)⁻¹ * (v:ZMod p)) ↔
        ∃ z : ZMod p, z^3 = (u:ZMod p)*(12:ZMod p)⁻¹) := by
  obtain ⟨r,hr,hm,hu,v,hv,hd⟩ := native_residue_has_normalized_digit p i k h u hp hp3 hi hh hB
  have hB0 := congrArg (fun z : ℤ => (z : ZMod p)) hB
  push_cast at hB0
  rw [show (p:ZMod p)^h = 0 from by rw [ZMod.natCast_self,zero_pow (by omega : h ≠ 0)],
    zero_mul] at hB0
  obtain ⟨hc,he,hi'⟩ := unit_cube_readout p hp hp3 (goldenLucas (3^i)) u hB0
  refine ⟨r,v,hr,hm,hu,hv,?_,hc,hd.trans he,?_⟩
  · intro w hw
    exact normalized_representative_eq p h hp w v (hw.symm.trans hv)
  simp only [hd,hi']

#print axioms native_residue_cube_readout
end D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit

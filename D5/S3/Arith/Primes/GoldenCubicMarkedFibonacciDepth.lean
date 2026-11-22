/- GID: D5/S3/Arith/Primes/GoldenCubicMarkedFibonacciDepth
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicMarkedFibonacciDepth
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The marked native cubic root at every finite precision reads the earlier Fibonacci entry depth. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import D5.S1.Scale.FibLucasDouble
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false

/-! # Marked native cubic roots and Fibonacci depth

The finite Hensel step selects each of the three simple seed classes separately.
Two unit divided differences compare root and parameter congruences. The
golden Lucas recurrence preserves the earlier block's depth, and Fibonacci
doubling and tripling identify the native entry measured by this depth.
-/

namespace D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth
open D5.S1.Scale

/-- Literal native cubic evaluated at an integral representative. -/
private def eval (x t : ℤ) : ℤ := t^3 - 3*(x^2+3)*t + 2*(x^2+3)*x

private def td (x t s : ℤ) : ℤ := t^2+t*s+s^2-3*(x^2+3)
private def xd (x y s : ℤ) : ℤ := 2*(x^2+x*y+y^2+3)-3*(x+y)*s

private theorem diff_divided (x y t s : ℤ) :
    eval x t - eval y s = (t-s)*td x t s + (x-y)*xd x y s := by
  unfold eval td xd
  ring

private theorem xdiff_coprime {p x y s : ℤ} (hp : IsCoprime p 6)
    (hx : p ∣ x) (hy : p ∣ y) : IsCoprime p (xd x y s) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  convert hp.add_mul_left_right (2*p*(a^2+a*b+b^2)-3*(a+b)*s) using 1
  unfold xd
  ring

private theorem tdiff_coprime {p x t s b : ℤ}
    (hp : IsCoprime p (3*b^2-9)) (hx : p ∣ x) (ht : p ∣ t-b) (hs : p ∣ s-b) :
    IsCoprime p (td x t s) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨u, hu⟩ := ht
  obtain ⟨v, hv⟩ := hs
  have he : t = b+p*u := by rw [← hu]; ring
  have hf : s = b+p*v := by rw [← hv]; ring
  rw [he, hf]
  convert hp.add_mul_left_right (3*b*(u+v)+p*(u^2+u*v+v^2-3*a^2)) using 1
  unfold td
  ring

private theorem seed_coprime {p b : ℤ} (hp : IsCoprime p 6)
    (hb : b = 0 ∨ b = 3 ∨ b = -3) : IsCoprime p (3*b^2-9) := by
  have h2 : IsCoprime p 2 := IsCoprime.of_mul_right_left
    (show IsCoprime p ((2:ℤ)*3) by convert hp using 1; decide)
  have h3 : IsCoprime p 3 := IsCoprime.of_mul_right_right
    (show IsCoprime p ((2:ℤ)*3) by convert hp using 1; decide)
  have h9 : IsCoprime p 9 := by convert h3.mul_right h3 using 1; decide
  rcases hb with rfl | rfl | rfl
  · convert h9.neg_right using 1; decide
  · convert h2.mul_right h9 using 1; decide
  · convert h2.mul_right h9 using 1; decide

/-- Both of the marked equations need only hold at the requested finite precision.
The modulus base is merely coprime to six; primality is unnecessary. -/
private theorem marked_root_isometry {p x y t s b : ℤ} (k : ℕ)
    (hp : IsCoprime p 6) (hb : b = 0 ∨ b = 3 ∨ b = -3)
    (hx : p ∣ x) (hy : p ∣ y) (ht : p ∣ t-b) (hs : p ∣ s-b)
    (hxt : p^k ∣ eval x t) (hys : p^k ∣ eval y s) :
    (p^k ∣ t-s) ↔ (p^k ∣ x-y) := by
  have hc := dvd_sub hxt hys
  rw [diff_divided] at hc
  have hT : IsCoprime (p^k) (td x t s) :=
    (tdiff_coprime (seed_coprime hp hb) hx ht hs).pow_left
  have hX : IsCoprime (p^k) (xd x y s) := (xdiff_coprime hp hx hy).pow_left
  constructor
  · intro h
    have h' := dvd_sub hc (dvd_mul_of_dvd_left h (td x t s))
    rw [add_sub_cancel_left] at h'
    exact hX.dvd_of_dvd_mul_right h'
  · intro h
    have h' := dvd_sub hc (dvd_mul_of_dvd_left h (xd x y s))
    rw [add_sub_cancel_right] at h'
    exact hT.dvd_of_dvd_mul_right h'

/-- The departure of a marked branch from its seed records the full truncated
depth of the cubic parameter. -/
private theorem marked_root_depth {p x t b : ℤ} (k : ℕ)
    (hp : IsCoprime p 6) (hb : b = 0 ∨ b = 3 ∨ b = -3)
    (hx : p ∣ x) (ht : p ∣ t-b) (hxt : p^k ∣ eval x t) :
    (p^k ∣ t-b) ↔ (p^k ∣ x) := by
  have hh : eval 0 b = 0 := by rcases hb with rfl|rfl|rfl <;> decide
  have h := marked_root_isometry k hp hb hx (dvd_zero p) ht
    (by simp) hxt (show p^k ∣ eval 0 b by rw [hh]; exact dvd_zero _)
  simpa using h

/-- A finite root can be advanced one digit without changing any old digit. -/
private theorem marked_root_lift_step {p x t b : ℤ} (k : ℕ) (hk : 1 ≤ k)
    (hp : IsCoprime p 6) (hb : b=0 ∨ b=3 ∨ b= -3)
    (hx : p ∣ x) (ht : p ∣ t-b) (hf : p^k ∣ eval x t) :
    ∃ u : ℤ, p^k ∣ u-t ∧ p ∣ u-b ∧ p^(k+1) ∣ eval x u := by
  obtain ⟨q,hq⟩ := hf
  let d := td x t t
  obtain ⟨a,c,hacz⟩ : IsCoprime p d :=
    tdiff_coprime (seed_coprime hp hb) hx ht ht
  let δ := p^k*(-q*c)
  have hδ : p^k ∣ δ := dvd_mul_right _ _
  refine ⟨t+δ, by simpa using hδ, ?_, ?_⟩
  · rw [show t+δ-b = (t-b)+δ by ring]
    exact dvd_add ht ((dvd_pow_self p (by omega : k ≠ 0)).trans hδ)
  have hlin : eval x t + δ*d = p^(k+1)*(q*a) := by
    calc
      eval x t+δ*d = p^k*q*(1-c*d) := by rw [hq]; unfold δ; ring
      _ = p^(k+1)*(q*a) := by
        rw [← hacz, pow_succ]
        ring
  have hrem : p^(k+1) ∣ δ^2*(3*t+δ) := by
    apply dvd_mul_of_dvd_left
    apply (pow_dvd_pow p (show k+1 ≤ k*2 by omega)).trans
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd hδ _
  rw [show eval x (t+δ) = (eval x t+δ*d)+δ^2*(3*t+δ) by
    unfold eval d td
    ring, hlin]
  exact dvd_add (dvd_mul_right _ _) hrem

/-- A root exists in every marked class and at every positive finite precision. -/
private theorem marked_root_exists {p x b : ℤ} (k : ℕ)
    (hp : IsCoprime p 6) (hb : b=0 ∨ b=3 ∨ b= -3) (hx : p ∣ x) :
    ∃ t : ℤ, p ∣ t-b ∧ p^(k+1) ∣ eval x t := by
  induction k with
  | zero =>
    have hh : eval 0 b = 0 := by rcases hb with rfl|rfl|rfl <;> decide
    have he := diff_divided x 0 b b
    rw [hh, sub_zero, sub_self, zero_mul, zero_add, sub_zero] at he
    refine ⟨b, by simp, ?_⟩
    simpa only [Nat.zero_add, pow_one, he] using dvd_mul_of_dvd_left hx (xd x 0 b)
  | succ k ih =>
    obtain ⟨t,ht,hf⟩ := ih
    obtain ⟨u,_,hu,huf⟩ := marked_root_lift_step (k+1) (by omega) hp hb hx ht hf
    exact ⟨u,hu,huf⟩



private theorem coprime_of_dvd_square_add_three (p x : ℤ) (hp : IsCoprime p 6)
    (hx : p ∣ x^2+3) : IsCoprime p x := by
  have h3 : IsCoprime p 3 := IsCoprime.of_mul_right_right
    (show IsCoprime p ((2:ℤ)*3) by convert hp using 1; decide)
  obtain ⟨a,b,h⟩ := h3
  obtain ⟨q,hq⟩ := hx
  refine ⟨a+b*q,-b*x,?_⟩
  calc
    (a+b*q)*p+(-b*x)*x = a*p+b*3 + b*(p*q-(x^2+3)) := by ring
    _ = 1 := by rw [←hq, sub_self, mul_zero, add_zero, h]

/-- No power of an earlier block prime is lost or acquired along the subsequent
literal golden Lucas sequence. The statement holds at every test precision. -/
private theorem native_power_depth (p : ℤ) (i j k : ℕ)
    (hp : IsCoprime p 6) (hi : 1 ≤ i) (hij : i < j)
    (hpi : p ∣ goldenLucas (3^i)^2+3) :
    (p^k ∣ goldenLucas (3^j)) ↔ (p^k ∣ goldenLucas (3^i)^2+3) := by
  let x (n : ℕ) := goldenLucas (3^n)
  have step (n : ℕ) (hn : 1 ≤ n) : x (n+1)=x n*(x n^2+3) :=
    (golden_cubic_lucas_block n hn).2.2.2.2.2
  change p ∣ x i^2+3 at hpi
  change (p^k ∣ x j) ↔ _
  have H (m : ℕ) :
      (∀ l : ℕ, (p^l ∣ x (i+1+m)) ↔ (p^l ∣ x i^2+3)) := by
    induction m with
    | zero =>
      intro l
      rw [Nat.add_zero, step i hi]
      exact ((coprime_of_dvd_square_add_three p (x i) hp hpi).pow_left
        (m := l)).dvd_mul_left_iff
    | succ m ih =>
      intro l
      have hd : p ∣ x (i+1+m) := by simpa using (ih 1).mpr (by simpa using hpi)
      obtain ⟨u,hu⟩ := hd
      have h3 : IsCoprime p 3 := IsCoprime.of_mul_right_right
        (show IsCoprime p ((2:ℤ)*3) by convert hp using 1; decide)
      have hB : IsCoprime p (x (i+1+m)^2+3) := by
        rw [hu]
        convert h3.add_mul_left_right (p*u^2) using 1
        ring
      rw [show i+1+(m+1)=(i+1+m)+1 by omega, step _ (by omega)]
      exact ((hB.pow_left (m := l)).dvd_mul_right_iff).trans (ih l)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (show i+1 ≤ j by omega)
  exact H m k

/-- A marked root of a later native cubic reports every power-divisibility test
on the earlier block, including the square-divisibility test at k=2. -/
private theorem native_marked_root_depth (p t b : ℤ) (i j k : ℕ)
    (hp : IsCoprime p 6) (hi : 1 ≤ i) (hij : i < j)
    (hpi : p ∣ goldenLucas (3^i)^2+3) (hb : b=0 ∨ b=3 ∨ b= -3)
    (ht : p ∣ t-b) (hroot : p^k ∣ eval (goldenLucas (3^j)) t) :
    (p^k ∣ t-b) ↔ (p^k ∣ goldenLucas (3^i)^2+3) := by
  have hx : p ∣ goldenLucas (3^j) := by
    simpa using (native_power_depth p i j 1 hp hi hij hpi).mpr (by simpa using hpi)
  exact (marked_root_depth k hp hb hx ht hroot).trans
    (native_power_depth p i j k hp hi hij hpi)



/-- Native cubic reduced to the actual residue ring. -/
def evalMod (n : ℕ) (x t : ZMod n) : ZMod n :=
  t^3 - 3*(x^2+3)*t + 2*(x^2+3)*x

private theorem eval_cast (n : ℕ) (x t : ℤ) :
    ((eval x t : ℤ) : ZMod n) = evalMod n x t := by
  unfold eval evalMod
  push_cast
  rfl

private theorem eq_cast_iff (n : ℕ) (x y : ℤ) :
    (x : ZMod n) = (y : ZMod n) ↔ (n : ℤ) ∣ x-y := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]

private theorem divide_pow_succ (p k : ℕ) : p ∣ p^(k+1) :=
  dvd_pow_self p (by omega)

/-- For every later native cubic and every marked seed, exactly one residue at
each positive precision is a solution in that seed class. The marked solution
equals the seed at full precision exactly when the earlier block vanishes there. -/
private theorem native_marked_residue (p i j k : ℕ) (b : ℤ)
    (hp : IsCoprime (p:ℤ) 6) (hi : 1 ≤ i) (hij : i < j)
    (hpi : (p:ℤ) ∣ goldenLucas (3^i)^2+3) (hb : b=0 ∨ b=3 ∨ b= -3) :
    ∃ r : ZMod (p^(k+1)),
      evalMod (p^(k+1)) (goldenLucas (3^j)) r = 0 ∧
      ZMod.castHom (divide_pow_succ p k) (ZMod p) r = (b : ZMod p) ∧
      (r = (b : ZMod (p^(k+1))) ↔ (p:ℤ)^(k+1) ∣ goldenLucas (3^i)^2+3) ∧
      ∀ s : ZMod (p^(k+1)), evalMod (p^(k+1)) (goldenLucas (3^j)) s = 0 →
        ZMod.castHom (divide_pow_succ p k) (ZMod p) s = (b : ZMod p) → s = r := by
  have hx : (p:ℤ) ∣ goldenLucas (3^j) := by
    simpa using (native_power_depth (p:ℤ) i j 1 hp hi hij hpi).mpr (by simpa using hpi)
  obtain ⟨t,ht,htf⟩ := marked_root_exists k hp hb hx
  refine ⟨(t : ZMod (p^(k+1))), ?_, ?_, ?_, ?_⟩
  · rw [← eval_cast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using htf
  · simpa only [map_intCast] using (eq_cast_iff p t b).mpr ht
  · rw [eq_cast_iff]
    simpa using native_marked_root_depth (p:ℤ) t b i j (k+1) hp hi hij hpi hb ht htf
  · intro s hsf hs
    obtain ⟨u,rfl⟩ := ZMod.intCast_surjective s
    have hu : (p:ℤ) ∣ u-b := (eq_cast_iff p u b).mp (by simpa using hs)
    have huf : (p:ℤ)^(k+1) ∣ eval (goldenLucas (3^j)) u := by
      rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, eval_cast]
      exact hsf
    rw [eq_cast_iff, Int.natCast_pow]
    exact (marked_root_isometry (k+1) hp hb hx hx hu ht huf htf).mpr
      (by simp)


private def x (j : ℕ) : ℤ := goldenLucas (3^j)
private def B (j : ℕ) : ℤ := x j ^ 2 + 3

private theorem int_coprime {p : ℕ} (hp : p.Prime) {z : ℤ} (hz : ¬(p:ℤ) ∣ z) :
    IsCoprime (p:ℤ) z := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  change p.Coprime z.natAbs
  exact hp.coprime_iff_not_dvd.mpr (fun h => hz (Int.natCast_dvd.mpr h))

private theorem not_small_dvd {p k : ℕ} (hk : 0 < k) (h : k < p) : ¬(p:ℤ) ∣ (k:ℤ) :=
  fun hd => (not_le_of_gt h) (Nat.le_of_dvd hk (Int.natCast_dvd_natCast.mp hd))

private theorem dvd_sq {p z : ℤ} (h : p ∣ z) : p ∣ z^2 := by
  simpa [pow_two] using dvd_mul_of_dvd_left h z

private theorem step (j : ℕ) (hj : 1 ≤ j) : x (j+1) = x j * B j :=
  (golden_cubic_lucas_block j hj).2.2.2.2.2

private theorem base_unit {p i : ℕ} (hp3 : 3 < p) (hB : (p:ℤ) ∣ B i) :
    ¬(p:ℤ) ∣ x i := by
  intro hx
  have h := dvd_sub hB (dvd_sq hx)
  exact not_small_dvd (by decide : 0 < 3) hp3 (by simpa [B] using h)

private theorem expand_fib (i : ℕ) (hi : 1 ≤ i) :
    (Nat.fib (6*3^i) : ℤ) =
      ((Nat.fib (3^i) : ℤ) * (x i ^ 2 + 1)) * (x i * B i) := by
  rw [show 6*3^i = 2*3^(i+1) from by rw [pow_succ]; omega, golden_fib_two_mul_eq_fib_mul_lucas]
  change (Nat.fib (3^(i+1)) : ℤ) * x (i+1) = _
  rw [(D5.S1.Scale.golden_cubic_fibonacci_block i hi).2.2,step i hi]
  rfl

private theorem earlier_fib_unit {p i : ℕ} (hp3 : 3 < p) (hB : (p:ℤ) ∣ B i) :
    ¬(p:ℤ) ∣ (Nat.fib (3^i) : ℤ) := by
  intro hn
  have ho : Odd (3^i : ℕ) := (by decide : Odd (3:ℕ)).pow
  have hd := D5.S1.Scale.golden_lucas_discriminant (3^i)
  rw [ho.neg_one_pow] at hd
  change x i ^ 2 - 5 * (Nat.fib (3^i) : ℤ)^2 = 4 * -1 at hd
  have he : 5*(Nat.fib (3^i) : ℤ)^2 - B i = 1 := by unfold B; linarith
  have hh := dvd_sub (dvd_mul_of_dvd_right (dvd_sq hn) (5:ℤ)) hB
  rw [he] at hh
  exact not_small_dvd (k:=1) (by decide) (by omega) hh

private theorem earlier_shift_unit {p i : ℕ} (hp3 : 3 < p) (hB : (p:ℤ) ∣ B i) :
    ¬(p:ℤ) ∣ x i ^ 2 + 1 := by
  intro hh
  have h := dvd_sub hB hh
  have he : B i - (x i ^ 2+1) = 2 := by simp [B]
  rw [he] at h
  exact not_small_dvd (k:=2) (by decide) (by omega) h

/-- Without a split extension, the full block valuation equals the full
valuation at the native Fibonacci entry point. -/
private theorem fibonacci_entry_iff_earlier_block (p i a : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hi : 1 ≤ i) (hB : (p:ℤ) ∣ B i) :
    ((p:ℤ)^a ∣ (Nat.fib (6*3^i) : ℤ)) ↔ ((p:ℤ)^a ∣ B i) := by
  rw [expand_fib i hi, ←mul_assoc]
  have H : IsCoprime ((p:ℤ)^a) (((Nat.fib (3^i) : ℤ) * (x i ^ 2 + 1))*x i) :=
    (((int_coprime hp (earlier_fib_unit hp3 hB)).mul_right
      (int_coprime hp (earlier_shift_unit hp3 hB))).mul_right
      (int_coprime hp (base_unit hp3 hB))).pow_left
  exact ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h _⟩


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

/-- At any positive native precision, each marked branch exists uniquely
and equals its seed for exactly the full depth of the native Fibonacci
entry. This statement uses the genuine `ZMod` residue ring. -/
theorem fibonacci_marked_residue (p i j k : ℕ) (b : ℤ)
    (hp : p.Prime) (hp3 : 3 < p) (hi : 1 ≤ i) (hij : i < j)
    (hpi : (p:ℤ) ∣ goldenLucas (3^i)^2+3) (hb : b=0 ∨ b=3 ∨ b= -3) :
    ∃ r : ZMod (p^(k+1)),
      evalMod (p^(k+1)) (goldenLucas (3^j)) r = 0 ∧
      ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p) r = (b : ZMod p) ∧
      (r = (b : ZMod (p^(k+1))) ↔ (p:ℤ)^(k+1) ∣ (Nat.fib (6*3^i) : ℤ)) ∧
      ∀ s : ZMod (p^(k+1)), evalMod (p^(k+1)) (goldenLucas (3^j)) s = 0 →
        ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p) s = (b : ZMod p) →
        s = r := by
  have hF := fibonacci_entry_iff_earlier_block p i (k+1) hp hp3 hi hpi
  simpa only [B,x,hF] using
    native_marked_residue p i j k b (coprime_six p hp hp3) hi hij hpi hb


#print axioms fibonacci_marked_residue
end D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth

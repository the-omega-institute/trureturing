/- GID: D5/S3/Arith/Primes/GoldenCubicBlockExponentOne
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockExponentOne
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Modular cubing and order certificates certify genuine exponent-one Lucas-block factors. -/

import D5.S3.Arith.Primes.GoldenCubicBlockRanks
import D5.S3.Arith.Powerful.PowerfulNumber
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicBlockExponentOne

open D5.S1.Scale
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.GoldenCubicBlockRanks
open D5.S3.Arith.Powerful.PowerfulNumber

/-- A modular trace sequence starting at the first positive cubic depth. -/
def residue (m : ℤ) : ℕ → ℤ
  | 0 => 4 % m
  | n + 1 => let u := residue m n; (u * (u^2+3)) % m

private theorem modEq_reduce (m a : ℤ) : a ≡ a % m [ZMOD m] := by
  simp [Int.ModEq]

/-- The modular computation follows the repository's actual golden trace. -/
theorem residue_sound (m : ℤ) (n : ℕ) :
    goldenLucas (3^(n+1)) ≡ residue m n [ZMOD m] := by
  induction n with
  | zero =>
    have h : goldenLucas (3^(0+1)) = 4 := by decide
    rw [h]
    exact modEq_reduce m 4
  | succ n ih =>
    rw [(golden_cubic_lucas_block (n+1) (by omega)).2.2.2.2.2]
    exact (ih.mul ((ih.pow 2).add Int.ModEq.rfl)).trans (modEq_reduce _ _)

/-- A nonzero multiple of a prime, observed modulo its square, certifies
an exponent-one divisor of the actual Lucas block. -/
theorem block_exponent_one_of_residue (p : ℕ) (n : ℕ) (k : ℤ)
    (hk0 : 0 < k) (hkp : k < p)
    (hcheck : (residue ((p : ℤ)^2) n ^ 2 + 3) % (p : ℤ)^2 = k*p) :
    (p : ℤ) ∣ goldenLucas (3^(n+1))^2+3 ∧
      ¬ (p : ℤ)^2 ∣ goldenLucas (3^(n+1))^2+3 := by
  let P : ℤ := p
  have hp : 0 < P := by omega
  have h1 := ((residue_sound (P^2) n).pow 2).add (Int.ModEq.rfl (a := 3))
  have h2 : goldenLucas (3^(n+1))^2+3 ≡ k*P [ZMOD P^2] := by
    apply h1.trans
    rw [← hcheck]
    exact modEq_reduce _ _
  refine ⟨((h2.of_dvd (show P ∣ P^2 by exact dvd_pow_self _ (by decide))).dvd_iff).mpr
    (dvd_mul_left _ _), ?_⟩
  intro h
  have hz : P^2 ∣ k*P := h2.dvd_iff.mp h
  obtain ⟨d, hd⟩ := hz
  have he : (k-P*d)*P = 0 := by nlinarith only [hd]
  have hzero : k-P*d = 0 := (mul_eq_zero.mp he).resolve_right hp.ne'
  have hdiv : P ∣ k := ⟨d, by omega⟩
  have hh := Int.emod_eq_zero_of_dvd hdiv
  rw [Int.emod_eq_of_lt hk0.le hkp] at hh
  omega

private theorem mem_of_prime_dvd_prod (q : ℕ) (hq : q.Prime) (fs : List ℕ)
    (hfs : ∀ r ∈ fs, Nat.Prime r) (hd : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil => exact (hq.not_dvd_one (by simpa using hd)).elim
  | cons r rs ih =>
    rw [List.prod_cons, hq.dvd_mul] at hd
    rcases hd with hqr | hqrs
    · exact List.mem_cons.mpr (.inl (((Nat.prime_dvd_prime_iff_eq hq (hfs r (by simp))).mp hqr)))
    · exact List.mem_cons.mpr (.inr (ih (fun t ht => hfs t (List.mem_cons_of_mem _ ht)) hqrs))

private theorem zpow_residue (p a e : ℕ) :
    (a : ZMod p)^e = (Nat.powMod a e p : ZMod p) := by
  rw [Nat.powMod_def, ZMod.natCast_mod, Nat.cast_pow]

/-- The finite primality checker uses only a factored predecessor and
square-and-multiply modular powers. The factor list may have repeats. -/
theorem prime_of_order_certificate (p a : ℕ) (fs : List ℕ)
    (hprod : fs.prod = p-1)
    (hfs : ∀ q ∈ fs, Nat.Prime q)
    (hpow : Nat.powMod a (p-1) p = 1)
    (hsub : ∀ q ∈ fs, Nat.powMod a ((p-1)/q) p ≠ 1) :
    p.Prime := by
  have hpos : 1 < p := by
    have hn : p ≠ 0 := by
      rintro rfl
      simp [Nat.powMod_zero] at hpow hprod
      have hzero : 0 ∈ fs := hprod
      exact Nat.not_prime_zero (hfs 0 hzero)
    have hn1 : p ≠ 1 := by
      intro h
      subst p
      simp [Nat.powMod_zero] at hpow
    omega
  apply lucas_primality p (a : ZMod p)
  · rw [zpow_residue, hpow, Nat.cast_one]
  · intro q hq hqd
    have hm := mem_of_prime_dvd_prod q hq fs hfs (hprod ▸ hqd)
    rw [zpow_residue]
    intro h
    have hval := congrArg ZMod.val h
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt] at hval
    · apply hsub q hm
      simpa [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hpos] using hval
    · rw [Nat.powMod_def]
      exact Nat.mod_lt _ (by omega)

/-- A factor certificate is expressed by a prime index and a checked
modular quotient, not by evaluating the full Lucas number. -/
structure Certificate where
  level : ℕ
  prime : ℕ
  quotient : ℤ
  base : ℕ
  predecessorFactors : List ℕ

/-- The checker validates all numerical information needed for primality
and exact divisibility. No factorization of a Lucas block is required. -/
def Certificate.Valid (c : Certificate) : Prop :=
  c.predecessorFactors.prod = c.prime - 1 ∧
    (∀ q ∈ c.predecessorFactors, Nat.Prime q) ∧
    Nat.powMod c.base (c.prime - 1) c.prime = 1 ∧
    (∀ q ∈ c.predecessorFactors,
      Nat.powMod c.base ((c.prime - 1) / q) c.prime ≠ 1) ∧
    0 < c.quotient ∧ c.quotient < c.prime ∧
    (residue ((c.prime : ℤ)^2) c.level ^ 2 + 3) % (c.prime : ℤ)^2 =
      c.quotient * c.prime

/-- Soundness of the certificate for the repository's Lucas sequence. -/
theorem Certificate.sound (c : Certificate) (h : c.Valid) :
    Nat.Prime c.prime ∧
    (c.prime : ℤ) ∣ goldenLucas (3^(c.level+1))^2+3 ∧
    ¬ (c.prime : ℤ)^2 ∣ goldenLucas (3^(c.level+1))^2+3 := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := h
  exact ⟨prime_of_order_certificate _ _ _ h1 h2 h3 h4,
    block_exponent_one_of_residue _ _ _ h5 h6 h7⟩

/-- A valid certificate rules out a powerful block and simultaneously
determines the exact Fibonacci entry rank and entry valuation of its prime.
The rank conclusion uses the repository's native rank theorem, not the
Fibonacci value at an unrelated index. -/
theorem Certificate.block_and_rank (c : Certificate) (h : c.Valid) :
    ¬ Powerful (goldenLucas (3^(c.level+1))^2+3).natAbs ∧
    fibonacciRank c.prime = 2*3^(c.level+2) ∧
    padicValNat c.prime (Nat.fib (fibonacciRank c.prime)) = 1 := by
  obtain ⟨hp, hdiv, hnod⟩ := c.sound h
  let B := goldenLucas (3^(c.level+1))^2+3
  have hBn : 0 ≤ B := by dsimp [B]; positivity
  have hBcast : (B.natAbs : ℤ) = B := Int.natAbs_of_nonneg hBn
  have hBdiv : c.prime ∣ B.natAbs := by
    exact Int.natCast_dvd.mp (by simpa only [hBcast] using hdiv)
  have hh := cubic_block_b_prime_rank (c.level+1) c.prime (by omega) hp hdiv
  have hlo : 1 ≤ padicValInt c.prime B := by
    have hdiv' : (c.prime : ℤ)^1 ∣ B := by simpa [B] using hdiv
    have hb : B ≠ 0 := by dsimp [B]; positivity
    exact ((padicValInt_dvd_iff_of_ne_one hp.ne_one 1 B).mp hdiv').resolve_left hb
  have hhi : ¬ 2 ≤ padicValInt c.prime B := by
    intro H
    exact hnod ((padicValInt_dvd_iff_of_ne_one hp.ne_one 2 B).mpr (Or.inr H))
  have hv : padicValNat c.prime (Nat.fib (fibonacciRank c.prime)) = 1 := by
    rw [← hh.2.2]
    change padicValInt c.prime B = 1
    omega
  refine ⟨?_, hh.1, hv⟩
  intro H
  exact hnod (by simpa only [Nat.cast_pow, hBcast] using
    (Int.natCast_dvd.mpr (H.2 c.prime hp hBdiv) :
      (((c.prime)^2 : ℕ) : ℤ) ∣ (B.natAbs : ℤ)))

set_option maxRecDepth 4096 in
/-- One certificate per tested Lucas block. -/
def checkedCertificates : List Certificate :=
  [
    ⟨5, 1277209, 1099229, 7, List.replicate 3 2 ++ List.replicate 7 3 ++ [73]⟩,
    ⟨6, 52489, 35349, 7, List.replicate 3 2 ++ List.replicate 8 3⟩,
    ⟨9, 5314411, 2827242, 2, [2] ++ List.replicate 12 3 ++ [5]⟩,
    ⟨14, 4218578659, 3728294996, 2, [2] ++ List.replicate 16 3 ++ List.replicate 2 7⟩,
    ⟨15, 6168509025859, 1173811268507, 2, [2] ++ List.replicate 18 3 ++ [19] ++ [419]⟩,
    ⟨16, 3874204891, 378126959, 2, [2] ++ List.replicate 18 3 ++ [5]⟩,
    ⟨22, 10438595668337761, 4992103250652003, 13, List.replicate 5 2 ++ List.replicate 25 3 ++ [5] ++ [7] ++ [11]⟩,
    ⟨25, 21458431322753419, 3649563001603057, 3, [2] ++ List.replicate 28 3 ++ [7] ++ [67]⟩,
    ⟨26, 411782264189299, 57385319878658, 3, [2] ++ List.replicate 30 3⟩,
    ⟨28, 8235645283785961, 7162072334163849, 13, List.replicate 3 2 ++ List.replicate 30 3 ++ [5]⟩,
    ⟨35, 11707381553165931439, 11577599392359611404, 3, [2] ++ List.replicate 37 3 ++ [13]⟩,
    ⟨36, 16210220612075905069, 15509995271268856400, 10, List.replicate 2 2 ++ List.replicate 39 3⟩,
    ⟨47, 11964966461530876479504151, 319726430097439153432670, 3, [2] ++ List.replicate 49 3 ++ List.replicate 2 5⟩,
    ⟨52, 116299474006080119380780339, 35936208001633579556596118, 3, [2] ++ List.replicate 54 3⟩,
    ⟨58, 1695646331008648140571777328041, 365402973643130941583530350929, 11, List.replicate 3 2 ++ List.replicate 60 3 ++ [5]⟩
  ]

set_option maxRecDepth 4096 in
/-- The table entries independently pass the checked Lucas and order tests. -/
theorem checkedCertificates_valid (c : Certificate) (hc : c ∈ checkedCertificates) : c.Valid := by
  simp only [checkedCertificates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold Certificate.Valid
    refine ⟨by decide, ?_, by decide, ?_, by decide, by decide, by decide⟩
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> decide

/-- Signed residues avoid truncated natural subtraction in the double formula.
The fuel bounds the bit length, not the Fibonacci index. -/
def fibPairMod (m : ℤ) : ℕ → ℕ → ℤ × ℤ
  | 0, _ => (0, 1 % m)
  | fuel+1, n =>
    let (a,b) := fibPairMod m fuel (n/2)
    let c := a*(2*b-a) % m
    let d := (a*a+b*b) % m
    if n%2=0 then (c,d) else (d,(c+d)%m)

private theorem even_identity (t : ℕ) :
    (Nat.fib (2*t) : ℤ) = (Nat.fib t : ℤ)*(2*Nat.fib (t+1)-Nat.fib t) := by
  rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub (by
    have := @Nat.fib_le_fib_succ t
    omega), Nat.cast_mul, Nat.cast_ofNat]

private theorem odd_identity (t : ℕ) :
    (Nat.fib (2*t+1) : ℤ) = (Nat.fib t : ℤ)*(Nat.fib t : ℤ)+
      (Nat.fib (t+1) : ℤ)*(Nat.fib (t+1) : ℤ) := by
  rw [Nat.fib_two_mul_add_one]
  push_cast
  ring

theorem fibPairMod_sound (m : ℤ) (fuel n : ℕ) (hn : n < 2^fuel) :
    (fibPairMod m fuel n).1 ≡ (Nat.fib n : ℤ) [ZMOD m] ∧
    (fibPairMod m fuel n).2 ≡ (Nat.fib (n+1) : ℤ) [ZMOD m] := by
  induction fuel generalizing n with
  | zero =>
    have hz : n = 0 := by simpa using hn
    subst n
    exact ⟨by simp [fibPairMod], by
      simp [fibPairMod]
      exact Int.mod_modEq _ _⟩
  | succ f ih =>
    rw [pow_succ] at hn
    have hhalf : n/2 < 2^f := by omega
    obtain ⟨ha,hb⟩ := ih (n/2) hhalf
    generalize hz : fibPairMod m f (n/2) = ab at *
    rcases ab with ⟨a,b⟩
    have hc : a*(2*b-a) % m ≡ (Nat.fib (2*(n/2)) : ℤ) [ZMOD m] := by
      rw [even_identity]
      exact (Int.mod_modEq _ _).trans (ha.mul ((Int.ModEq.mul_left 2 hb).sub ha))
    have hd : (a*a+b*b) % m ≡ (Nat.fib (2*(n/2)+1) : ℤ) [ZMOD m] := by
      rw [odd_identity]
      exact (Int.mod_modEq _ _).trans ((ha.mul ha).add (hb.mul hb))
    change (fibPairMod m (f+1) n).1 ≡ _ [ZMOD m] ∧ (fibPairMod m (f+1) n).2 ≡ _ [ZMOD m]
    rw [fibPairMod, hz]
    by_cases he : n%2=0
    · simp only [he, ite_true]
      have hindex : 2*(n/2)=n := by omega
      simpa only [hindex] using And.intro hc hd
    · simp only [he, ite_false]
      have hindex : 2*(n/2)+1=n := by omega
      constructor
      · simpa only [hindex] using hd
      · have hh := (Int.mod_modEq (a*(2*b-a) % m + (a*a+b*b) % m) m).trans (hc.add hd)
        rw [← Nat.cast_add, ← Nat.fib_add_two] at hh
        have hnext : 2*(n/2)+2=n+1 := by omega
        simpa only [hnext] using hh

/-- A closed residue computation gives the exact residue in the
original Fibonacci sequence. The theorem does not evaluate that sequence. -/
theorem fib_residue_of_check (p n q fuel : ℕ) (hn : n < 2^fuel)
    (hcheck : (fibPairMod (p^2 : ℕ) fuel n).1 = (q : ℤ))
    (hq : q < p^2) :
    Nat.fib n % p^2 = q := by
  have hh := (fibPairMod_sound ((p^2 : ℕ) : ℤ) fuel n hn).1
  rw [hcheck, Int.natCast_modEq_iff] at hh
  change q % p^2 = Nat.fib n % p^2 at hh
  rwa [Nat.mod_eq_of_lt hq, eq_comm] at hh

/-- Exact depth one at the original Fibonacci test index (for split primes). -/
theorem fib_depth_one_of_residue (p q : ℕ)
    (hq0 : 0 < q) (hqp : q < p)
    (h : Nat.fib (p-1) % p^2 = p*q) :
    p ∣ Nat.fib (p-1) ∧ ¬ p^2 ∣ Nat.fib (p-1) := by
  have hp2 : p ∣ p^2 := dvd_pow_self _ (by decide)
  constructor
  · rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd _ hp2, h]
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_right _ _)
  · rw [Nat.dvd_iff_mod_eq_zero, h]
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.zero_lt_of_lt hqp) hq0)

/-- The fifteen certified primes give non-powerful blocks, exact Fibonacci
entry ranks, and exponent one at their respective first zero. -/
theorem checked_block_and_rank (c : Certificate) (hc : c ∈ checkedCertificates) :
    ¬ Powerful (goldenLucas (3^(c.level+1))^2+3).natAbs ∧
    fibonacciRank c.prime = 2*3^(c.level+2) ∧
    padicValNat c.prime (Nat.fib (fibonacciRank c.prime)) = 1 :=
  c.block_and_rank (checkedCertificates_valid c hc)

set_option maxRecDepth 4096 in
/-- Independently of the Lucas recurrence, direct fast doubling computes
a nonzero multiple of p modulo p squared at F_(p-1) for every listed
prime, which is split in the golden quadratic field. -/
theorem checked_fib_depth_one (c : Certificate) (hc : c ∈ checkedCertificates) :
    (c.prime % 5 = 1 ∨ c.prime % 5 = 4) ∧
    c.prime ∣ Nat.fib (c.prime - 1) ∧
    ¬ c.prime^2 ∣ Nat.fib (c.prime - 1) := by
  simp only [checkedCertificates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide, ?_⟩
  · apply fib_depth_one_of_residue _ 370140 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 9179 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 327614 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 3320225186 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 946131694180 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 136667374 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 8468236043518575 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 1128634195704406 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 355187649747627 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 1098271795568800 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 60 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 11668859670806791068 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 112 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 7766181804890571490 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 112 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 9683365435205014450059340 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 112 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 13240592223204804733431947 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 112 (by decide) (by decide) (by decide)
  · apply fib_depth_one_of_residue _ 619091887780393287073556119154 (by decide) (by decide)
    exact fib_residue_of_check _ _ _ 112 (by decide) (by decide) (by decide)

/-- The classical split-prime Wall–Sun–Sun test fails on each certified p.
The split condition here is the actual Legendre symbol, and the nonzero
residue is the independent calculation at the classical test index. -/
theorem checked_wss_test (c : Certificate) (hc : c ∈ checkedCertificates) :
    ∃ hp : c.prime.Prime, @legendreSym c.prime ⟨hp⟩ 5 = 1 ∧
    c.prime ∣ Nat.fib (c.prime-1) ∧ ¬ c.prime^2 ∣ Nat.fib (c.prime-1) := by
  obtain ⟨hp, hdvd, _⟩ := c.sound (checkedCertificates_valid c hc)
  exact ⟨hp, (cubic_block_b_prime_rank (c.level+1) c.prime (by omega) hp hdvd).2.1,
    (checked_fib_depth_one c hc).2⟩

end D5.S3.Arith.Primes.GoldenCubicBlockExponentOne

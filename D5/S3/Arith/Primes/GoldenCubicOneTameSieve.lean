/- GID: D5/S3/Arith/Primes/GoldenCubicOneTameSieve
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicOneTameSieve
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Five finite readouts give a common-orientation noncube sieve at every positive native Lucas level. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-! # Five-probe sieve for a compatible local cubic character

This is an operational finite orbit certificate followed by a character
obstruction. It does not identify any global reciprocity character or
assert existence of a candidate conductor.
-/

namespace D5.S3.Arith.Primes.GoldenCubicOneTameSieve

open D5.S0.Carrier D5.S1.Scale

/-- Canonical residue pair for a+bδ with δ²=-3; the split branch uses b=0. -/
private abbrev RPair := Int × Int

private def reducePair (q : Nat) (z : RPair) : RPair := (z.1 % q, z.2 % q)

private def pairMul (q : Nat) (a b : RPair) : RPair :=
  reducePair q (a.1*b.1-3*a.2*b.2, a.1*b.2+a.2*b.1)

/-- Binary powering in the same canonical residue pair arithmetic. -/
private def pairPow (q : Nat) (z : RPair) (e : Nat) : RPair :=
  if he : e = 0 then (1,0) else
    let y := pairPow q (pairMul q z z) (e/2)
    if e % 2 = 0 then y else pairMul q z y
termination_by e
decreasing_by omega

private def firstDelta (q : Nat) : Option Nat :=
  (List.range q).find? (fun d => (d*d+3)%q == 0)

private def rootLabel (q : Nat) (w z : RPair) : Option Nat :=
  if z = (1,0) then some 0 else
    if z = w then some 1 else if z = pairMul q w w then some 2 else none

private def wild (q : Nat) : Nat :=
  let k := if q % 3 = 1 then q % 9 else 9-q%9
  if k=1 then 0 else if k=4 then 2 else 1

/-- Operational raw cubic probe: exact finite Cardano residue powers,
with the degree-two orientation already converted to a rational exponent. -/
private def rawProbe (q : Nat) (x : Int) : Option Nat :=
  let x := x % q
  let B := (x*x+3) % q
  let h : Int := (q+1)/2
  if B=0 ∨ q<5 then none else
    if q%3=1 then
      (firstDelta q).bind fun d =>
        let b := reducePair q (B*(-x+d),0)
        let w := reducePair q (((d:Int)-1)*h,0)
        rootLabel q w (pairPow q b ((q-1)/3))
    else
      let b := reducePair q (-B*x,B)
      let w := reducePair q (-h,h)
      (rootLabel q w (pairPow q b ((q*q-1)/3))).map fun c => (2*c)%3

private def correctedProbe (q : Nat) (x : Int) : Option Nat :=
  (rawProbe q x).map fun c => (c+wild q)%3

private def clock (q : Nat) : Nat → Int
  | 0 => 4 % q
  | j+1 => let x := clock q j; (x*(x*x+3))%q

/-- Literal native positive level computed in the residue clock. -/
private theorem clock_eq_native (q j : ℕ) : goldenLucas (3^(j+1)) % q = clock q j := by
  induction j with
  | zero =>
    have h : goldenLucas (3^(0+1)) = 4 := by
      norm_num [goldenLucas, trace, phi, pow_succ]
    rw [clock,h]
  | succ j ih =>
    rw [(golden_cubic_lucas_block (j+1) (by omega)).2.2.2.2.2, clock]
    rw [← ih]
    have hm (x m : ℤ) :
        (x * (x^2+3)) % m = ((x%m)*((x%m)*(x%m)+3))%m := by
      rw [show x*(x^2+3) = x*x*x+3*x by ring]
      rw [show (x%m)*((x%m)*(x%m)+3) = (x%m)*(x%m)*(x%m)+3*(x%m) by ring]
      rw [Int.add_emod (x*x*x) (3*x) m,
          Int.mul_emod (x*x) x m, Int.mul_emod x x m, Int.mul_emod 3 x m]
      rw [Int.add_emod ((x%m)*(x%m)*(x%m)) (3*(x%m)) m,
          Int.mul_emod ((x%m)*(x%m)) (x%m) m,
          Int.mul_emod 3 (x%m) m, Int.emod_emod]
    rw [hm]

private theorem corrected_mod (q : ℕ) (x : ℤ) :
    correctedProbe q x = correctedProbe q (x % q) := by
  simp [correctedProbe, rawProbe]

private def q (i : Fin 5) : Nat := [7,11,17,23,47][i.val]?.getD 0

private def orbit (i : Fin 5) : List Int :=
  let rows : List (List Int) := [[4,6,3,1],[4,10,7,1],[4,8,9],[4,7,19,16],[4,29,36,46,43,18,11,1]]
  rows[i.val]?.getD []

private def step (p : Nat) (x : Int) : Int := (x*(x*x+3)) % p

private def allowed (i : Fin 5) (k : Nat) : Prop :=
  if i=3 then k=2 else if i=2 then k=1∨k=2 else k=0∨k=2

private instance (i : Fin 5) (k : Nat) : Decidable (allowed i k) := by unfold allowed; infer_instance

private def computedAllowed (i : Fin 5) (x : Int) : Bool :=
  match correctedProbe (q i) x with
  | none => false
  | some k => decide (allowed i k)

private theorem init (i : Fin 5) : clock (q i) 0 ∈ orbit i := by
  fin_cases i <;> decide +kernel

private theorem closed (i : Fin 5) :
    (orbit i).all (fun x => decide (step (q i) x ∈ orbit i)) = true := by
  fin_cases i <;> decide +kernel

private theorem allowedOnOrbit (i : Fin 5) : (orbit i).all (computedAllowed i) = true := by
  fin_cases i <;> decide +kernel

private theorem clock_mem (i : Fin 5) (n : Nat) : clock (q i) n ∈ orbit i := by
  induction n with
  | zero => exact init i
  | succ n ih =>
    exact of_decide_eq_true ((List.all_eq_true.mp (closed i)) _ ih)

/-- The literal Lucas sequence at every positive level obeys the five small
corrected-label restrictions; there is no global character interpretation here. -/
private theorem native_fixed_corrected (i : Fin 5) (n : ℕ) :
    ∃ k, correctedProbe (q i) (goldenLucas (3^(n+1))) = some k ∧ allowed i k := by
  rw [corrected_mod,clock_eq_native]
  have h := (List.all_eq_true.mp (allowedOnOrbit i)) _ (clock_mem i n)
  unfold computedAllowed at h
  split at h
  · contradiction
  · rename_i k hk
    exact ⟨k,hk,of_decide_eq_true h⟩

private theorem native_corrected_twenty_three (n : ℕ) :
    correctedProbe 23 (goldenLucas (3^(n+1))) = some 2 := by
  obtain ⟨k,h,ha⟩ := native_fixed_corrected 3 n
  have hk : k=2 := by simpa [allowed] using ha
  subst k
  exact h

/-- The value of the local test as an element of F₃; the all-level orbit
certificate rules out the default at each of the five fixed probes. -/
def nativeDigit (i : Fin 5) (n : ℕ) : ZMod 3 :=
  ((correctedProbe (q i) (goldenLucas (3^(n+1)))).getD 0 : ℕ)

private theorem prime_probe (i : Fin 5) : (q i).Prime := by
  fin_cases i <;> decide +kernel

private theorem not_same_progression (i : Fin 5) : q i % 18 ≠ 1 := by
  fin_cases i <;> decide +kernel

private theorem primeProbeNotDvd (P : ℕ) (hP : P.Prime) (h18 : P%18=1) (i : Fin 5) :
    ¬ q i ∣ P := fun hd => not_same_progression i
      (((Nat.prime_dvd_prime_iff_eq (prime_probe i) hP).mp hd) ▸ h18)

private def unitAt (P : ℕ) (hP : P.Prime) (h18 : P%18=1) (i : Fin 5) : (ZMod P)ˣ :=
  ZMod.unitOfCoprime (q i) ((prime_probe i).coprime_iff_not_dvd.mpr (primeProbeNotDvd P hP h18 i))

private theorem coe_unitAt (P : ℕ) (hP : P.Prime) (h18 : P%18=1) (i : Fin 5) :
    (unitAt P hP h18 i : ZMod P) = (q i : ZMod P) := rfl

private def charVal {P : ℕ} (ψ : (ZMod P)ˣ →* Multiplicative (ZMod 3)) (a : (ZMod P)ˣ) :=
  (ψ a).toAdd

private theorem value_mul {P : ℕ} (ψ : (ZMod P)ˣ →* Multiplicative (ZMod 3))
    (a b : (ZMod P)ˣ) : charVal ψ (a*b)=charVal ψ a+charVal ψ b := by
  simp [charVal,toAdd_mul]

private theorem noncube_of_nonzero {P : ℕ} (ψ : (ZMod P)ˣ →* Multiplicative (ZMod 3))
    (a : (ZMod P)ˣ) (ha : charVal ψ a≠0) : ¬∃ y : ZMod P, y^3=(a:ZMod P) := by
  rintro ⟨y,hy⟩
  have he : IsUnit (y^3) := hy ▸ a.isUnit
  obtain ⟨u,hu⟩ := (isUnit_pow_iff (by decide : (3:ℕ)≠0)).mp he
  have h : u^3=a := Units.ext (by simpa [← hu] using hy)
  apply ha
  rw [← h,charVal,map_pow,toAdd_pow,nsmul_eq_mul]
  change (3:ZMod 3)*(ψ u).toAdd=0
  rw [show (3:ZMod 3)=0 by decide,zero_mul]

private theorem digit_allowed (i : Fin 5) (n : ℕ) :
    ∃ k : ℕ, allowed i k ∧ nativeDigit i n=(k:ZMod 3) := by
  obtain ⟨k,h,hk⟩ := native_fixed_corrected i n
  exact ⟨k,hk,by rw [nativeDigit,h]; rfl⟩

private theorem digit_twenty_three (n : ℕ) : nativeDigit 3 n=2 := by
  unfold nativeDigit
  change ((correctedProbe 23 (goldenLucas (3^(n+1)))).getD 0 : ℕ) = (2:ZMod 3)
  rw [native_corrected_twenty_three]
  rfl

private theorem seventeen_clock_succ (n : ℕ) :
    clock 17 (n+1) = if n%2=0 then 8 else 9 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    by_cases hn : n%2=0
    · rw [ite_eq_left hn] at ih
      rw [ite_eq_right (by omega), clock, ih]
      decide +kernel
    · rw [ite_eq_right hn] at ih
      rw [ite_eq_left (by omega), clock, ih]
      decide +kernel

private theorem seventeen_exact (n : ℕ) :
    nativeDigit 2 n = if n%2=0 then 1 else 2 := by
  unfold nativeDigit
  rw [corrected_mod, clock_eq_native]
  cases n with
  | zero => decide +kernel
  | succ n =>
    change (((correctedProbe 17 (clock 17 (n+1))).getD 0 : ℕ) : ZMod 3) = _
    rw [seventeen_clock_succ]
    by_cases hn : n%2=0
    · rw [ite_eq_left hn, ite_eq_right (by omega)]
      decide +kernel
    · rw [ite_eq_right hn, ite_eq_left (by omega)]
      decide +kernel

private theorem digit_even (i : Fin 5) (n : ℕ) (hi2 : i≠2) (hi3 : i≠3) :
    nativeDigit i n=0 ∨ nativeDigit i n=2 := by
  obtain ⟨k,h,hk⟩ := digit_allowed i n
  have he : k=0∨k=2 := by simpa [allowed,hi2,hi3] using h
  rcases he with rfl|rfl
  · exact Or.inl hk
  · exact Or.inr hk

private theorem nonzero_slopes : ∀ ε : ZMod 3, ε≠0 →
    ε*1≠0 ∧ ε*2≠0 ∧ ε*2+ε*0≠0 ∧ ε*2+ε*2≠0 := by decide +kernel

/-- A single candidate prime, character and orientation explain all five
operational readouts at the selected native level. The premise is explicit;
no relation to a global conductor is part of the definition. -/
def Compatible (P n : ℕ) : Prop :=
  ∃ (hP : P.Prime) (h18 : P%18=1)
    (ψ : (ZMod P)ˣ →* Multiplicative (ZMod 3)) (ε : ZMod 3), ε≠0 ∧
      ∀ i : Fin 5, charVal ψ (unitAt P hP h18 i)=ε*nativeDigit i n

/-- The ordinary untwisted finite-field cube obstructions delivered by the sieve. -/
def FiveNoncubes (P : ℕ) : Prop :=
  (¬∃ y : ZMod P, y^3=17) ∧
    (¬∃ y : ZMod P, y^3=23) ∧
    (¬∃ y : ZMod P, y^3=161) ∧
    (¬∃ y : ZMod P, y^3=253) ∧
    (¬∃ y : ZMod P, y^3=1081)

/-- A single compatible local cubic character, calibrated globally by the
same nonzero orientation, excludes the five concrete cube residues.
Compatibility is explicit: there is no assumption here of a proved global
conductor identification. -/
private theorem native_five_noncubes_of_one_char (P n : ℕ) (hP : P.Prime) (h18 : P%18=1)
    (ψ : (ZMod P)ˣ →* Multiplicative (ZMod 3)) (ε : ZMod 3) (hε : ε≠0)
    (compat : ∀ i : Fin 5, charVal ψ (unitAt P hP h18 i)=ε*nativeDigit i n) :
    FiveNoncubes P := by
  let u := unitAt P hP h18
  have H17 : charVal ψ (u 2) ≠ 0 := by
    rw [compat, seventeen_exact]
    split
    · exact (nonzero_slopes ε hε).1
    · exact (nonzero_slopes ε hε).2.1
  have H23 : charVal ψ (u 3) ≠ 0 := by
    rw [compat,digit_twenty_three]
    exact (nonzero_slopes ε hε).2.1
  have Hmul (i : Fin 5) (hi2 : i≠2) (hi3 : i≠3) :
      charVal ψ (u 3 * u i) ≠ 0 := by
    rw [value_mul,compat,compat,digit_twenty_three]
    rcases digit_even i n hi2 hi3 with h|h
    · rw [h]; exact (nonzero_slopes ε hε).2.2.1
    · rw [h]; exact (nonzero_slopes ε hε).2.2.2
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [show (u 2 : ZMod P)=17 by rfl] using noncube_of_nonzero ψ _ H17
  · simpa only [show (u 3 : ZMod P)=23 by rfl] using noncube_of_nonzero ψ _ H23
  · simpa only [show ((u 3*u 0 : (ZMod P)ˣ) : ZMod P)=161 by
      rw [Units.val_mul]; change (23:ZMod P)*7=161; norm_num] using
      noncube_of_nonzero ψ _ (Hmul 0 (by decide) (by decide))
  · simpa only [show ((u 3*u 1 : (ZMod P)ˣ) : ZMod P)=253 by
      rw [Units.val_mul]; change (23:ZMod P)*11=253; norm_num] using
      noncube_of_nonzero ψ _ (Hmul 1 (by decide) (by decide))
  · simpa only [show ((u 3*u 4 : (ZMod P)ˣ) : ZMod P)=1081 by
      rw [Units.val_mul]; change (23:ZMod P)*47=1081; norm_num] using
      noncube_of_nonzero ψ _ (Hmul 4 (by decide) (by decide))

/-- The marked q=17 readout alternates exactly with the level. If one local
cubic character agrees at all five probes with one orientation, all five
listed values are noncubes at its candidate prime. -/
theorem marked_one_tame_sieve (n : ℕ) :
    (nativeDigit 2 n = if n%2=0 then 1 else 2) ∧
    ∀ P : ℕ, Compatible P n → FiveNoncubes P := by
  refine ⟨seventeen_exact n, ?_⟩
  rintro P ⟨hp,h18,ψ,ε,hε,compat⟩
  exact native_five_noncubes_of_one_char P n hp h18 ψ ε hε compat

end D5.S3.Arith.Primes.GoldenCubicOneTameSieve

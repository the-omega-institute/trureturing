/- GID: D5/S3/Arith/Primes/GoldenCubicNativePhaseRecovery
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicNativePhaseRecovery
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact decoder and sharp probe complexity for all positive native Lucas levels. -/

import D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout
import Mathlib.Data.Finset.Card
import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-! # Four-probe native mod-24 decoder

Operational simultaneous orbit certificate. No global character identification.
-/

namespace D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery

open D5.S0.Carrier D5.S1.Scale

open D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout (block numer probePower)

private def wild (q : Nat) : Nat :=
  let k := if q % 3 = 1 then q % 9 else 9-q%9
  if k=1 then 0 else if k=4 then 2 else 1

/-- Base-field scalar cubic readout using the protected numerator and
probe power; no fresh quadratic Cardano arithmetic. -/
private def correctedProbe (q : Nat) (u : ZMod q) : Option Nat :=
  let B := block u
  let m := probePower q
  let N := numer u m
  let D := B^m
  if B = 0 ∨ q<5 then none else
    let a : Option Nat := if N = 0 then some 0 else
      if N=D then some 1 else if N = -D then some 2 else none
    a.map fun t => ((if q%3=1 then t else 2*t) + wild q)%3

private def clock (q : Nat) : Nat → ZMod q
  | 0 => 4
  | n+1 => let x := clock q n; x*(x^2+3)

/-- The field clock is the image of the actual integer Lucas recurrence. -/
private theorem clock_eq_native (q j : ℕ) :
    (goldenLucas (3^(j+1)) : ZMod q) = clock q j := by
  induction j with
  | zero =>
    have h : goldenLucas (3^(0+1)) = 4 := by
      norm_num [goldenLucas, trace, phi, pow_succ]
    rw [h]
    norm_num [clock]
  | succ j ih =>
    rw [(golden_cubic_lucas_block (j+1) (by omega)).2.2.2.2.2, clock]
    push_cast
    rw [ih]

abbrev Readout := Nat × Nat × Nat × Nat

private def readout (x5 : ZMod 5) (x7 : ZMod 7) (x47 : ZMod 47) (x83 : ZMod 83) : Option Readout := do
  let a ← correctedProbe 5 x5
  let b ← correctedProbe 7 x7
  let c ← correctedProbe 47 x47
  let d ← correctedProbe 83 x83
  pure (a,b,c,d)

/-- Literal all-level native readout, returning none for any failed local test. -/
def nativeWord (j : Nat) : Option Readout :=
  let x := goldenLucas (3^j)
  readout x x x x

private def clockWord (k : Nat) : Option Readout :=
  readout (clock 5 k) (clock 7 k) (clock 47 k) (clock 83 k)

private theorem word_eq_clock (k : Nat) :
    nativeWord (k+1) = clockWord k := by
  dsimp only [nativeWord, readout, clockWord]
  simp only [clock_eq_native]

/-- Any eventual periodic point propagates and permits exact reduction of all
later iterates, with the initial point left explicit. -/
private theorem exact_period (q s t : Nat) (h : clock q (s+t) = clock q s) (k : Nat) :
    clock q (s+k+t) = clock q (s+k) := by
  induction k with
  | zero => simpa using h
  | succ k hk =>
    rw [show s+(k+1)+t = (s+k+t)+1 by omega,
      show s+(k+1) = (s+k)+1 by omega, clock, clock, hk]

private theorem at_residue (q s t : Nat) (ht : 0<t)
    (h : clock q (s+t) = clock q s) (k : Nat) :
    clock q (s+k) = clock q (s+k%t) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k<t
    · rw [Nat.mod_eq_of_lt hk]
    · have hk' : k-t < k := by omega
      have he : k-t+t = k := by omega
      calc
        clock q (s+k) = clock q (s+(k-t)+t) := by rw [Nat.add_assoc,he]
        _ = clock q (s+(k-t)) := exact_period q s t h _
        _ = clock q (s+(k-t)%t) := ih _ hk'
        _ = clock q (s+k%t) := by
          rw [← Nat.add_mod_right, he]

private theorem cycle5 : clock 5 (2+24) = clock 5 2 := by decide +kernel
private theorem cycle7 : clock 7 (2+24) = clock 7 2 := by decide +kernel
private theorem cycle47 : clock 47 (2+24) = clock 47 2 := by decide +kernel
private theorem cycle83 : clock 83 (2+24) = clock 83 2 := by decide +kernel

/-- The lookup entries are not floating data or a choice of residue model:
they are computed from the literal Cardano residue evaluator. -/
def reference (r : Fin 24) : Option Readout := clockWord (2+r.val)

/-- A decidable operational decoder. The range includes all 24 possible
recurrent phases and returns the genuine native index modulo 24. -/
def decode (word : Option Readout) : Option Nat :=
  ((List.finRange 24).find? (fun r => decide (reference r = word))).map
    (fun r => (r.val+3)%24)

private theorem cert : ∀ r : Fin 24, (reference r).isSome = true ∧
    decode (reference r) = some ((r.val+3)%24) := by
  decide +kernel

private theorem native_ref (r : Nat) :
    nativeWord (3+r) = reference ⟨r%24, Nat.mod_lt _ (by decide)⟩ := by
  rw [show 3+r = (2+r)+1 by omega, word_eq_clock]
  unfold reference clockWord
  rw [at_residue 5 2 24 (by decide) cycle5,
      at_residue 7 2 24 (by decide) cycle7,
      at_residue 47 2 24 (by decide) cycle47,
      at_residue 83 2 24 (by decide) cycle83]

/-- For every native Lucas level j≥3, all four corrected cubic probes are
good, and their ordered values recover the level modulo 24 with no oracle. -/
private theorem native_mod24_decoder (j : Nat) (hj : 3 ≤ j) :
    (nativeWord j).isSome = true ∧ decode (nativeWord j) = some (j%24) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [native_ref]
  have hc := cert ⟨r%24, Nat.mod_lt _ (by decide)⟩
  exact hc.imp_right (fun h => by simpa [Nat.add_comm r 3, Nat.mod_add_mod] using h)

/-- Two recurrent levels agree on all four normalized readouts exactly when
their native indices agree modulo 24. -/
private theorem native_mod24_iff (i j : Nat) (hi : 3 ≤ i) (hj : 3 ≤ j) :
    nativeWord i = nativeWord j ↔ i%24 = j%24 := by
  constructor
  · intro h
    exact Option.some.inj ((native_mod24_decoder i hi).2.symm.trans
      ((congrArg decode h).trans (native_mod24_decoder j hj).2))
  · obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hi
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hj
    intro h
    have hh : s%24 = t%24 := by omega
    rw [native_ref,native_ref]
    congr 1
    exact Fin.ext hh

/-- The parity readout at five holds already at every positive level. -/
private theorem native_five_parity (j : Nat) (hj : 1 ≤ j) :
    correctedProbe 5 (goldenLucas (3^j)) = some (j%2) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1+r = r+1 by omega, clock_eq_native]
  have hc : clock 5 (0+2) = clock 5 0 := by decide +kernel
  have h := at_residue 5 0 2 (by decide) hc r
  rw [Nat.zero_add, Nat.zero_add] at h
  rw [h]
  have hr : r%2=0 ∨ r%2=1 := by omega
  rcases hr with h | h
  · rw [h,show (r+1)%2=1 by omega]
    decide +kernel
  · rw [h,show (r+1)%2=0 by omega]
    decide +kernel


/-- A fifth actual probe at 53 separates the exceptional first native level
from the entire recurrent family. -/
def nativeWord5 (j : Nat) : Option (Readout × Nat) := do
  let w ← nativeWord j
  let d ← correctedProbe 53 (goldenLucas (3^j))
  pure (w,d)

private def clockWord5 (k : Nat) : Option (Readout × Nat) := do
  let w ← clockWord k
  let d ← correctedProbe 53 (clock 53 k)
  pure (w,d)

private theorem word5_eq_clock (k : Nat) :
    nativeWord5 (k+1) = clockWord5 k := by
  unfold nativeWord5 clockWord5
  rw [word_eq_clock, clock_eq_native]

def reference5 (r : Fin 24) : Option (Readout × Nat) := clockWord5 (2+r.val)

private def first5 : Option (Readout × Nat) := clockWord5 0

/-- Return 24 for the exceptional first level, 0 through 23 for a recovered
modular phase, and none for every other (incompatible) five-reading word. -/
def decode5 (word : Option (Readout × Nat)) : Option Nat :=
  if word = first5 then some 24 else
    ((List.finRange 24).find? (fun r => decide (reference5 r = word))).map
      (fun r => (r.val+3)%24)

private theorem cycle53 : clock 53 (2+24) = clock 53 2 := by decide +kernel

private theorem cert5 : ∀ r : Fin 24, (reference5 r).isSome = true ∧
    decode5 (reference5 r) = some ((r.val+3)%24) := by
  decide +kernel

private theorem native_ref5 (r : Nat) :
    nativeWord5 (3+r) = reference5 ⟨r%24, Nat.mod_lt _ (by decide)⟩ := by
  rw [show 3+r = (2+r)+1 by omega, word5_eq_clock]
  unfold reference5 clockWord5 clockWord
  rw [at_residue 5 2 24 (by decide) cycle5,
      at_residue 7 2 24 (by decide) cycle7,
      at_residue 47 2 24 (by decide) cycle47,
      at_residue 83 2 24 (by decide) cycle83,
      at_residue 53 2 24 (by decide) cycle53]

/-- Every positive level is detected by the five probes. Level 1 is special;
level 2 already shares the recurrent phase indexed by 2. -/
private theorem native_five_probe_decoder (j : Nat) (hj : 1 ≤ j) :
    (nativeWord5 j).isSome = true ∧
      decode5 (nativeWord5 j) = some (if j=1 then 24 else j%24) := by
  by_cases h : 3 ≤ j
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
    rw [native_ref5,ite_eq_right (by omega)]
    have hc := cert5 ⟨r%24, Nat.mod_lt _ (by decide)⟩
    exact hc.imp_right (fun h => by simpa [Nat.add_comm r 3, Nat.mod_add_mod] using h)
  · have h' : j=1 ∨ j=2 := by omega
    rcases h' with rfl | rfl
    · rw [show (1:Nat)=0+1 by rfl,word5_eq_clock]
      decide +kernel
    · rw [show (2:Nat)=1+1 by rfl,word5_eq_clock]
      decide +kernel

/-- The additional probe is genuinely used: the four probes conflate level 1
and recurrent phase 1 (at level 25), whereas the fifth separates them. -/
private theorem first_exception_needs_extra_probe :
    nativeWord 1 = nativeWord 25 ∧
    nativeWord5 1 ≠ nativeWord5 25 := by
  rw [show (1:Nat)=0+1 by rfl, word_eq_clock, word5_eq_clock,
      show (25:Nat)=24+1 by rfl, word_eq_clock, word5_eq_clock]
  decide +kernel

/-- The second positive level adds no extra five-coordinate word. -/
private theorem second_recurrent_word : nativeWord5 2 = nativeWord5 26 := by
  rw [show (2:Nat)=1+1 by rfl,word5_eq_clock,
    show (26:Nat)=25+1 by rfl,word5_eq_clock]
  decide +kernel

end D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery
namespace D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery.Erasure

def rowData : List (List Nat) := [
  [1,0,0,2,1,2,2,0,1,2,2,2,1,0,0,0,1,0,2,2,1],
  [0,2,2,0,2,2,0,2,0,0,0,1,0,2,0,2,1,1,2,1,0],
  [1,2,2,1,1,2,2,1,1,0,0,2,1,1,0,2,2,1,0,1,1],
  [0,0,0,2,2,2,0,2,0,2,0,1,1,0,2,2,1,0,1,2,1],
  [1,0,0,1,1,2,2,0,1,0,0,2,0,2,0,2,2,2,1,2,1],
  [0,2,2,0,2,2,0,2,0,2,0,1,1,1,1,2,1,2,2,1,2],
  [1,2,2,2,1,2,2,1,1,2,0,2,1,0,1,2,2,0,2,1,0],
  [0,0,0,0,2,2,0,2,0,0,0,1,0,2,1,2,1,0,2,2,0],
  [1,0,0,1,1,2,2,0,1,2,0,2,1,1,1,2,2,0,1,2,1],
  [0,2,2,2,2,2,0,2,0,0,0,1,1,0,2,2,1,1,0,1,1],
  [1,2,2,1,1,2,2,1,1,0,0,2,0,2,1,2,2,1,0,1,2],
  [0,0,0,0,2,2,0,2,0,2,0,1,1,1,0,2,1,0,2,2,1],
  [1,0,0,2,1,2,2,0,1,0,0,2,1,0,0,2,2,2,2,2,1],
  [0,2,2,0,2,2,0,2,0,2,0,1,0,2,0,2,1,2,2,1,2],
  [1,2,2,1,1,2,2,1,1,2,0,2,1,1,0,2,2,0,0,1,1],
  [0,0,0,2,2,2,0,2,0,0,0,1,1,0,2,2,1,0,1,2,1],
  [1,0,0,1,1,2,2,0,1,2,0,2,0,2,0,2,2,0,1,2,1],
  [0,2,2,0,2,2,0,2,0,0,0,1,1,1,1,2,1,1,2,1,2],
  [1,2,2,2,1,2,2,1,1,0,0,2,1,0,1,2,2,1,2,1,1],
  [0,0,0,0,2,2,0,2,0,2,0,1,0,2,1,2,1,0,2,2,2],
  [1,0,0,1,1,2,2,0,1,0,0,2,1,1,1,2,2,2,1,2,2],
  [0,2,2,2,2,2,0,2,0,2,0,1,1,0,2,2,1,2,0,1,2],
  [1,2,2,1,1,2,2,1,1,2,0,2,0,2,1,2,2,0,0,1,1],
  [0,0,0,0,2,2,0,2,0,0,0,1,1,1,0,2,1,0,2,2,0],
  [1,0,0,2,1,2,2,0,1,2,0,2,1,0,0,2,2,0,2,2,1]
]

def phaseDigit (j : Fin 25) (q : Fin 21) : Nat :=
  ((rowData[j.val]?).getD [])[q.val]?.getD 3

/-- Every exact separator of the indexed phase table must read coordinate 47.
The first index is the exceptional positive level j=1, and slot 9 is prime 47. -/
private theorem mandatory_fortyseven (O : Fin 21 → Prop)
    (hsep : ∀ j k : Fin 25, (∀ q, O q → phaseDigit j q = phaseDigit k q) → j=k) :
    O 9 := by
  classical
  by_contra hno
  have hdiff : ∀ q : Fin 21, q ≠ 9 → phaseDigit 3 q = phaseDigit 15 q :=
    by decide +kernel
  have hzero : (3:Fin 25) = 15 := hsep 3 15 (fun q hq =>
    hdiff q (fun hq9 => hno (hq9 ▸ hq)))
  exact (by decide : (3:Fin 25) ≠ 15) hzero

abbrev obs4 (j : Fin 25) : Nat × Nat × Nat × Nat :=
  (phaseDigit j 0, phaseDigit j 1, phaseDigit j 9, phaseDigit j 13)
abbrev obs5 (j : Fin 25) : Nat × Nat × Nat × Nat × Nat :=
  (phaseDigit j 0, phaseDigit j 1, phaseDigit j 9, phaseDigit j 10, phaseDigit j 13)

/-- The initial exceptional word obstructs the recurrent decoder. -/
private theorem exception_alias : obs4 0 = obs4 24 ∧ (0:Fin 25) ≠ 24 := by decide +kernel

private theorem four_decodes_recurrent :
    ∀ j k : Fin 25, 2≤j.val → 2≤k.val → obs4 j=obs4 k → j=k := by
  decide +kernel

private theorem five_decodes_all : ∀ j k : Fin 25, obs5 j=obs5 k → j=k := by
  decide +kernel

def partA (i : Fin 3) : Fin 21 := [10,15,16][i.val]!
def partB (i : Fin 3) : Fin 21 := [12,13,14][i.val]!
def partC (i : Fin 5) : Fin 21 := [1,2,17,18,19][i.val]!

def fourSet (a b : Fin 3) (c : Fin 5) : Finset (Fin 21) :=
  {9, partA a, partB b, partC c}

def aliases : List (Fin 25 × Fin 25) := [(1,10),(1,10),(1,10),(1,7),(1,10),(1,10),(1,10),(1,10),(1,7),(1,10),(1,2),(1,2),(1,2),(1,12),(1,2),(1,10),(1,10),(1,10),(1,7),(1,10),(1,10),(1,10),(1,10),(1,7),(1,10),(1,2),(1,2),(1,2),(1,12),(1,2),(0,3),(0,3),(0,3),(0,5),(0,3),(0,3),(0,3),(0,3),(1,7),(0,3),(0,11),(0,11),(0,11),(0,11),(0,11)]

def aliasAt (a b : Fin 3) (c : Fin 5) : Fin 25 × Fin 25 :=
  (aliases[a.val*15+b.val*5+c.val]?).getD (0,0)

private theorem exactAliases : ∀ a b : Fin 3, ∀ c : Fin 5,
    let v := aliasAt a b c
    v.1 ≠ v.2 ∧ ∀ q : Fin 21, q ∈ fourSet a b c → phaseDigit v.1 q = phaseDigit v.2 q := by
  decide +kernel

private theorem cardFour : ∀ a b : Fin 3, ∀ c : Fin 5, (fourSet a b c).card = 4 := by
  decide +kernel

private theorem needPartA : ∀ q : Fin 21, (¬∃ i, q=partA i) →
    phaseDigit 0 q = phaseDigit 24 q := by decide +kernel

private theorem needPartB : ∀ q : Fin 21, (¬∃ i, q=partB i) →
    phaseDigit 5 q = phaseDigit 13 q := by decide +kernel

private theorem needPartC : ∀ q : Fin 21, (¬∃ i, q=partC i) →
    phaseDigit 9 q = phaseDigit 15 q := by decide +kernel

/-- Any exact separator of the full table needs five columns. The proof has
only 45 explicit collision witnesses after restricting to four forced,
disjoint column classes. It does not enumerate all four-subsets. -/
private theorem separator_card_ge_five (S : Finset (Fin 21))
    (hsep : ∀ j k : Fin 25, (∀ q, q ∈ S → phaseDigit j q = phaseDigit k q) → j=k) :
    5 ≤ S.card := by
  classical
  by_contra hs
  have hS : S.card ≤ 4 := by omega
  have h47 : (9:Fin 21) ∈ S := mandatory_fortyseven (fun q => q∈S) hsep
  have hA : ∃ a, partA a∈S := by
    by_contra h
    have eq := hsep 0 24 (fun q hq => needPartA q (fun ⟨a,ha⟩ => h ⟨a,ha ▸ hq⟩))
    exact (by decide : (0:Fin 25) ≠ 24) eq
  have hB : ∃ b, partB b∈S := by
    by_contra h
    have eq := hsep 5 13 (fun q hq => needPartB q (fun ⟨b,hb⟩ => h ⟨b,hb ▸ hq⟩))
    exact (by decide : (5:Fin 25) ≠ 13) eq
  have hC : ∃ c, partC c∈S := by
    by_contra h
    have eq := hsep 9 15 (fun q hq => needPartC q (fun ⟨c,hc⟩ => h ⟨c,hc ▸ hq⟩))
    exact (by decide : (9:Fin 25) ≠ 15) eq
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  obtain ⟨c,hc⟩ := hC
  have hsub : fourSet a b c ⊆ S := by
    intro q hq
    simp [fourSet] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact h47
    · exact ha
    · exact hb
    · exact hc
  have hset : fourSet a b c = S := Finset.eq_of_subset_of_card_le hsub (by rw [cardFour]; exact hS)
  rw [← hset] at hsep
  exact (exactAliases a b c).1 (hsep _ _ (exactAliases a b c).2)

end D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery.Erasure
namespace D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery
open D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery.Erasure
open D5.S0.Carrier D5.S1.Scale

def actualPrime (q : Fin 21) : Nat :=
  [5,7,11,13,17,23,29,31,41,47,53,61,79,83,103,107,109,163,167,181,193][q.val]!

def actualDigit (j : Nat) (q : Fin 21) : Option Nat :=
  correctedProbe (actualPrime q) (goldenLucas (3^j))

private theorem actual_clock (n : Nat) (q : Fin 21) :
    actualDigit (n+1) q = correctedProbe (actualPrime q) (clock (actualPrime q) n) := by
  unfold actualDigit
  rw [clock_eq_native]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem exactTable : ∀ i : Fin 25, ∀ q : Fin 21,
    correctedProbe (actualPrime q) (clock (actualPrime q) i.val) = some (phaseDigit i q) := by
  decide +kernel

private theorem actual_table (i : Fin 25) (q : Fin 21) :
    actualDigit (i.val+1) q = some (phaseDigit i q) := by
  rw [actual_clock,exactTable]

private theorem allCycles : ∀ q : Fin 21, clock (actualPrime q) (2+24)=clock (actualPrime q) 2 := by
  decide +kernel

private theorem tailCoincides : ∀ q : Fin 21,
    correctedProbe (actualPrime q) (clock (actualPrime q) 25) =
      correctedProbe (actualPrime q) (clock (actualPrime q) 1) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- Each positive native level is exactly a row of the canonical 25-word
table, proved from a bounded periodic orbit certificate and literal Lucas. -/
private theorem actual_word_into_table (j : Nat) (hj : 1 ≤ j) :
    ∃ i : Fin 25, ∀ q : Fin 21,
      actualDigit j q = some (phaseDigit i q) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm]
  by_cases hn : n<25
  · exact ⟨⟨n,hn⟩,actual_table ⟨n,hn⟩⟩
  · have hn' : 2≤n := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn'
    have hr : k%24 < 24 := Nat.mod_lt _ (by decide)
    by_cases hl : k%24=23
    · refine ⟨1,fun q => ?_⟩
      rw [actual_clock, at_residue _ 2 24 (by decide) (allCycles q),hl]
      change correctedProbe (actualPrime q) (clock (actualPrime q) 25) = some (phaseDigit 1 q)
      rw [tailCoincides]
      exact exactTable 1 q
    · have hfin : 2+k%24<25 := by omega
      refine ⟨⟨2+k%24,hfin⟩,fun q => ?_⟩
      rw [actual_clock, at_residue _ 2 24 (by decide) (allCycles q)]
      exact exactTable ⟨2+k%24,hfin⟩ q

/-- Exact five-column lower bound for the actual native sequence, not just
for unconstrained letter words. S separates when equality of tests in S
forces all 21 native tests equal. -/
private theorem actual_separator_needs_five (S : Finset (Fin 21))
    (hsep : ∀ j k : Nat, 1≤j → 1≤k →
      (∀ q∈S, actualDigit j q=actualDigit k q) → ∀ q, actualDigit j q=actualDigit k q) :
    5 ≤ S.card := by
  apply separator_card_ge_five S
  intro i j h
  have h' := hsep (i.val+1) (j.val+1) (by omega) (by omega)
  have he := h' (fun q hq => by rw [actual_table,actual_table,h q hq])
  apply five_decodes_all i j
  have hcols (q : Fin 21) : phaseDigit i q=phaseDigit j q := by
    have H := he q
    rw [actual_table,actual_table] at H
    exact Option.some.inj H
  change (phaseDigit i 0,phaseDigit i 1,phaseDigit i 9,phaseDigit i 10,phaseDigit i 13) =
    (phaseDigit j 0,phaseDigit j 1,phaseDigit j 9,phaseDigit j 10,phaseDigit j 13)
  rw [hcols 0,hcols 1,hcols 9,hcols 10,hcols 13]

/-- This explicit five-prime subset is a separator for all positive native
levels, including the initial nonrecurrent word. -/
private theorem chosen_five_separate (j k : Nat) (hj : 1≤j) (hk : 1≤k)
    (he : ∀ q : Fin 21, q∈({0,1,9,10,13} : Finset (Fin 21)) →
      actualDigit j q = actualDigit k q) : ∀ q, actualDigit j q = actualDigit k q := by
  obtain ⟨u,hu⟩ := actual_word_into_table j hj
  obtain ⟨v,hv⟩ := actual_word_into_table k hk
  have hq (q : Fin 21) (hs : q∈({0,1,9,10,13} : Finset (Fin 21))) :
      phaseDigit u q = phaseDigit v q := by
    have H := he q hs
    rw [hu q,hv q] at H
    exact Option.some.inj H
  have huv : u=v := five_decodes_all _ _ (by
    change (phaseDigit u 0,phaseDigit u 1,phaseDigit u 9,phaseDigit u 10,phaseDigit u 13) =
      (phaseDigit v 0,phaseDigit v 1,phaseDigit v 9,phaseDigit v 10,phaseDigit v 13)
    rw [hq 0 (by decide),hq 1 (by decide),hq 9 (by decide),hq 10 (by decide),hq 13 (by decide)])
  intro q
  rw [hu q,hv q,huv]

/-- Even if all 20 other probes are available, prime 47 is indispensable:
the full native words at positive levels four and sixteen only differ there. -/
private theorem actual_fortyseven_is_mandatory (S : Finset (Fin 21))
    (hsep : ∀ j k : Nat, 1≤j → 1≤k →
      (∀ q∈S, actualDigit j q=actualDigit k q) → ∀ q, actualDigit j q=actualDigit k q) :
    (9:Fin 21) ∈ S := by
  classical
  by_contra hno
  have hdiff : ∀ q : Fin 21, q ≠ 9 → phaseDigit 3 q=phaseDigit 15 q := by decide +kernel
  have hs : ∀ q∈S, actualDigit 4 q = actualDigit 16 q := by
    intro q hq
    have h3 := actual_table 3 q
    have h15 := actual_table 15 q
    change actualDigit 4 q = _ at h3
    change actualDigit 16 q = _ at h15
    rw [h3,h15,hdiff q (fun hh => hno (hh ▸ hq))]
  have H := hsep 4 16 (by decide) (by decide) hs 9
  have h3 := actual_table 3 9
  have h15 := actual_table 15 9
  change actualDigit 4 9 = _ at h3
  change actualDigit 16 9 = _ at h15
  rw [h3,h15] at H
  exact (by decide +kernel : phaseDigit 3 9 ≠ phaseDigit 15 9) (Option.some.inj H)


/-- Flip the global orientation of a 0,1,2 cubic exponent. -/
def signedDigit (g : Bool) (n : Nat) : Nat := if g then (3-n)%3 else n

def orientationBlindSet : Finset (Fin 21) := {0,1,9,13,16}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem signed_five_certificate :
    ∀ u v : Fin 25, ∀ a b : Bool,
      (∀ q∈orientationBlindSet, signedDigit a (phaseDigit u q) = signedDigit b (phaseDigit v q)) →
      u=v ∧ a=b := by
  decide +kernel

/-- The second optimal set uses probe 109 instead of 53. These five
readings recover both the native word and the common orientation, without
reading the usual calibrator q=23. -/
private theorem five_without_calibration (j k : Nat) (hj : 1≤j) (hk : 1≤k) (a b : Bool)
    (H : ∀ q∈orientationBlindSet,
      (actualDigit j q).map (signedDigit a) = (actualDigit k q).map (signedDigit b)) :
    a=b ∧ ∀ q, actualDigit j q=actualDigit k q := by
  obtain ⟨u,hu⟩ := actual_word_into_table j hj
  obtain ⟨v,hv⟩ := actual_word_into_table k hk
  have hc := signed_five_certificate u v a b (fun q hq =>
    Option.some.inj (by simpa only [hu q,hv q,Option.map_some] using H q hq))
  exact ⟨hc.2, fun q => by rw [hu q,hv q,hc.1]⟩

/-- A subset separates if agreement on it between any two positive
native levels forces agreement on every probe in the fixed alphabet. -/
def Separates (S : Finset (Fin 21)) : Prop :=
    ∀ j k : Nat, 1≤j → 1≤k →
      (∀ q∈S, actualDigit j q=actualDigit k q) → ∀ q, actualDigit j q=actualDigit k q

/-- Signed separation recovers the common orientation together with the
entire normalized native observation vector. -/
def SignedSeparates (S : Finset (Fin 21)) : Prop :=
  ∀ j k : Nat, 1≤j → 1≤k → ∀ a b : Bool,
    (∀ q∈S, (actualDigit j q).map (signedDigit a) = (actualDigit k q).map (signedDigit b)) →
    a=b ∧ ∀ q, actualDigit j q=actualDigit k q

/-- The optimal five-probe decoder for genuine positive Lucas levels. It
identifies the one exceptional level, recovers the remaining phase, and
proves every separating subset needs at least five probes, including 47. -/
theorem native_phase_recovery (j : ℕ) (hj : 1≤j) :
    let phase := decode5 (nativeWord5 j)
    phase = some (if j=1 then 24 else j%24) ∧
    Separates {0,1,9,10,13} ∧ SignedSeparates orientationBlindSet ∧
    ∀ S : Finset (Fin 21), Separates S → 5≤S.card ∧ (9:Fin 21)∈S := by
  dsimp only
  refine ⟨(native_five_probe_decoder j hj).2, chosen_five_separate, five_without_calibration, ?_⟩
  intro S H
  exact ⟨actual_separator_needs_five S H,actual_fortyseven_is_mandatory S H⟩

end D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery

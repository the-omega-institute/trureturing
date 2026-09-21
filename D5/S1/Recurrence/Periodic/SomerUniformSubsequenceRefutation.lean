/- GID: D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.fullClaim; result=D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.result; claim=D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.fullClaim
   digest: A third-order integer recurrence refutes Somer and Krizek's uniform-subsequence conjecture. -/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation

/-- The paper orders coefficients from the newest preceding term to the oldest. -/
def paperRecurrence {k : Nat} (a : Fin k -> Int) : LinearRecurrence Int where
  order := k
  coeffs i := a i.rev

/-- Exact least positive period after reduction modulo `modulus`. -/
def IsLeastPositivePeriodMod (modulus : Nat) (w : Nat -> Int) (period : Nat) : Prop :=
  0 < period /\
    Function.Periodic (fun n => (w n : ZMod modulus)) period /\
    forall t, 0 < t -> Function.Periodic (fun n => (w n : ZMod modulus)) t -> period <= t

/-- Every residue occurs `copies` times in the indicated full period. -/
def UniformCounts (modulus copies : Nat) (w : Nat -> Int) : Prop :=
  forall residue : Fin modulus,
    ((Finset.range (modulus * copies)).filter fun n =>
      (w n : ZMod modulus) = ((residue : Nat) : ZMod modulus)).card = copies

/-- Every residue occurs `copies` times in the prescribed arithmetic subsequence. -/
def UniformSubsequenceCounts (modulus copies step start : Nat) (w : Nat -> Int) : Prop :=
  forall residue : Fin modulus,
    ((Finset.range (modulus * copies)).filter fun n =>
      (w (start + n * step) : ZMod modulus) = ((residue : Nat) : ZMod modulus)).card = copies

/-- Somer and Krizek's Conjecture 4.2, with all source quantifiers explicit. -/
def fullClaim : Prop :=
  forall (k : Nat) (hk : 2 <= k) (a : Fin k -> Int) (w : Nat -> Int),
    (paperRecurrence a).IsSolution w ->
    forall (p e E : Nat),
      Nat.Prime p ->
      1 <= e ->
      0 < E ->
      Int.gcd (a ⟨k - 1, by omega⟩) p = 1 ->
      IsLeastPositivePeriodMod (p ^ e) w (p ^ e * E) ->
      UniformCounts (p ^ e) E w ->
      forall (g : Nat), 0 < g -> Nat.Coprime g p -> forall (s : Nat),
        let r := E / Nat.gcd g E
        UniformSubsequenceCounts (p ^ e) r g s w

abbrev CertificateWord := Fin 6 -> Fin 5

/-- Codes for the integer period `(0, 1, 2, 0, -1, -2)`. -/
def actualWord : CertificateWord := ![2, 3, 4, 2, 1, 0]

def decodeCode (x : Fin 5) : Int := (x.1 : Int) - 2

def sequenceOfWord (word : CertificateWord) (n : Nat) : Int :=
  decodeCode (word ⟨n % 6, Nat.mod_lt _ (by omega)⟩)

/-- The paper-order coefficient vector `(0, 0, -1)`. -/
def actualCoefficients : Fin 3 -> Int := ![0, 0, -1]

private theorem actualSequence_recurrence (n : Nat) :
    sequenceOfWord actualWord (n + 3) = -sequenceOfWord actualWord n := by
  have hlt : n % 6 < 6 := Nat.mod_lt n (by omega)
  interval_cases h : n % 6 <;>
    norm_num [sequenceOfWord, actualWord, decodeCode, Nat.add_mod, h]

private theorem actualSequence_periodic : Function.Periodic (sequenceOfWord actualWord) 6 := by
  intro n
  simp [sequenceOfWord]

private theorem actualSolution :
    (paperRecurrence actualCoefficients).IsSolution (sequenceOfWord actualWord) := by
  intro n
  change sequenceOfWord actualWord (n + 3) =
    ∑ i : Fin 3, actualCoefficients i.rev * sequenceOfWord actualWord (n + i)
  rw [actualSequence_recurrence]
  rw [Fin.sum_univ_three]
  norm_num [actualCoefficients, Fin.rev]

private theorem actualLeastPeriod :
    IsLeastPositivePeriodMod 3 (sequenceOfWord actualWord) 6 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro n
    exact congrArg (fun z : Int => (z : ZMod 3)) (actualSequence_periodic n)
  · intro t ht hperiod
    by_contra hnot
    have htlt : t < 6 := by omega
    interval_cases t
    · have h := hperiod 0
      change (1 : ZMod 3) = 0 at h
      exact (by decide : (1 : ZMod 3) ≠ 0) h
    · have h := hperiod 0
      change (2 : ZMod 3) = 0 at h
      exact (by decide : (2 : ZMod 3) ≠ 0) h
    · have h := hperiod 1
      change ((-1 : Int) : ZMod 3) = 1 at h
      exact (by decide : ((-1 : Int) : ZMod 3) ≠ 1) h
    · have h := hperiod 0
      change ((-1 : Int) : ZMod 3) = 0 at h
      exact (by decide : ((-1 : Int) : ZMod 3) ≠ 0) h
    · have h := hperiod 0
      change ((-2 : Int) : ZMod 3) = 0 at h
      exact (by decide : ((-2 : Int) : ZMod 3) ≠ 0) h

private theorem actualUniform : UniformCounts 3 2 (sequenceOfWord actualWord) := by
  intro residue
  fin_cases residue <;> decide

private theorem actualSubsequenceFailure :
    ¬ UniformSubsequenceCounts 3 1 2 0 (sequenceOfWord actualWord) := by
  intro uniform
  have h := uniform (1 : Fin 3)
  have emptyCount :
      ((Finset.range (3 * 1)).filter fun n =>
        (sequenceOfWord actualWord (0 + n * 2) : ZMod 3) = ((1 : Nat) : ZMod 3)).card = 0 := by
    decide
  have h' :
      ((Finset.range (3 * 1)).filter fun n =>
        (sequenceOfWord actualWord (0 + n * 2) : ZMod 3) = ((1 : Nat) : ZMod 3)).card = 1 := by
    simpa using h
  rw [emptyCount] at h'
  exact Nat.zero_ne_one h'

structure CounterexampleCertificate (word : CertificateWord) : Prop where
  solution : (paperRecurrence actualCoefficients).IsSolution (sequenceOfWord word)
  leastPeriod : IsLeastPositivePeriodMod 3 (sequenceOfWord word) 6
  uniform : UniformCounts 3 2 (sequenceOfWord word)
  subsequenceFailure : ¬ UniformSubsequenceCounts 3 1 2 0 (sequenceOfWord word)

private theorem actualCertificate : CounterexampleCertificate actualWord :=
  ⟨actualSolution, actualLeastPeriod, actualUniform, actualSubsequenceFailure⟩

private theorem certificate_refutes_fullClaim {word : CertificateWord}
    (certificate : CounterexampleCertificate word) : ¬ fullClaim := by
  intro claim
  have conclusion := claim 3 (by omega) actualCoefficients (sequenceOfWord word)
    certificate.solution 3 1 2 (by decide) (by omega) (by omega)
    (by norm_num [actualCoefficients]) certificate.leastPeriod certificate.uniform
    2 (by omega) (by decide) 0
  norm_num at conclusion
  exact certificate.subsequenceFailure conclusion

structure RefutationEvidence : Type where
  certificate : CounterexampleCertificate actualWord
  refutes : forall {word : CertificateWord}, CounterexampleCertificate word -> ¬ fullClaim

def actualRefutationEvidence : RefutationEvidence :=
  ⟨actualCertificate, certificate_refutes_fullClaim⟩

/-- The actual six-word counterexample refutes the complete published conjecture. -/
theorem result : (let counterexample := actualWord; Not fullClaim) := by
  exact actualRefutationEvidence.refutes actualRefutationEvidence.certificate

end D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation

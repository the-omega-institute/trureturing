/- GID: D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.claim; result=D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.result; claim=D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.claim
   digest: Refutes arXiv:2510.24280v2 Conjecture 4 at S={4,22,35,38}, heap 161. -/

import D5.S0.Certificates.SelfInterestConventionDeviationGain

namespace D5.S0.Certificates.Games.BhagatKulkarniLarssonMuraliConjectureFourRefutation
open D5.S0.Certificates.SelfInterestConventionDeviationGain

/-- Conjecture 4 of arXiv:2510.24280v2: for every finite nonempty set of positive
integers, presented as a duplicate-free list, and every heap, the antagonistic
outcome is coordinatewise at most the friendly outcome. -/
def claim : Prop :=
  ∀ (subtractions : List Nat), subtractions ≠ [] → (∀ s ∈ subtractions, 0 < s) →
    subtractions.Nodup → ∀ heap : Nat,
      (outcome subtractions AvA heap).1 ≤ (outcome subtractions FvF heap).1 ∧
      (outcome subtractions AvA heap).2 ≤ (outcome subtractions FvF heap).2

/-- The subtraction set of the counterexample. -/
def witnessSubtractions : List Nat := [4, 22, 35, 38]

set_option maxRecDepth 100000 in
/-- At heap 161, Bob receives 77 under FvF and 78 under AvA. -/
theorem result : ¬ claim := by
  intro conjecture
  have witnessValues :
      outcome witnessSubtractions FvF 161 = (84, 77) ∧
      outcome witnessSubtractions AvA 161 = (83, 78) := by
    decide +kernel
  have bound :=
    (conjecture witnessSubtractions (by decide) (by decide) (by decide) 161).2
  rw [witnessValues.1, witnessValues.2] at bound
  omega

#print axioms claim
#print axioms witnessSubtractions
#print axioms result

end D5.S0.Certificates.Games.BhagatKulkarniLarssonMuraliConjectureFourRefutation

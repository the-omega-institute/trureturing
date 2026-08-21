/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineMajorityRecovery
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/ByzantineMajorityRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A strict majority recovers a binary truth under a sub-half Byzantine bound. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/- Library-search audit trail (2026-08-21):
   * Repository search for `majority`, `Byzantine`, `n > 2 * f`, and report
     recovery found no accepted declaration for this threshold theorem.
   * Pinned Mathlib exact hit `Finset.card_filter_add_card_filter_not`
     partitions the finite report population into matching and mismatching
     reports; `omega` closes the resulting natural-number inequalities.
   * `loogle` and `leansearch` were unavailable on PATH; no third-party
     declaration was needed after the local and pinned-library searches.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineMajorityRecovery

/- The strict-majority rule is partial exactly when the two Boolean counts
   tie; the theorem below proves it returns the common honest value. -/
def strictMajority {n : Nat} (reports : Fin n → Bool) : Option Bool :=
  let trueCount := (Finset.univ.filter fun i => reports i).card
  let falseCount := (Finset.univ.filter fun i => ¬reports i).card
  if trueCount > falseCount then some true
  else if falseCount > trueCount then some false
  else none

/- The number of reports that disagree with the common honest value. -/
def byzantineCount {n : Nat} (reports : Fin n → Bool) (truth : Bool) : Nat :=
  (Finset.univ.filter fun i => reports i ≠ truth).card

/- At most `f` Byzantine reports means at most `f` entries differ from the
   common honest Boolean value `truth`. -/
theorem strict_majority_recovers
    {n f : Nat} (truth : Bool) (reports : Fin n → Bool)
    (threshold : n > 2 * f)
    (byzantine_bound :
      byzantineCount reports truth ≤ f) :
    strictMajority reports = some truth := by
  have partition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i => reports i = truth)
  have matching_count :
      (Finset.univ.filter fun i => reports i = truth).card +
        (Finset.univ.filter fun i => ¬reports i = truth).card = n := by
    simpa using partition
  have opposite_count :
      (Finset.univ.filter fun i => ¬reports i = truth).card ≤ f := by
    simpa only [byzantineCount, ne_eq] using byzantine_bound
  have strict_count :
      (Finset.univ.filter fun i => reports i = truth).card >
        (Finset.univ.filter fun i => ¬reports i = truth).card := by
    omega
  cases truth with
  | false =>
      have hfalse :
          (Finset.univ.filter fun i => ¬reports i).card >
            (Finset.univ.filter fun i => reports i).card := by
        simpa using strict_count
      unfold strictMajority
      dsimp
      rw [if_neg (Nat.not_lt_of_ge (Nat.le_of_lt hfalse)),
        if_pos hfalse]
  | true =>
      have htrue :
          (Finset.univ.filter fun i => reports i).card >
            (Finset.univ.filter fun i => ¬reports i).card := by
        simpa using strict_count
      unfold strictMajority
      dsimp
      rw [if_pos htrue]

/- The report domain and hypotheses have a checked concrete inhabitant. -/
example :
    strictMajority (n := 3) (fun _ => true) = some true := by
  apply strict_majority_recovers true (fun _ => true) (f := 1)
  · decide
  · simp [byzantineCount]

#print axioms strict_majority_recovers

end D5.S3.ConceptDynamics.InstitutionalCapture.ByzantineMajorityRecovery

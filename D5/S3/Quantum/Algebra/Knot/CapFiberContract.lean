/- GID: D5/S3/Quantum/Algebra/Knot/CapFiberContract
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Knot/CapFiberContract
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Legal-path cap fibers. -/
import D5.S3.Combinatorics.PerfectMatchings.OrderedMatchingCore
import D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CupCapBridgeProposal
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb

/-- This specialization uses the repository's actual LegalPath, not a new path carrier. -/
def legalPotential {L : Type*} [Fintype L] [DecidableEq L]
    {m : ℕ} (R : L → L → Prop) (q : L → ℝ) (s : L)
    (M : NCMatching m) (p : LegalPath R m s s) : ℝ :=
  boundaryPotential q M p.val

section ExactFirstUnpaidLemma

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- A proposition specifying the exact still-unproved source obligation,
to be proved under symmetry of R and nonvanishing of q.
This is not an axiom or a theorem, and it does not assume a circle evaluation.
The smaller matching is tied to the actual rewiring, not freely supplied. -/
def CapFiberGoal (R : L → L → Prop) (q : L → ℝ) (s : L)
    (m : ℕ) (M : NCMatching (m + 2)) (j : Fin (m + 1)) : Prop :=
  ∃ N : NCMatching m,
    (∀ k : Fin m, skipPair j (N.partner k) =
      reconnectPartner M j (skipPair j k)) ∧
    ∀ y : LegalPath R m s s,
      let A := {b : L // R (y.val j) b}
      let closed := M.partner j.castSucc = j.succ
      (closed →
        (∀ b : A,
          Compatible M (detourLabels j y.val b.val) ↔ Compatible N y.val) ∧
        (∀ b : A,
          boundaryPotential q M (detourLabels j y.val b.val) *
              (q b.val / q (y.val j)) =
            (q b.val / q (y.val j)) ^ 2 * boundaryPotential q N y.val)) ∧
      (¬ closed →
        (Compatible N y.val ↔
          ∃! b : A, Compatible M (detourLabels j y.val b.val)) ∧
        (∀ b : A, Compatible M (detourLabels j y.val b.val) →
          boundaryPotential q M (detourLabels j y.val b.val) *
              (q b.val / q (y.val j)) = boundaryPotential q N y.val))

end ExactFirstUnpaidLemma


end CupCapBridgeProposal

/- GID: D5/S3/Quantum/Algebra/Knot/CapSurgeryLabelFiber
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Knot/CapSurgeryLabelFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Arbitrary symmetric-label cap surgery. -/
import D5.S3.Combinatorics.PerfectMatchings.NonclosedCapPotential
import D5.S3.Quantum.Algebra.Knot.LegalCapFibers

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CupCapBridgeProposal

/-- Constructive surgery for the full unchanged CapFiberGoal, on the supplier's
actual LegalPath R m s s, with symmetry and nonvanishing explicitly quantified. -/
theorem capSurgery_labelFiber {L : Type*} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (hR : Symmetric R)
    (q : L → ℝ) (hq : ∀ a, q a ≠ 0) (s : L)
    (m : ℕ) (M : NCMatching (m + 2)) (j : Fin (m + 1)) :
    CapFiberGoal R q s m M j := by
  refine ⟨capSurgery M j, capSurgery_reconnect M j, ?_⟩
  intro y
  dsimp only
  constructor
  · intro hc
    exact capSurgery_close_fiber M j hc R q s y
  · intro hn
    exact ⟨nonclose_legal_fiber M j hn R hR s y,
      fun B hB => nonclose_boundaryPotential M j hn q hq y.val B.val hB⟩

#print axioms capSurgery_labelFiber

end CupCapBridgeProposal

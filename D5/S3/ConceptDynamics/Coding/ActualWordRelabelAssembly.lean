/- SOURCE ONLY, UNCOMPILED. Constructor assembly immediately after the
actual relabel comparison. No original-h theorem is named or specialized.
-/
import D5.S3.ConceptDynamics.Coding.ActualRelabelCharts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SourceOnly.ActualRelabelResidue
open D5.S3.ConceptDynamics.Coding
open TwoSidedFiniteInduction TypedPositiveSplitWord
open SourceOnly.ActualWordMatrixPath (dictionary)
open SourceOnly.FiniteKernelLadder (Based Path)

/-- Consumed finite-list helper. The predecessor supplied this computation
only as a local anonymous proof, not as a callable library declaration. -/
theorem path_append_weight {X Y Z : Based} {n m : ℕ}
    (u : Path X Y n) (v : Path Y Z m) (d : ℕ) [NeZero d] :
    (u.append v).weight d = u.weight d + v.weight d := by
  induction u with
  | nil X =>
      simp only [SourceOnly.FiniteKernelLadder.Path.append,
        Nat.zero_add, SourceOnly.FiniteKernelLadder.Path.weight, zero_add]
  | cons e tail ih =>
      simpa only [SourceOnly.FiniteKernelLadder.Path.append, Nat.add_right_comm,
        SourceOnly.FiniteKernelLadder.Path.weight, add_assoc] using
        congrArg (fun z => e.weight d + z) ih

/-- Actual matrix dictionary weight is the same P1 localized cochain.
Both positive-leaf charts and every relabel-leaf phase are retained. -/
theorem dictionary_residue : ∀ {F H : Presentation} (w : Word F H)
    (d : ℕ) [NeZero d] (hd : 3 ∣ d),
    (dictionary w).weight d = ActualWordLocalizedComparison.localizedCochain d hd w
  | _, _, .relabel r, d, _, hd => by
      simpa only [dictionary, SourceOnly.FiniteKernelLadder.Path.weight,
        ActualWordLocalizedComparison.localizedCochain, add_zero] using
        presentation_relabel_residue r d hd
  | _, _, .positive R S old next, d, _, hd => positive_leaf_residue R S old next d hd
  | _, _, .comp u v, d, _, hd => by
      change ((dictionary u).append (dictionary v)).weight d =
        ActualWordLocalizedComparison.localizedCochain d hd u +
          ActualWordLocalizedComparison.localizedCochain d hd v
      rw [path_append_weight, dictionary_residue u d hd, dictionary_residue v d hd]

end SourceOnly.ActualRelabelResidue

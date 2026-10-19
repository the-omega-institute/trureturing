/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Assemble actual dictionary weights over typed words. -/

/- Assemble the actual relabel and positive-leaf comparisons over endpoint-typed words, retaining both chart corrections. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualRelabelCharts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.ActualRelabelResidue
open D5.S3.ConceptDynamics.Coding
open TwoSidedFiniteInduction TypedPositiveSplitWord
open SourceOnly.ActualWordMatrixPath (dictionary)
open SourceOnly.FiniteKernelLadder (Based Path)

private theorem path_weight_mpr {X Y : Based} {k l : ℕ} (h : k = l)
    (e : Path X Y l = Path X Y k) (u : Path X Y k) (d : ℕ) [NeZero d] :
    (e.mpr u).weight d = u.weight d := by
  subst l
  have he : e = rfl := Subsingleton.elim _ _
  cases he
  rfl

/-- Weight is additive under actual path concatenation. -/
theorem path_append_weight {X Y Z : Based} {n m : ℕ}
    (u : Path X Y n) (v : Path Y Z m) (d : ℕ) [NeZero d] :
    (u.append v).weight d = u.weight d + v.weight d := by
  induction u with
  | nil X =>
      simp only [SourceOnly.FiniteKernelLadder.Path.append]
      rw [path_weight_mpr (Nat.zero_add m).symm]
      exact (zero_add _).symm
  | @cons X Y W k e tail ih =>
      simp only [SourceOnly.FiniteKernelLadder.Path.append]
      rw [path_weight_mpr (k := (k+m)+1) (l := (k+1)+m) (by omega)]
      simpa only [SourceOnly.FiniteKernelLadder.Path.weight, add_assoc] using
        congrArg (fun z => e.weight d + z) (ih v)

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

/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes4
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes4
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Certificate.transition_counts; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes4.class_successors
   digest: Width-five exact-budget transfer measurement. -/

/-
admission_basis: escape-witness
escape_witness: class_successors verifies the sorted successor multiplicities of every valid canonical width-five source in class 4. The decision checks all canonical row tails after the proof fixes the first colour to zero. Certificate.canonical_successors substitutes the list into the transfer sum.
class_successors: proof_shape=content; consumers=Width5.Certificate.canonical_successors
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
/-! A single output class of the canonical-boundary defect transfer. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes4
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
private local instance (p : Row) : Decidable
    (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p) := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem class_successors : ∀ p (d : Fin 3), Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    cl p d.val = (4 : Fin 43) → successors p d.val = classList 4 := by
  have h : ∀ a b c e : Fin 4, ∀ d : Fin 3, Valid (![0, a, b, c, e] : Row) d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical (![0, a, b, c, e] : Row) →
    cl (![0, a, b, c, e] : Row) d.val = (4 : Fin 43) → successors (![0, a, b, c, e] : Row) d.val = classList 4 := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide +kernel
  intro p d hv hc hcl
  have hz : p 0 = 0 := by
    by_contra hn
    obtain ⟨j, hj, _⟩ := hc 0 0 (Fin.pos_iff_ne_zero.mpr hn)
    exact (Fin.not_lt_zero j) hj
  have hp : p = ![0, p 1, p 2, p 3, p 4] := by
    funext i
    fin_cases i <;> simp [hz]
  rw [hp] at hv hc hcl ⊢
  exact h (p 1) (p 2) (p 3) (p 4) d hv hc hcl
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes4

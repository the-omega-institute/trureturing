/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Hardin's order-27 recurrence for the literal width-six two-defect HDA count. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635IntegerCertificate
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635

open HardinA229584StripData (horizontal)
open WidthSix.HardinA229532StripData (between)
open DefectTransfer (lumped_count literalCount bondDefects)
open HardinA229635State (Valid cl legal legal_start)
open HardinA229635Transfer
open HardinA229635Residual
open HardinA229635Literal (six_labellings)

private theorem scalar_count (k : ℕ) :
    scalar T initial terminal k = 6 * (HardinA229637RowColumn.T (k + 1) 6 : ℤ) := by
  have labelled : (literalCount (q := 3) horizontal between 2 (k + 1) : ℤ) =
      scalar T initial terminal k :=
    lumped_count horizontal between id (bondDefects between) Valid cl T initial terminal 2
      (fun _ _ => rfl) terminal_correct legal transition_counts legal_start initial_correct k
  rw [← labelled, six_labellings]
  push_cast
  rfl

/-- R. H. Hardin's empirical A229635 recurrence for the literal two-defect HDA count. -/
theorem result (n : ℕ) (hn : 31 ≤ n) :
    (HardinA229637RowColumn.T n 6 : ℤ) =
      ∑ j : Fin 27, coefficients j * (HardinA229637RowColumn.T (n - (j.val + 1)) 6 : ℤ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hzero := HardinA229635IntegerCertificate.residual_all_offsets t
  unfold HardinA229635Residual.residual at hzero
  have hlead : 30 + t + 1 = 31 + t := by omega
  have hlag (j : Fin 27) : 29 - j.val + t + 1 = 31 + t - (j.val + 1) := by omega
  simp only [scalar_count, hlead, hlag] at hzero
  simp_rw [mul_left_comm (coefficients _) 6, ← Finset.mul_sum] at hzero
  omega

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635

/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Canonical pattern coverage and boundary laws for the width-six transfer. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open WidthSix HardinA229635State

local instance (p : Row) : Decidable (Canonical p) := by
  unfold Canonical
  infer_instance

private def coverCheck (i : RowNumber) : Prop :=
  h (rowEquiv i) ≤ 2 → Canonical (rowEquiv i) →
    rep (fresh (rowEquiv i)) = rowEquiv i

local instance (i : RowNumber) : Decidable (coverCheck i) := by
  unfold coverCheck
  infer_instance

private theorem cover0 : ∀ i : Fin 243, coverCheck (i.castAdd 486) := by decide +kernel
private theorem cover1 : ∀ i : Fin 243, coverCheck ⟨243 + i.val, by omega⟩ := by decide +kernel
private theorem cover2 : ∀ i : Fin 243, coverCheck (i.natAdd 486) := by decide +kernel

theorem representatives_complete (p : Row) (hc : Canonical p) (hh : h p ≤ 2) :
    rep (fresh p) = p := by
  let i := rowEquiv.symm p
  have hi (j : Fin 243) (k : ℕ) (hk : k + j.val < 729)
      (he : k + j.val = i.val) :
      (⟨k + j.val, hk⟩ : RowNumber) = i := Fin.ext he
  have h : coverCheck i := by
    by_cases h0 : i.val < 243
    · let j : Fin 243 := ⟨i.val, h0⟩
      exact (show j.castAdd 486 = i from Fin.ext rfl) ▸ cover0 j
    by_cases h1 : i.val < 486
    · let j : Fin 243 := ⟨i.val - 243, by omega⟩
      exact (hi j 243 (by dsimp [j]; omega) (by dsimp [j]; omega)) ▸ cover1 j
    · let j : Fin 243 := ⟨i.val - 486, by omega⟩
      exact (hi j 486 (by dsimp [j]; omega) (by dsimp [j]; omega)) ▸ cover2 j
  unfold coverCheck at h
  dsimp [i] at h
  rw [Equiv.apply_symm_apply] at h
  exact h hh hc


end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws

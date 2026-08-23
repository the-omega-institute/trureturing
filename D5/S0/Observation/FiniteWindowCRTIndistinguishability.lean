/- GID: D5/S0/Observation/FiniteWindowCRTIndistinguishability
   generality: G
   mirror-B: D5/B/S0/Observation/FiniteWindowCRTIndistinguishability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite coprime ZMod window is reproduced by a natural-number shift. -/

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'finite_window_cannot_separate_shift' D5 Golden/Frozen/accepted`
     returned no matches.
   * Searches for `chineseRemainder`, `CRT`, `ZMod`, and pairwise coprimality found
     `D5.S3.ArithUnits.FiniteWindowResidues.finite_window_residues_realizable`, a more
     general bounded `Nat.ModEq` CRT wrapper, but no `{4, 9, 25}` / `511` witness.
   * Pinned mathlib provides `Nat.chineseRemainderOfFinset` and
     `ZMod.natCast_eq_natCast_iff`; the proof below uses these directly to bridge the
     finite CRT certificate to equality of dependent `ZMod` readings.
   * No S0 module imports S3, so the higher-stratum wrapper is not imported across the
     repository's downward-only dependency order.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Observation.FiniteWindowCRTIndistinguishability

/-- The readings of an integer walk at every modulus in a finite observation window. -/
def windowReading (window : Finset ℕ) (n : ℕ) : ∀ m : window, ZMod m.1 :=
  fun _ => n

/-- Every target on a finite window of positive pairwise-coprime moduli is reproduced by
an integer step, so such a window cannot distinguish a shift from walking the same line. -/
theorem finite_window_cannot_separate_shift (window : Finset ℕ)
    (hpositive : ∀ m ∈ window, 0 < m)
    (hcoprime : Set.Pairwise (window : Set ℕ) Nat.Coprime) :
    Function.Surjective (windowReading window) := by
  intro target
  let residues : ℕ → ℕ := fun m =>
    if hm : m ∈ window then (target ⟨m, hm⟩).val else 0
  have hnonzero : ∀ m ∈ window, m ≠ 0 := fun m hm => Nat.ne_of_gt (hpositive m hm)
  let crt := Nat.chineseRemainderOfFinset residues id window hnonzero hcoprime
  refine ⟨crt, ?_⟩
  funext m
  haveI : NeZero m.1 := ⟨hnonzero m.1 m.2⟩
  rw [show windowReading window crt m = (crt : ZMod m.1) by rfl]
  rw [← ZMod.natCast_zmod_val (target m)]
  exact (ZMod.natCast_eq_natCast_iff crt (target m).val m.1).2
    (by simpa [crt, residues, m.2] using crt.property m.1 m.2)

/-- The source certificate: the window has 900 residue classes and step 511 reads
`(3, 7, 11)` modulo `(4, 9, 25)`. -/
theorem window_4_9_25_certificate :
    Fintype.card (ZMod 4 × ZMod 9 × ZMod 25) = 900 ∧
      (511 : ZMod 4) = 3 ∧ (511 : ZMod 9) = 7 ∧ (511 : ZMod 25) = 11 := by
  constructor
  · rw [Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card, ZMod.card]
  · decide

example :
    (511 : ZMod 4) = 3 ∧ (511 : ZMod 9) = 7 ∧ (511 : ZMod 25) = 11 := by
  exact window_4_9_25_certificate.2

#print axioms finite_window_cannot_separate_shift

end D5.S0.Observation.FiniteWindowCRTIndistinguishability

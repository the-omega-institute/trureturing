/- GID: D5/S3/Combinatorics/AdditiveCodes/NonsquareExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AdditiveCodes/NonsquareExtension
   mirror-E: none(waiver:alderson-problem-nine-two)
   anchors: []
   utility: none
   digest: Every nonsquare nonprime base field admits an additively maximal extendable code. -/

import D5.S3.Combinatorics.AdditiveCodes.AdditiveCodesFrobenius
import D5.S3.Combinatorics.AdditiveCodes.AdditiveCodesWeighting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.AdditiveCodes.NonsquareExtension

/-- Problem 9.2, first sentence, of Alderson's maximality questions. -/
theorem result : AdditiveExtensionDefs.claimNonsquare := by
  classical
  intro p hp e he _
  let F := GaloisField p e
  let : Fintype F := Fintype.ofFinite F
  have hF : ∃ c : F, c ^ p ≠ c := by
    by_contra hn
    push Not at hn
    have hf : FiniteField.frobeniusAlgHom (ZMod p) F = 1 := by
      ext c
      simpa only [FiniteField.coe_frobeniusAlgHom, ZMod.card, AlgHom.one_apply] using hn c
    have ho := FiniteField.orderOf_frobeniusAlgHom (ZMod p) F
    rw [hf, orderOf_one, GaloisField.finrank p (by omega)] at ho
    omega
  obtain ⟨B, label, hB, _, block, avoid⟩ := frobeniusBlocking F p hF
  exact incidenceConstruction 2 2 2 (by omega) (by omega)
    (by simp [F]) (by omega) B hB block label avoid

end D5.S3.Combinatorics.AdditiveCodes.NonsquareExtension

/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Leech mixed Verlinde coefficients agree with native field multiplicities. -/

import D5.S3.VertexAlgebra.Characters.ActualLeechSectorCharacters
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedMultiplicityOne

/-! The finite Verlinde sums from the sector character matrix agree with the
dimensions of the actual parity-changing mixed fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Matrix BigOperators

namespace D5.S3.VertexAlgebra.ActualLeechMixedVerlinde

open ActualLeechHyperbolic (leechData)
open ActualLeechSectorCharacters (sectorS)
open TwistedGround.Orbifold.NativeOddTwistedIntertwiner

/-- The finite Verlinde sum for the matrix acting on the four literal characters. -/
def verlindeCoefficient (i j k : Fin 4) : ℂ :=
  ∑ x : Fin 4, sectorS i x * sectorS j x * (star (sectorS k x)) / sectorS 0 x

/-- The input label of the native mixed field at the given oscillator parity. -/
def twistedLabel (odd : Bool) : Fin 4 := if odd then 2 else 3

/-- The native mixed coefficient line inside the space of all coefficient families. -/
def mixedCoefficientSpace (odd : Bool) : Submodule ℂ (MixedCoefficients leechData leechUnit odd) :=
  ℂ ∙ (nativeMixedField leechData leechUnit odd).coeff

/-- The line consists exactly of families realized by lawful mixed fields. -/
theorem mem_mixedCoefficientSpace (odd : Bool) (x : MixedCoefficients leechData leechUnit odd) :
    x ∈ mixedCoefficientSpace odd ↔
      ∃ F : LawfulMixedField leechData leechUnit odd, F.coeff = x := by
  rw [mixedCoefficientSpace, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨(nativeMixedField leechData leechUnit odd).scale z, hz⟩
  · rintro ⟨F, rfl⟩
    obtain ⟨z, hz, _⟩ := leech_mixed_multiplicity_one odd F
    exact ⟨z, (congrArg LawfulMixedField.coeff hz).symm⟩

private theorem coeff_injective (odd : Bool) :
    Function.Injective (LawfulMixedField.coeff (D := leechData) (hu := leechUnit) (s := odd)) := by
  intro F G h
  cases F
  cases G
  cases h
  rfl

private theorem native_coeff_ne_zero (odd : Bool) :
    (nativeMixedField leechData leechUnit odd).coeff ≠ 0 := by
  intro hz
  let F := nativeMixedField leechData leechUnit odd
  have hs (z : ℂ) : (F.scale z).coeff = 0 :=
    (congrArg (fun a : MixedCoefficients leechData leechUnit odd => z • a) hz).trans
      (smul_zero z)
  have h : F.scale 1 = F.scale 0 :=
    coeff_injective odd ((hs 1).trans (hs 0).symm)
  have hi := leech_nativeMixedField_scale_injective odd
  exact one_ne_zero (@hi 1 0 h)

/-- The native field generates a one-dimensional space in each mixed direction. -/
theorem mixedCoefficientSpace_finrank (odd : Bool) :
    Module.finrank ℂ (mixedCoefficientSpace odd) = 1 := by
  unfold mixedCoefficientSpace
  exact @finrank_span_singleton ℂ (MixedCoefficients leechData leechUnit odd)
    _ _ _ (nativeMixedField leechData leechUnit odd).coeff (native_coeff_ne_zero odd)

private theorem mixed_verlinde_value (odd : Bool) (k : Fin 4) :
    verlindeCoefficient 1 (twistedLabel odd) k = if k = twistedLabel (!odd) then 1 else 0 := by
  cases odd <;> fin_cases k <;>
    simp [verlindeCoefficient, twistedLabel, sectorS, Fin.sum_univ_succ] <;>
    norm_num

/-- The sole nonzero Verlinde coefficient in each mixed row equals the
complex dimension of the actual lawful mixed coefficient space. -/
theorem mixed_verlinde_agrees_with_native_finrank (odd : Bool) (k : Fin 4) :
    verlindeCoefficient 1 (twistedLabel odd) k =
      if k = twistedLabel (!odd) then
        (Module.finrank ℂ (mixedCoefficientSpace odd) : ℂ) else 0 := by
  have hrank : (Module.finrank ℂ (mixedCoefficientSpace odd) : ℂ) = 1 :=
    (congrArg (fun n : ℕ => (n : ℂ)) (mixedCoefficientSpace_finrank odd)).trans Nat.cast_one
  exact (mixed_verlinde_value odd k).trans
    (congrArg (fun d : ℂ => if k = twistedLabel (!odd) then d else 0) hrank.symm)

end D5.S3.VertexAlgebra.ActualLeechMixedVerlinde

#print axioms D5.S3.VertexAlgebra.ActualLeechMixedVerlinde.mem_mixedCoefficientSpace
#print axioms D5.S3.VertexAlgebra.ActualLeechMixedVerlinde.mixed_verlinde_agrees_with_native_finrank

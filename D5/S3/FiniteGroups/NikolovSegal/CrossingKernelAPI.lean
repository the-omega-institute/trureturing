/- GID: D5/S3/FiniteGroups/NikolovSegal/CrossingKernelAPI
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/CrossingKernelAPI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.QuantitativeExtraction

set_option autoImplicit false
open scoped List

namespace NikolovSegal.CrossingKernel
open Equation47WordCoupling BalancedCrossing Equation47Colours
open Equation47ValueNormalization (colourType)
universe u v
variable {S : Type u} [Group S] {V : Type v} [DecidableEq V] {m : ℕ}

/-- Proposition8.4 as actual inductive extraction, exact support loss, retained
literal colour bound, 2D distinct selected keys, and final-residual freshness. -/
theorem proposition8_4 (chi : V → Fin m) (n D : ℕ) (W : List (Letter V S))
    (hb : Balanced (signedVariables W))
    (hc : colourType (colours chi (signedVariables W)) <+ colourBound m n)
    (hs : n+2*D ≤ (support (signedVariables W)).card) :
    ∃ P : Extraction D W,
      Balanced (signedVariables (finalWord P)) ∧
      colourType (colours chi (signedVariables (finalWord P))) <+ colourBound m n ∧
      (support (signedVariables (finalWord P))).card + 2*D =
        (support (signedVariables W)).card ∧
      (extractedKeys P).Nodup ∧ (extractedKeys P).length = 2*D ∧
      (∀ x ∈ extractedKeys P, avoids (finalWord P) x) := by
  obtain ⟨P,hbP,hcP,hsP⟩ := extraction_exists chi n D W hb hc hs
  exact ⟨P,hbP,hcP,hsP,extractedKeys_nodup P,extractedKeys_length P,finalWord_avoids_extracted P⟩

/-- Exact integration adapter for the owner's proved signed count formula.
No forest integration or colour budget is fabricated by this adapter. -/
theorem extraction_from_owner_counts (chi : V → Fin m) (n D : ℕ)
    (W : List (Letter V S)) (Y : Finset V)
    (hb : ∀ x s, (Equation47ValueNormalization.signedVariables W).count (x,s) =
      if x ∈ Y then 1 else 0)
    (hc : colourType ((Equation47ValueNormalization.signedVariables W).map
      (fun p => (chi p.1,p.2))) <+ colourBound m n)
    (hs : n+2*D ≤ Y.card) : Nonempty (Extraction D W) := by
  have hbal := balanced_of_owner_counts W Y hb
  have hcolour : colourType (colours chi (signedVariables W)) <+ colourBound m n := by
    simpa only [colours,signedVariables_eq_owner] using hc
  have hbudget : n+2*D ≤ (support (signedVariables W)).card := by
    rw [support_eq_of_owner_counts W Y hb]
    exact hs
  obtain ⟨P,_⟩ := extraction_exists chi n D W hbal hcolour hbudget
  exact ⟨P⟩

/-- Definitional adapter to the owner's actual Arc colours. -/
theorem colours_eq_owner {I : Type u} [Finite I] [DecidableEq I]
    (W : List (Letter (Equation47.Arc m I) S)) :
    colours Prod.fst (signedVariables W) = Equation47ValueNormalization.wordColours W := rfl

end NikolovSegal.CrossingKernel

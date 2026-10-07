/- GID: D5/S3/FiniteGroups/NikolovSegal/TwistedProductPadding
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TwistedProductPadding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.BoundedSimpleTwistedProduct

set_option autoImplicit false

namespace NikolovSegal.SmallTwistedProduct
open Equation47WordCoupling
universe u
variable {S : Type u} [Group S]

/-- Pad an actual ordered twisted product by a last identity value, for the
arbitrary new automorphisms. No factors are reordered or discarded. -/
theorem twisted_input_succ {d : ℕ} (h : PartIITwistedProductInput S d) :
    PartIITwistedProductInput S (d+1) := by
  intro a b target
  obtain ⟨xi,eta,he⟩ := h (fun j => a j.castSucc) (fun j => b j.castSucc) target
  refine ⟨Fin.snoc xi 1,Fin.snoc eta 1,?_⟩
  simp only [orderedProduct,List.ofFn_succ',List.prod_concat,
    Fin.snoc_castSucc,Fin.snoc_last]
  simpa [twistedValue,orderedProduct] using he

/-- Monotonicity in the length retains all prescribed automorphisms and
uses actual identity witnesses for every additional factor. -/
theorem twisted_input_mono {d e : ℕ} (hde : d ≤ e)
    (h : PartIITwistedProductInput S d) : PartIITwistedProductInput S e := by
  induction hde with
  | refl => exact h
  | step hde ih => exact twisted_input_succ ih

end NikolovSegal.SmallTwistedProduct

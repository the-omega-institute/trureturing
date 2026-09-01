/- GID: D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/EffectiveImageNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transport factorization is natural on the effective image. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-21).
   * `rg -n "transport|naturality|Set\.range|factor" D5 --glob '*.lean'`
     found the adjacent `layer_shift_naturality` wrapper and the canonical
     `Concept` readout, but no theorem combining two factorization equations
     with an image-restricted naturality conclusion.
   * The pinned Mathlib equality tools `Function.comp_apply`, `congrFun`,
     and `congrArg` were checked; no exact image-restricted theorem was found.
   * The source family import supplies the canonical `Concept` carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.EffectiveImageNaturality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A natural transport square descends through two source factorisations on
the effective image of the first concept readout. -/
theorem effective_image_naturality
    {XE XEPrime YE YEPrime WE WEPrime : Type*}
    (C : Concept XE YE) (CPrime : Concept XEPrime YEPrime)
    (T : Concept XE WE) (TPrime : Concept XEPrime WEPrime)
    (f : Concept YE WE) (fPrime : Concept YEPrime WEPrime)
    (Xmap : Concept XE XEPrime)
    (Bmap : Concept YE YEPrime)
    (Ymap : Concept WE WEPrime)
    (h_transport : TPrime ∘ Xmap = Ymap ∘ T)
    (h_readout : CPrime ∘ Xmap = Bmap ∘ C)
    (h_factor : T = f ∘ C)
    (h_factorPrime : TPrime = fPrime ∘ CPrime) :
    ∀ y ∈ Set.range C, Ymap (f y) = fPrime (Bmap y) := by
  rintro y ⟨x, rfl⟩
  have h_factor_x : T x = f (C x) := by
    have hpoint := congrFun h_factor x
    unfold Function.comp at hpoint
    exact hpoint
  have h_transport_x : TPrime (Xmap x) = Ymap (T x) := by
    have hpoint := congrFun h_transport x
    unfold Function.comp at hpoint
    exact hpoint
  have h_factor_prime_x : TPrime (Xmap x) = fPrime (CPrime (Xmap x)) := by
    have hpoint := congrFun h_factorPrime (Xmap x)
    unfold Function.comp at hpoint
    exact hpoint
  have h_readout_x : CPrime (Xmap x) = Bmap (C x) := by
    have hpoint := congrFun h_readout x
    unfold Function.comp at hpoint
    exact hpoint
  calc
    Ymap (f (C x)) = Ymap (T x) := by rw [h_factor_x]
    _ = TPrime (Xmap x) := h_transport_x.symm
    _ = fPrime (CPrime (Xmap x)) := h_factor_prime_x
    _ = fPrime (Bmap (C x)) := congrArg fPrime h_readout_x

/-- The source carriers admit a concrete inhabited instance of all four
factorisations and both naturality equations. -/
example :
    let C : Concept Bool Bool := id
    let CPrime : Concept Bool Bool := id
    let T : Concept Bool Bool := id
    let TPrime : Concept Bool Bool := id
    let f : Concept Bool Bool := id
    let fPrime : Concept Bool Bool := id
    let Xmap : Concept Bool Bool := id
    let Bmap : Concept Bool Bool := id
    let Ymap : Concept Bool Bool := id
    (T ∘ Xmap = Ymap ∘ T) ∧
      (CPrime ∘ Xmap = Bmap ∘ C) ∧
      (T = f ∘ C) ∧
      (TPrime = fPrime ∘ CPrime) := by
  simp <;> rfl

example : Concept Bool Bool := id

#print axioms effective_image_naturality

end D5.S3.ConceptDynamics.Transport.EffectiveImageNaturality

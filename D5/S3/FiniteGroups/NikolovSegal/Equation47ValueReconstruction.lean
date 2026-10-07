/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueReconstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueSequence

set_option autoImplicit false

/-! Actual corrected-action consumer of the complete normalized VALUE forest
contraction, Part I p.225.  The arbitrary cycle witness parameters and every
unused nonbase VALUE are retained.  This module proves reconstruction and
balance, not uniform scalar/twisted existence or the quantitative extraction.
-/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
universe u
variable {S I : Type u} [Group S] [Fintype I] [DecidableEq I] {m q : ℕ}

/-- For EVERY residual assignment, construct actual commutator witnesses.
All unused nonbase VALUES retain their prescribed values.  Cycle scalar
witnesses are retained independently.  Targets enter after the fixed y. -/
theorem corrected_value_forest_extension
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (L : List (I × Arc m I))
    (hL : ValueLeafOrder (fun j => sigma j ^ q) L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (u : ∀ j, ActualCycle (sigma j ^ q) → S) (kappa : I → S)
    (z : Arc m I → S)
    (hz : ∀ v, v = r v → wordValue
      (contractValueSystem kappa L (normalizedVertexWord (fun j => sigma j ^ q)
        (fun j i => correctedCycleComponent beta sigma y j i q) u) v) z = kappa v) :
    ∃ c : Fin m → I → S,
      (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
      (∀ v, orderedProduct (fun j => (c j v)⁻¹ *
        (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v) ∧
      (∀ e : Arc m I, e.2 ≠ base (sigma e.1 ^ q) e.2 →
        (∀ p ∈ L, e ≠ p.2) →
        (c e.1 e.2)⁻¹ * (((k e.1 * MulAut.conj (y e.1)⁻¹)^q) (c e.1)) e.2 = z e) := by
  let tau := fun j => sigma j ^ q
  let alpha := fun j i => correctedCycleComponent beta sigma y j i q
  let a := extendValueSystem kappa L (normalizedVertexWord tau alpha u) z
  have hext := (normalized_value_forest_reconstruction tau alpha u kappa L hL r hroots).1 z
  have ha : ∀ v, wordValue (normalizedVertexWord tau alpha u v) a = kappa v := by
    intro v
    by_cases hv : v = r v
    · rw [← contractValueSystem_value]
      exact hz v hv
    · exact hext.2.1 v hv
  obtain ⟨c,hc,hx⟩ := (corrected_value_tuple_with_parameters_iff k sigma beta hcoord y
      (normalizedValues tau alpha u a) u).mpr
        (normalizedValues_cycle_constraints tau alpha u a)
  refine ⟨c,hc,?_,?_⟩
  · intro v
    rw [← ha v,normalizedVertexWord_value]
    congr 1
    funext j
    exact (hx j v).symm
  · intro e he hu
    rw [← hx e.1 e.2,normalizedValues_nonbase tau alpha u a e.1 e.2 he]
    exact extendValueSystem_unused kappa L _ z e hu

/-- A single actual forest, chosen before scalar cycle witnesses and ALL
targets, supplies full coordinate reconstruction and exact signed support
for each genuine powered component.  Scalar parameters are not fixed to1.
There is no whole-block coverage or extraction assumption in this theorem.
-/
theorem actual_corrected_value_component_residuals
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (r : I → I)
    (hr : ∀ v, (qPowerGraph sigma q).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph sigma q).Reachable v w → r v = r w) :
    ∃ L : List (I × Arc m I), ValueLeafOrder (fun j => sigma j ^ q) L ∧
      (∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v) ∧
      ∀ (u : ∀ j, ActualCycle (sigma j ^ q) → S) (kappa : I → S),
      (∀ z : Arc m I → S,
        (∀ v, v = r v → wordValue
          (contractValueSystem kappa L (normalizedVertexWord (fun j => sigma j ^ q)
            (fun j i => correctedCycleComponent beta sigma y j i q) u) v) z = kappa v) →
        ∃ c : Fin m → I → S,
          (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
          (∀ v, orderedProduct (fun j => (c j v)⁻¹ *
            (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v) ∧
          (∀ e : Arc m I, e.2 ≠ base (sigma e.1 ^ q) e.2 →
            (∀ p ∈ L, e ≠ p.2) →
            (c e.1 e.2)⁻¹ * (((k e.1 * MulAut.conj (y e.1)⁻¹)^q) (c e.1)) e.2 = z e)) ∧
      (∀ root, root = r root → ∀ e s,
        (signedVariables (contractValueSystem kappa L
          (normalizedVertexWord (fun j => sigma j ^ q)
            (fun j i => correctedCycleComponent beta sigma y j i q) u) root)).count (e,s) =
        if e.2 ≠ base (sigma e.1 ^ q) e.2 ∧ (∀ p ∈ L, e ≠ p.2) ∧ r e.2 = root
        then 1 else 0) := by
  have hgraph : qPowerGraph (fun j => sigma j ^ q) 1 = qPowerGraph sigma q := by
    ext v w
    simp only [qPowerGraph,pow_one]
  obtain ⟨F,L,hF,hacyc,hreach,hL,hroots,hedges⟩ :=
    exists_value_leafOrder (fun j => sigma j ^ q) r
      (by simpa only [hgraph] using hr) (by simpa only [hgraph] using hconst)
  refine ⟨L,hL,hroots,?_⟩
  intro u kappa
  constructor
  · exact fun z hz => corrected_value_forest_extension k sigma beta hcoord y L hL r hroots u kappa z hz
  · intro root hroot e s
    exact normalized_value_residual_sign_count _ _ _ _ L hL r hroots
      (by simpa only [hgraph] using hconst) root hroot e s

end NikolovSegal.Equation47ValueNormalization

import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

namespace LeanInformationAudit.ReifierTemplates
open D5.S3.ConceptDynamics.InformationEscape PointwiseRegistrationTemplates

/-- Uniform source descriptor. Direct carrier parameters retain the source telescope.
This is judge infrastructure adapting the existing template, not new D5 content. -/
theorem pointwise {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (f g : X → Y) :
    LegacyPrimitiveRealization (pointwiseEqArena (Arena.ofFintype X) Y)
      (∀ x : X, f x = g x) (pointwiseEqRealization f g) := pointwiseEqLegacy _ _ _

/-- Evidence provider: nondegeneracy supplies a state, Nontrivial supplies outputs. -/
theorem sensitivity {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    [Nontrivial Y] (h : (Arena.ofFintype X).Nondegenerate) :
    FiniteSlotSensitivity (pointwiseEqArena (Arena.ofFintype X) Y) := by
  obtain ⟨x, _, _⟩ := Arena.exists_ne_of_nondegenerate _ h
  obtain ⟨a, b, hab⟩ := exists_pair_ne Y
  exact pointwiseEq_sensitivity _ x a b hab

/-- Arena-indexed variation, from an inhabited readout slot; no enumeration. -/
theorem variation (A : PrimitiveLawArena) (i : A.signature.Index)
    (h : FiniteSlotSensitivity A) : FiniteLawVariation A := by
  classical
  obtain ⟨r, r', _, _, hr⟩ := h.1 i
  by_cases hp : A.Law r
  · exact ⟨r, r', hp, hr.mp hp⟩
  · have hp' : A.Law r' := Classical.byContradiction (fun hn => hp (hr.mpr hn))
    exact ⟨r', r, hp', hp⟩

end LeanInformationAudit.ReifierTemplates

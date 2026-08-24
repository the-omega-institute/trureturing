/- GID: D5/S3/Observer/HiddenFlow/NormalizedHiddenAddressConservation
   generality: I
   mirror-B: D5/B/S3/Observer/HiddenFlow/NormalizedHiddenAddressConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized streamline addresses are conserved on connected time segments. -/

import D5.S3.Observer.HiddenFlow.StreamlineExistence

/- Library-search audit trail (2026-08-24):
   * Exact family hit `existsUnique_frozen_streamline_decomposition` constructs
     the canonical normalized real lift and hidden kernel element and is applied
     directly below.
   * Exact family hits `frozen_streamline_throat_component_constant` and
     `nonconstant_offset_not_continuous` respectively supply conservation of the
     constructed hidden coordinate and the independent changing-address
     obstruction; both are imported and applied rather than reconstructed.
   * Pinned Mathlib exact hits `IsPreconnected.constant`,
     `PreconnectedSpace.constant`, and
     `TotallyDisconnectedSpace.eq_of_continuous` underlie the imported rigidity
     theorem. Repository and pinned-Mathlib searches found no existing theorem
     packaging normalized existence with both public clauses.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

namespace D5.S3.Observer.HiddenFlow.NormalizedHiddenAddressConservation

open Set
open D5.S1.Dynamics
open D5.S3.Observer.StreamlineTheorem
open D5.S3.Observer.HiddenFlow.StreamlineExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- Every continuous solenoid history has unique normalized streamline data
whose canonical hidden address is constant on each connected time segment.
Moreover, under any fixed normalized visible lift, a proposed hidden offset
with two different values on such a segment cannot be continuous there. -/
theorem normalized_streamline_hidden_address_conservation
    (path : C(ℝ, UniversalSolenoid)) :
    (∃! data : C(ℝ, ℝ) × UniversalSolenoid.projection.ker,
      data.1 0 =
          D5.S1.Solenoid.StreamlineDecomposition.baseRepresentative path 0 ∧
        ∃ hReconstruct : ∀ t,
            path t = UniversalSolenoid.realFlow (data.1 t) + data.2.1,
          ∀ (segment : Set ℝ), IsPreconnected segment ->
            ∀ {first second : ℝ}, first ∈ segment -> second ∈ segment ->
              throatComponent
                  (toFrozenDecomposition path data hReconstruct) first =
                throatComponent
                  (toFrozenDecomposition path data hReconstruct) second) ∧
    (∀ (visible : C(ℝ, ℝ)) (offset : ℝ -> HiddenAddress)
        (segment : Set ℝ),
      visible 0 =
          D5.S1.Solenoid.StreamlineDecomposition.baseRepresentative path 0 ->
        IsPreconnected segment ->
        ∀ {first second : ℝ}, first ∈ segment -> second ∈ segment ->
          (∀ t ∈ segment,
            path t = UniversalSolenoid.realFlow (visible t) +
              (hiddenKernelAddEquiv (offset t)).1) ->
          offset first ≠ offset second ->
          ¬ ContinuousOn offset segment) := by
  constructor
  · rcases existsUnique_frozen_streamline_decomposition path with
      ⟨data, hdata, hunique⟩
    rcases hdata.2 with ⟨hReconstruct, hconstant⟩
    refine ⟨data, ⟨hdata.1, hReconstruct, ?_⟩, ?_⟩
    · intro segment _ first second _ _
      rw [hconstant first, hconstant second]
    · intro other hother
      rcases hother.2 with ⟨hOtherReconstruct, _⟩
      apply hunique other
      refine ⟨hother.1, hOtherReconstruct, ?_⟩
      exact frozen_streamline_throat_component_constant
        path other hOtherReconstruct
  · intro visible offset segment _ hs first second hfirst hsecond _ hdifferent
    exact nonconstant_offset_not_continuous
      hs offset hfirst hsecond hdifferent

example : C(ℝ, UniversalSolenoid) :=
  ContinuousMap.const ℝ 0

#print axioms normalized_streamline_hidden_address_conservation

end

end D5.S3.Observer.HiddenFlow.NormalizedHiddenAddressConservation

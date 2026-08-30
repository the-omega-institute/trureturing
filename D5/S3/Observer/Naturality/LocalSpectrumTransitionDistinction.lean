/- GID: D5/S3/Observer/Naturality/LocalSpectrumTransitionDistinction
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/LocalSpectrumTransitionDistinction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal local spectra can hide distinct axes related by an observer transition. -/

import D5.S3.Observer.Naturality.ObserverWorldCovariance

/- Library-search audit trail (2026-08-30):
   * `InvariantOriginRecoveryObstruction.no_absolute_origin_reconstruction`
     is the exact frozen owner for non-recovery and a distinct equal-readout pair,
     but it does not expose a transition map in its public conclusion. Its two
     required projections are derived here from the same Mathlib action primitive.
   * `ObserverWorldCovariance.observer_world_covariance` is the exact frozen
     owner for the observer-world equivalence and its transition computation
     rule, but it does not expose indistinguishable internal scalar readings.
   * Body-shape searches found no frozen theorem combining both public clauses.
     Mathlib's `MulAction.exists_smul_eq` is the supporting transitivity result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Naturality.LocalSpectrumTransitionDistinction

open D5.S3.Observer.Naturality.ObserverWorldCovariance

/-- An invariant local-spectrum readout cannot recover an absolute axis. Two
distinct axes can have the same local spectrum while the covariant observer
worlds are related by an explicit transition equivalence. -/
theorem local_spectrum_transition_distinction
    {G Axis State Output Spectrum : Type*} [Group G]
    [MulAction G Axis] [MulAction G State]
    [MulAction.IsPretransitive G Axis] [Nontrivial Axis]
    (observer : Axis -> State -> Output)
    (transport : G -> Output ≃ Output)
    (covariant : forall (g : G) (axis : Axis) (state : State),
      observer (g • axis) (g • state) = transport g (observer axis state))
    (localSpectrum : Axis -> Spectrum)
    (spectrumInvariant : forall (g : G) (axis : Axis),
      localSpectrum (g • axis) = localSpectrum axis) :
    (Not (exists locate : Spectrum -> Axis,
      Function.LeftInverse locate localSpectrum)) /\
    exists a b : Axis, exists g : G, exists worldEquiv :
        Set.range (observer a) ≃ Set.range (observer b),
      Not (a = b) /\
        localSpectrum a = localSpectrum b /\
        g • a = b /\
        forall state : State,
          (worldEquiv ⟨observer a state, ⟨state, rfl⟩⟩ : Output) =
            transport g (observer a state) := by
  have sameSpectrum : forall a b : Axis, localSpectrum a = localSpectrum b := by
    intro a b
    obtain ⟨g, action_eq⟩ := MulAction.exists_smul_eq G a b
    calc
      localSpectrum a = localSpectrum (g • a) := (spectrumInvariant g a).symm
      _ = localSpectrum b := congrArg localSpectrum action_eq
  obtain ⟨a, b, distinct⟩ := exists_pair_ne Axis
  have noDecoder : Not (exists locate : Spectrum -> Axis,
      Function.LeftInverse locate localSpectrum) := by
    rintro ⟨locate, leftInverse⟩
    apply distinct
    calc
      a = locate (localSpectrum a) := (leftInverse a).symm
      _ = locate (localSpectrum b) := congrArg locate (sameSpectrum a b)
      _ = b := leftInverse b
  obtain ⟨g, worldEquiv, axisTransition, transitionRule⟩ :=
    observer_world_covariance observer transport covariant a b
  exact
    ⟨noDecoder, a, b, g, worldEquiv, distinct, sameSpectrum a b,
      axisTransition, transitionRule⟩

#print axioms local_spectrum_transition_distinction

end D5.S3.Observer.Naturality.LocalSpectrumTransitionDistinction

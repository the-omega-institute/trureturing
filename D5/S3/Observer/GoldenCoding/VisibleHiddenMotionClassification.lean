/- GID: D5/S3/Observer/GoldenCoding/VisibleHiddenMotionClassification
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/VisibleHiddenMotionClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Solenoid connectedness and quantified visible-hidden motion classification. -/

import D5.S1.Solenoid.Connectivity.SameFiberPathOrbitCriterion
import D5.S1.Solenoid.HiddenMotionRigidity
import D5.S3.Observer.HiddenFlow.DiscreteRigidity
import D5.S3.Observer.HiddenFlow.StreamlineExistence

/- Library-search audit trail (2026-09-02):
   * Frozen `path_joined_iff_real_flow_orbit` classifies every solenoid path
     component, while `existsUnique_normalized_streamline` gives every continuous
     solenoid history a visible real lift and a constant hidden offset.
   * Frozen `prime_adic_hidden_motion_rigidity` quantifies over every continuous
     unit-interval history in the full product of prime-adic hidden addresses.
   * Frozen `nonzero_integer_action_has_no_continuous_real_extension` applies to
     every nonzero integer-address action, not only the canonical witness.
   * The current D5 tree and pinned Mathlib contain no existing theorem packaging
     connectedness, non-path-connectedness, and both exhaustive motion branches.
     Pinned Mathlib supplies the general `PathConnectedSpace` and `Joined` APIs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenCoding.VisibleHiddenMotionClassification

open Set
open D5.S1.Dynamics
open D5.S1.Solenoid.HiddenMotionRigidity
open D5.S1.Solenoid.PathOrbitClassification
open D5.S1.Solenoid.StreamlineDecomposition
open D5.S1.Solenoid.Connectivity.SameFiberPathOrbitCriterion
open D5.S3.Observer.StreamlineTheorem
open D5.S3.Observer.HiddenFlow.ContinuousRigidity
open D5.S3.Observer.HiddenFlow.DiscreteRigidity
open D5.S3.Observer.HiddenFlow.StreamlineExistence

noncomputable section

private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private theorem all_one_address_maps_to_hidden_unit :
    hiddenKernelAddEquiv (1 : HiddenAddress) = hiddenUnitOffset := by
  apply Subtype.ext
  apply Subtype.ext
  funext m
  change
    ZMod.toAddCircle
        ((D5.S3.Factorization.ProfinitePrimeDecomposition.assemble
          (fun _ => 1)).1 m) =
      (((1 : Real) / m.1 : Real) : AddCircle (1 : Real))
  have residue_is_one :
      (D5.S3.Factorization.ProfinitePrimeDecomposition.assemble
          (fun _ => 1)).1 m = 1 := by
    change
      (ZMod.equivPi m.1 m.2.ne').symm
          (fun q => @PadicInt.toZModPow q.1
            ⟨Nat.prime_of_mem_primeFactors q.2⟩
            (m.1.factorization q.1) 1) = 1
    apply (ZMod.equivPi m.1 m.2.ne').injective
    funext q
    simp
  rw [residue_is_one]
  simpa using
    (ZMod.toAddCircle_intCast (N := m.1) (1 : Int))

/-- The universal solenoid is connected but has more than one path component.
Every continuous solenoid history consists of a visible real-flow lift and one
constant hidden offset. In contrast, every genuine change between prime-adic
hidden addresses is excluded from continuous motion, canonically generates a
nonzero integer-address jump with no continuous real extension, and every
nonzero integer-address action has the same obstruction. -/
theorem universal_solenoid_visible_hidden_motion_classification :
    (ConnectedSpace UniversalSolenoid ∧
      ¬ PathConnectedSpace UniversalSolenoid) ∧
    (∀ x y : UniversalSolenoid,
      Joined x y ↔ ∃ t : Real,
        y = UniversalSolenoid.realFlow t + x) ∧
    (∀ x y : UniversalSolenoid,
      ∀ sameProjection :
          UniversalSolenoid.projection x = UniversalSolenoid.projection y,
      let hiddenDifference : UniversalSolenoid.projection.ker :=
        ⟨y - x, by
          change UniversalSolenoid.projection (y - x) = 0
          rw [map_sub, sub_eq_zero]
          exact sameProjection.symm⟩
      let hiddenCoordinate :
          UniversalSolenoid →+
            UniversalSolenoid ⧸ UniversalSolenoid.realFlowHom.range :=
        QuotientAddGroup.mk' UniversalSolenoid.realFlowHom.range
      (hiddenCoordinate x ≠ hiddenCoordinate y →
        (∃ jump : Int →+ HiddenAddress,
          jump 1 = hiddenKernelAddEquiv.symm hiddenDifference ∧
            jump ≠ 0 ∧
            ¬ ∃ flow : ContinuousAddMonoidHom Real HiddenAddress,
              flow.toAddMonoidHom.comp (Int.castAddHom Real) = jump) ∧
          ¬ Joined x y) ∧
        (Joined x y → hiddenCoordinate x = hiddenCoordinate y)) ∧
    (∀ path : C(Real, UniversalSolenoid),
      ∃! data : C(Real, Real) × UniversalSolenoid.projection.ker,
        data.1 0 = baseRepresentative path 0 ∧
          ∀ t, path t =
            UniversalSolenoid.realFlow (data.1 t) + data.2.1) ∧
    (∀ first second : HiddenAddress, first ≠ second →
      (¬ ∃ motion : unitInterval → HiddenAddress,
        Continuous motion ∧ motion 0 = first ∧ motion 1 = second) ∧
      ∃ jump : Int →+ HiddenAddress,
        jump 1 = second - first ∧ jump ≠ 0 ∧
          ¬ ∃ flow : ContinuousAddMonoidHom Real HiddenAddress,
            flow.toAddMonoidHom.comp (Int.castAddHom Real) = jump) ∧
    (∀ jump : Int →+ HiddenAddress, jump ≠ 0 →
      ¬ ∃ flow : ContinuousAddMonoidHom Real HiddenAddress,
        flow.toAddMonoidHom.comp (Int.castAddHom Real) = jump) := by
  have difference_generates_discrete_jump :
      ∀ difference : HiddenAddress, difference ≠ 0 →
        ∃ jump : Int →+ HiddenAddress,
          jump 1 = difference ∧ jump ≠ 0 ∧
            ¬ ∃ flow : ContinuousAddMonoidHom Real HiddenAddress,
              flow.toAddMonoidHom.comp (Int.castAddHom Real) = jump := by
    intro difference difference_nonzero
    let jump : Int →+ HiddenAddress :=
      zmultiplesHom HiddenAddress difference
    have jump_nonzero : jump ≠ 0 := by
      intro jump_zero
      have at_one := congrArg (fun action : Int →+ HiddenAddress => action 1)
        jump_zero
      exact difference_nonzero (by simpa [jump] using at_one)
    refine ⟨jump, by simp [jump], jump_nonzero, ?_⟩
    exact nonzero_integer_action_has_no_continuous_real_extension
      jump jump_nonzero
  let hiddenAddress : HiddenAddress := fun p => if p.1 = 2 then 0 else 1
  let hiddenOffset : UniversalSolenoid.projection.ker :=
    hiddenKernelAddEquiv hiddenAddress
  have hiddenOffset_not_joined :
      ¬ Joined (0 : UniversalSolenoid) hiddenOffset.1 := by
    intro joined
    have sameProjection :
        UniversalSolenoid.projection (0 : UniversalSolenoid) =
          UniversalSolenoid.projection hiddenOffset.1 := by
      simpa using hiddenOffset.property.symm
    rcases (same_fiber_path_orbit_criterion
        0 hiddenOffset.1 sameProjection).1 joined with
      ⟨n, hn⟩
    have offset_is_integer : hiddenOffset = n • hiddenUnitOffset := by
      apply Subtype.ext
      calc
        hiddenOffset.1 = UniversalSolenoid.realFlow (n : Real) := by
          simpa using hn
        _ = n • hiddenUnitOffset.1 := by
          simpa [UniversalSolenoid.realFlowHom, hiddenUnitOffset] using
            UniversalSolenoid.realFlowHom.map_zsmul n (1 : Real)
    change hiddenKernelAddEquiv hiddenAddress =
      n • hiddenUnitOffset at offset_is_integer
    rw [← all_one_address_maps_to_hidden_unit] at offset_is_integer
    have address_is_integer : hiddenAddress = n • (1 : HiddenAddress) := by
      simpa using congrArg hiddenKernelAddEquiv.symm offset_is_integer
    letI : Fact (Nat.Prime 2) := ⟨by decide⟩
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have at_two := congrFun address_is_integer
      (⟨2, by decide⟩ : Nat.Primes)
    have at_three := congrFun address_is_integer
      (⟨3, by decide⟩ : Nat.Primes)
    have n_is_zero : n = 0 := by
      change (0 : ℤ_[2]) = n • 1 at at_two
      apply Int.cast_injective (α := ℤ_[2])
      simpa using at_two.symm
    subst n
    change (1 : ℤ_[3]) = (0 : Int) • 1 at at_three
    norm_num at at_three
  have not_path_connected : ¬ PathConnectedSpace UniversalSolenoid := by
    intro pathConnected
    exact hiddenOffset_not_joined
      (pathConnected.joined (0 : UniversalSolenoid) hiddenOffset.1)
  refine ⟨⟨inferInstance, not_path_connected⟩,
    path_joined_iff_real_flow_orbit, ?_, ?_, ?_, ?_⟩
  · intro x y same_projection
    let hiddenDifference : UniversalSolenoid.projection.ker :=
      ⟨y - x, by
        change UniversalSolenoid.projection (y - x) = 0
        rw [map_sub, sub_eq_zero]
        exact same_projection.symm⟩
    let hiddenCoordinate :
        UniversalSolenoid →+
          UniversalSolenoid ⧸ UniversalSolenoid.realFlowHom.range :=
      QuotientAddGroup.mk' UniversalSolenoid.realFlowHom.range
    change
      (hiddenCoordinate x ≠ hiddenCoordinate y →
        (∃ jump : Int →+ HiddenAddress,
          jump 1 = hiddenKernelAddEquiv.symm hiddenDifference ∧
            jump ≠ 0 ∧
            ¬ ∃ flow : ContinuousAddMonoidHom Real HiddenAddress,
              flow.toAddMonoidHom.comp (Int.castAddHom Real) = jump) ∧
          ¬ Joined x y) ∧
        (Joined x y → hiddenCoordinate x = hiddenCoordinate y)
    have joined_same_hidden_coordinate :
        Joined x y → hiddenCoordinate x = hiddenCoordinate y := by
      intro joined
      rcases (path_joined_iff_real_flow_orbit x y).1 joined with ⟨t, rfl⟩
      rw [map_add]
      have real_flow_is_zero :
          hiddenCoordinate (UniversalSolenoid.realFlow t) = 0 := by
        change
          ((UniversalSolenoid.realFlow t : UniversalSolenoid) :
            UniversalSolenoid ⧸ UniversalSolenoid.realFlowHom.range) = 0
        rw [QuotientAddGroup.eq_zero_iff]
        exact ⟨t, rfl⟩
      rw [real_flow_is_zero, zero_add]
    refine ⟨?_, joined_same_hidden_coordinate⟩
    intro hidden_coordinates_differ
    have hidden_difference_nonzero :
        hiddenKernelAddEquiv.symm hiddenDifference ≠ 0 := by
      intro hidden_difference_zero
      have kernel_difference_zero : hiddenDifference = 0 := by
        apply hiddenKernelAddEquiv.symm.injective
        simpa using hidden_difference_zero
      have points_equal : y = x := by
        apply sub_eq_zero.mp
        simpa [hiddenDifference] using
          congrArg Subtype.val kernel_difference_zero
      exact hidden_coordinates_differ (by rw [points_equal])
    exact ⟨difference_generates_discrete_jump
        (hiddenKernelAddEquiv.symm hiddenDifference)
        hidden_difference_nonzero,
      fun joined => hidden_coordinates_differ
        (joined_same_hidden_coordinate joined)⟩
  · intro path
    exact existsUnique_normalized_streamline path 0
  · intro first second different
    constructor
    · rintro ⟨motion, continuous, starts, ends⟩
      apply different
      calc
        first = motion 0 := starts.symm
        _ = motion 1 := prime_adic_hidden_motion_rigidity motion continuous 0 1
        _ = second := ends
    · exact difference_generates_discrete_jump
        (second - first) (sub_ne_zero.mpr different.symm)
  · exact nonzero_integer_action_has_no_continuous_real_extension

#print axioms universal_solenoid_visible_hidden_motion_classification

end

end D5.S3.Observer.GoldenCoding.VisibleHiddenMotionClassification

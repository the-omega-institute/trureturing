/- GID: D5/S3/Arith/Primes/GoldenCubicOrbitClosure
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicOrbitClosure
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The native cubic Lucas omega-limit is the full profinite adding machine. -/

import D5.S3.Arith.Primes.ProfiniteObservationTopology
import D5.S3.Arith.Primes.GoldenCubicProfiniteClock

set_option autoImplicit false

/-! The actual topological closure and its cubic adding machine. -/

namespace D5.S3.Arith.Primes.GoldenCubicOrbitClosure
open WSSProfiniteClock
open GoldenCubicProfiniteClock GoldenCubicClockCofinality GoldenCubicBlockThreeAdic

instance nativeStateTopology (m : Positive) : TopologicalSpace (nativeSystem.State m) :=
  inferInstanceAs (TopologicalSpace ℤ)

instance nativeStateDiscrete (m : Positive) : DiscreteTopology (nativeSystem.State m) :=
  inferInstanceAs (DiscreteTopology ℤ)

private theorem directed (i j : Positive) : ∃ k, refinement i k ∧ refinement j k :=
  ⟨⟨i.val*j.val, Nat.mul_pos i.prop j.prop⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩

private theorem transitive {i j k : Positive} (hij : refinement i j) (hjk : refinement j k) :
    refinement i k := dvd_trans hij hjk

private theorem cofinal (m : Positive) : ∃ i, m.val ∣ period i := by
  obtain ⟨M,hM,hp⟩ := native_period_cofinal m.val m.prop
  exact ⟨⟨M,hM⟩,hp⟩

instance : Nonempty Positive := ⟨⟨1,by decide⟩⟩

/-- The actual cubic Lucas omega-limit is the full positive-modulus
profinite integer clock, in its product topology. -/
noncomputable def nativeAddingMachine : EveryClock ≃ₜ {x // x ∈ nativeSystem.omegaLimit} :=
  nativeSystem.allClockOmegaHomeomorph directed transitive cofinal

/-- One increment of absolute time is the native cubic polynomial on
each ambient residue coordinate. -/
theorem nativeAddingMachine_next (x : EveryClock) (m : Positive) :
    (nativeAddingMachine (EveryClock.next x)).val m =
      nativeUpdate m ((nativeAddingMachine x).val m) :=
  nativeSystem.allClockOmega_next_is_native directed transitive cofinal
    nativeUpdate native_observe_next x m

theorem native_full_closure :
    closure (Set.range nativeSystem.observationTuple) =
      Set.range nativeSystem.observationTuple ∪ nativeSystem.omegaLimit :=
  nativeSystem.closure_observation_range

theorem native_actual_not_in_omega (i : ℕ) :
    nativeSystem.observationTuple i ∉ nativeSystem.omegaLimit := by
  intro hi
  let x := nativeSystem.limitToFamily ⟨nativeSystem.observationTuple i,hi⟩
  obtain ⟨m,hm⟩ := finite_block_not_eventual i x
  exact hm rfl

/-- The ambient ternary coordinate of the limit is one at every
precision, even though cross-prime observation recovers all time digits. -/
theorem native_omega_three (a : ℕ) (x : {x // x ∈ nativeSystem.omegaLimit}) :
    x.val ⟨3^a,by positivity⟩ = ((1:ℤ) % (3:ℤ)^a) := by
  let m : Positive := ⟨3^a,by positivity⟩
  let y := nativeSystem.limitToFamily x
  obtain ⟨n,hn,he,_⟩ := nativeSystem.late_cone y m (a-1)
  have he3 := ternary_state_eventually_one a n hn
  change cubicBlock n % (3:ℤ)^a = (1:ℤ) % (3:ℤ)^a at he3
  change cubicBlock n % (m.val:ℤ) = x.val m at he
  simp only [m,Nat.cast_pow,Nat.cast_ofNat] at he
  exact he.symm.trans he3

abbrev FullClosure := {x // x ∈ closure (Set.range nativeSystem.observationTuple)}

noncomputable def actualReading (i : ℕ) : FullClosure :=
  ⟨nativeSystem.observationTuple i, subset_closure (Set.mem_range_self i)⟩

/-- Each finite Lucas reading is an isolated point of the full
closure, with one coordinate cylinder providing an open singleton. -/
theorem actualReading_open (i : ℕ) : IsOpen ({actualReading i} : Set FullClosure) := by
  let m : Positive := ⟨3^(i+2),by positivity⟩
  have hu (n : ℕ) (hn : nativeSystem.observe m n = nativeSystem.observe m i) : n=i := by
    apply (native_block_isolated_at_three i n).mp
    change cubicBlock n % (3:ℤ)^(i+2) = cubicBlock i % (3:ℤ)^(i+2)
    change cubicBlock n % (m.val:ℤ) = cubicBlock i % (m.val:ℤ) at hn
    simpa only [m,Nat.cast_pow,Nat.cast_ofNat] using hn
  have hs : {actualReading i} =
      {x : FullClosure | x.val m = nativeSystem.observe m i} := by
    ext x
    constructor
    · intro he
      have hx : x = actualReading i := he
      subst x
      rfl
    · intro he
      exact Subtype.ext (nativeSystem.unique_coordinate_on_closure i m hu x.prop he)
  rw [hs]
  exact (isOpen_discrete ({nativeSystem.observe m i} : Set (nativeSystem.State m))).preimage
    ((continuous_apply m).comp continuous_subtype_val)


end D5.S3.Arith.Primes.GoldenCubicOrbitClosure

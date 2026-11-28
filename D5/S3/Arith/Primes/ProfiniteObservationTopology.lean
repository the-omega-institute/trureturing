/- GID: D5/S3/Arith/Primes/ProfiniteObservationTopology
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/ProfiniteObservationTopology
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Cofinal exact finite clocks identify their actual topological omega-limit. -/

import D5.S3.Arith.Primes.ProfiniteObservationClock
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order

set_option autoImplicit false

/-! The cofinal clock equivalence respects the discrete product topology. -/

namespace WSSProfiniteClock

universe u v

open Function
open scoped Classical

instance labelsTopology {I : Type u} (P : I → ℕ) (refines : I → I → Prop) :
    TopologicalSpace (Labels P refines) :=
  TopologicalSpace.induced (Labels.value (P := P) (refines := refines)) inferInstance

variable {I : Type u} {P : I → ℕ} {refines : I → I → Prop}

theorem continuous_label_coordinate (i : I) :
    Continuous (fun x : Labels P refines => x.value i) :=
  (continuous_apply i).comp continuous_induced_dom

namespace ObservationSystem

variable (O : ObservationSystem P refines)
variable [∀ i, TopologicalSpace (O.State i)] [∀ i, DiscreteTopology (O.State i)]

def stateCoordinates (x : O.Family) : ∀ i, O.State i := fun i => (x.state i).val

instance familyTopology : TopologicalSpace O.Family :=
  TopologicalSpace.induced O.stateCoordinates inferInstance

omit [∀ i, DiscreteTopology (O.State i)] in
theorem continuous_state_coordinate (i : I) :
    Continuous (fun x : O.Family => (x.state i).val) := by
  have hc : Continuous O.stateCoordinates := continuous_induced_dom
  exact (continuous_apply i).comp hc

/-- The finite label can be evaluated as a continuous function of the
single discrete observation coordinate. -/
private noncomputable def extendedLabel (i : I) (s : O.State i) : Fin (P i) :=
  if h : ∃ n, O.threshold i ≤ n ∧ O.observe i n = s then
    TailState.label (O.positive i) (⟨s,h⟩ : TailState (O.observe i) (O.threshold i))
  else ⟨0,O.positive i⟩

omit [(i : I) → TopologicalSpace (O.State i)] [∀ i, DiscreteTopology (O.State i)] in
private theorem extendedLabel_eq (i : I) (x : O.Family) :
    O.extendedLabel i (x.state i).val = TailState.label (O.positive i) (x.state i) := by
  unfold extendedLabel
  rw [dite_eq_left (x.state i).prop]
  exact congrArg (TailState.label (O.positive i)) (Subtype.ext rfl)

variable (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
variable (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i)

/-- Cofinality gives a homeomorphism, not just a bijection. For each
coordinate of the inverse a single refining observation is sufficient. -/
noncomputable def allClockHomeomorph : EveryClock ≃ₜ O.Family where
  toEquiv := O.allClockEquiv directed cofinal
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    change Continuous (fun x : EveryClock =>
      ((TailState.equiv (O.positive i) (O.kernel i)).symm (x.value ⟨P i,O.positive i⟩)).val)
    let f (z : Fin (P i)) : O.State i := ((TailState.equiv (O.positive i) (O.kernel i)).symm z).val
    exact (continuous_of_discreteTopology (f := f)).comp
      (continuous_label_coordinate (P := fun m : Positive => m.val)
        (refines := fun m n => m.val ∣ n.val) ⟨P i,O.positive i⟩)
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro m
    let i := Classical.choose (cofinal m)
    let red (z : Fin (P i)) : Fin m.val := ⟨z.val % m.val, Nat.mod_lt _ m.prop⟩
    change Continuous (fun x : O.Family =>
      red (TailState.label (O.positive i) (x.state i)))
    have h : Continuous (fun x : O.Family => O.extendedLabel i (x.state i).val) :=
      (continuous_of_discreteTopology (f := O.extendedLabel i)).comp (O.continuous_state_coordinate i)
    simpa only [Function.comp_def, O.extendedLabel_eq] using (continuous_of_discreteTopology (f := red)).comp h


/-- Tuples of native observations at one shared time. -/
def observationTuple (n : ℕ) : ∀ i, O.State i := fun i => O.observe i n

/-- Closure of every forward tail, in the product of discrete observations. -/
def omegaLimit : Set (∀ i, O.State i) :=
  {x | ∀ B : ℕ, x ∈ closure {y | ∃ n : ℕ, B ≤ n ∧ O.observationTuple n = y}}

private theorem finite_upper [Nonempty I] (F : Finset I)
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (htrans : ∀ {i j k}, refines i j → refines j k → refines i k) :
    ∃ j, ∀ i ∈ F, refines i j := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨Classical.choice inferInstance, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨j,hj⟩ := ih
    obtain ⟨k,hik,hjk⟩ := directed i j
    refine ⟨k,?_⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · exact hu ▸ hik
    · exact htrans (hj u hu) hjk

omit [∀ i, DiscreteTopology (O.State i)] in
theorem stateCoordinates_in_omegaLimit [Nonempty I]
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (htrans : ∀ {i j k}, refines i j → refines j k → refines i k) (x : O.Family) :
    O.stateCoordinates x ∈ O.omegaLimit := by
  intro B
  rw [mem_closure_iff]
  intro U hU hx
  obtain ⟨F,V,hV,hsub⟩ := isOpen_pi_iff.mp hU (O.stateCoordinates x) hx
  obtain ⟨j,hj⟩ := finite_upper F directed htrans
  obtain ⟨n,hn,_,h⟩ := O.late_cone x j B
  refine ⟨O.observationTuple n, hsub ?_, ⟨n,hn,rfl⟩⟩
  intro i hi
  have he := h i (hj i hi)
  change O.observe i n ∈ V i
  rw [he]
  exact (hV i hi).2

private theorem limit_hits_finite (x : {x // x ∈ O.omegaLimit})
    (F : Finset I) (B : ℕ) :
    ∃ n, B ≤ n ∧ ∀ i ∈ F, O.observe i n = x.val i := by
  let U : Set (∀ i, O.State i) := (F : Set I).pi (fun i => {x.val i})
  have ho : IsOpen U :=
    isOpen_set_pi F.finite_toSet (fun _ _ => isOpen_discrete _)
  have hx : x.val ∈ U := fun _ _ => rfl
  have hc := (mem_closure_iff.mp (x.prop B)) U ho hx
  obtain ⟨y,hy,n,hn,he⟩ := hc
  subst y
  exact ⟨n,hn,fun i hi => hy i hi⟩

/-- An omega-limit point determines a compatible family of actual
eventual states. Every finite coordinate constraint can be realized late. -/
noncomputable def limitToFamily (x : {x // x ∈ O.omegaLimit}) : O.Family where
  state i := ⟨x.val i, by
    classical
    obtain ⟨n,hn,h⟩ := O.limit_hits_finite x {i} (O.threshold i)
    exact ⟨n,hn,h i (by simp)⟩⟩
  compatible {i j} h := by
    classical
    obtain ⟨n,_,hn⟩ := O.limit_hits_finite x {i,j} 0
    change O.reduce h (x.val j) = x.val i
    rw [← hn j (by simp), O.reduce_observe h, hn i (by simp)]

/-- The actual omega-limit in the product topology is exactly the
inverse limit of the finite eventual observation cycles. -/
noncomputable def familyOmegaHomeomorph [Nonempty I]
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (htrans : ∀ {i j k}, refines i j → refines j k → refines i k) :
    O.Family ≃ₜ {x // x ∈ O.omegaLimit} where
  toFun x := ⟨O.stateCoordinates x, O.stateCoordinates_in_omegaLimit directed htrans x⟩
  invFun := O.limitToFamily
  left_inv x := by
    apply Family.ext'
    intro i
    exact Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  continuous_toFun := continuous_induced_dom.subtype_mk _
  continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val

/-- A point in the full closure is either an actual observation tuple or
is in the closure of every forward tail. -/
theorem closure_observation_range :
    closure (Set.range O.observationTuple) =
      Set.range O.observationTuple ∪ O.omegaLimit := by
  ext x
  constructor
  · intro hx
    by_cases hactual : x ∈ Set.range O.observationTuple
    · exact Or.inl hactual
    · right
      intro B
      let E : Set (∀ i, O.State i) := O.observationTuple '' Set.Iio B
      let L : Set (∀ i, O.State i) := {y | ∃ n : ℕ, B ≤ n ∧ O.observationTuple n = y}
      have he : IsClosed E := ((Set.finite_Iio B).image O.observationTuple).isClosed
      have hl : Set.range O.observationTuple = E ∪ L := by
        ext y
        constructor
        · rintro ⟨n,rfl⟩
          by_cases hn : n<B
          · exact Or.inl ⟨n,hn,rfl⟩
          · exact Or.inr ⟨n,by omega,rfl⟩
        · rintro (⟨n,_,rfl⟩ | ⟨n,_,rfl⟩) <;> exact ⟨n,rfl⟩
      have hne : x ∉ E := by
        rintro ⟨n,_,he⟩
        exact hactual ⟨n,he⟩
      rw [hl, closure_union, he.closure_eq] at hx
      exact hx.resolve_left hne
  · rintro (hx | hx)
    · exact subset_closure hx
    · have h0 := hx 0
      have hsub : {y | ∃ n : ℕ, 0 ≤ n ∧ O.observationTuple n = y} ⊆
          Set.range O.observationTuple := by
        rintro y ⟨n,_,hn⟩
        exact ⟨n,hn⟩
      exact closure_mono hsub h0

/-- A coordinate which distinguishes a time from every other time
also separates that actual tuple from the omega-limit and from all
other tuples in the full closure. -/
theorem unique_coordinate_on_closure (k : ℕ) (j : I)
    (hunique : ∀ n, O.observe j n = O.observe j k → n=k)
    {x : ∀ i, O.State i} (hx : x ∈ closure (Set.range O.observationTuple))
    (he : x j = O.observe j k) : x = O.observationTuple k := by
  classical
  rw [O.closure_observation_range] at hx
  rcases hx with hx | hx
  · obtain ⟨n,rfl⟩ := hx
    rw [hunique n he]
  · obtain ⟨n,hn,hnj⟩ := O.limit_hits_finite ⟨x,hx⟩ {j} (k+1)
    have hn' := hunique n ((hnj j (by simp)).trans he)
    omega

/-- The full positive-modulus clock with its usual product topology is
homeomorphic to the actual forward omega-limit of the observations. -/
noncomputable def allClockOmegaHomeomorph [Nonempty I]
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (htrans : ∀ {i j k}, refines i j → refines j k → refines i k)
    (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i) :
    EveryClock ≃ₜ {x // x ∈ O.omegaLimit} :=
  (O.allClockHomeomorph directed cofinal).trans (O.familyOmegaHomeomorph directed htrans)

/-- Adding one in the full clock acts as the native observation update
on every coordinate of the topological omega-limit. -/
theorem allClockOmega_next_is_native [Nonempty I]
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (htrans : ∀ {i j k}, refines i j → refines j k → refines i k)
    (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i)
    (step : ∀ i, O.State i → O.State i)
    (recurrence : ∀ i n, O.observe i (n+1) = step i (O.observe i n))
    (x : EveryClock) (i : I) :
    (O.allClockOmegaHomeomorph directed htrans cofinal (EveryClock.next x)).val i =
      step i ((O.allClockOmegaHomeomorph directed htrans cofinal x).val i) := by
  change ((O.allClockEquiv directed cofinal (EveryClock.next x)).state i).val =
    step i ((O.allClockEquiv directed cofinal x).state i).val
  rw [O.allClock_next directed cofinal]
  exact O.next_is_native step recurrence (O.allClockEquiv directed cofinal x) i

end ObservationSystem
end WSSProfiniteClock

namespace D5.S3.Arith.Primes.ProfiniteObservationTopology

open WSSProfiniteClock

universe u v

/-- The full positive-modulus clock with product topology is homeomorphic
to the intersection of all actual forward tail closures. -/
noncomputable def cofinalOmegaHomeomorph {I : Type u} [Nonempty I] {P : I → ℕ}
    {refines : I → I → Prop} (O : ObservationSystem.{u,v} P refines)
    [∀ i, TopologicalSpace (O.State i)] [∀ i, DiscreteTopology (O.State i)]
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (htrans : ∀ {i j k}, refines i j → refines j k → refines i k)
    (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i) :
    EveryClock ≃ₜ {x // x ∈ O.omegaLimit} :=
  O.allClockOmegaHomeomorph directed htrans cofinal

end D5.S3.Arith.Primes.ProfiniteObservationTopology

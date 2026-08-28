/- GID: D5/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Product dynamic indistinguishability is exactly coordinatewise. -/

/- Library-search audit trail (2026-08-28):
   * The repository definitions `infiniteFutureRelation` and `FutureIndistinguishable`
     package all-time readout equality, but no existing declaration proves its product
     factorization for an arbitrary finite dependent family.
   * Pinned Mathlib supplies `Function.iterate_succ_apply'`, `Function.iterate_zero_apply`,
     `Fin.elim0`, and `Fin.eq_zero`; these are used directly below.
   * The concrete FPOD 105.1 declaration
     `all_four_premises_give_behavior_product_control` is only an M = 6, ZMod 2 x ZMod 3
     admission-product control, so it does not cover this general dynamic iff. -/

import Mathlib.Logic.Function.Iterate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementGeometry.DynamicIndistinguishabilityCoordinatewise

/-- The dependent product of a finite family of state carriers. -/
def ProductState {k : Nat} (X : Fin k → Type*) := ∀ i, X i

/-- The update obtained by applying one local update at each coordinate. -/
def coordinateUpdate {k : Nat} {X : Fin k → Type*}
    (F : ∀ i, X i → X i) : ProductState X → ProductState X :=
  fun x i => F i (x i)

/-- The readout obtained by applying one local readout at each coordinate. -/
def coordinateReadout {k : Nat} {X : Fin k → Type*} {O : Fin k → Type*}
    (q : ∀ i, X i → O i) : ProductState X → ProductState O :=
  fun x i => q i (x i)

/-- Two states are dynamically indistinguishable when every finite-time readout agrees. -/
def DynamicIndistinguishable {Y O : Type*} (F : Y → Y) (q : Y → O)
    (x y : Y) : Prop :=
  ∀ n : Nat, q ((F^[n]) x) = q ((F^[n]) y)

/-- A product update depends on one input coordinate at each output coordinate. -/
def UpdateActsFactorwise {k : Nat} {X : Fin k → Type*}
    (F : ProductState X → ProductState X) : Prop :=
  ∃ locals : ∀ i, X i → X i, ∀ x i, F x i = locals i (x i)

/-- A product readout depends on one input coordinate at each output coordinate. -/
def ReadoutActsFactorwise {k : Nat} {X : Fin k → Type*} {O : Fin k → Type*}
    (q : ProductState X → ProductState O) : Prop :=
  ∃ locals : ∀ i, X i → O i, ∀ x i, q x i = locals i (x i)

private theorem coordinateUpdate_iterate_apply
    {k : Nat} {X : Fin k → Type*} (F : ∀ i, X i → X i)
    (n : Nat) (x : ProductState X) (i : Fin k) :
    ((coordinateUpdate F)^[n]) x i = ((F i)^[n]) (x i) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg (F i) (ih x)

/-- Dynamic indistinguishability on a finite independent product is exactly the
coordinatewise conjunction of the local dynamic indistinguishabilities. -/
theorem dynamic_indistinguishability_iff_coordinatewise
    {k : Nat} {X : Fin k → Type*} {O : Fin k → Type*}
    (F : ∀ i, X i → X i) (q : ∀ i, X i → O i)
    (x y : ProductState X) :
    DynamicIndistinguishable (coordinateUpdate F) (coordinateReadout q) x y ↔
      ∀ i, DynamicIndistinguishable (F i) (q i) (x i) (y i) := by
  constructor
  · intro h i n
    have hAt := h n
    have hCoordinate := congrFun hAt i
    simpa [coordinateReadout, coordinateUpdate_iterate_apply] using hCoordinate
  · intro h n
    funext i
    have hCoordinate := h i n
    simpa [coordinateReadout, coordinateUpdate_iterate_apply] using hCoordinate

#print axioms dynamic_indistinguishability_iff_coordinatewise

private def crossBooleanReadout : ProductState (fun _ : Fin 2 => Bool) →
    ProductState (fun _ : Fin 2 => Bool) :=
  fun state _ => state 0

private def booleanStateA : ProductState (fun _ : Fin 2 => Bool) :=
  fun _ => false

private def booleanStateB : ProductState (fun _ : Fin 2 => Bool) :=
  fun i => decide (i = 0)

private theorem crossBooleanReadout_not_factorwise :
    ¬ReadoutActsFactorwise crossBooleanReadout := by
  intro h
  rcases h with ⟨locals, hlocal⟩
  have hEqual : crossBooleanReadout booleanStateA 1 =
      crossBooleanReadout booleanStateB 1 := by
    calc
      crossBooleanReadout booleanStateA 1 = locals 1 (booleanStateA 1) :=
        hlocal booleanStateA 1
      _ = locals 1 (booleanStateB 1) := by
        simp [booleanStateA, booleanStateB]
      _ = crossBooleanReadout booleanStateB 1 := (hlocal booleanStateB 1).symm
  simpa [crossBooleanReadout, booleanStateA, booleanStateB] using hEqual

/-- Without a factorwise readout, locally constant observations can hide a
cross-coordinate global observation. -/
theorem readout_factorwise_is_necessary :
    UpdateActsFactorwise (id : ProductState (fun _ : Fin 2 => Bool) →
      ProductState (fun _ : Fin 2 => Bool)) ∧
      ¬ReadoutActsFactorwise crossBooleanReadout ∧
      ¬(DynamicIndistinguishable (id : ProductState (fun _ : Fin 2 => Bool) →
          ProductState (fun _ : Fin 2 => Bool)) crossBooleanReadout
          booleanStateA booleanStateB ↔
        ∀ i : Fin 2,
          DynamicIndistinguishable (id : Bool → Bool) (fun _ => false)
            (booleanStateA i) (booleanStateB i)) := by
  have hUpdate :
      UpdateActsFactorwise (id : ProductState (fun _ : Fin 2 => Bool) →
        ProductState (fun _ : Fin 2 => Bool)) := by
    refine ⟨fun _ => id, ?_⟩
    intro state i
    rfl
  have hLocal :
      ∀ i : Fin 2,
        DynamicIndistinguishable (id : Bool → Bool) (fun _ => false)
          (booleanStateA i) (booleanStateB i) := by
    intro i n
    simp [DynamicIndistinguishable]
  have hGlobal :
      ¬DynamicIndistinguishable (id : ProductState (fun _ : Fin 2 => Bool) →
        ProductState (fun _ : Fin 2 => Bool)) crossBooleanReadout
        booleanStateA booleanStateB := by
    intro h
    have hAt := h 0
    have hCoordinate := congrFun hAt 0
    simpa [DynamicIndistinguishable, crossBooleanReadout,
      booleanStateA, booleanStateB] using hCoordinate
  refine ⟨hUpdate, crossBooleanReadout_not_factorwise, ?_⟩
  intro hiff
  exact hGlobal (hiff.mpr hLocal)

private def hiddenStateA : ProductState (fun _ : Fin 2 => Bool × Bool) :=
  fun _ => (false, false)

private def hiddenStateB : ProductState (fun _ : Fin 2 => Bool × Bool) :=
  fun i => (false, decide (i = 0))

private def hiddenCrossUpdate :
    ProductState (fun _ : Fin 2 => Bool × Bool) →
      ProductState (fun _ : Fin 2 => Bool × Bool) :=
  fun state i =>
    if i = 1 then ((state 0).2, (state 1).2) else state i

private def firstCoordinateReadout :
    ProductState (fun _ : Fin 2 => Bool × Bool) →
      ProductState (fun _ : Fin 2 => Bool) :=
  fun state i => (state i).1

private theorem firstCoordinateReadout_factorwise :
    ReadoutActsFactorwise firstCoordinateReadout := by
  refine ⟨fun _ state => state.1, ?_⟩
  intro state i
  rfl

private theorem hiddenCrossUpdate_not_factorwise :
    ¬UpdateActsFactorwise hiddenCrossUpdate := by
  intro h
  rcases h with ⟨locals, hlocal⟩
  have hEqual : hiddenCrossUpdate hiddenStateA 1 =
      hiddenCrossUpdate hiddenStateB 1 := by
    calc
      hiddenCrossUpdate hiddenStateA 1 = locals 1 (hiddenStateA 1) :=
        hlocal hiddenStateA 1
      _ = locals 1 (hiddenStateB 1) := by
        simp [hiddenStateA, hiddenStateB]
      _ = hiddenCrossUpdate hiddenStateB 1 := (hlocal hiddenStateB 1).symm
  have hFirst := congrArg Prod.fst hEqual
  simpa [hiddenCrossUpdate, hiddenStateA, hiddenStateB] using hFirst

/-- Without a factorwise update, hidden local states can become globally visible
after one step even when the product readout is factorwise. -/
theorem update_factorwise_is_necessary :
    ReadoutActsFactorwise firstCoordinateReadout ∧
      ¬UpdateActsFactorwise hiddenCrossUpdate ∧
      ¬(DynamicIndistinguishable hiddenCrossUpdate firstCoordinateReadout
          hiddenStateA hiddenStateB ↔
        ∀ i : Fin 2,
          DynamicIndistinguishable (id : Bool × Bool → Bool × Bool)
            (fun state => state.1) (hiddenStateA i) (hiddenStateB i)) := by
  have hLocal :
      ∀ i : Fin 2,
        DynamicIndistinguishable (id : Bool × Bool → Bool × Bool)
          (fun state => state.1) (hiddenStateA i) (hiddenStateB i) := by
    intro i n
    simp [DynamicIndistinguishable, hiddenStateA, hiddenStateB]
  have hGlobal :
      ¬DynamicIndistinguishable hiddenCrossUpdate firstCoordinateReadout
        hiddenStateA hiddenStateB := by
    intro h
    have hAt := h 1
    have hCoordinate := congrFun hAt 1
    simpa [DynamicIndistinguishable, hiddenCrossUpdate, firstCoordinateReadout,
      hiddenStateA, hiddenStateB] using hCoordinate
  refine ⟨firstCoordinateReadout_factorwise, hiddenCrossUpdate_not_factorwise, ?_⟩
  intro hiff
  exact hGlobal (hiff.mpr hLocal)

#print axioms readout_factorwise_is_necessary
#print axioms update_factorwise_is_necessary

/- Empty-index audit: the product state and product readout are both singletons,
so the global relation and the vacuous coordinatewise relation are true. -/
example (x y : ProductState (fun _ : Fin 0 => Unit)) :
    DynamicIndistinguishable
        (coordinateUpdate (fun _ : Fin 0 => (id : Unit → Unit)))
        (coordinateReadout (fun _ : Fin 0 => (id : Unit → Unit))) x y := by
  intro n
  funext i
  exact Fin.elim0 i

example (x y : ProductState (fun _ : Fin 0 => Unit)) :
    ∀ i : Fin 0,
      DynamicIndistinguishable (id : Unit → Unit) (id : Unit → Unit)
        (x i) (y i) := by
  intro i
  exact Fin.elim0 i

/- Single-factor audit: for Fin 1, the coordinate conjunction is just the sole
coordinate, so the general iff has the expected identity shape. -/
example {X O : Fin 1 → Type*} (F : ∀ i, X i → X i) (q : ∀ i, X i → O i)
    (x y : ProductState X) :
    (∀ i : Fin 1,
      DynamicIndistinguishable (F i) (q i) (x i) (y i)) ↔
      DynamicIndistinguishable (F 0) (q 0) (x 0) (y 0) := by
  constructor
  · intro h
    exact h 0
  · intro h i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h

/- Constant-readout audit: a constant coordinate contributes no restriction at
any time, while the remaining coordinates are still governed by their readouts. -/
example (a b : Bool) :
    DynamicIndistinguishable (id : Bool → Bool) (fun _ => false) a b := by
  intro n
  rfl

/- Identity-update audit: all-time indistinguishability collapses to the current
readout equality. -/
example {Y O : Type*} (q : Y → O) (x y : Y) :
    DynamicIndistinguishable (id : Y → Y) q x y ↔ q x = q y := by
  constructor
  · intro h
    simpa [DynamicIndistinguishable] using h 0
  · intro h n
    simpa [DynamicIndistinguishable, h]

/- Empty and singleton carrier audit: there are no states in the first case,
and the singleton state has equal observations for every update and readout. -/
example (F : Empty → Empty) (q : Empty → Unit) :
    ∀ x y : Empty, DynamicIndistinguishable F q x y := by
  intro x
  exact Empty.elim x

example (F : Unit → Unit) (q : Unit → Unit) :
    DynamicIndistinguishable F q () () := by
  intro n
  rfl

/- Zero-map and n=0 audit: the constant zero update/readout has equal output at
time zero and at every later time. -/
example (x y : Nat) :
    DynamicIndistinguishable (fun _ : Nat => 0) (fun _ : Nat => 0) x y := by
  intro n
  rfl

example {Y O : Type*} (F : Y → Y) (q : Y → O) (x y : Y)
    (h0 : q x = q y) :
    q ((F^[0]) x) = q ((F^[0]) y) := by
  simpa using h0

/- The proof is valid for any finite index family; no primality or prime-power
assumption occurs in the definitions or theorem. -/

end D5.S3.ConceptDynamics.RefinementGeometry.DynamicIndistinguishabilityCoordinatewise

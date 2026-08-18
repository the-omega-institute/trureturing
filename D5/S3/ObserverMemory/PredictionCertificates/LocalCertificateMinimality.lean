/- GID: D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local pair-distance checks certify the canonical minimal predictive quotient. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-18):
   * Repository search found the exact state-count universal property
     `controlled_behavior_universal_property`; it is specialized and applied below.
   * Pinned Mathlib supplies `Setoid.quotientKerEquivOfSurjective`,
     `Fintype.card_congr`, and `Asymptotics.isBigO_refl`; each exact declaration
     is applied below.
   * Repository and pinned-Mathlib searches found no theorem packaging the local
     distance recurrence, quotient identification, depth equality, minimality,
     and quadratic verification bound in one result.
   * `loogle` and `leansearch` executables are absent from PATH. -/

namespace D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

open Filter
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The recursively checkable assertion that `n` is the first future time at
which the two readouts disagree. -/
def FirstMismatch {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :
    Y -> Y -> Nat -> Prop
  | y, y', 0 => q y ≠ q y'
  | y, y', n + 1 =>
      q y = q y' ∧ FirstMismatch tau q (tau y) (tau y') n

/-- The two local table checks: a current mismatch has distance zero, while a
current match inherits the successor of the next-pair distance. `none` is the
infinite value. -/
def LocalDistanceChecks {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (delta : Y -> Y -> Option Nat) : Prop :=
  ∀ y y',
    (q y ≠ q y' -> delta y y' = some 0) ∧
      (q y = q y' ->
        delta y y' = Option.map Nat.succ (delta (tau y) (tau y')))

/-- The canonical shortest-distance table determined by first-mismatch
certificates. -/
noncomputable def shortestDistance {Y O : Type*} (tau : Y -> Y)
    (q : Y -> O) (y y' : Y) : Option Nat :=
  by
    classical
    exact if h : ∃ n, FirstMismatch tau q y y' n then some (Nat.find h) else none

/-- The maximum finite entry of the canonical distance table, with `none`
contributing zero as in the constant-readout convention. -/
noncomputable def stabilityDepth {Y O : Type*} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) : Nat := by
  classical
  exact Finset.univ.sup fun pair : Y × Y =>
    (shortestDistance tau q pair.1 pair.2).getD 0

/-- The maximum finite entry claimed by a supplied certificate. -/
def certificateDepth {Y : Type*} [Fintype Y]
    (delta : Y -> Y -> Option Nat) : Nat := by
  classical
  exact Finset.univ.sup fun pair : Y × Y => (delta pair.1 pair.2).getD 0

/-- The canonical predictive completion: states modulo equality of their full
future readout itineraries. -/
abbrev PredictiveCompletion {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :=
  Quotient (Setoid.ker (completeItinerary tau q))

/-- State-count minimality among finite surjective deterministic realizations
that preserve both transition and readout. -/
def MinimalStateCount {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (C : Type*) [Fintype C] : Prop :=
  ∀ (W : Type*) [Fintype W]
    (realization : Y -> W) (realizedUpdate : W -> W)
    (realizedReadout : W -> O),
    Function.Surjective realization ->
      realization ∘ tau = realizedUpdate ∘ realization ->
      q = realizedReadout ∘ realization ->
      Fintype.card C <= Fintype.card W

/-- A cell-by-cell local verifier examines the square table once. -/
def certificateCheckWork (n : Nat) : Real := (n : Real) ^ 2

private theorem option_map_succ_eq_some (value : Option Nat) (n : Nat) :
    Option.map Nat.succ value = some (n + 1) ↔ value = some n := by
  cases value <;> simp

private theorem option_map_succ_ne_zero (value : Option Nat) :
    Option.map Nat.succ value ≠ some 0 := by
  cases value <;> simp

/-- The local recurrence assigns `some n` exactly at a first-mismatch
certificate of length `n`. -/
theorem local_distance_some_iff {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (delta : Y -> Y -> Option Nat) (checks : LocalDistanceChecks tau q delta)
    (y y' : Y) (n : Nat) :
    delta y y' = some n ↔ FirstMismatch tau q y y' n := by
  induction n generalizing y y' with
  | zero =>
      constructor
      · intro hdelta
        by_contra hnot
        have heq : q y = q y' := of_not_not hnot
        rw [(checks y y').2 heq] at hdelta
        exact option_map_succ_ne_zero _ hdelta
      · intro hmismatch
        exact (checks y y').1 hmismatch
  | succ n ih =>
      constructor
      · intro hdelta
        have heq : q y = q y' := by
          by_contra hne
          have hzero := (checks y y').1 hne
          rw [hzero] at hdelta
          simp at hdelta
        refine ⟨heq, ?_⟩
        have hrec := (checks y y').2 heq
        rw [hrec, option_map_succ_eq_some] at hdelta
        exact (ih (tau y) (tau y')).mp hdelta
      · rintro ⟨heq, hnext⟩
        rw [(checks y y').2 heq, option_map_succ_eq_some]
        exact (ih (tau y) (tau y')).mpr hnext

private theorem first_mismatch_unique {Y O : Type*} (tau : Y -> Y)
    (q : Y -> O) {y y' : Y} {m n : Nat}
    (hm : FirstMismatch tau q y y' m)
    (hn : FirstMismatch tau q y y' n) : m = n := by
  induction m generalizing y y' n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [FirstMismatch] at hm hn
          exact False.elim (hm hn.1)
  | succ m ih =>
      cases n with
      | zero =>
          simp only [FirstMismatch] at hm hn
          exact False.elim (hn hm.1)
      | succ n =>
          simp only [FirstMismatch] at hm hn
          exact congrArg Nat.succ (ih hm.2 hn.2)

private theorem complete_itinerary_shift {Y O : Type*} (tau : Y -> Y)
    (q : Y -> O) (y : Y) (n : Nat) :
    completeItinerary tau q (tau y) n =
      completeItinerary tau q y (n + 1) := by
  simp [completeItinerary, Function.iterate_succ_apply]

private theorem first_mismatch_distinguishes {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) {y y' : Y} {n : Nat}
    (h : FirstMismatch tau q y y' n) :
    completeItinerary tau q y n ≠ completeItinerary tau q y' n := by
  induction n generalizing y y' with
  | zero => simpa [FirstMismatch, completeItinerary] using h
  | succ n ih =>
      simp only [FirstMismatch] at h
      rw [← complete_itinerary_shift tau q y n,
        ← complete_itinerary_shift tau q y' n]
      exact ih h.2

private theorem exists_first_mismatch_of_distinguishes_at {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) {y y' : Y} {n : Nat}
    (h : completeItinerary tau q y n ≠ completeItinerary tau q y' n) :
    ∃ k, FirstMismatch tau q y y' k := by
  induction n generalizing y y' with
  | zero =>
      refine ⟨0, ?_⟩
      simpa [FirstMismatch, completeItinerary] using h
  | succ n ih =>
      by_cases hnow : q y ≠ q y'
      · exact ⟨0, hnow⟩
      · have heq : q y = q y' := of_not_not hnow
        have hnext :
            completeItinerary tau q (tau y) n ≠
              completeItinerary tau q (tau y') n := by
          simpa only [complete_itinerary_shift] using h
        rcases ih hnext with ⟨k, hk⟩
        exact ⟨k + 1, ⟨heq, hk⟩⟩

/-- Infinite certified distance is exactly equality of complete future
itineraries. -/
theorem shortest_distance_eq_none_iff {Y O : Type*} (tau : Y -> Y)
    (q : Y -> O) (y y' : Y) :
    shortestDistance tau q y y' = none ↔
      completeItinerary tau q y = completeItinerary tau q y' := by
  classical
  constructor
  · intro hnone
    by_contra hne
    rcases Function.ne_iff.mp hne with ⟨n, hn⟩
    rcases exists_first_mismatch_of_distinguishes_at tau q hn with ⟨k, hk⟩
    have hexists : ∃ k, FirstMismatch tau q y y' k := ⟨k, hk⟩
    simp [shortestDistance, hexists] at hnone
  · intro heq
    rw [shortestDistance]
    split_ifs with hexists
    · rcases hexists with ⟨n, hn⟩
      exact False.elim
        (first_mismatch_distinguishes tau q hn (congrFun heq n))
    · rfl

/-- A locally valid distance table is the canonical shortest-distance table. -/
theorem local_distance_eq_shortest {Y O : Type*} (tau : Y -> Y)
    (q : Y -> O) (delta : Y -> Y -> Option Nat)
    (checks : LocalDistanceChecks tau q delta) :
    delta = fun y y' => shortestDistance tau q y y' := by
  classical
  funext y y'
  cases hdelta : delta y y' with
  | none =>
      have hno : ¬∃ n, FirstMismatch tau q y y' n := by
        rintro ⟨n, hn⟩
        have := (local_distance_some_iff tau q delta checks y y' n).mpr hn
        rw [hdelta] at this
        simp at this
      simp [shortestDistance, hno]
  | some n =>
      have hn := (local_distance_some_iff tau q delta checks y y' n).mp hdelta
      have hexists : ∃ k, FirstMismatch tau q y y' k := ⟨n, hn⟩
      have hfind : Nat.find hexists = n :=
        first_mismatch_unique tau q (Nat.find_spec hexists) hn
      simp [shortestDistance, hexists, hfind]

/-- A surjective labelling with the same kernel as an observation map is
canonically equivalent to that map's kernel quotient. -/
noncomputable def quotientEquivOfExactKernel {Y C L : Type*}
    (label : Y -> C) (observe : Y -> L)
    (label_surjective : Function.Surjective label)
    (same_kernel : ∀ y y', label y = label y' ↔ observe y = observe y') :
    C ≃ Quotient (Setoid.ker observe) := by
  have hker : Setoid.ker label = Setoid.ker observe := Setoid.ext same_kernel
  rw [← hker]
  exact (Setoid.quotientKerEquivOfSurjective label label_surjective).symm

private theorem run_unit_word {Y : Type*} (tau : Y -> Y)
    (word : List Unit) (y : Y) :
    runWord (fun _ : Unit => tau) word y = (tau^[word.length]) y := by
  induction word generalizing y with
  | nil => rfl
  | cons head tail ih =>
      simp only [runWord, List.length_cons]
      rw [ih, Function.iterate_succ_apply]

private theorem complete_kernel_iff_controlled_kernel {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (y y' : Y) :
    completeItinerary tau q y = completeItinerary tau q y' ↔
      controlledBehavior (fun _ : Unit => tau) q y =
        controlledBehavior (fun _ : Unit => tau) q y' := by
  constructor
  · intro hitinerary
    funext word
    simpa [controlledBehavior, run_unit_word, completeItinerary] using
      congrFun hitinerary word.length
  · intro hbehavior
    funext n
    have hcoordinate := congrFun hbehavior (List.replicate n ())
    simpa [controlledBehavior, run_unit_word, completeItinerary] using hcoordinate

/-- Local distance and fibre checks imply the whole global certificate:
fibres are complete-future classes, the quotient transition is well-defined,
the labelled carrier is the predictive completion, its depth is exact, its
state count is minimal among exact deterministic realizations, and a table
scan has quadratic asymptotic work. -/
theorem local_certificate_global_minimality
    {Y O C : Type*} [Fintype Y] [Fintype C]
    (tau : Y -> Y) (q : Y -> O) (label : Y -> C)
    (delta : Y -> Y -> Option Nat)
    (label_surjective : Function.Surjective label)
    (fiber_check : ∀ y y', label y = label y' ↔ delta y y' = none)
    (distance_checks : LocalDistanceChecks tau q delta) :
    (∀ y y', label y = label y' ↔
      completeItinerary tau q y = completeItinerary tau q y') ∧
    (∃ quotientUpdate : C -> C,
      ∀ y, quotientUpdate (label y) = label (tau y)) ∧
    Nonempty (C ≃ PredictiveCompletion tau q) ∧
    certificateDepth delta = stabilityDepth tau q ∧
    MinimalStateCount tau q C ∧
    (fun n : Nat => certificateCheckWork n) =O[atTop]
      (fun n : Nat => (n : Real) ^ 2) := by
  classical
  have hdelta : delta = fun y y' => shortestDistance tau q y y' :=
    local_distance_eq_shortest tau q delta distance_checks
  have hcomplete : ∀ y y', label y = label y' ↔
      completeItinerary tau q y = completeItinerary tau q y' := by
    intro y y'
    rw [fiber_check, congrFun (congrFun hdelta y) y',
      shortest_distance_eq_none_iff]
  have hupdate_respects : ∀ {y y' : Y}, label y = label y' ->
      label (tau y) = label (tau y') := by
    intro y y' hlabel
    apply (hcomplete (tau y) (tau y')).mpr
    have hitinerary := (hcomplete y y').mp hlabel
    funext n
    rw [complete_itinerary_shift, complete_itinerary_shift]
    exact congrFun hitinerary (n + 1)
  let representative : C -> Y :=
    Classical.choose label_surjective.hasRightInverse
  have representative_right : Function.RightInverse representative label :=
    Classical.choose_spec label_surjective.hasRightInverse
  let quotientUpdate : C -> C :=
    fun state => label (tau (representative state))
  have hquotientUpdate : ∀ y,
      quotientUpdate (label y) = label (tau y) := by
    intro y
    exact hupdate_respects (representative_right (label y))
  have hcompletionEquiv : C ≃ PredictiveCompletion tau q :=
    quotientEquivOfExactKernel label (completeItinerary tau q)
      label_surjective hcomplete
  have hdepth : certificateDepth delta = stabilityDepth tau q := by
    simp only [certificateDepth, stabilityDepth]
    rw [hdelta]
  have hcontrolled : ∀ y y', label y = label y' ↔
      controlledBehavior (fun _ : Unit => tau) q y =
        controlledBehavior (fun _ : Unit => tau) q y' := by
    intro y y'
    exact (hcomplete y y').trans
      (complete_kernel_iff_controlled_kernel tau q y y')
  have hcontrolledEquiv :
      C ≃ ControlledCompletion (fun _ : Unit => tau) q :=
    quotientEquivOfExactKernel label
      (controlledBehavior (fun _ : Unit => tau) q)
      label_surjective hcontrolled
  have hminimal : MinimalStateCount tau q C := by
    intro W instW realization realizedUpdate realizedReadout
      realization_surjective updates_commute readouts_commute
    letI : Fintype W := instW
    have hcanonical :=
      (controlled_behavior_universal_property
        (fun _ : Unit => tau) q realization
        (fun _ : Unit => realizedUpdate) realizedReadout
        realization_surjective (fun _ => updates_commute) readouts_commute).2
    exact (Fintype.card_congr hcontrolledEquiv).trans_le hcanonical
  have hwork : (fun n : Nat => certificateCheckWork n) =O[atTop]
      (fun n : Nat => (n : Real) ^ 2) := by
    simpa [certificateCheckWork] using
      (Asymptotics.isBigO_refl
        (fun n : Nat => (n : Real) ^ 2) atTop)
  exact ⟨hcomplete, ⟨quotientUpdate, hquotientUpdate⟩,
    ⟨hcompletionEquiv⟩, hdepth, hminimal, hwork⟩

/-- The certificate hypotheses have a concrete finite model. -/
example :
    let tau : Unit -> Unit := id
    let q : Unit -> Unit := id
    let delta : Unit -> Unit -> Option Nat := fun _ _ => none
    LocalDistanceChecks tau q delta := by
  simp [LocalDistanceChecks]

#print axioms local_certificate_global_minimality

end D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

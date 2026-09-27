/- GID: D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite predictors correspond to invariant covers with bounded future diameter. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Topology.MetricSpace.Basic

namespace D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)

/-- All words, including the empty word, must be predicted from the initialized
machine state. Neither a clock nor a fresh observation is an update argument. -/
def HasFinitePredictor {X A Y : Type*} [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (ε : ℝ) (s : ℕ) : Prop :=
  ∃ (S : Type) (finiteS : Fintype S),
    Nonempty S ∧ @Fintype.card S finiteS ≤ s ∧
      ∃ (e : X → S) (G : A → S → S) (h : S → Y),
        ∀ x w, dist (h (runWord G w (e x))) (o (runWord F w x)) ≤ ε

/-- A cover with one deterministic successor per action and index. Its members
can overlap. The extended supremum makes the radius meaningful without a
prior boundedness assumption. -/
structure IsInvariantCover {X A Y I : Type*} [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (ε : ℝ)
    (C : I → Set X) (δ : A → I → I) (y : I → Y) : Prop where
  nonempty : ∀ i, (C i).Nonempty
  covers : ∀ x, ∃ i, x ∈ C i
  successor : ∀ a i, Set.MapsTo (F a) (C i) (C (δ a i))
  radius : ∀ i, (⨆ x : C i, edist (o x) (y i)) ≤ ENNReal.ofReal ε

/-- Existence of at most `s` nonempty members with deterministic successors. -/
def HasFiniteInvariantCover {X A Y : Type*} [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (ε : ℝ) (s : ℕ) : Prop :=
  ∃ (I : Type) (finiteI : Fintype I),
    Nonempty I ∧ @Fintype.card I finiteI ≤ s ∧
      ∃ (C : I → Set X) (δ : A → I → I) (y : I → Y),
        IsInvariantCover F o ε C δ y

/-- Uniform distance between the observations of all future controlled words. -/
noncomputable def futureDistance {X A Y : Type*} [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (x x' : X) : ENNReal :=
  ⨆ w : List A, edist (o (runWord F w x)) (o (runWord F w x'))

/-- Finite full-future prediction is equivalent to a finite deterministic
forward-invariant cover. Every such cover has future diameter at most twice
the error, including covers unrelated to a chosen predictor. -/
theorem finite_predictor_iff_forward_invariant_cover
    {X A Y : Type*} [Nonempty X] [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (ε : ℝ) (hε : 0 ≤ ε)
    (s : ℕ) (_hs : 1 ≤ s) :
    (HasFinitePredictor F o ε s ↔ HasFiniteInvariantCover F o ε s) ∧
      (∀ (I : Type) (C : I → Set X) (δ : A → I → I) (y : I → Y),
        IsInvariantCover F o ε C δ y →
          ∀ i x, x ∈ C i → ∀ x', x' ∈ C i →
            futureDistance F o x x' ≤ ENNReal.ofReal (2 * ε)) := by
  classical
  have word_mem (I : Type) (C : I → Set X) (δ : A → I → I) (y : I → Y)
      (hc : IsInvariantCover F o ε C δ y) :
      ∀ w i x, x ∈ C i → runWord F w x ∈ C (runWord δ w i) := by
    intro w
    induction w with
    | nil => exact fun _ _ hx => hx
    | cons a w ih =>
        intro i x hx
        exact ih (δ a i) (F a x) (hc.successor a i hx)
  have point_radius (I : Type) (C : I → Set X) (δ : A → I → I) (y : I → Y)
      (hc : IsInvariantCover F o ε C δ y) (i : I) (x : X) (hx : x ∈ C i) :
      edist (o x) (y i) ≤ ENNReal.ofReal ε :=
    (le_iSup (fun z : C i => edist (o z) (y i)) ⟨x, hx⟩).trans (hc.radius i)
  constructor
  · constructor
    · rintro ⟨S, finiteS, _hne, hcard, e, G, h, herr⟩
      let : Fintype S := finiteS
      let C : S → Set X := fun i =>
        {z | ∃ x w, runWord F w x = z ∧ runWord G w (e x) = i}
      have snoc : ∀ (w : List A) (x : X) (q : S) (a : A),
          runWord F (w ++ [a]) x = F a (runWord F w x) ∧
          runWord G (w ++ [a]) q = G a (runWord G w q) := by
        intro w
        induction w with
        | nil => exact fun _ _ _ => ⟨rfl, rfl⟩
        | cons b w ih => exact fun x q a => ih (F b x) (G b q) a
      have step (a : A) (i : S) : Set.MapsTo (F a) (C i) (C (G a i)) := by
        rintro z ⟨x, w, rfl, hi⟩
        exact ⟨x, w ++ [a], (snoc w x (e x) a).1,
          (snoc w x (e x) a).2.trans (congrArg (G a) hi)⟩
      let R := {i : S // (C i).Nonempty}
      let δ : A → R → R := fun a i =>
        ⟨G a i, i.property.image (F a) |>.mono (Set.image_subset_iff.mpr (step a i))⟩
      let x₀ : X := Classical.choice inferInstance
      have reach_initial (x : X) : x ∈ C (e x) := ⟨x, [], rfl, rfl⟩
      refine ⟨R, inferInstance, ⟨⟨e x₀, x₀, reach_initial x₀⟩⟩,
        (Fintype.card_subtype_le _).trans hcard,
        (fun i => C i.val), δ, (fun i => h i.val), ?_⟩
      constructor
      · exact fun i => i.property
      · exact fun x => ⟨⟨e x, x, reach_initial x⟩, reach_initial x⟩
      · exact fun a i => step a i.val
      · intro i
        apply iSup_le
        rintro ⟨z, x, w, rfl, hi⟩
        apply (edist_le_ofReal hε).2
        change dist (o (runWord F w x)) (h i.val) ≤ ε
        rw [← hi, dist_comm]
        exact herr x w
    · rintro ⟨I, finiteI, hne, hcard, C, δ, y, hc⟩
      let e : X → I := fun x => Classical.choose (hc.covers x)
      refine ⟨I, finiteI, hne, hcard, e, δ, y, ?_⟩
      intro x w
      rw [dist_comm]
      apply (edist_le_ofReal hε).1
      exact point_radius I C δ y hc _ _
        (word_mem I C δ y hc w (e x) x (Classical.choose_spec (hc.covers x)))
  · intro I C δ y hc i x hx x' hx'
    apply iSup_le
    intro w
    calc
      edist (o (runWord F w x)) (o (runWord F w x')) ≤
          edist (o (runWord F w x)) (y (runWord δ w i)) +
          edist (y (runWord δ w i)) (o (runWord F w x')) := edist_triangle _ _ _
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := by
        apply add_le_add
        · exact point_radius I C δ y hc _ _ (word_mem I C δ y hc w i x hx)
        · rw [edist_comm]
          exact point_radius I C δ y hc _ _ (word_mem I C δ y hc w i x' hx')
      _ = ENNReal.ofReal (2 * ε) := by rw [← ENNReal.ofReal_add hε hε, two_mul]

#print axioms finite_predictor_iff_forward_invariant_cover

end D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover

/- GID: D5/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite operational quotient admits a finite protocol certificate even for an infinite protocol family. -/

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Image

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionCertificates.FiniteDistinguishingCertificate

theorem finite_distinguishing_certificate
    {X Protocol Observation Class : Type*} [Finite Class]
    (evaluate : Protocol → X → Observation) (available : Set Protocol)
    (classify : X → Class) (classify_surjective : Function.Surjective classify)
    (class_exact : ∀ x y,
      classify x = classify y ↔
        ∀ protocol ∈ available, evaluate protocol x = evaluate protocol y) :
    ∃ selected : Finset Protocol,
      (selected : Set Protocol) ⊆ available ∧
        ∀ x y, classify x = classify y ↔
          ∀ protocol ∈ selected, evaluate protocol x = evaluate protocol y := by
  classical
  letI := Fintype.ofFinite Class
  let representative : Class → X := fun c => Classical.choose (classify_surjective c)
  have representative_spec : ∀ c, classify (representative c) = c := fun c =>
    Classical.choose_spec (classify_surjective c)
  let distinctPairs := {pair : Class × Class // pair.1 ≠ pair.2}
  have exists_separator : ∀ pair : distinctPairs,
      ∃ protocol, protocol ∈ available ∧
        evaluate protocol (representative pair.1.1) ≠
          evaluate protocol (representative pair.1.2) := by
    intro pair
    have different_classes :
        classify (representative pair.1.1) ≠
          classify (representative pair.1.2) := by
      rw [representative_spec, representative_spec]
      exact pair.property
    have not_all_equal :
        ¬ ∀ protocol ∈ available,
          evaluate protocol (representative pair.1.1) =
            evaluate protocol (representative pair.1.2) := by
      intro all_equal
      exact different_classes ((class_exact _ _).2 all_equal)
    push Not at not_all_equal
    exact not_all_equal
  let chosen : distinctPairs → Protocol := fun pair =>
    Classical.choose (exists_separator pair)
  let selected : Finset Protocol := Finset.univ.image chosen
  refine ⟨selected, ?_, ?_⟩
  · intro protocol hprotocol
    simp only [selected, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hprotocol
    obtain ⟨pair, rfl⟩ := hprotocol
    exact (Classical.choose_spec (exists_separator pair)).1
  · intro x y
    constructor
    · intro same_class protocol hprotocol
      exact (class_exact x y).1 same_class protocol
        ((show (selected : Set Protocol) ⊆ available by
          intro candidate hcandidate
          simp only [selected, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
            true_and] at hcandidate
          obtain ⟨pair, rfl⟩ := hcandidate
          exact (Classical.choose_spec (exists_separator pair)).1) hprotocol)
    · intro selected_equal
      by_contra different_class
      let pair : distinctPairs := ⟨(classify x, classify y), different_class⟩
      have chosen_mem : chosen pair ∈ selected := by
        simp [selected]
      have x_matches_representative :
          evaluate (chosen pair) x =
            evaluate (chosen pair) (representative (classify x)) := by
        exact (class_exact x (representative (classify x))).1
          (representative_spec (classify x)).symm (chosen pair)
          (Classical.choose_spec (exists_separator pair)).1
      have y_matches_representative :
          evaluate (chosen pair) y =
            evaluate (chosen pair) (representative (classify y)) := by
        exact (class_exact y (representative (classify y))).1
          (representative_spec (classify y)).symm (chosen pair)
          (Classical.choose_spec (exists_separator pair)).1
      have representatives_differ :
          evaluate (chosen pair) (representative (classify x)) ≠
            evaluate (chosen pair) (representative (classify y)) :=
        (Classical.choose_spec (exists_separator pair)).2
      exact representatives_differ
        (x_matches_representative.symm.trans
          ((selected_equal (chosen pair) chosen_mem).trans y_matches_representative))

#print axioms finite_distinguishing_certificate

end D5.S3.ObserverMemory.PredictionCertificates.FiniteDistinguishingCertificate

/- GID: D5/S3/Combinatorics/Zigzag/DisconnectedSupport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/DisconnectedSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Actual disconnected labelled choices and separation by edge colorings. -/

import D5.S3.Combinatorics.Zigzag.ActiveSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

/-- Connectivity only quantifies over endpoints of actual selected edges. -/
def ActiveConnected {t : Nat} (c : Choices t) : Prop :=
  ∀ u v : ActiveVertex c, (supportSetoid c).r u.1 v.1

/-- The original labelled choices are counted without a closure restriction. -/
noncomputable def disconnectedCount (t : Nat) : Nat := by
  classical
  exact ((Finset.univ : Finset (Choices t)).filter
    (fun c => Balanced c ∧ ¬ ActiveConnected c)).card

private theorem connected_of_missing_plus (t : Nat) (ht : 2 ≤ t) (c : Choices t)
    (hc : Balanced c) (hp : ¬ Active c 1) : ActiveConnected c := by
  have anchor (v : ActiveVertex c) : (supportSetoid c).r v.1 (-1) := by
    rcases active_rooted t ht c hc v with hv | hv
    · exact (hp ((active_iff_of_related c hv).mp v.2)).elim
    · exact hv
  intro u v
  exact (supportSetoid c).trans (anchor u) ((supportSetoid c).symm (anchor v))

private theorem connected_of_missing_minus (t : Nat) (ht : 2 ≤ t) (c : Choices t)
    (hc : Balanced c) (hm : ¬ Active c (-1)) : ActiveConnected c := by
  have anchor (v : ActiveVertex c) : (supportSetoid c).r v.1 1 := by
    rcases active_rooted t ht c hc v with hv | hv
    · exact hv
    · exact (hm ((active_iff_of_related c hv).mp v.2)).elim
  intro u v
  exact (supportSetoid c).trans (anchor u) ((supportSetoid c).symm (anchor v))

private theorem connected_of_joined_semitones (t : Nat) (ht : 2 ≤ t)
    (c : Choices t) (hc : Balanced c)
    (hs : (supportSetoid c).r 1 (-1)) : ActiveConnected c := by
  have anchor (v : ActiveVertex c) : (supportSetoid c).r v.1 1 := by
    rcases active_rooted t ht c hc v with hv | hv
    · exact hv
    · exact (supportSetoid c).trans hv ((supportSetoid c).symm hs)
  intro u v
  exact (supportSetoid c).trans (anchor u) ((supportSetoid c).symm (anchor v))

private theorem actual_disconnected_iff (t : Nat) (ht : 2 ≤ t) (c : Choices t)
    (hc : Balanced c) : ¬ ActiveConnected c ↔
      Active c 1 ∧ Active c (-1) ∧ ¬ (supportSetoid c).r 1 (-1) := by
  classical
  constructor
  · intro hd
    refine ⟨?_, ?_, ?_⟩
    · by_contra hp
      exact hd (connected_of_missing_plus t ht c hc hp)
    · by_contra hm
      exact hd (connected_of_missing_minus t ht c hc hm)
    · intro hs
      exact hd (connected_of_joined_semitones t ht c hc hs)
  · rintro ⟨hp, hm, hs⟩ hconn
    exact hs (hconn ⟨1, hp⟩ ⟨-1, hm⟩)

private theorem semitone_separation_iff_coloring {t : Nat} (c : Choices t) :
    ¬ (supportSetoid c).r 1 (-1) ↔
      ∃ color : ZMod (3*t) → Bool, color 1 = true ∧ color (-1) = false ∧
        ∀ i, color (chosenPair c i).1 = color (chosenPair c i).2 := by
  classical
  constructor
  · intro hs
    let color : ZMod (3*t) → Bool := fun v => decide ((supportSetoid c).r v 1)
    refine ⟨color, ?_, ?_, ?_⟩
    · simp [color, (supportSetoid c).refl]
    · have hm : ¬ (supportSetoid c).r (-1) 1 :=
        fun h => hs ((supportSetoid c).symm h)
      simp [color, hm]
    · intro i
      have he : (supportSetoid c).r (chosenPair c i).1 (chosenPair c i).2 :=
        Relation.EqvGen.rel _ _ ⟨i, Prod.eta _⟩
      change decide ((supportSetoid c).r (chosenPair c i).1 1) =
        decide ((supportSetoid c).r (chosenPair c i).2 1)
      apply decide_eq_decide.mpr
      exact ⟨fun h => (supportSetoid c).trans ((supportSetoid c).symm he) h,
        fun h => (supportSetoid c).trans he h⟩
  · rintro ⟨color, hp, hm, he⟩ hs
    have respects : ∀ {u v}, (supportSetoid c).r u v → color u = color v := by
      intro u v huv
      induction huv with
      | rel u v h =>
          obtain ⟨i, hi⟩ := h
          simpa only [hi, Prod.fst, Prod.snd] using he i
      | refl => rfl
      | symm u v h ih => exact ih.symm
      | trans u v w h h' ih ih' => exact ih.trans ih'
    have h := respects hs
    rw [hp, hm] at h
    cases h

/-- Both semitones must actually occur; an unused semitone is not a component.
The coloring is an existence witness and is not part of the counted object. -/
theorem actual_disconnected_iff_coloring (t : Nat) (ht : 2 ≤ t) (c : Choices t)
    (hc : Balanced c) : ¬ ActiveConnected c ↔
      Active c 1 ∧ Active c (-1) ∧
        ∃ color : ZMod (3*t) → Bool, color 1 = true ∧ color (-1) = false ∧
          ∀ i, color (chosenPair c i).1 = color (chosenPair c i).2 := by
  rw [actual_disconnected_iff t ht c hc, semitone_separation_iff_coloring c]

end D5.S3.Combinatorics.Zigzag

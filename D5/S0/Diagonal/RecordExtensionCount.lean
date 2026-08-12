/- GID: D5/S0/Diagonal/RecordExtensionCount
   generality: G
   mirror-B: D5/B/S0/Diagonal/RecordExtensionCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A class restricted by a fixed record is bounded by unrecorded choices. -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

universe u v

namespace D5.S0.Diagonal.RecordExtensionCount

variable {D : Type u} {Y : Type v}

/-- Functions that agree with prescribed values at every recorded position. -/
def RecordExtensions (record : Finset D) (prescribed : D -> Y) :=
  {f : D -> Y // forall d, d ∈ record -> f d = prescribed d}

/-- Members of a candidate class that agree with the prescribed finite record. -/
def RestrictedExtensions (candidate : Set (D -> Y))
    (record : Finset D) (prescribed : D -> Y) :=
  {f : D -> Y // f ∈ candidate /\ forall d, d ∈ record -> f d = prescribed d}

private abbrev FreePositions (record : Finset D) := {d : D // d ∉ record}

private def recordExtensionEquiv [DecidableEq D]
    (record : Finset D) (prescribed : D -> Y) :
    RecordExtensions record prescribed ≃ (FreePositions record -> Y) where
  toFun f d := f.1 d
  invFun g :=
    ⟨fun d => if hd : d ∈ record then prescribed d else g ⟨d, hd⟩,
      by intro d hd; simp [hd]⟩
  left_inv f := by
    apply Subtype.ext
    funext d
    by_cases hd : d ∈ record
    · simp [hd, f.2 d hd]
    · simp [hd]
  right_inv g := by
    funext d
    simp [d.2]

/-- The full space of extensions is the function space on the unrecorded positions. -/
theorem record_extension_card [Fintype D] [Fintype Y]
    (record : Finset D) (prescribed : D -> Y) :
    Nat.card (RecordExtensions record prescribed) =
      Fintype.card Y ^ (Fintype.card D - record.card) := by
  classical
  calc
    Nat.card (RecordExtensions record prescribed) =
        Nat.card (FreePositions record -> Y) :=
      Nat.card_congr (recordExtensionEquiv record prescribed)
    _ = Nat.card Y ^ Nat.card (FreePositions record) := Nat.card_fun
    _ = _ := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl]
      simp

private def restrictedEmbedding (candidate : Set (D -> Y))
    (record : Finset D) (prescribed : D -> Y) :
    RestrictedExtensions candidate record prescribed ↪ RecordExtensions record prescribed where
  toFun f := ⟨f.1, f.2.2⟩
  inj' f g h := by
    apply Subtype.ext
    exact congrArg (fun x : RecordExtensions record prescribed => x.1) h

/-- Any candidate class restricted by a record has at most the full number of extensions. -/
theorem restricted_extension_card_le [Fintype D] [Fintype Y]
    (candidate : Set (D -> Y)) (record : Finset D) (prescribed : D -> Y) :
    Nat.card (RestrictedExtensions candidate record prescribed) <=
      Fintype.card Y ^ (Fintype.card D - record.card) := by
  classical
  letI : Finite (RecordExtensions record prescribed) :=
    Finite.of_injective (recordExtensionEquiv record prescribed).toFun
      (recordExtensionEquiv record prescribed).injective
  calc
    Nat.card (RestrictedExtensions candidate record prescribed) <=
        Nat.card (RecordExtensions record prescribed) :=
      Nat.card_le_card_of_injective
        (restrictedEmbedding candidate record prescribed)
        (restrictedEmbedding candidate record prescribed).injective
    _ = _ := record_extension_card record prescribed

/-- The domains in the finite counting statement can be inhabited. -/
example : Nonempty (Fin 2 × Fin 3) := inferInstance

/-- Fixing one of two binary positions leaves exactly two extensions, and every restricted
candidate class has at most two members agreeing with that record. -/
example :
    let record : Finset (Fin 2) := {0}
    let prescribed : Fin 2 -> Fin 2 := fun _ => 1
    Nat.card (RecordExtensions record prescribed) = 2 /\
      Nat.card (RestrictedExtensions Set.univ record prescribed) <= 2 := by
  dsimp
  constructor
  · simpa using record_extension_card ({0} : Finset (Fin 2)) (fun _ => (1 : Fin 2))
  · simpa using restricted_extension_card_le Set.univ ({0} : Finset (Fin 2))
      (fun _ => (1 : Fin 2))

end D5.S0.Diagonal.RecordExtensionCount

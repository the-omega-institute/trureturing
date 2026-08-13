/- GID: D5/S0/Rewriting/BinaryPatchFamily
   generality: G
   mirror-B: D5/B/S0/Rewriting/BinaryPatchFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary choices on disjoint off-record slots give distinct record-consistent functions. -/

import Mathlib.Data.Finset.Basic

namespace D5.S0.Rewriting.BinaryPatchFamily

/-- Apply a binary word at designated slots, using `base` away from those slots. -/
noncomputable def patchedFamily {D Y : Type*} {ell : Nat} (base : D -> Y) (slot : Fin ell -> D)
    (twist : Y -> Y) (word : Fin ell -> Bool) : D -> Y :=
  Function.extend slot
    (fun j => if word j then twist (base (slot j)) else base (slot j)) base

/-- Injective off-record slots and a fixed-point-free twist produce one distinct, record-consistent
function for every binary patch word. -/
theorem binary_patch_family_injective_and_consistent
    {D Y : Type*} {ell : Nat}
    (record : Finset D) (prescribed base : D -> Y) (slot : Fin ell -> D) (twist : Y -> Y)
    (hBase : forall d, d ∈ record -> base d = prescribed d)
    (hSlot : Function.Injective slot) (hOutside : forall j, slot j ∉ record)
    (hTwist : forall y, twist y ≠ y) :
    Function.Injective (patchedFamily base slot twist) ∧
      forall word d, d ∈ record -> patchedFamily base slot twist word d = prescribed d := by
  constructor
  · intro left right hEqual
    funext j
    have hAt := congrFun hEqual (slot j)
    unfold patchedFamily at hAt
    rw [hSlot.extend_apply, hSlot.extend_apply] at hAt
    have choice_injective :
        Function.Injective (fun choice : Bool =>
          if choice then twist (base (slot j)) else base (slot j)) := by
      intro first second hChoice
      cases first <;> cases second
      · rfl
      · exact (hTwist _ hChoice.symm).elim
      · exact (hTwist _ hChoice).elim
      · rfl
    exact choice_injective hAt
  · intro word d hd
    rw [patchedFamily, Function.extend_apply']
    · exact hBase d hd
    · rintro ⟨j, hj⟩
      exact hOutside j (by simpa [hj] using hd)

/-- The generic domains and hypotheses have a concrete finite witness. -/
example :
    let record : Finset Bool := {true}
    let base : Bool -> Bool := fun _ => false
    let slot : Fin 1 -> Bool := fun _ => false
    Function.Injective slot ∧
      (forall j, slot j ∉ record) ∧
      (forall y : Bool, Bool.not y ≠ y) ∧
      (forall d, d ∈ record -> base d = false) := by
  dsimp
  refine ⟨?_, by decide, by decide, ?_⟩
  · intro i j _
    exact Subsingleton.elim i j
  · intro d hd
    rfl

end D5.S0.Rewriting.BinaryPatchFamily

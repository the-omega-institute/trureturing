/- GID: D5/S3/Combinatorics/CayleyHosts/DoubleStarHostUpper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleyHosts/DoubleStarHostUpper
   mirror-E: none(waiver:explicit-cyclic-host)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: An explicit cyclic induced host of order five times the double-star leaf count. -/

import D5.S3.Combinatorics.CayleyHosts.DoubleStarHostDefs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CayleyHosts.DoubleStarHostUpper

open DoubleStarHostDefs

/-- Residue classes modulo five separate all forbidden pairs in the cyclic construction. -/
theorem upper_attained (q : ℕ) (hq : 1 ≤ q) :
    ∃ (s : Set (ZMod (5 * q))) (f : Bool × Option (Fin q) → ZMod (5 * q)),
      IsInducedEmbedding (doubleStar q) s f := by
  classical
  let : NeZero (5 * q) := ⟨by omega⟩
  let k : Bool × Option (Fin q) → ℕ := fun x =>
    match x with
    | (false, none) => 0
    | (true, none) => 1
    | (false, some i) => 4 + 5 * i.val
    | (true, some i) => 2 + 5 * i.val
  let f : Bool × Option (Fin q) → ZMod (5 * q) := fun x => (k x : ZMod (5 * q))
  have hk : ∀ x, k x < 5 * q := by
    rintro ⟨a, b⟩
    cases a <;> cases b with
    | none => dsimp [k]; omega
    | some i => have hi := i.isLt; dsimp [k]; omega
  have hfval : ∀ x, (f x).val = k x := fun x => ZMod.val_natCast_of_lt (hk x)
  have hkinj : Function.Injective k := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    cases a <;> cases c <;> cases b <;> cases d <;> dsimp [k] at h
    all_goals first | rfl | congr 2; apply Fin.ext; omega | omega
  have hfinj : Function.Injective f := by
    intro x y h
    apply hkinj
    simpa only [hfval] using congrArg ZMod.val h
  let ρ : ZMod (5 * q) →+* ZMod 5 := ZMod.castHom (dvd_mul_right 5 q) (ZMod 5)
  let s : Set (ZMod (5 * q)) := {z | ρ z = 1 ∨ ρ z = 4}
  refine ⟨s, f, hfinj, ?_⟩
  intro x y hxy
  have hfxy : f x ≠ f y := fun h => hxy (hfinj h)
  rw [SimpleGraph.addCayley_adj]
  apply Iff.trans (and_iff_right hfxy)
  change ((ρ (-f x + f y) = 1 ∨ ρ (-f x + f y) = 4) ∨
    (ρ (-f y + f x) = 1 ∨ ρ (-f y + f x) = 4)) ↔ _
  simp only [map_add, map_neg]
  have hr : ∀ x, ρ (f x) = (k x : ZMod 5) := fun x => map_natCast ρ (k x)
  simp only [hr]
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  have h5 : (5 : ZMod 5) = 0 := by decide
  cases a <;> cases c <;> cases b <;> cases d <;>
    simp [k, doubleStar, SimpleGraph.fromRel_adj, hxy, Nat.cast_add, Nat.cast_mul, h5] <;>
    decide

end D5.S3.Combinatorics.CayleyHosts.DoubleStarHostUpper

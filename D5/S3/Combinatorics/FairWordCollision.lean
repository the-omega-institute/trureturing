/- GID: D5/S3/Combinatorics/FairWordCollision
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FairWordCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shifted binary blocks collide with exact fair probability two to minus their length. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FairWordCollision

/-- The first and the shifted length-m blocks of a single complete context agree. -/
def collisionWords (m d : ℕ) : Finset (Fin (m + d) → Fin 2) :=
  Finset.univ.filter (fun x => ∀ i : Fin m,
    x ⟨i.val, by omega⟩ = x ⟨i.val + d, by omega⟩)

/-- The exact iid fair probability of a collision in this finite context. -/
def collisionProbability (m d : ℕ) : ℚ :=
  ((collisionWords m d).card : ℚ) / 2 ^ (m + d)

/-- The collision constraints leave precisely d free bits. In particular, overlap
does not change the collision probability `2^(-m)`. -/
theorem fair_word_collision (m d : ℕ) (hd : 0 < d) :
    (collisionWords m d).card = 2 ^ d ∧
      collisionProbability m d = 1 / (2 : ℚ) ^ m := by
  classical
  let C := {x : Fin (m + d) → Fin 2 // x ∈ collisionWords m d}
  let restrict (x : C) : Fin d → Fin 2 := fun i => x.val ⟨i.val, by omega⟩
  have hperiod (x : C) : List.HasPeriod (List.ofFn x.val) d := by
    rw [List.hasPeriod_iff_getElem?]
    intro i hi
    have him : i < m := by simpa using hi
    have hfirst : i < m + d := by omega
    have hsecond : i + d < m + d := by omega
    have hx : ∀ j : Fin m,
        x.val ⟨j.val, by omega⟩ = x.val ⟨j.val + d, by omega⟩ := by
      simpa [collisionWords] using x.property
    simpa [List.getElem?_ofFn, hfirst, hsecond] using congrArg some (hx ⟨i, him⟩)
  have hmod (x : C) (i : Fin (m + d)) :
      x.val i = x.val ⟨i.val % d, by have := Nat.mod_lt i.val hd; omega⟩ := by
    have hp := (hperiod x).getElem?_mod d i.val (List.ofFn x.val) (by simpa using i.isLt)
    have hm : i.val % d < m + d := by have := Nat.mod_lt i.val hd; omega
    simpa [List.getElem?_ofFn, i.isLt, hm] using hp.symm
  have hbij : Function.Bijective restrict := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      funext i
      rw [hmod x i, hmod y i]
      exact congr_fun hxy ⟨i.val % d, Nat.mod_lt i.val hd⟩
    · intro y
      let x : Fin (m + d) → Fin 2 := fun i => y ⟨i.val % d, Nat.mod_lt i.val hd⟩
      have hx : x ∈ collisionWords m d := by
        simp only [collisionWords, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i
        dsimp [x]
        congr 1
        exact Fin.ext (Nat.add_mod_right i.val d).symm
      refine ⟨⟨x, hx⟩, ?_⟩
      funext i
      change y ⟨i.val % d, Nat.mod_lt i.val hd⟩ = y i
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hcard : (collisionWords m d).card = 2 ^ d := by
    have hc := Fintype.card_congr (Equiv.ofBijective restrict hbij)
    simpa [C, Fintype.card_coe] using hc
  refine ⟨hcard, ?_⟩
  rw [collisionProbability, hcard]
  push_cast
  rw [pow_add]
  have hd0 : (2 : ℚ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm0 : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

#print axioms fair_word_collision

end D5.S3.Combinatorics.FairWordCollision

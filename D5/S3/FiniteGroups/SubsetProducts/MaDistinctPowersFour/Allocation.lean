/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Allocate disjoint exponent positions to classes of sizes one through four. -/

import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

namespace D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour

/-- A row index consists of a class size minus one, a class of that size,
and a position inside that class. -/
abbrev ClassPositions (count : Fin 4 → ℕ) :=
  Σ k : Fin 4, Fin (count k) × Fin (k.val + 1)

theorem card_classPositions (count : Fin 4 → ℕ) :
    Fintype.card (ClassPositions count) =
      2 * count 1 + 3 * count 2 + 4 * count 3 + count 0 := by
  simp only [ClassPositions, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fin.sum_univ_four]
  change count 0 * 1 + count 1 * 2 + count 2 * 3 + count 3 * 4 = _
  omega

/-- Zero-based exponent positions. Two-element classes take the endpoints
first. Triples, four-blocks, and singletons fill the middle interval in order. -/
def slot (n : ℕ) (count : Fin 4 → ℕ) (k : Fin 4)
    (i : Fin (count k)) (j : Fin (k.val + 1)) : ℕ :=
  match k.val with
  | 0 => count 1 + 3 * count 2 + 4 * count 3 + i.val
  | 1 => if j.val = 0 then i.val else n - (i.val + 1)
  | 2 => count 1 + 3 * i.val + j.val
  | _ => count 1 + 3 * count 2 + 4 * i.val + j.val

theorem slot_lt {n : ℕ} {count : Fin 4 → ℕ}
    (hn : n = 2 * count 1 + 3 * count 2 + 4 * count 3 + count 0)
    (k : Fin 4) (i : Fin (count k)) (j : Fin (k.val + 1)) :
    slot n count k i j < n := by
  fin_cases k
  all_goals
    have hi := i.isLt
    have hj := j.isLt
    first
    | change i.val < count 0 at hi
    | change i.val < count 1 at hi
    | change i.val < count 2 at hi
    | change i.val < count 3 at hi
    simp only [slot, Fin.val_mk] at hj ⊢
    try split
    all_goals omega

theorem slot_injective {n : ℕ} {count : Fin 4 → ℕ}
    (hn : n = 2 * count 1 + 3 * count 2 + 4 * count 3 + count 0) :
    Function.Injective (fun p : ClassPositions count => slot n count p.1 p.2.1 p.2.2) := by
  rintro ⟨k, i, j⟩ ⟨l, i', j'⟩ h
  change slot n count k i j = slot n count l i' j' at h
  fin_cases k <;> fin_cases l
  all_goals
    have hi := i.isLt
    have hi' := i'.isLt
    have hj := j.isLt
    have hj' := j'.isLt
    first
    | change i.val < count 0 at hi
    | change i.val < count 1 at hi
    | change i.val < count 2 at hi
    | change i.val < count 3 at hi
    first
    | change i'.val < count 0 at hi'
    | change i'.val < count 1 at hi'
    | change i'.val < count 2 at hi'
    | change i'.val < count 3 at hi'
    simp only [slot, Fin.val_mk] at h hj hj'
    try split at h
  all_goals try split at h
  all_goals
    first
    | exfalso
      omega
    | have hiEq : i = i' := Fin.ext (by omega)
      have hjEq : j = j' := Fin.ext (by omega)
      subst i'
      subst j'
      rfl


theorem pair_slots {n : ℕ} {count : Fin 4 → ℕ}
    (hn : n = 2 * count 1 + 3 * count 2 + 4 * count 3 + count 0)
    (i : Fin (count 1)) :
    slot n count 1 i 0 + 1 = i.val + 1 ∧
      slot n count 1 i 1 + 1 = n - i.val ∧
      i.val + 1 < n - i.val ∧ (i.val + 1) + (n - i.val) = n + 1 := by
  have hi := i.isLt
  change i.val + 1 = i.val + 1 ∧ n - (i.val + 1) + 1 = n - i.val ∧
    i.val + 1 < n - i.val ∧ (i.val + 1) + (n - i.val) = n + 1
  omega

theorem triple_slots (n : ℕ) (count : Fin 4 → ℕ) (i : Fin (count 2)) (j : Fin 3) :
    slot n count 2 i j + 1 = (count 1 + 3 * i.val + 1) + j.val := by
  change count 1 + 3 * i.val + j.val + 1 = (count 1 + 3 * i.val + 1) + j.val
  omega

theorem four_slots (n : ℕ) (count : Fin 4 → ℕ) (i : Fin (count 3)) (j : Fin 4) :
    slot n count 3 i j + 1 = (count 1 + 3 * count 2 + 4 * i.val + 1) + j.val := by
  change count 1 + 3 * count 2 + 4 * i.val + j.val + 1 =
    (count 1 + 3 * count 2 + 4 * i.val + 1) + j.val
  omega

end D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour

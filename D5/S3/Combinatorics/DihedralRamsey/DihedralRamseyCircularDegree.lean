/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyCircularDegree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyCircularDegree
   mirror-E: none(waiver:shared-circular-neighbour-count)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Circular offsets enumerate exactly the neighbours in a short-edge graph. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPermutations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

/-- Forward and backward offsets enumerate each short circular neighbour exactly once. -/
theorem short_circular_degree {n t : ℕ} (hn : 2 * t < n)
    (G : SimpleGraph (Fin n))
    (hadj : ∀ x y, G.Adj x y ↔ x ≠ y ∧
      (Nat.dist x.val y.val ≤ t ∨ n - Nat.dist x.val y.val ≤ t)) :
    letI := Classical.propDecidable
    ∀ x, G.degree x = 2 * t := by
  classical
  intro x
  let : Fintype (G.neighborSet x) :=
    @Subtype.fintype (Fin n) (fun y => y ∈ G.neighborSet x)
      (fun _ => Classical.propDecidable _) (Fin.fintype n)
  have hnpos : 0 < n := by omega
  let offset (i : Fin (2 * t)) := if i.val < t then i.val + 1 else n + t - i.val - 1
  have hoff : ∀ i, 0 < offset i ∧ offset i < n ∧
      (offset i ≤ t ∨ n - offset i ≤ t) := by
    intro i
    have := i.isLt
    dsimp [offset]
    split_ifs <;> omega
  let f (i : Fin (2 * t)) : Fin n :=
    ⟨(x.val + offset i) % n, Nat.mod_lt _ hnpos⟩
  have hfval : ∀ i, (f i).val = if x.val + offset i < n then x.val + offset i
      else x.val + offset i - n := by
    intro i
    change (x.val + offset i) % n = _
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by
        have := x.isLt
        have := hoff i
        omega)]
  have hfinj : Function.Injective f := by
    intro i j he
    have he' := congrArg Fin.val he
    rw [hfval, hfval] at he'
    have hi := hoff i
    have hj := hoff j
    have heoff : offset i = offset j := by
      split_ifs at he' <;> omega
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    dsimp [offset] at heoff
    split_ifs at heoff <;> omega
  have hfred : ∀ i, G.Adj x (f i) := by
    intro i
    apply (hadj _ _).mpr
    have hi := hoff i
    have hv := hfval i
    constructor
    · intro he
      have he' := congrArg Fin.val he
      split_ifs at hv <;> omega
    · unfold Nat.dist
      split_ifs at hv <;> omega
  have hfsurj : ∀ y, G.Adj x y → ∃ i, f i = y := by
    intro y hy
    obtain ⟨hne, hdist⟩ := (hadj x y).mp hy
    have hneval : x.val ≠ y.val := fun he => hne (Fin.ext he)
    let d := if x.val < y.val then y.val - x.val else n + y.val - x.val
    have hd : 0 < d ∧ d < n ∧ (d ≤ t ∨ n - d ≤ t) := by
      have := x.isLt
      have := y.isLt
      dsimp [d]
      unfold Nat.dist at hdist
      split_ifs <;> omega
    have choose : ∃ i : Fin (2 * t), offset i = d := by
      rcases hd.2.2 with h | h
      · let i : Fin (2 * t) := ⟨d - 1, by omega⟩
        refine ⟨i, ?_⟩
        have hi : i.val < t := by change d - 1 < t; omega
        dsimp [offset]
        rw [if_pos hi]
        change d - 1 + 1 = d
        omega
      · let i : Fin (2 * t) := ⟨t + n - d - 1, by omega⟩
        refine ⟨i, ?_⟩
        have hi : ¬i.val < t := by change ¬t + n - d - 1 < t; omega
        dsimp [offset]
        rw [if_neg hi]
        change n + t - (t + n - d - 1) - 1 = d
        omega
    obtain ⟨i, hi⟩ := choose
    refine ⟨i, Fin.ext ?_⟩
    have hv := hfval i
    rw [hi] at hv
    dsimp [d] at hv
    split_ifs at hv <;> omega
  let f' : Fin (2 * t) → G.neighborSet x := fun i => ⟨f i, hfred i⟩
  have hf' : Function.Bijective f' := by
    constructor
    · intro i j he
      exact hfinj (congrArg Subtype.val he)
    · intro y
      obtain ⟨i, hi⟩ := hfsurj y.val y.property
      exact ⟨i, Subtype.ext hi⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f' hf')
  convert hcard.symm using 1
  · exact (SimpleGraph.card_neighborSet_eq_degree G x).symm
  · exact (Fintype.card_fin (2 * t)).symm

end D5.S3.Combinatorics.DihedralRamsey

/- GID: D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive fixed-step graphs on integer intervals have min(m,d) connected components. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.StepGraphComponentCount

/-- The loopless graph on `0,...,d-1` with moves of size `m` in either direction. -/
def stepGraph (d m : ℕ) : SimpleGraph (Fin d) :=
  SimpleGraph.fromRel fun i j => i.val + m = j.val

/-- The residues modulo `m` that actually occur among the vertex labels. -/
def occurringResidues (d m : ℕ) : Finset ℕ :=
  (Finset.range d).image (fun i => i % m)

private lemma adj_iff {d m : ℕ} (hm : 1 ≤ m) (i j : Fin d) :
    (stepGraph d m).Adj i j ↔ i.val + m = j.val ∨ j.val + m = i.val := by
  rw [stepGraph, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    intro hij
    subst j
    rcases h with h | h <;> omega

private lemma mod_eq_of_adj {d m : ℕ} {i j : Fin d}
    (h : (stepGraph d m).Adj i j) : i.val % m = j.val % m := by
  rcases h.2 with h | h
  · rw [← h, Nat.add_mod_right]
  · rw [← h, Nat.add_mod_right]

private lemma mod_eq_of_reachable {d m : ℕ} {i j : Fin d}
    (h : (stepGraph d m).Reachable i j) : i.val % m = j.val % m := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih => exact (mod_eq_of_adj h).trans ih

private lemma reachable_remainder {d m : ℕ} (hm : 1 ≤ m) (i : Fin d) :
    (stepGraph d m).Reachable i
      ⟨i.val % m, lt_of_le_of_lt (Nat.mod_le _ _) i.isLt⟩ := by
  obtain ⟨n, hn⟩ := i
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnm : n < m
    · have heq : (⟨n % m, lt_of_le_of_lt (Nat.mod_le _ _) hn⟩ : Fin d) = ⟨n, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hnm
      rw [heq]
    · have hmn : m ≤ n := Nat.le_of_not_gt hnm
      have hsub : n - m < n := by omega
      have hsubd : n - m < d := lt_trans hsub hn
      have edge : (stepGraph d m).Adj ⟨n, hn⟩ ⟨n - m, hsubd⟩ := by
        apply (adj_iff hm _ _).2
        exact Or.inr (Nat.sub_add_cancel hmn)
      have tail := ih (n - m) hsub hsubd
      have hmod : (n - m) % m = n % m := (Nat.mod_eq_sub_mod hmn).symm
      have heq : (⟨(n - m) % m, lt_of_le_of_lt (Nat.mod_le _ _) hsubd⟩ : Fin d) =
          ⟨n % m, lt_of_le_of_lt (Nat.mod_le _ _) hn⟩ := Fin.ext hmod
      rw [heq] at tail
      exact edge.reachable.trans tail

/-- Two labels are connected exactly when their remainders modulo the positive step agree. -/
theorem reachable_iff_mod_eq {d m : ℕ} (hm : 1 ≤ m) (i j : Fin d) :
    (stepGraph d m).Reachable i j ↔ i.val % m = j.val % m := by
  refine ⟨mod_eq_of_reachable, ?_⟩
  intro h
  have hj := reachable_remainder hm j
  have heq : (⟨j.val % m, lt_of_le_of_lt (Nat.mod_le _ _) j.isLt⟩ : Fin d) =
      ⟨i.val % m, lt_of_le_of_lt (Nat.mod_le _ _) i.isLt⟩ := Fin.ext h.symm
  rw [heq] at hj
  exact (reachable_remainder hm i).trans hj.symm

private def vertexResidue {d m : ℕ} (i : Fin d) : ↥(occurringResidues d m) :=
  ⟨i.val % m, Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩⟩

/-- Components correspond bijectively to the remainders that occur in the interval. -/
noncomputable def componentEquivResidues (d m : ℕ) (hm : 1 ≤ m) :
    (stepGraph d m).ConnectedComponent ≃ ↥(occurringResidues d m) :=
  Equiv.ofBijective
    (Quot.lift vertexResidue (fun _ _ h => Subtype.ext (mod_eq_of_reachable h))) (by
      constructor
      · intro c c'
        induction c using SimpleGraph.ConnectedComponent.ind with
        | _ i =>
          induction c' using SimpleGraph.ConnectedComponent.ind with
          | _ j =>
            intro h
            apply SimpleGraph.ConnectedComponent.sound
            apply (reachable_iff_mod_eq hm i j).2
            exact congrArg Subtype.val h
      · rintro ⟨r, hr⟩
        obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
        refine ⟨(stepGraph d m).connectedComponentMk ⟨i, Finset.mem_range.mp hi⟩, ?_⟩
        exact Subtype.ext hir)

private lemma occurringResidues_eq_range {d m : ℕ} (hm : 1 ≤ m) :
    occurringResidues d m = Finset.range (min m d) := by
  ext r
  simp only [occurringResidues, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact lt_min (Nat.mod_lt _ (by omega)) (lt_of_le_of_lt (Nat.mod_le _ _) hi)
  · intro hr
    refine ⟨r, (lt_min_iff.mp hr).2, ?_⟩
    exact Nat.mod_eq_of_lt (lt_min_iff.mp hr).1

/-- For every interval size, including zero, the number of components is `min m d`. -/
theorem connectedComponent_card (d m : ℕ) (hm : 1 ≤ m) :
    Nat.card (stepGraph d m).ConnectedComponent = min m d := by
  classical
  let : Fintype (stepGraph d m).ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (componentEquivResidues d m hm),
    Fintype.card_coe, occurringResidues_eq_range hm, Finset.card_range]

#print axioms reachable_iff_mod_eq
#print axioms componentEquivResidues
#print axioms connectedComponent_card

end D5.S3.ConceptDynamics.GraphColoring.StepGraphComponentCount

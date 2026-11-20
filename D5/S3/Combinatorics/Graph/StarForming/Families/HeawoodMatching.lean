/- GID: D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: A parametric induced matching for binary Heawood lifts. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
import D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodMatrixAction
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The Fano labels and matrix gain are those of HEAWOOD_DOUBLE_COVER_GAIN,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. -/

namespace D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodMatching

open HeawoodSwitching HeawoodLift StarFormingDissociationRefutation

private def signSlot (e : Fin 21) : Fin 7 :=
  match e.val with
  | 9 => 1       -- (4, 1)
  | 10 => 2      -- (4, 2)
  | 13 => 3      -- (5, 5)
  | 0 => 4       -- (1, 2)
  | 1 => 5       -- (1, 4)
  | 4 => 6       -- (2, 4)
  | _ => 0

private def signing (u v a b c : F2) (e : Fin 21) : F2 :=
  ![0, 1, u, v, a, b + v, c] (signSlot e)

/-- The gain coordinates in which the same matching gives both extra vertices. -/
def gain (u v a b c : F2) : Mat :=
  !![v, a, b; 0, 0, c; 1 + v, u, v]

private theorem signing_gain (u v a b c : F2) : phi (signing u v a b c) = gain u v a b c := by
  ext i j
  change (∑ e : Fin 21, signing u v a b c e * coordinate (flags e).1 i *
    coordinate (flags e).2 j) = _
  fin_cases i <;> fin_cases j <;>
    norm_num [signing, signSlot, gain, flags, coordinate, Fin.sum_univ_succ] <;>
    reduce_mod_char <;> try ring_nf
  all_goals simp [show (2 : F2) = 0 by decide +kernel]

-- A line and its designated point have the same index.
private def pointBase (i : Fin 8) : Vertex := ![1, 1, 2, 2, 3, 4, 5, 6] i
private def lineBase (i : Fin 8) : Vertex := ![7, 11, 13, 9, 8, 8, 12, 12] i

private def pointLift (u : F2) (i : Fin 8) : Vertex × F2 :=
  (pointBase i, ![0, 1, 0, 1, 0, 1 + u, 1, 0] i)

private def lineLift (u : F2) (i : Fin 8) : Vertex × F2 :=
  (lineBase i, ![0, 1, 0, 1, u, 1 + u, 1, 0] i)

private theorem point_injective (u : F2) : Function.Injective (pointLift u) := by
  have coincident : ∀ i j : Fin 8, pointBase i = pointBase j →
      i = j ∨ i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 ∨ i = 2 ∧ j = 3 ∨ i = 3 ∧ j = 2 := by
    decide +kernel
  intro i j hij
  have hs := congrArg Prod.snd hij
  rcases coincident i j (congrArg Prod.fst hij) with he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact he
  all_goals exact (zero_ne_one (α := F2) (by first | exact hs | exact hs.symm)).elim

private theorem line_injective (u : F2) : Function.Injective (lineLift u) := by
  have coincident : ∀ i j : Fin 8, lineBase i = lineBase j →
      i = j ∨ i = 4 ∧ j = 5 ∨ i = 5 ∧ j = 4 ∨ i = 6 ∧ j = 7 ∨ i = 7 ∧ j = 6 := by
    decide +kernel
  have hne : u ≠ 1 + u := fun h => one_ne_zero (add_right_cancel (h.symm.trans (zero_add u).symm))
  intro i j hij
  have hs := congrArg Prod.snd hij
  rcases coincident i j (congrArg Prod.fst hij) with he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact he
  · exact (hne hs).elim
  · exact (hne hs.symm).elim
  · exact (one_ne_zero (α := F2) hs).elim
  · exact (zero_ne_one (α := F2) hs).elim

private theorem separate (u : F2) (i j : Fin 8) : pointLift u i ≠ lineLift u j := by
  have sides : ∀ i j, pointBase i ≠ lineBase j := by decide +kernel
  exact fun h => sides i j (congrArg Prod.fst h)

private theorem no_point_edges (i j : Fin 8) : ¬ base.Adj (pointBase i) (pointBase j) := by
  revert i j
  decide +kernel

private theorem no_line_edges (i j : Fin 8) : ¬ base.Adj (lineBase i) (lineBase j) := by
  revert i j
  decide +kernel

private def active (u v : F2) (j : Fin 8) : Prop :=
  (j = 1 → u + v = 1) ∧ (j = 2 → u = 0)

private instance (u v : F2) (j : Fin 8) : Decidable (active u v j) :=
  inferInstanceAs (Decidable ((_ → _) ∧ (_ → _)))

-- The sign at an incident candidate pair is independent of a, b and c.
private def candidateSignSlot (i j : Fin 8) : Fin 7 :=
  if pointBase i = 3 ∧ lineBase j = 7 then 1
  else if pointBase i = 3 ∧ lineBase j = 8 then 2
  else if pointBase i = 4 ∧ lineBase j = 11 then 3
  else 0

private theorem candidate_sign : ∀ i j, base.Adj (pointBase i) (lineBase j) →
    signSlot (edgeIndex (pointBase i) (lineBase j)) = candidateSignSlot i j := by
  decide +kernel

-- The incidence and sign lookup depend only on the base graph. The proof
-- below then works with the sheet equations and both optional-line hypotheses.
set_option maxHeartbeats 1600000 in
private theorem cross_edge (u v a b c : F2) (i j : Fin 8) (hj : active u v j) :
    (graph (signing u v a b c)).Adj (pointLift u i) (lineLift u j) ↔ i = j := by
  have one_add_ne : 1 + u ≠ u := fun h => one_ne_zero (add_right_cancel (h.trans (zero_add u).symm))
  have h11 : (1 : F2) + 1 = 0 := by decide +kernel
  have toggle : 1 + (u + 1) = u := by
    calc
      _ = u + (1 + 1) := by ring
      _ = _ := by rw [h11, add_zero]
  have self_add : u + u = 0 := by rw [← two_mul, show (2 : F2) = 0 by decide +kernel, zero_mul]
  have untoggle : u + (1 + u) = 1 := by
    calc
      _ = 1 + (u + u) := by ring
      _ = _ := by rw [self_add, add_zero]
  have optional_one : j = 1 → u ≠ v := by
    intro h huv
    exact zero_ne_one (self_add.symm.trans (huv ▸ hj.1 h))
  have optional_two := hj.2
  clear hj
  change (base.Adj (pointBase i) (lineBase j) ∧
    (pointLift u i).2 + (lineLift u j).2 =
      ![0, 1, u, v, a, b + v, c] (signSlot (edgeIndex (pointBase i) (lineBase j)))) ↔ i = j
  by_cases h : base.Adj (pointBase i) (lineBase j)
  · simp only [h, true_and, candidate_sign i j h]
    fin_cases i <;> fin_cases j
    all_goals
      first
      | (exfalso; revert h; decide +kernel)
      | (clear h
         simp at optional_one optional_two
         simp (config := {decide := true}) [pointLift, lineLift, candidateSignSlot, pointBase,
           lineBase, add_assoc, one_add_ne, toggle, untoggle, optional_one, optional_two, h11, self_add])
  · simp only [h, false_and, false_iff]
    rintro rfl
    have diagonal : ∀ i, base.Adj (pointBase i) (lineBase i) := by decide +kernel
    exact h (diagonal i)

private theorem matching_set (u v a b c : F2) :
    ∃ S : Finset (Vertex × F2), IsKIndependent (graph (signing u v a b c)) 2 S ∧
      S.card = 14 + (if u = 0 then 1 else 0) + (if u + v = 1 then 1 else 0) := by
  let P := Finset.univ.map ⟨pointLift u, point_injective u⟩
  let L := (Finset.univ.filter (active u v)).map ⟨lineLift u, line_injective u⟩
  have hp {x} : x ∈ P ↔ ∃ i, pointLift u i = x := by simp [P]
  have hl {x} : x ∈ L ↔ ∃ j, active u v j ∧ lineLift u j = x := by simp [L]
  have hdisj : Disjoint P L := Finset.disjoint_left.mpr fun _ hx hy => by
    obtain ⟨i, rfl⟩ := hp.mp hx
    obtain ⟨j, _, hj⟩ := hl.mp hy
    exact separate u i j hj.symm
  have hcross {i j} (hj : active u v j) :=
    cross_edge u v a b c i j hj
  refine ⟨P ∪ L, (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr ?_, ?_⟩
  · intro x hx y hy z hz hxy hxz
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := hp.mp hx
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨j, rfl⟩ := hp.mp hy
        exact (no_point_edges i j hxy.1).elim
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨k, rfl⟩ := hp.mp hz
        exact (no_point_edges i k hxz.1).elim
      obtain ⟨j, hj, rfl⟩ := hl.mp hy
      obtain ⟨k, hk, rfl⟩ := hl.mp hz
      rw [← (hcross hj).mp hxy, ← (hcross hk).mp hxz]
    · obtain ⟨i, hi, rfl⟩ := hl.mp hx
      rcases Finset.mem_union.mp hy with hy | hy
      · rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨j, rfl⟩ := hp.mp hy
          obtain ⟨k, rfl⟩ := hp.mp hz
          rw [(hcross hi).mp ((graph _).adj_symm hxy), (hcross hi).mp ((graph _).adj_symm hxz)]
        · obtain ⟨k, _, rfl⟩ := hl.mp hz
          exact (no_line_edges i k hxz.1).elim
      · obtain ⟨j, _, rfl⟩ := hl.mp hy
        exact (no_line_edges i j hxy.1).elim
  · rw [Finset.card_union_of_disjoint hdisj]
    have hP : P.card = 8 := by simp [P]
    have hL : L.card = 6 + (if u = 0 then 1 else 0) + (if u + v = 1 then 1 else 0) := by
      simp only [L, Finset.card_map]
      by_cases hu : u = 0
      · subst u
        simp only [zero_add]
        by_cases hv : v = 1 <;>
          simp [Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton, active, hv]
      · by_cases huv : u + v = 1 <;>
          simp [Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton, active, hu, huv]
    rw [hP, hL]
    omega

/-- A gain conjugate to the displayed form gives the parametric lower bound
and the Heawood upper bound. The three entries above the diagonal are unrestricted. -/
theorem beta_bounds (s : Signing) (g : Matˣ) (u v a b c : F2)
    (h : phi s = (g : Mat) * gain u v a b c * (↑g⁻¹ : Mat)) :
    14 + (if u = 0 then 1 else 0) + (if u + v = 1 then 1 else 0) ≤ beta (graph s) 2 ∧ beta (graph s) 2 ≤ 16 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨iso⟩ := HeawoodMatrixAction.isomorphic_of_phi_conjugate (signing u v a b c) s g
      (by rwa [signing_gain])
    obtain ⟨S, hS, hcard⟩ := matching_set u v a b c
    rw [← (Isomorphism.parameters iso).1, ← hcard]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩)
  · simpa only [HeawoodCoverParameters.sf_all] using (beta_le_sf (graph s))

end D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodMatching

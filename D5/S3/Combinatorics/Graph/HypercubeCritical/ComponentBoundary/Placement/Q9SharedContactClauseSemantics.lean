/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactClauseSemantics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Cubicity and exterior evenness constrain neighbor bits and their prefix parity. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized

/-! Degree and prefix parity for the direct shared-contact clauses. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactClauseSemantics

open Finset
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9SharedContactNormalized (LocalRules)

def occupiedBit (S : Finset (Q 9)) (x : Q 9) : Bool :=
  decide (x ∈ S)

def directionBit (S : Finset (Q 9)) (x : Q 9) (i : Fin 9) : Bool :=
  decide (i ∈ directions S x)

theorem directionBit_eq_occupiedBit_flip (S : Finset (Q 9)) (x : Q 9) (i : Fin 9) :
    directionBit S x i = occupiedBit S (flip x i) :=
  Bool.decide_congr (mem_directions S x i)

/-- Among four axes at an occupied vertex, some axis leads outside the support. -/
theorem upperDegree {S : Finset (Q 9)} (hS : LocalRules S) {x : Q 9} (hx : x ∈ S)
    {axes : Finset (Fin 9)} (haxes : axes.card = 4) :
    ∃ i ∈ axes, directionBit S x i = false := by
  have hnot : ¬ axes ⊆ directions S x := by
    intro hsub
    have hcard := card_le_card hsub
    rw [haxes, hS.occupied_degree x hx] at hcard
    omega
  obtain ⟨i, hi, hout⟩ := Finset.not_subset.mp hnot
  exact ⟨i, hi, Bool.decide_false hout⟩

/-- Among seven axes at an occupied vertex, some axis leads into the support. -/
theorem lowerDegree {S : Finset (Q 9)} (hS : LocalRules S) {x : Q 9} (hx : x ∈ S)
    {axes : Finset (Fin 9)} (haxes : axes.card = 7) :
    ∃ i ∈ axes, directionBit S x i = true := by
  classical
  have hnot : ¬ axes ⊆ univ \ directions S x := by
    intro hsub
    have hcard := card_le_card hsub
    rw [haxes, card_univ_sdiff, Fintype.card_fin, hS.occupied_degree x hx] at hcard
    omega
  obtain ⟨i, hi, hin⟩ := Finset.not_subset.mp hnot
  have hdir : i ∈ directions S x := by
    simpa only [mem_sdiff, mem_univ, true_and, not_not] using hin
  exact ⟨i, hi, Bool.decide_true hdir⟩

private def prefixDirections (S : Finset (Q 9)) (x : Q 9) (i : Fin 9) : Finset (Fin 9) :=
  (directions S x).filter fun j => j ≤ i

/-- The parity of occupied neighbors along axes zero through `i`, inclusive. -/
def prefixParity (S : Finset (Q 9)) (x : Q 9) (i : Fin 9) : Bool :=
  decide (Odd (prefixDirections S x i).card)

theorem prefixParity_zero (S : Finset (Q 9)) (x : Q 9) :
    prefixParity S x 0 = directionBit S x 0 := by
  have hprefix : prefixDirections S x 0 =
      if (0 : Fin 9) ∈ directions S x then {0} else ∅ := by
    calc
      _ = (directions S x).filter (fun j => j = 0) := by
        unfold prefixDirections
        exact filter_congr (fun _ _ => Fin.le_zero_iff)
      _ = _ := filter_eq' _ _
  by_cases h0 : (0 : Fin 9) ∈ directions S x
  · simp only [prefixParity, directionBit, hprefix, if_pos h0, card_singleton,
      Bool.decide_true h0] <;> decide
  · simp only [prefixParity, directionBit, hprefix, if_neg h0, card_empty,
      Bool.decide_false h0] <;> decide

theorem prefixParity_succ (S : Finset (Q 9)) (x : Q 9) (i : Fin 8) :
    prefixParity S x i.succ = (prefixParity S x i.castSucc ^^ directionBit S x i.succ) := by
  have hstep (j : Fin 9) : j ≤ i.succ ↔ j = i.succ ∨ j ≤ i.castSucc := by
    rw [Fin.le_castSucc_iff]
    exact ⟨Fin.eq_or_lt_of_le, fun h => h.elim Fin.le_of_eq Fin.le_of_lt⟩
  by_cases hi : i.succ ∈ directions S x
  · have hprefix : prefixDirections S x i.succ = insert i.succ (prefixDirections S x i.castSucc) := by
      apply Finset.ext
      intro j
      by_cases hj : j = i.succ
      · subst j
        simp only [prefixDirections, mem_filter, mem_insert, le_refl, and_true, hi, eq_self,
          true_or]
      · simp only [prefixDirections, mem_filter, mem_insert, hstep, hj, false_or]
    have hnew : i.succ ∉ prefixDirections S x i.castSucc := by
      intro hmem
      simp only [prefixDirections, mem_filter] at hmem
      exact (not_le_of_gt Fin.castSucc_lt_succ) hmem.2
    calc
      prefixParity S x i.succ = decide (Odd ((prefixDirections S x i.castSucc).card + 1)) := by
        rw [prefixParity, hprefix, card_insert_of_notMem hnew]
      _ = !prefixParity S x i.castSucc :=
        (Bool.decide_congr Nat.odd_add_one).trans decide_not
      _ = _ := by simp only [directionBit, Bool.decide_true hi, Bool.xor_true]
  · have hprefix : prefixDirections S x i.succ = prefixDirections S x i.castSucc := by
      unfold prefixDirections
      apply filter_congr
      intro j hj
      have hne : j ≠ i.succ := fun heq => hi (heq ▸ hj)
      simp only [hstep, hne, false_or]
    simp only [prefixParity, hprefix, directionBit, Bool.decide_false hi, Bool.xor_false]

theorem prefixParity_last {S : Finset (Q 9)} (hS : LocalRules S) (x : Q 9) :
    prefixParity S x (Fin.last 8) = occupiedBit S x := by
  have hprefix : prefixDirections S x (Fin.last 8) = directions S x := by
    unfold prefixDirections
    exact filter_eq_self.mpr (fun j _ => Fin.le_last j)
  unfold prefixParity occupiedBit
  rw [hprefix]
  apply Bool.decide_congr
  constructor
  · intro hodd
    by_contra hx
    exact (Nat.not_odd_iff_even.mpr (hS.exterior_degree x hx)) hodd
  · intro hx
    rw [hS.occupied_degree x hx]
    decide

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactClauseSemantics

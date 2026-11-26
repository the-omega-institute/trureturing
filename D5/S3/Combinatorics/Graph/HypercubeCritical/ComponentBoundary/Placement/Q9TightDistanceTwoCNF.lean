/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCNF
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCNF
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Normalized opposing-star geometry supplies the inputs of the distance-two refutations. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

/-! Semantics of the direct opposing-star CNFs at radius two. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF

open Finset
open BalancedCriticalSpectrum (Q flip flip_adj)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (origin)
open Q9IsotropicHuang (parity)
open Q9SharedContactCNF (Axis Word Variable wordIndex pos neg)
open Q9SharedContactClauseSemantics
open Q9SharedContactNormalized (LocalRules)
open Q9TightDistanceTwoNormalized
  (DirectGeometry DirectStar baseAxes rightCenter exteriorShell exteriorShell_eq_zero_iff)
open private adjacentWord adjacentWord_spec prefixVariable xorClause
  satisfies_negative_list satisfies_positive_list from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF

private abbrev occ := Variable.occupied

/-- SAT literal indices are zero-based. DIMACS numbers are one-based. -/
theorem occupied_dimacs (s : Bool) (w : Word) :
    (occ s w).index + 1 = (if s then 512 else 0) + w.toNat + 1 := rfl

/-- The shared prefix variable at step `i` has the direct generator's DIMACS number.
The chain uses this variable at steps 1 through 7. -/
theorem prefix_dimacs (s : Bool) (w : Word) (i : Fin 8) :
    (Variable.parityPrefix s w i).index + 1 = 1025 + 8 * wordIndex s w + i.val := by
  simp only [Variable.index]
  omega

def support (C D : Finset (Q 9)) (s : Bool) : Finset (Q 9) :=
  if s then D else C

private def atom (S : Bool → Finset (Q 9)) : Variable → Prop
  | .occupied s w => cubeBitVec 9 w ∈ S s
  | .parityPrefix s w i => prefixParity (S s) (cubeBitVec 9 w) i.castSucc = true

/-- The shared-contact valuation only needs its two supports. -/
noncomputable def valuation (S : Bool → Finset (Q 9)) : Sat.Valuation :=
  Function.extend Variable.index (atom S) (fun _ => False)

theorem valuation_shared {k : Fin 3} (M : Q9SharedContactCNF.Model k) :
    valuation M.support = Q9SharedContactCNF.valuation M := rfl

@[simp] private theorem valuation_index (S : Bool → Finset (Q 9)) (v : Variable) :
    valuation S v.index = atom S v :=
  Variable.index_injective.extend_apply _ _ _

@[simp] theorem valuation_occupied (S : Bool → Finset (Q 9)) (s : Bool) (w : Word) :
    valuation S (occ s w).index ↔ cubeBitVec 9 w ∈ S s := by
  rw [valuation_index]
  rfl

private def upperRow (s : Bool) (w : Word) (L : List Axis) : Sat.Clause :=
  neg (occ s w) :: (L.map fun i => occ s (adjacentWord w i)).map neg

private def lowerRow (s : Bool) (w : Word) (L : List Axis) : Sat.Clause :=
  neg (occ s w) :: (L.map fun i => occ s (adjacentWord w i)).map pos

private def squareRow (s : Bool) (w : Word) (i j : Axis) : Sat.Clause :=
  [neg (occ s w), neg (occ s (adjacentWord w i)),
    neg (occ s (adjacentWord w j)), neg (occ s (adjacentWord (adjacentWord w i) j))]

private def parityRow (s : Bool) (w : Word) (i : Fin 8) (signs : Fin 4) : Sat.Clause :=
  xorClause (prefixVariable s w i.castSucc) (occ s (adjacentWord w i.succ))
    (prefixVariable s w i.succ) signs

private theorem neighbor_value (S : Bool → Finset (Q 9)) (s : Bool) (w : Word) (i : Axis) :
    valuation S (occ s (adjacentWord w i)).index ↔
      directionBit (S s) (cubeBitVec 9 w) i = true := by
  rw [valuation_occupied, adjacentWord_spec, directionBit_eq_occupiedBit_flip]
  simp [occupiedBit]

theorem upperClause {S : Bool → Finset (Q 9)} (s : Bool) (hS : LocalRules (S s)) (w : Word)
    (L : List Axis) (hL : L.toFinset.card = 4) :
    (valuation S).satisfies (upperRow s w L) := by
  intro hx
  apply satisfies_negative_list
  intro hall
  obtain ⟨i, hi, hout⟩ := upperDegree hS ((valuation_occupied S s w).mp hx) hL
  have hmem := hall (occ s (adjacentWord w i))
    (List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, rfl⟩)
  exact Bool.noConfusion (hout.symm.trans ((neighbor_value S s w i).mp hmem))

theorem lowerClause {S : Bool → Finset (Q 9)} (s : Bool) (hS : LocalRules (S s)) (w : Word)
    (L : List Axis) (hL : L.toFinset.card = 7) :
    (valuation S).satisfies (lowerRow s w L) := by
  intro hx
  apply satisfies_positive_list
  intro hall
  obtain ⟨i, hi, hin⟩ := lowerDegree hS ((valuation_occupied S s w).mp hx) hL
  exact hall (occ s (adjacentWord w i)) (List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, rfl⟩)
    ((neighbor_value S s w i).mpr hin)

theorem squareClause {S : Bool → Finset (Q 9)} (s : Bool) (hS : LocalRules (S s))
    (w : Word) (i j : Axis) (hij : i ≠ j) :
    (valuation S).satisfies (squareRow s w i j) := by
  intro hx hi hj hij'
  apply hS.no_square (cubeBitVec 9 w) i j hij
  · exact (valuation_occupied S s w).mp hx
  · simpa only [adjacentWord_spec] using (valuation_occupied S s (adjacentWord w i)).mp hi
  · simpa only [adjacentWord_spec] using (valuation_occupied S s (adjacentWord w j)).mp hj
  · simpa only [adjacentWord_spec] using
      (valuation_occupied S s (adjacentWord (adjacentWord w i) j)).mp hij'

private theorem prefix_value {S : Bool → Finset (Q 9)} (s : Bool) (hS : LocalRules (S s))
    (w : Word) (i : Axis) :
    valuation S (prefixVariable s w i).index ↔ prefixParity (S s) (cubeBitVec 9 w) i = true := by
  by_cases hzero : i = 0
  · subst i
    simp only [prefixVariable, prefixParity_zero]
    exact neighbor_value S s w 0
  by_cases hlast : i = Fin.last 8
  · subst i
    rw [prefixParity_last hS]
    simp [prefixVariable, atom, occupiedBit]
  · simp only [prefixVariable, ite_eq_right hzero, dite_eq_right hlast, valuation_index, atom]
    have he (j : Fin 8) (hj : j.val = i.val) : j.castSucc = i := Fin.ext hj
    rw [he _ rfl]

theorem parityClause {S : Bool → Finset (Q 9)} (s : Bool) (hS : LocalRules (S s))
    (w : Word) (i : Fin 8) (signs : Fin 4) :
    (valuation S).satisfies (parityRow s w i signs) := by
  have hp := prefix_value s hS w i.castSucc
  have hq := neighbor_value S s w i.succ
  have hr := prefix_value s hS w i.succ
  rw [prefixParity_succ] at hr
  generalize ha : prefixParity (S s) (cubeBitVec 9 w) i.castSucc = a at hp hr
  generalize hb : directionBit (S s) (cubeBitVec 9 w) i.succ = b at hq hr
  fin_cases signs <;> cases a <;> cases b <;>
    simp [parityRow, xorClause, Sat.Valuation.satisfies, Sat.Valuation.neg, pos, neg, hp, hq, hr]

private def rootWord (s : Bool) : Word := if s then 15 else 0

private def root (s : Bool) : Q 9 := if s then rightCenter else origin

private theorem cube_rootWord (s : Bool) : cubeBitVec 9 (rootWord s) = root s := by
  cases s <;> funext i <;> fin_cases i <;> decide

private def baseWord (v : Fin 16) : Word := BitVec.ofNat 9 v.val

set_option maxRecDepth 20000 in
private theorem baseWord_shell : ∀ v : Fin 16, exteriorShell (cubeBitVec 9 (baseWord v)) = 0 := by
  decide +kernel

private def baseRequired (s : Bool) (w : Word) : Bool :=
  (List.finRange 4).any (fun i => adjacentWord (rootWord s) ⟨i.val, by omega⟩ == w)

private def exteriorAxis (i : Fin 5) : Axis := ⟨4 + i.val, by omega⟩

private def missingAxis (m : Axis) (s : Bool) : Axis := if s then m else 4

private def signed (b : Bool) (v : Variable) : Sat.Literal := if b then pos v else neg v

private def baseRow (s : Bool) (v : Fin 16) : Sat.Clause :=
  [signed (baseRequired s (baseWord v)) (occ s (baseWord v))]

private def exteriorRow (m : Axis) (s : Bool) (i : Fin 5) : Sat.Clause :=
  [signed (decide (exteriorAxis i ≠ missingAxis m s))
    (occ s (adjacentWord (rootWord s) (exteriorAxis i)))]

private theorem satisfies_signed_unit {S : Bool → Finset (Q 9)} {b s : Bool} {w : Word}
    (h : b = true ↔ cubeBitVec 9 w ∈ S s) :
    (valuation S).satisfies [signed b (occ s w)] := by
  cases b with
  | false =>
    intro hx
    exact Bool.noConfusion (h.mpr ((valuation_occupied S s w).mp hx))
  | true =>
    intro hx
    exact hx ((valuation_occupied S s w).mpr (h.mp rfl))

theorem baseClause {C D : Finset (Q 9)} {m : Axis} (h : DirectGeometry C D m)
    (s : Bool) (v : Fin 16) :
    (valuation (support C D)).satisfies (baseRow s v) := by
  apply satisfies_signed_unit
  have hbase : cubeBitVec 9 (baseWord v) ∈ support C D s ↔
      ∃ i ∈ baseAxes, flip (root s) i = cubeBitVec 9 (baseWord v) := by
    cases s
    · exact (h.base_membership (baseWord_shell v)).1
    · exact (h.base_membership (baseWord_shell v)).2
  rw [hbase]
  simp only [baseRequired, List.any_eq_true, List.mem_finRange, true_and, beq_iff_eq]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨⟨i.val, by omega⟩, Finset.mem_filter.mpr ⟨mem_univ _, i.isLt⟩, ?_⟩
    simpa only [adjacentWord_spec, cube_rootWord] using congrArg (cubeBitVec 9) hi
  · rintro ⟨i, hi, he⟩
    have hilt : i.val < 4 := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val, hilt⟩, (cubeBitVec 9).injective ?_⟩
    simpa only [adjacentWord_spec, cube_rootWord] using he

theorem exteriorClause {C D : Finset (Q 9)} {m : Axis} (h : DirectGeometry C D m)
    (s : Bool) (i : Fin 5) :
    (valuation (support C D)).satisfies (exteriorRow m s i) := by
  have hstar : DirectStar (support C D s) (root s) (missingAxis m s) := by
    cases s
    · exact h.left_star
    · exact h.right_star
  apply satisfies_signed_unit
  rw [decide_eq_true_eq, adjacentWord_spec, cube_rootWord]
  exact (hstar.external_neighbor (exteriorAxis i)).symm

private def crossRow (u v : Word) : Sat.Clause :=
  [neg (occ false u), neg (occ true v)]

theorem separationClause {C D : Finset (Q 9)} {m : Axis} (h : DirectGeometry C D m)
    (u v : Word) (hd : hammingDist (cubeBitVec 9 u) (cubeBitVec 9 v) ≤ 1) :
    (valuation (support C D)).satisfies (crossRow u v) := by
  intro hu hv
  exact h.forbidden_close ((valuation_occupied (support C D) false u).mp hu) hd
    ((valuation_occupied (support C D) true v).mp hv)

theorem oddExteriorPairClause {C D : Finset (Q 9)} {m : Axis} (h : DirectGeometry C D m)
    (w : Word) (i j : Axis) (hp : parity (cubeBitVec 9 w) = true) (hij : i ≠ j)
    (hext : i ∉ baseAxes ∨ j ∉ baseAxes) :
    (valuation (support C D)).satisfies (crossRow w (adjacentWord (adjacentWord w i) j)) := by
  intro hu hv
  apply h.forbidden_pair_flip ((valuation_occupied (support C D) false w).mp hu) hp hij hext
  simpa [adjacentWord_spec, support] using
    (valuation_occupied (support C D) true (adjacentWord (adjacentWord w i) j)).mp hv

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF

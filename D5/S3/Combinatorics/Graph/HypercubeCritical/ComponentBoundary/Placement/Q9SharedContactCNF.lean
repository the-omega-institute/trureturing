/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Normalized shared-contact supports satisfy the degree, parity and geometric clauses. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactClauseSemantics
import Mathlib.Tactic.Sat.FromLRAT

/-! The local geometric constraints generate satisfied clauses in the normalized cube. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF

open Finset
open BalancedCriticalSpectrum (Q flip)
open D5.S3.Combinatorics.Graph.HypercubeCritical
  (cubeBitVec cubeBitVec_xor_single)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (origin)
open Q9SharedContactAxisOrbits (canonicalDifference canonicalLeft canonicalRight)
open Q9SharedContactNormalized (LocalRules)
open Q9SharedContactClauseSemantics

abbrev Word := BitVec 9
abbrev Axis := Fin 9

/-- The two supports in one of the three normalized shared-contact cases. -/
structure Model (k : Fin 3) where
  support : Bool → Finset (Q 9)
  localRules : ∀ s, LocalRules (support s)
  separate : ∀ x ∈ support false, ∀ y ∈ support true, 3 ≤ hammingDist x y
  leftRoot : canonicalDifference ∈ support false
  rightRoot : origin ∈ support true
  leftDirection : ∀ i, canonicalLeft k i = true → flip canonicalDifference i ∈ support false
  rightDirection : ∀ i, canonicalRight i = true → flip origin i ∈ support true

/-- Each variable is either a vertex's membership or a prefix parity in its neighbor list. -/
inductive Variable
  | occupied (side : Bool) (word : Word)
  | parityPrefix (side : Bool) (word : Word) (i : Fin 8)

def wordIndex (side : Bool) (word : Word) : ℕ :=
  (if side then 512 else 0) + word.toNat

def Variable.index : Variable → ℕ
  | .occupied s w => wordIndex s w
  | .parityPrefix s w i => 1024 + 8 * wordIndex s w + i.val

private theorem wordIndex_lt (s : Bool) (w : Word) : wordIndex s w < 1024 := by
  have hw : w.toNat < 512 := w.toFin.isLt
  cases s <;> simp [wordIndex] <;> omega

private theorem same_wordIndex {s t : Bool} {u v : Word}
    (h : wordIndex s u = wordIndex t v) : s = t ∧ u = v := by
  have hu : u.toNat < 512 := u.toFin.isLt
  have hv : v.toNat < 512 := v.toFin.isLt
  cases s <;> cases t <;> simp [wordIndex] at h ⊢
  · exact BitVec.eq_of_toNat_eq h
  · omega
  · omega
  · exact BitVec.eq_of_toNat_eq (by omega)

theorem Variable.index_injective : Function.Injective Variable.index := by
  intro a b h
  cases a with
  | occupied s u =>
    cases b with
    | occupied t v =>
      obtain ⟨rfl, rfl⟩ := same_wordIndex h
      rfl
    | parityPrefix t v j =>
      have hu := wordIndex_lt s u
      simp only [Variable.index] at h
      omega
  | parityPrefix s u i =>
    cases b with
    | occupied t v =>
      have hv := wordIndex_lt t v
      simp only [Variable.index] at h
      omega
    | parityPrefix t v j =>
      simp only [Variable.index] at h
      have hw : wordIndex s u = wordIndex t v := by omega
      obtain ⟨rfl, rfl⟩ := same_wordIndex hw
      congr 1
      exact Fin.ext (by omega)

private def atom {k : Fin 3} (M : Model k) : Variable → Prop
  | .occupied s w => cubeBitVec 9 w ∈ M.support s
  | .parityPrefix s w i => prefixParity (M.support s) (cubeBitVec 9 w) i.castSucc = true

def valuation {k : Fin 3} (M : Model k) : Sat.Valuation :=
  Function.extend Variable.index (atom M) (fun _ => False)

@[simp] theorem valuation_index {k : Fin 3} (M : Model k) (v : Variable) :
    valuation M v.index = atom M v :=
  Variable.index_injective.extend_apply _ _ _

private def adjacentWord (w : Word) (i : Axis) : Word :=
  w ^^^ BitVec.ofNat 9 (2 ^ i.val)

private theorem adjacentWord_spec (w : Word) (i : Axis) :
    cubeBitVec 9 (adjacentWord w i) = flip (cubeBitVec 9 w) i :=
  cubeBitVec_xor_single w i

def pos (v : Variable) : Sat.Literal := .pos v.index

def neg (v : Variable) : Sat.Literal := .neg v.index

private abbrev occ := Variable.occupied

private theorem satisfies_negative_list {v : Sat.Valuation} {vars : List Variable}
    (h : (∀ z ∈ vars, v z.index) → False) :
    v.satisfies (vars.map neg) := by
  induction vars with
  | nil =>
    exact h (by simp)
  | cons z zs ih =>
    intro hz
    apply ih
    intro hs
    apply h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hz
    · exact hs a ha

private theorem satisfies_positive_list {v : Sat.Valuation} {vars : List Variable}
    (h : (∀ z ∈ vars, ¬v z.index) → False) :
    v.satisfies (vars.map pos) := by
  induction vars with
  | nil =>
    exact h (by simp)
  | cons z zs ih =>
    intro hz
    apply ih
    intro hs
    apply h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hz
    · exact hs a ha

theorem upperClause {k : Fin 3} (M : Model k) (s : Bool) (w : Word)
    (L : List Axis) (hL : L.toFinset.card = 4) :
    (valuation M).satisfies (neg (occ s w) :: (L.map (fun i => occ s (adjacentWord w i))).map neg) := by
  intro hx
  have hx' : cubeBitVec 9 w ∈ M.support s := by simpa [Sat.Valuation.neg, neg, atom] using hx
  apply satisfies_negative_list
  intro h
  obtain ⟨i, hi, hout⟩ := upperDegree (M.localRules s) hx' hL
  have hi' : i ∈ L := List.mem_toFinset.mp hi
  have hy := h (occ s (adjacentWord w i)) (List.mem_map.mpr ⟨i, hi', rfl⟩)
  have hmem : flip (cubeBitVec 9 w) i ∈ M.support s := by simpa [Sat.Valuation.neg, neg, atom, adjacentWord_spec] using hy
  rw [directionBit_eq_occupiedBit_flip, occupiedBit, Bool.decide_true hmem] at hout
  exact Bool.noConfusion hout

theorem lowerClause {k : Fin 3} (M : Model k) (s : Bool) (w : Word)
    (L : List Axis) (hL : L.toFinset.card = 7) :
    (valuation M).satisfies (neg (occ s w) :: (L.map (fun i => occ s (adjacentWord w i))).map pos) := by
  intro hx
  have hx' : cubeBitVec 9 w ∈ M.support s := by simpa [Sat.Valuation.neg, neg, atom] using hx
  apply satisfies_positive_list
  intro h
  obtain ⟨i, hi, hin⟩ := lowerDegree (M.localRules s) hx' hL
  have hi' : i ∈ L := List.mem_toFinset.mp hi
  have hnot := h (occ s (adjacentWord w i)) (List.mem_map.mpr ⟨i, hi', rfl⟩)
  rw [directionBit_eq_occupiedBit_flip, occupiedBit] at hin
  apply hnot
  simp [Sat.Valuation.neg, neg, atom, adjacentWord_spec, of_decide_eq_true hin]

theorem squareClause {k : Fin 3} (M : Model k) (s : Bool)
    (w : Word) (i j : Axis) (hij : i ≠ j) :
    (valuation M).satisfies [neg (occ s w), neg (occ s (adjacentWord w i)),
      neg (occ s (adjacentWord w j)), neg (occ s (adjacentWord (adjacentWord w i) j))] := by
  intro hx hi hj hij'
  apply (M.localRules s).no_square (cubeBitVec 9 w) i j hij
  · simpa [Sat.Valuation.neg, neg, atom] using hx
  · simpa [Sat.Valuation.neg, neg, atom, adjacentWord_spec] using hi
  · simpa [Sat.Valuation.neg, neg, atom, adjacentWord_spec] using hj
  · simpa [Sat.Valuation.neg, neg, atom, adjacentWord_spec] using hij'

theorem separationClause {k : Fin 3} (M : Model k) (u v : Word)
    (h : hammingDist (cubeBitVec 9 u) (cubeBitVec 9 v) ≤ 2) :
    (valuation M).satisfies [neg (occ false u), neg (occ true v)] := by
  intro hu hv
  have hn := M.separate (cubeBitVec 9 u) (by simpa [Sat.Valuation.neg, neg, atom] using hu)
    (cubeBitVec 9 v) (by simpa [Sat.Valuation.neg, neg, atom] using hv)
  omega

private def prefixVariable (s : Bool) (w : Word) (i : Axis) : Variable :=
  if i = 0 then occ s (adjacentWord w i)
  else if h : i = Fin.last 8 then occ s w
  else .parityPrefix s w ⟨i.val, by
    have hi : i.val ≠ 8 := fun he => h (Fin.ext he)
    omega⟩

private theorem neighbor_value {k : Fin 3} (M : Model k) (s : Bool) (w : Word) (i : Axis) :
    valuation M (occ s (adjacentWord w i)).index ↔
      directionBit (M.support s) (cubeBitVec 9 w) i = true := by
  simp [atom, adjacentWord_spec, directionBit_eq_occupiedBit_flip, occupiedBit]

private theorem prefix_value {k : Fin 3} (M : Model k) (s : Bool) (w : Word) (i : Axis) :
    valuation M (prefixVariable s w i).index ↔
      prefixParity (M.support s) (cubeBitVec 9 w) i = true := by
  by_cases hzero : i = 0
  · subst i
    simp only [prefixVariable, prefixParity_zero]
    exact neighbor_value M s w 0
  by_cases hlast : i = Fin.last 8
  · subst i
    rw [prefixParity_last (M.localRules s)]
    simp [prefixVariable, atom, occupiedBit]
  · simp only [prefixVariable, ite_eq_right hzero, dite_eq_right hlast, valuation_index, atom]
    have he (j : Fin 8) (hj : j.val = i.val) : j.castSucc = i := Fin.ext hj
    rw [he _ rfl]

private def xorClause (a b c : Variable) (polarity : Fin 4) : Sat.Clause :=
  ![[neg a, neg b, neg c], [pos a, pos b, neg c],
    [pos a, neg b, pos c], [neg a, pos b, pos c]] polarity

theorem parityClause {k : Fin 3} (M : Model k) (s : Bool) (w : Word)
    (i : Fin 8) (polarity : Fin 4) :
    (valuation M).satisfies
      (xorClause (prefixVariable s w i.castSucc) (occ s (adjacentWord w i.succ))
        (prefixVariable s w i.succ) polarity) := by
  have hp := prefix_value M s w i.castSucc
  have hq := neighbor_value M s w i.succ
  have hr := prefix_value M s w i.succ
  rw [prefixParity_succ] at hr
  generalize ha : prefixParity (M.support s) (cubeBitVec 9 w) i.castSucc = a at hp hr
  generalize hb : directionBit (M.support s) (cubeBitVec 9 w) i.succ = b at hq hr
  fin_cases polarity <;> cases a <;> cases b <;>
    simp [xorClause, Sat.Valuation.satisfies, Sat.Valuation.neg, pos, neg, hp, hq, hr]

private theorem left_root_word : cubeBitVec 9 (7 : Word) = canonicalDifference := by
  funext i
  fin_cases i <;> decide

private theorem right_root_word : cubeBitVec 9 (0 : Word) = origin := by
  funext i
  fin_cases i <;> decide

theorem leftRootClause {k : Fin 3} (M : Model k) :
    (valuation M).satisfies [pos (occ false 7)] := by
  intro h
  apply h
  change valuation M (occ false 7).index
  rw [valuation_index]
  change cubeBitVec 9 (7 : Word) ∈ M.support false
  rw [left_root_word]
  exact M.leftRoot

theorem rightRootClause {k : Fin 3} (M : Model k) :
    (valuation M).satisfies [pos (occ true 0)] := by
  intro h
  apply h
  change valuation M (occ true 0).index
  rw [valuation_index]
  change cubeBitVec 9 (0 : Word) ∈ M.support true
  rw [right_root_word]
  exact M.rightRoot

theorem leftDirectionClause {k : Fin 3} (M : Model k) (i : Axis)
    (hi : canonicalLeft k i = true) :
    (valuation M).satisfies [pos (occ false (adjacentWord 7 i))] := by
  intro h
  apply h
  change valuation M (occ false (adjacentWord 7 i)).index
  rw [valuation_index]
  change cubeBitVec 9 (adjacentWord 7 i) ∈ M.support false
  rw [adjacentWord_spec, left_root_word]
  exact M.leftDirection i hi

theorem rightDirectionClause {k : Fin 3} (M : Model k) (i : Axis)
    (hi : canonicalRight i = true) :
    (valuation M).satisfies [pos (occ true (adjacentWord 0 i))] := by
  intro h
  apply h
  change valuation M (occ true (adjacentWord 0 i)).index
  rw [valuation_index]
  change cubeBitVec 9 (adjacentWord 0 i) ∈ M.support true
  rw [adjacentWord_spec, right_root_word]
  exact M.rightDirection i hi

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF

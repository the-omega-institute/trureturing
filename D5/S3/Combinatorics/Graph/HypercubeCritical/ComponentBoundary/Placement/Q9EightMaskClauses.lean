/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskClauses
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskClauses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A realized displacement supplies an occupied pair in the normalized cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisMissingContact
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF

/-! The contact witnesses used by the compact eight-mask refutation. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses

open Finset
open BalancedCriticalSpectrum (Q)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedContactCNF (Word Axis Variable pos neg)
open Q9FiveAxisMissingContact (Geometry firstFiveAxes missingMask rightRoot)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (origin)
open Q9TightDistanceTwoCNF (support)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open private differingAxes mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

private abbrev occ := Variable.occupied

/-- Every consecutive pair of words contains exactly one even word. -/
private def evenWord (i : Fin 256) : Word :=
  let x := BitVec.ofNat 9 (2 * i.val)
  if parity (cubeBitVec 9 x) = false then x else x + 1

private def indexOfWord (x : Word) : Fin 256 := ⟨x.toNat / 2, by
  have hx : x.toNat < 512 := x.toFin.isLt
  omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the 512 words.
private theorem evenWord_index : ∀ x : Word,
    parity (cubeBitVec 9 x) = false → evenWord (indexOfWord x) = x := by
  decide +kernel

private def witnessMasks : Fin 8 → Word := ![3, 5, 9, 10, 12, 17, 18, 20]

private def witnessIndex (m : Fin 8) (i : Fin 256) : ℕ := 10240 + 256 * m.val + i.val

/-- The displacement family supplied by the chosen eight-mask normalization. -/
def normalizedFamily : Finset (Finset Axis) :=
  firstFiveAxes.powersetCard 2 \ {missingMask, ({3, 4} : Finset Axis)}

noncomputable def witnessValuation (C D : Finset (Q 9)) : Sat.Valuation := fun n =>
  if hn : 10240 ≤ n ∧ n < 12288 then
    let k := n - 10240
    let m : Fin 8 := ⟨k / 256, by omega⟩
    let i : Fin 256 := ⟨k % 256, Nat.mod_lt _ (by decide)⟩
    cubeBitVec 9 (evenWord i) ∈ C ∧ cubeBitVec 9 (evenWord i ^^^ witnessMasks m) ∈ D
  else Q9TightDistanceTwoCNF.valuation (support C D) n

private theorem witness_value (C D : Finset (Q 9)) (m : Fin 8) (i : Fin 256) :
    witnessValuation C D (witnessIndex m i) ↔
      cubeBitVec 9 (evenWord i) ∈ C ∧ cubeBitVec 9 (evenWord i ^^^ witnessMasks m) ∈ D := by
  have hm := m.isLt
  have hi := i.isLt
  have hn : 10240 ≤ witnessIndex m i ∧ witnessIndex m i < 12288 := by
    unfold witnessIndex
    omega
  have hdiv : (witnessIndex m i - 10240) / 256 = m.val := by
    unfold witnessIndex
    omega
  have hmod : (witnessIndex m i - 10240) % 256 = i.val := by
    unfold witnessIndex
    omega
  have hM (h : ((witnessIndex m i - 10240) / 256) < 8) :
      (⟨(witnessIndex m i - 10240) / 256, h⟩ : Fin 8) = m := Fin.ext hdiv
  have hI (h : ((witnessIndex m i - 10240) % 256) < 256) :
      (⟨(witnessIndex m i - 10240) % 256, h⟩ : Fin 256) = i := Fin.ext hmod
  simp only [witnessValuation, dite_eq_left hn, hM, hI]

private theorem variable_index_lt (v : Variable) : v.index < 10240 := by
  cases v with
  | occupied s w =>
    have hw : w.toNat < 512 := w.toFin.isLt
    cases s <;> simp [Variable.index, Q9SharedContactCNF.wordIndex] <;> omega
  | parityPrefix s w i =>
    have hw : w.toNat < 512 := w.toFin.isLt
    have hi := i.isLt
    cases s <;> simp [Variable.index, Q9SharedContactCNF.wordIndex] <;> omega

private theorem ordinary_value (C D : Finset (Q 9)) (v : Variable) :
    witnessValuation C D v.index = Q9TightDistanceTwoCNF.valuation (support C D) v.index := by
  have hn : ¬ (10240 ≤ v.index ∧ v.index < 12288) :=
    fun h => (Nat.not_le_of_lt (variable_index_lt v)) h.1
  simp only [witnessValuation, dite_eq_right hn]

theorem witnesses_imply_left {C D : Finset (Q 9)} (m : Fin 8) (i : Fin 256) :
    (witnessValuation C D).satisfies
      [.neg (witnessIndex m i), pos (occ false (evenWord i))] := by
  intro hw ha
  apply ha
  rw [ordinary_value]
  exact (Q9TightDistanceTwoCNF.valuation_occupied _ _ _).mpr ((witness_value C D m i).mp hw).1

theorem witnesses_imply_right {C D : Finset (Q 9)} (m : Fin 8) (i : Fin 256) :
    (witnessValuation C D).satisfies
      [.neg (witnessIndex m i), pos (occ true (evenWord i ^^^ witnessMasks m))] := by
  intro hw ha
  apply ha
  rw [ordinary_value]
  exact (Q9TightDistanceTwoCNF.valuation_occupied _ _ _).mpr ((witness_value C D m i).mp hw).2

private theorem positive_list {v : Sat.Valuation} {indices : List ℕ}
    (h : ∃ i ∈ indices, v i) : v.satisfies (indices.map Sat.Literal.pos) := by
  induction indices with
  | nil => simp at h
  | cons x xs ih =>
    intro hx
    obtain ⟨i, hi, hv⟩ := h
    rcases List.mem_cons.mp hi with rfl | hi
    · exact False.elim (hx hv)
    · exact ih ⟨i, hi, hv⟩

/-- Every realized mask supplies a true witness literal in the enumeration
of all even starting words. -/
theorem realizedClause {C D : Finset (Q 9)} (m : Fin 8)
    (h : ∃ x : Word, parity (cubeBitVec 9 x) = false ∧ cubeBitVec 9 x ∈ C ∧
      cubeBitVec 9 (x ^^^ witnessMasks m) ∈ D) :
    (witnessValuation C D).satisfies
      ((List.finRange 256).map (fun i => Sat.Literal.pos (witnessIndex m i))) := by
  obtain ⟨x, hp, hx, hy⟩ := h
  have hw := (witness_value C D m (indexOfWord x)).mpr
    (by rw [evenWord_index x hp]; exact ⟨hx, hy⟩)
  have hmem : witnessIndex m (indexOfWord x) ∈ (List.finRange 256).map (witnessIndex m) :=
    List.mem_map.mpr ⟨indexOfWord x, List.mem_finRange (indexOfWord x), rfl⟩
  have hs := positive_list (v := witnessValuation C D) ⟨_, hmem, hw⟩
  rw [List.map_map] at hs
  exact hs

private def literalIndex : Sat.Literal → ℕ
  | .pos n => n
  | .neg n => n

/-- Auxiliary contact witnesses leave the original cubicity and parity rows intact. -/
theorem ordinaryClause {C D : Finset (Q 9)} {c : Sat.Clause}
    (h : (Q9TightDistanceTwoCNF.valuation (support C D)).satisfies c)
    (hsmall : List.all c (fun l => decide (literalIndex l < 10240)) = true) :
    (witnessValuation C D).satisfies c := by
  change List Sat.Literal at c
  induction c with
  | nil => exact h
  | cons x xs ih =>
    rw [List.all_cons, Bool.and_eq_true] at hsmall
    have hsize : literalIndex x < 10240 := of_decide_eq_true hsmall.1
    have he : witnessValuation C D (literalIndex x) =
        Q9TightDistanceTwoCNF.valuation (support C D) (literalIndex x) := by
      have hn : ¬ (10240 ≤ literalIndex x ∧ literalIndex x < 12288) :=
        fun ho => (Nat.not_le_of_lt hsize) ho.1
      simp only [witnessValuation, dite_eq_right hn]
    intro hx
    refine ih (h ?_) hsmall.2
    cases x <;> simp only [literalIndex] at he <;>
      simpa only [Sat.Valuation.neg, ← he] using hx

private def rootWord (s : Bool) : Word := if s then 3 else 0

private theorem rootWord_cube (s : Bool) :
    cubeBitVec 9 (rootWord s) = if s then rightRoot else origin := by
  cases s <;> funext i <;> fin_cases i <;> decide

theorem rootClause {C D : Finset (Q 9)} (h : Geometry C D) (s : Bool) :
    (witnessValuation C D).satisfies [pos (occ s (rootWord s))] := by
  intro hn
  apply hn
  rw [ordinary_value]
  apply (Q9TightDistanceTwoCNF.valuation_occupied _ _ _).mpr
  cases s
  · simpa [rootWord_cube, support] using h.left_root
  · simpa [rootWord_cube, support] using h.right_root

theorem closeClause {C D : Finset (Q 9)} (h : Geometry C D)
    (x y : Word) (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) ≤ 1) :
    (witnessValuation C D).satisfies [neg (occ false x), neg (occ true y)] := by
  intro hx hy
  change witnessValuation C D (occ false x).index at hx
  change witnessValuation C D (occ true y).index at hy
  rw [ordinary_value] at hx hy
  exact h.forbidden_close ((Q9TightDistanceTwoCNF.valuation_occupied _ _ _).mp hx) hd
    ((Q9TightDistanceTwoCNF.valuation_occupied _ _ _).mp hy)

private def axesOf (w : Word) : Finset Axis := univ.filter fun i => w.getLsbD i.val

private theorem xor_mask {u v : Word} :
    differingAxes (cubeBitVec 9 u) (cubeBitVec 9 v) = axesOf (u ^^^ v) := by
  ext i
  rw [show i ∈ axesOf (u ^^^ v) ↔ (u ^^^ v).getLsbD i.val = true by simp [axesOf]]
  rw [BitVec.getLsbD_xor]
  have hD : i ∈ differingAxes (cubeBitVec 9 u) (cubeBitVec 9 v) ↔
      u.getLsbD i.val ≠ v.getLsbD i.val := by
    unfold differingAxes
    constructor
    · exact fun h => (mem_filter.mp h).2
    · exact fun h => mem_filter.mpr ⟨mem_univ _, h⟩
  rw [hD]
  cases u.getLsbD i.val <;> cases v.getLsbD i.val <;> decide

/-- Every two-flip even contact uses a mask in the normalized family. -/
theorem absentMaskClause {C D : Finset (Q 9)}
    (hfamily : minimumDisplacements C D false 2 = normalizedFamily) (x y : Word)
    (hp : parity (cubeBitVec 9 x) = false)
    (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 2)
    (hbad : axesOf (x ^^^ y) ∉ normalizedFamily) :
    (witnessValuation C D).satisfies [neg (occ false x), neg (occ true y)] := by
  intro hx hy
  change witnessValuation C D (occ false x).index at hx
  change witnessValuation C D (occ true y).index at hy
  rw [ordinary_value] at hx hy
  apply hbad
  rw [← xor_mask, ← hfamily]
  exact mem_minimumDisplacements.mpr
    ⟨_, (Q9TightDistanceTwoCNF.valuation_occupied _ _ _).mp hx,
      _, (Q9TightDistanceTwoCNF.valuation_occupied _ _ _).mp hy, hp, hd, rfl⟩

/-- A realized displacement gives the associated pair of bit words. -/
private theorem realizedOfMask {C D : Finset (Q 9)} (m : Fin 8)
    (hm : axesOf (witnessMasks m) ∈ minimumDisplacements C D false 2) :
    ∃ x : Word, parity (cubeBitVec 9 x) = false ∧ cubeBitVec 9 x ∈ C ∧
      cubeBitVec 9 (x ^^^ witnessMasks m) ∈ D := by
  obtain ⟨x, hx, y, hy, hp, _, hmask⟩ := mem_minimumDisplacements.mp hm
  obtain ⟨u, rfl⟩ := (cubeBitVec 9).surjective x
  obtain ⟨v, rfl⟩ := (cubeBitVec 9).surjective y
  have hax : axesOf (u ^^^ v) = axesOf (witnessMasks m) := xor_mask.symm.trans hmask
  have he : u ^^^ v = witnessMasks m := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h := (Finset.ext_iff.mp hax ⟨j, hj⟩)
    simp only [axesOf, mem_filter, mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h
  have hv : u ^^^ witnessMasks m = v := by
    rw [← he, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  exact ⟨u, hp, hx, hv.symm ▸ hy⟩

private theorem witnessMask_mem (m : Fin 8) : axesOf (witnessMasks m) ∈ normalizedFamily := by
  fin_cases m <;> decide +kernel

/-- The normalized family contains the mask for every required witness row. -/
theorem normalizedRealizedClause {C D : Finset (Q 9)}
    (hfamily : minimumDisplacements C D false 2 = normalizedFamily) (m : Fin 8) :
    (witnessValuation C D).satisfies
      ((List.finRange 256).map (fun i => Sat.Literal.pos (witnessIndex m i))) :=
  realizedClause m (realizedOfMask m (by rw [hfamily]; exact witnessMask_mem m))

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses

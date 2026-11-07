/- GID: D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/ElongatedTriangularDualCoordination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Distances and coordination shells in the elongated triangular dual net. -/

/-
admission_basis: open-problem-resolution (#27565; Proved)
escape_witness: geodesic (constructs an attaining walk for every vertex;
  consumed by distance_formula and the shell and series identities).
Direct frozen dependency:
D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.potential_dist
statement_id: sha256:2360c26ddcdab5109d1906cf2b6884cebb254549f8cf9a5078002397a1098f09
frozen_module_statement_id: sha256:f8b677ea402e38581fbfa04887d18040684e7baa21f05cad6421d45525c0cd21
Vertex: proof_shape=bind-only; consumers=graph, distance, a
Vertex.S: proof_shape=bind-only; consumers=adjacent, decode
Vertex.U: proof_shape=bind-only; consumers=adjacent, root, decode
Vertex.D: proof_shape=bind-only; consumers=adjacent, decode
adjacent: proof_shape=bind-only; consumers=graph, score_step, score_descent
graph: proof_shape=bind-only; consumers=distance, geodesic, distance_formula
root: proof_shape=bind-only; consumers=distance, score_zero, geodesic, distance_formula
distance: proof_shape=bind-only; consumers=a, distance_formula, actualShell_mem
a: proof_shape=bind-only; consumers=a_card, a_formula, shell_tail, coefficient_identity, result
row: proof_shape=bind-only; consumers=score, rowShell_mem, strip_mem, decode_score
score: proof_shape=bind-only; consumers=score_nonneg, score_zero, score_step, score_descent, geodesic
score_nonneg: proof_shape=bind-only; consumers=geodesic, distance_formula, actualShell_mem
score_zero: proof_shape=bind-only; consumers=geodesic
score_step: proof_shape=bind-only; consumers=distance_formula
score_descent: proof_shape=bind-only; consumers=geodesic
geodesic: proof_shape=content; consumers=distance_formula
distance_formula: proof_shape=content; consumers=actualShell_mem
rowShell: proof_shape=bind-only; consumers=rowShell_mem, rowShell_card, strip
rowShell_mem: proof_shape=bind-only; consumers=strip_mem
rowShell_card: proof_shape=bind-only; consumers=strip_card
strip: proof_shape=bind-only; consumers=strip_mem, strip_card, shellCoords
strip_mem: proof_shape=bind-only; consumers=shellCoords_mem
strip_card: proof_shape=bind-only; consumers=a_formula
Coords: proof_shape=bind-only; consumers=decode, encode, coordinateEquiv, shellCoords
decode: proof_shape=bind-only; consumers=coordinateEquiv, decode_score, centralShell_mem
encode: proof_shape=bind-only; consumers=coordinateEquiv
coordinateEquiv: proof_shape=bind-only; consumers=actualShell, actualShell_mem
offset: proof_shape=bind-only; consumers=decode_score, shellCoords, a_formula
width: proof_shape=bind-only; consumers=decode_score, shellCoords, a_formula
decode_score: proof_shape=bind-only; consumers=shellCoords_mem
centralShell: proof_shape=bind-only; consumers=centralShell_mem, centralShell_card, shellCoords
centralShell_mem: proof_shape=bind-only; consumers=shellCoords_mem
centralShell_card: proof_shape=bind-only; consumers=a_formula
shellCoords: proof_shape=bind-only; consumers=shellCoords_mem, actualShell, a_formula
shellCoords_mem: proof_shape=bind-only; consumers=actualShell_mem
actualShell: proof_shape=bind-only; consumers=actualShell_mem, shell_finite, a_card
actualShell_mem: proof_shape=content; consumers=shell_finite, a_card
shell_finite: proof_shape=content; consumers=a_card
a_card: proof_shape=content; consumers=a_formula
stripCount: proof_shape=bind-only; consumers=a_formula, shell_tail, coefficient_identity
a_formula: proof_shape=content; consumers=shell_tail, coefficient_identity
shell_tail: proof_shape=content; consumers=coefficient_identity
coefficient_identity: proof_shape=content; consumers=result
result: proof_shape=content; consumers=terminal result
-/

import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! The face adjacency graph of the elongated triangular tiling. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.StatisticalMechanics.ElongatedTriangularDualCoordination

/-- Squares, upward triangles and downward triangles, with integral strip coordinates. -/
inductive Vertex
  | S (m k : ℤ)
  | U (m k : ℤ)
  | D (m k : ℤ)
  deriving DecidableEq

private def adjacent : Vertex → Vertex → Prop
  | .S m k, .S p q => m = p ∧ (k = q + 1 ∨ q = k + 1)
  | .S m k, .U p q => m = p ∧ k = q
  | .U m k, .S p q => m = p ∧ k = q
  | .S m k, .D p q => m = p + 1 ∧ k = q
  | .D m k, .S p q => p = m + 1 ∧ k = q
  | .U m k, .D p q => m = p ∧ (q = k - 1 ∨ q = k)
  | .D m k, .U p q => m = p ∧ (k = q - 1 ∨ k = q)
  | _, _ => False

/-- The symmetric edge adjacency of the square and triangular faces. -/
def graph : SimpleGraph Vertex where
  Adj := adjacent
  symm := ⟨by intro u v h; cases u <;> cases v <;> simp only [adjacent] at * <;> omega⟩
  loopless := ⟨by intro u h; cases u <;> simp only [adjacent] at h <;> omega⟩

/-- The upward triangle at the origin. -/
def root : Vertex := .U 0 0

/-- The shortest walk distance from the upward triangle at the origin. -/
def distance (v : Vertex) : ℕ := graph.dist root v

/-- The natural cardinality of the distance shell. -/
def a (n : ℕ) : ℕ := Set.ncard {v | distance v = n}

private def row (b l u k : ℤ) : ℤ := b + max 0 (max (l - k) (k - u))

private def score : Vertex → ℤ
  | .S m k => if m ≤ 0 then row (1 - 3*m) 0 (-m) k
      else row (3*m - 1) (-m) 0 k
  | .U m k => if m = 0 then min (2 * |k|) (|k| + 2)
      else if m < 0 then row (-3*m) 0 (-m) k else row (3*m) (-m) 0 k
  | .D m k => if m = 0 then min |2*k+1| (min |k| |k+1| + 3)
      else if m < 0 then row (-3*m-1) 0 (-m-1) k else row (3*m+1) (-m-1) 0 k

private lemma score_nonneg (v : Vertex) : 0 ≤ score v := by
  cases v <;> simp only [score, row, abs_eq_max_neg, max_def, min_def] <;> split_ifs at * <;> omega

private lemma score_zero (v : Vertex) : score v = 0 ↔ v = root := by
  cases v <;> simp only [score, row, root, Vertex.U.injEq, reduceCtorEq, abs_eq_max_neg, max_def, min_def] <;> split_ifs at * <;> simp_all <;> omega

set_option maxHeartbeats 2000000 in
private lemma score_step (v w : Vertex) (h : graph.Adj v w) : score v ≤ score w + 1 := by
  cases v <;> cases w <;> simp only [graph, adjacent] at h
  all_goals try contradiction
  all_goals
    rename_i m k p q
    by_cases hm0 : m = 0 <;> by_cases hmn : m < 0 <;> by_cases hml : m ≤ 0 <;>
      by_cases hp0 : p = 0 <;> by_cases hpn : p < 0 <;> by_cases hpl : p ≤ 0
    all_goals simp only [score, hm0, hmn, hml, hp0, hpn, hpl,
      ite_true, ite_false, row, abs_eq_max_neg] <;> omega

set_option maxHeartbeats 2000000 in
private lemma score_descent (v : Vertex) (hv : 0 < score v) :
    ∃ w, graph.Adj v w ∧ score w = score v - 1 := by
  cases v with
  | S m k =>
    have h : score (.S m (k-1)) = score (.S m k) - 1 ∨
        score (.S m (k+1)) = score (.S m k) - 1 ∨
        score (.U m k) = score (.S m k) - 1 ∨
        score (.D (m-1) k) = score (.S m k) - 1 := by
      by_cases hm0 : m = 0 <;> by_cases hmn : m < 0 <;> by_cases hml : m ≤ 0 <;>
        by_cases hd0 : m-1 = 0 <;> by_cases hdn : m-1 < 0 <;>
        by_cases hsl : m+1 ≤ 0
      all_goals simp only [score, hm0, hmn, hml, hd0, hdn, hsl,
        ite_true, ite_false, row, abs_eq_max_neg] at hv ⊢ <;> omega
    rcases h with h | h | h | h
    · exact ⟨.S m (k-1), by simp [graph, adjacent], h⟩
    · exact ⟨.S m (k+1), by simp [graph, adjacent], h⟩
    · exact ⟨.U m k, by simp [graph, adjacent], h⟩
    · exact ⟨.D (m-1) k, by simp [graph, adjacent], h⟩
  | U m k =>
    have h : score (.S m k) = score (.U m k) - 1 ∨
        score (.D m k) = score (.U m k) - 1 ∨
        score (.D m (k-1)) = score (.U m k) - 1 := by
      by_cases hm0 : m = 0 <;> by_cases hmn : m < 0 <;> by_cases hml : m ≤ 0 <;>
        by_cases hd0 : m-1 = 0 <;> by_cases hdn : m-1 < 0 <;>
        by_cases hsl : m+1 ≤ 0
      all_goals simp only [score, hm0, hmn, hml, hd0, hdn, hsl,
        ite_true, ite_false, row, abs_eq_max_neg] at hv ⊢ <;> omega
    rcases h with h | h | h
    · exact ⟨.S m k, by simp [graph, adjacent], h⟩
    · exact ⟨.D m k, by simp [graph, adjacent], h⟩
    · exact ⟨.D m (k-1), by simp [graph, adjacent], h⟩
  | D m k =>
    have h : score (.S (m+1) k) = score (.D m k) - 1 ∨
        score (.U m k) = score (.D m k) - 1 ∨
        score (.U m (k+1)) = score (.D m k) - 1 := by
      by_cases hm0 : m = 0 <;> by_cases hmn : m < 0 <;> by_cases hml : m ≤ 0 <;>
        by_cases hd0 : m-1 = 0 <;> by_cases hdn : m-1 < 0 <;>
        by_cases hsl : m+1 ≤ 0
      all_goals simp only [score, hm0, hmn, hml, hd0, hdn, hsl,
        ite_true, ite_false, row, abs_eq_max_neg] at hv ⊢ <;> omega
    rcases h with h | h | h
    · exact ⟨.S (m+1) k, by simp [graph, adjacent], h⟩
    · exact ⟨.U m k, by simp [graph, adjacent], h⟩
    · exact ⟨.U m (k+1), by simp [graph, adjacent], h⟩

private lemma geodesic (v : Vertex) :
    ∃ w : graph.Walk root v, w.length = (score v).toNat := by
  suffices h : ∀ n : ℕ, ∀ v, (score v).toNat = n →
      ∃ w : graph.Walk root v, w.length = n from h _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hv
    by_cases hn : n = 0
    · have he : v = root := (score_zero v).mp (by have := score_nonneg v; omega)
      subst v
      exact ⟨.nil, hn.symm⟩
    · obtain ⟨u, hu, he⟩ := score_descent v (by have := score_nonneg v; omega)
      have hu0 := score_nonneg u
      obtain ⟨w, hw⟩ := ih (score u).toNat (by omega) u rfl
      exact ⟨w.append hu.symm.toWalk, by simp [hw]; omega⟩

private lemma distance_formula (v : Vertex) : distance v = (score v).toNat := by
  obtain ⟨w, hw⟩ := geodesic v
  refine le_antisymm (hw ▸ graph.dist_le w) ?_
  have hl := D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.potential_dist
    graph (fun u => (score u).toNat) (by
      intro u v huv
      have := score_step u v huv
      have := score_nonneg u
      have := score_nonneg v
      omega) w.reachable.symm
  have hz : (score root).toNat = 0 := by norm_num [score, root]
  simpa only [hz, zero_add, SimpleGraph.dist_comm, distance] using hl


private def rowShell (c L n r : ℕ) : Finset ℤ :=
  if 3*r+c > n then ∅ else
  if 3*r+c = n then Finset.Icc 0 ((r+L : ℕ) - 1 : ℤ) else
    {-((n : ℤ)-3*r-c), (r+L : ℕ)-1+((n : ℤ)-3*r-c)}

private lemma rowShell_mem (c L n r : ℕ) (hL : 0 < L) (k : ℤ) :
    k ∈ rowShell c L n r ↔ row (3*r+c) 0 ((r+L : ℕ)-1 : ℤ) k = n := by
  by_cases hlt : 3*r+c > n
  · simp only [rowShell, ite_eq_left hlt, Finset.notMem_empty, false_iff]
    dsimp only [row]
    omega
  · by_cases he : 3*r+c = n
    · simp only [rowShell, ite_eq_right hlt, ite_eq_left he, Finset.mem_Icc]
      dsimp only [row]
      omega
    · simp only [rowShell, ite_eq_right hlt, ite_eq_right he,
        Finset.mem_insert, Finset.mem_singleton]
      dsimp only [row]
      omega

private lemma rowShell_card (c L n r : ℕ) (hL : 0 < L) :
    (rowShell c L n r).card =
      (if 3*r+c < n then 2 else 0) + (if 3*r+c = n then r+L else 0) := by
  by_cases hlt : 3*r+c > n
  · simp [rowShell, hlt, show ¬3*r+c < n by omega, show ¬3*r+c = n by omega]
  · by_cases he : 3*r+c = n
    · simp only [rowShell, ite_eq_right hlt, ite_eq_left he,
        ite_eq_right (show ¬3*r+c < n by omega), zero_add, Int.card_Icc]
      omega
    · have hn : 3*r+c < n := by omega
      have hne : -((n : ℤ)-3*r-c) ≠ (r+L : ℕ)-1+((n : ℤ)-3*r-c) := by omega
      simp only [rowShell, ite_eq_right hlt, ite_eq_right he, ite_eq_left hn,
        Finset.card_insert_of_notMem (show -((n : ℤ)-3*r-c) ∉
          {(r+L : ℕ)-1+((n : ℤ)-3*r-c)} by simpa only [Finset.mem_singleton] using hne),
        Finset.card_singleton, add_zero]

private def strip (c L n : ℕ) : Finset (ℕ × ℤ) :=
  (Finset.range (n+1)).biUnion fun r => (rowShell c L n r).image (r, ·)

private lemma strip_mem (c L n : ℕ) (hc : 0 < c) (hL : 0 < L) (r : ℕ) (k : ℤ) :
    (r,k) ∈ strip c L n ↔ row (3*r+c) 0 ((r+L : ℕ)-1 : ℤ) k = n := by
  constructor
  · intro h
    obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hs
    have hs : s = r := (Prod.mk.inj he).1
    have hk : j = k := (Prod.mk.inj he).2
    subst s; subst j
    exact (rowShell_mem c L n r hL k).mp hj
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_range.mpr ?_, ?_⟩
    · dsimp only [row] at h; omega
    · exact Finset.mem_image.mpr ⟨k, (rowShell_mem c L n r hL k).mpr h, rfl⟩

private lemma strip_card (c L n : ℕ) (hc : 0 < c) (hL : 0 < L) :
    (strip c L n).card = 2*((n+2-c)/3) +
      if c ≤ n ∧ (n-c)%3 = 0 then (n-c)/3+L else 0 := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.range (n+1)) : Set ℕ)
      (fun r => (rowShell c L n r).image (r, ·)) := by
    intro r _ s _ hrs
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hq
    exact hrs (by simpa using congrArg Prod.fst (hi.trans hj.symm))
  rw [strip, Finset.card_biUnion hd]
  simp only [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
    rowShell_card c L n _ hL, Finset.sum_add_distrib]
  congr 1
  · have hs : (Finset.range (n+1)).filter (fun r => 3*r+c < n) =
        Finset.range ((n+2-c)/3) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.sum_filter, hs]
    simp [mul_comm]
  · by_cases h : c ≤ n ∧ (n-c)%3 = 0
    · rw [ite_eq_left h]
      have he : 3*((n-c)/3)+c = n := by omega
      rw [Finset.sum_eq_single ((n-c)/3)]
      · simp [he]
      · intro b _ hb
        have : ¬ 3*b+c = n := by omega
        simp [this]
      · intro hn
        have : (n-c)/3 < n+1 := by omega
        exact False.elim (hn (Finset.mem_range.mpr this))
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro b _
      have : ¬ 3*b+c = n := by omega
      simp [this]

private abbrev Coords := (Fin 6 × (ℕ × ℤ)) ⊕ (Bool × ℤ)

private def decode : Coords → Vertex
  | .inl (t,r,j) => match t with
    | 0 => .S (-r) j
    | 1 => .S (r+1) (j-(r+1))
    | 2 => .U (-r-1) j
    | 3 => .U (r+1) (j-(r+1))
    | 4 => .D (-r-1) j
    | 5 => .D (r+1) (j-(r+2))
  | .inr (false,j) => .U 0 j
  | .inr (true,j) => .D 0 j

private def encode : Vertex → Coords
  | .S m k => if m ≤ 0 then .inl (0,(-m).toNat,k)
      else .inl (1,(m-1).toNat,k+m)
  | .U m k => if m = 0 then .inr (false,k) else
      if m < 0 then .inl (2,(-m-1).toNat,k) else .inl (3,(m-1).toNat,k+m)
  | .D m k => if m = 0 then .inr (true,k) else
      if m < 0 then .inl (4,(-m-1).toNat,k) else .inl (5,(m-1).toNat,k+m+1)

private def coordinateEquiv : Coords ≃ Vertex where
  toFun := decode
  invFun := encode
  left_inv := by
    rintro (⟨t,r,k⟩ | ⟨b,k⟩)
    · fin_cases t <;> norm_num [decode, encode, Prod.ext_iff] <;>
        split_ifs <;> (try simp_all only [Sum.inl.injEq, Prod.mk.injEq, true_and]) <;> omega
    · cases b <;> simp [decode, encode]
  right_inv := by
    intro v
    cases v <;> simp only [encode] <;> split_ifs <;>
      simp only [decode, Vertex.S.injEq, Vertex.U.injEq, Vertex.D.injEq]
    all_goals simp_all <;> omega

private def offset (t : Fin 6) : ℕ := match t with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 3 | 4 => 2 | 5 => 4

private def width (t : Fin 6) : ℕ := match t with
  | 0 => 1 | 1 => 2 | 2 => 2 | 3 => 2 | 4 => 1 | 5 => 3

private lemma decode_score (t : Fin 6) (r : ℕ) (j : ℤ) :
    score (decode (.inl (t,r,j))) =
      row (3*r+offset t) 0 ((r+width t : ℕ)-1 : ℤ) j := by
  fin_cases t <;> simp [decode, score, row, offset, width] <;> omega

private def centralShell (b : Bool) (n : ℕ) : Finset ℤ :=
  if b then
    if n = 1 then {-1,0} else if n = 3 then {-2,1} else
      if 5 ≤ n then {-((n:ℤ)-2), (n:ℤ)-3} else ∅
  else
    if n = 0 then {0} else if n = 2 then {-1,1} else
      if 4 ≤ n then {-((n:ℤ)-2), (n:ℤ)-2} else ∅

private lemma centralShell_mem (b : Bool) (n : ℕ) (k : ℤ) :
    k ∈ centralShell b n ↔ score (decode (.inr (b,k))) = n := by
  cases b <;> simp only [centralShell, decode, score, ite_true, ite_false,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, abs_eq_max_neg, max_def, min_def] <;>
    split_ifs <;> simp_all [decode, score, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> omega

private lemma centralShell_card (b : Bool) (n : ℕ) :
    (centralShell b n).card = if b then
      (if n=1 then 2 else 0) + (if n=3 then 2 else 0) + (if 5≤n then 2 else 0)
    else (if n=0 then 1 else 0) + (if n=2 then 2 else 0) + (if 4≤n then 2 else 0) := by
  cases b <;> simp only [centralShell, Bool.false_eq_true, ite_false, ite_true] <;>
    split_ifs <;> simp_all <;>
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
        Finset.card_singleton]


private def shellCoords (n : ℕ) : Finset Coords :=
  ((Finset.univ.sigma fun t : Fin 6 => strip (offset t) (width t) n).map
    (Equiv.sigmaEquivProd (Fin 6) (ℕ × ℤ)).toEmbedding).disjSum
  ((Finset.univ.sigma fun b : Bool => centralShell b n).map
    (Equiv.sigmaEquivProd Bool ℤ).toEmbedding)

private lemma shellCoords_mem (n : ℕ) (z : Coords) :
    z ∈ shellCoords n ↔ score (decode z) = n := by
  rcases z with ⟨t,r,j⟩ | ⟨b,j⟩
  · simp only [shellCoords, Finset.inl_mem_disjSum, Finset.mem_map_equiv,
      Equiv.sigmaEquivProd_symm_apply, Finset.mem_sigma, Finset.mem_univ,
      true_and, decode_score]
    apply strip_mem
    · fin_cases t <;> simp [offset]
    · fin_cases t <;> simp [width]
  · simpa [shellCoords] using centralShell_mem b n j

private def actualShell (n : ℕ) : Finset Vertex :=
  (shellCoords n).map coordinateEquiv.toEmbedding

private lemma actualShell_mem (n : ℕ) (v : Vertex) :
    v ∈ actualShell n ↔ distance v = n := by
  simp only [actualShell, Finset.mem_map_equiv, shellCoords_mem]
  change score (coordinateEquiv (coordinateEquiv.symm v)) = (n:ℤ) ↔ _
  rw [coordinateEquiv.apply_symm_apply, distance_formula]
  have := score_nonneg v
  omega

private lemma shell_finite (n : ℕ) : {v | distance v = n}.Finite := by
  exact (actualShell n).finite_toSet.subset (fun v hv => (actualShell_mem n v).mpr hv)

private lemma a_card (n : ℕ) : a n = (actualShell n).card := by
  rw [a, Set.ncard_eq_toFinset_card _ (shell_finite n)]
  congr 1
  ext v
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, actualShell_mem]

private def stripCount (c L n : ℕ) : ℕ :=
  2*((n+2-c)/3) + if c ≤ n ∧ (n-c)%3=0 then (n-c)/3+L else 0

private lemma a_formula (n : ℕ) : a n =
    stripCount 1 1 n + stripCount 2 2 n + stripCount 2 1 n +
    2*stripCount 3 2 n + stripCount 4 3 n +
    ((if n=0 then 1 else 0) + (if n=2 then 2 else 0) + (if 4≤n then 2 else 0)) +
    ((if n=1 then 2 else 0) + (if n=3 then 2 else 0) + (if 5≤n then 2 else 0)) := by
  have hc (t : Fin 6) : 0 < offset t := by fin_cases t <;> norm_num [offset]
  have hw (t : Fin 6) : 0 < width t := by fin_cases t <;> norm_num [width]
  rw [a_card]
  simp only [actualShell, Finset.card_map, shellCoords, Finset.card_disjSum, Finset.card_sigma]
  simp_rw [strip_card _ _ n (hc _) (hw _), centralShell_card]
  norm_num [Fin.sum_univ_succ, Fintype.sum_bool, offset, width, stripCount]
  ring

set_option maxHeartbeats 2000000 in
private lemma shell_tail (n : ℕ) (hn : 5 ≤ n) :
    a n = 14*(n/3) + (if n%3=0 then 0 else if n%3=1 then 5 else 9) := by
  have hmod := Nat.mod_lt n (by omega : 0 < 3)
  rw [a_formula]
  simp (disch := omega) only [stripCount, ite_eq_left, ite_eq_right]
  interval_cases hm : n%3 <;> norm_num only [hm]
  all_goals split_ifs <;> simp_all <;> omega

set_option maxHeartbeats 2000000 in
private lemma coefficient_identity (n : ℕ) :
    (a n : ℤ) - (if 1≤n then (a (n-1):ℤ) else 0) -
      (if 3≤n then (a (n-3):ℤ) else 0) + (if 4≤n then (a (n-4):ℤ) else 0) =
      (if n=0 then 1 else 0) + (if n=1 then 2 else 0) +
      (if n=2 then 4 else 0) + (if n=3 then 4 else 0) +
      (if n=4 then 3 else 0) + (if n=5 then 2 else 0) - (if n=8 then 2 else 0) := by
  by_cases hn : n < 9
  · interval_cases n <;> norm_num [a_formula, stripCount]
  · have hn9 : 9 ≤ n := by omega
    simp (disch := omega) only [ite_eq_left, ite_eq_right]
    have hm3 : (n-3)%3 = n%3 := by omega
    have hm4 : (n-4)%3 = (n-1)%3 := by omega
    have hq0 : n/3 = (n-3)/3+1 := by omega
    have hq1 : (n-1)/3 = (n-4)/3+1 := by omega
    have he0 : a n = a (n-3) + 14 := by
      rw [shell_tail n (by omega), shell_tail (n-3) (by omega), hm3, hq0]
      omega
    have he1 : a (n-1) = a (n-4) + 14 := by
      rw [shell_tail (n-1) (by omega), shell_tail (n-4) (by omega), hm4, hq1]
      omega
    omega

/-- Barker's identity for the coordination sequence at a trivalent node of the cem-d net. -/
theorem result :
    (1 - PowerSeries.X)^2 * (1 + PowerSeries.X + PowerSeries.X^2) *
      (PowerSeries.mk fun n => (a n : ℤ)) =
      1 + 2*PowerSeries.X + 4*PowerSeries.X^2 + 4*PowerSeries.X^3 +
        3*PowerSeries.X^4 + 2*PowerSeries.X^5 - 2*PowerSeries.X^8 := by
  have hd : (1 - (PowerSeries.X : PowerSeries ℤ))^2 * (1 + PowerSeries.X + PowerSeries.X^2) =
      1 - PowerSeries.X - PowerSeries.X^3 + PowerSeries.X^4 := by ring
  rw [hd, add_mul, sub_mul, sub_mul, one_mul]
  ext n
  have hx (p : PowerSeries ℤ) :
      PowerSeries.coeff n (PowerSeries.X * p) =
        if 1 ≤ n then PowerSeries.coeff (n-1) p else 0 := by
    simpa only [pow_one] using PowerSeries.coeff_X_pow_mul' p 1 n
  simpa only [map_add, map_sub, PowerSeries.coeff_one,
    PowerSeries.coeff_X, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', hx,
    PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_X_pow,
    mul_ite, mul_one, mul_zero] using coefficient_identity n

end D5.S3.StatisticalMechanics.ElongatedTriangularDualCoordination

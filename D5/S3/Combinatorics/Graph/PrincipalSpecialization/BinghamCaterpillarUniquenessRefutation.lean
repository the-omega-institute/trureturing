/- GID: D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.claim; result=D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.result; claim=D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.claim
   digest: An eighteen-vertex pair refutes the exhaustive-pairs question of Remark 3.11. -/

import D5.S3.Combinatorics.Graph.PrincipalSpecialization.BinghamCaterpillarPs3Family
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Decide

namespace Trureturing.OpenProblems.BinghamCaterpillarUniquenessRefutation

open scoped BigOperators
open BinghamCaterpillarPs3Family

/-- Definition 2.1's positive compositions, including the exceptional singleton (1). -/
def admissible {l : ℕ} (a : Parts l) : Prop :=
  (l = 1 ∧ ∀ i, a i = 1) ∨
    (1 ≤ l ∧ ∀ i : Fin l, i.val = 0 ∨ i.val + 1 = l → 2 ≤ (a i).val)

/-- The source's ordinary polynomial over its coefficient ring C. -/
noncomputable def ordinary {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Polynomial ℂ := ∑ c : G.Coloring (Fin k), Polynomial.X ^ (∑ v : V, (c v).val)

/-- Unordered pairs of graph-isomorphism classes; both pair orders are included. -/
def pairIso {la lb lc ld : ℕ} (a : Parts la) (b : Parts lb) (c : Parts lc) (d : Parts ld) : Prop :=
  (Nonempty (caterpillar a ≃g caterpillar c) ∧ Nonempty (caterpillar b ≃g caterpillar d)) ∨
  (Nonempty (caterpillar a ≃g caterpillar d) ∧ Nonempty (caterpillar b ≃g caterpillar c))

def baseA : Parts 3 := ![5,4,3]
def baseB : Parts 3 := ![4,5,3]

/-- Every listed exception, with arbitrary relabelings, reversals and pair exchange. -/
def listed {la lb : ℕ} (a : Parts la) (b : Parts lb) : Prop :=
  pairIso a b baseA baseB ∨ ∃ j : ℕ+, pairIso a b (alpha j) (beta j)

/-- The entire second question: all sizes and all source-admissible compositions. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ la lb : ℕ, ∀ a : Parts la, ∀ b : Parts lb,
    admissible a → admissible b →
    (∑ i, (a i).val) = n → (∑ i, (b i).val) = n →
    ordinary (caterpillar a) 2 ≠ ordinary (caterpillar b) 2 →
    ordinary (caterpillar a) 3 = ordinary (caterpillar b) 3 → listed a b

/-- The first eighteen-vertex caterpillar. -/
def witnessA : Parts 8 := ![2,2,2,2,2,1,4,3]
/-- The second eighteen-vertex caterpillar. -/
def witnessB : Parts 7 := ![2,2,3,2,3,4,2]

private lemma ordinary_eq_map {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    ordinary G k = (ps G k).map (Int.castRingHom ℂ) := by
  classical
  simp [ordinary, ps, Polynomial.map_sum, Polynomial.map_pow]

private lemma ordinary_eq_iff {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) :
    ordinary G k = ordinary H k ↔ ps G k = ps H k := by
  rw [ordinary_eq_map, ordinary_eq_map]
  exact (Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective).eq_iff

private noncomputable def eightSum {k : ℕ} (w : Fin 8 → Fin k → Polynomial ℤ) :=
  ∑ c0 : Fin k, ∑ c1 : Fin k, ∑ c2 : Fin k, ∑ c3 : Fin k,
  ∑ c4 : Fin k, ∑ c5 : Fin k, ∑ c6 : Fin k, ∑ c7 : Fin k,
    if c0 ≠ c1 ∧ c1 ≠ c2 ∧ c2 ≠ c3 ∧ c3 ≠ c4 ∧ c4 ≠ c5 ∧ c5 ≠ c6 ∧ c6 ≠ c7 then
      w 0 c0 * w 1 c1 * w 2 c2 * w 3 c3 * w 4 c4 * w 5 c5 * w 6 c6 * w 7 c7 else 0

private noncomputable def sevenSum {k : ℕ} (w : Fin 7 → Fin k → Polynomial ℤ) :=
  ∑ c0 : Fin k, ∑ c1 : Fin k, ∑ c2 : Fin k, ∑ c3 : Fin k,
  ∑ c4 : Fin k, ∑ c5 : Fin k, ∑ c6 : Fin k,
    if c0 ≠ c1 ∧ c1 ≠ c2 ∧ c2 ≠ c3 ∧ c3 ≠ c4 ∧ c4 ≠ c5 ∧ c5 ≠ c6 then
      w 0 c0 * w 1 c1 * w 2 c2 * w 3 c3 * w 4 c4 * w 5 c5 * w 6 c6 else 0

private lemma eight_good {k : ℕ} (c : Fin 8 → Fin k) :
    SpineGood c ↔ c 0 ≠ c 1 ∧ c 1 ≠ c 2 ∧ c 2 ≠ c 3 ∧ c 3 ≠ c 4 ∧
      c 4 ≠ c 5 ∧ c 5 ≠ c 6 ∧ c 6 ≠ c 7 := by
  constructor
  · intro h
    exact ⟨h 0 1 rfl,h 1 2 rfl,h 2 3 rfl,h 3 4 rfl,h 4 5 rfl,h 5 6 rfl,h 6 7 rfl⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private lemma seven_good {k : ℕ} (c : Fin 7 → Fin k) :
    SpineGood c ↔ c 0 ≠ c 1 ∧ c 1 ≠ c 2 ∧ c 2 ≠ c 3 ∧ c 3 ≠ c 4 ∧
      c 4 ≠ c 5 ∧ c 5 ≠ c 6 := by
  constructor
  · intro h
    exact ⟨h 0 1 rfl,h 1 2 rfl,h 2 3 rfl,h 3 4 rfl,h 4 5 rfl,h 5 6 rfl⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

set_option maxHeartbeats 1600000 in
private lemma ps_eight {k : ℕ} (a : Parts 8) :
    ps (caterpillar a) k = eightSum (fun i c => blockWeight (a i) c) := by
  rw [ps_spine_sum]
  simp_rw [eight_good]
  unfold eightSum
  iterate 8
    rw [sum_finfun_succ]
    apply Finset.sum_congr rfl
    intro _ _
  simp [Fin.prod_univ_succ, mul_assoc]
  rfl

set_option maxHeartbeats 1600000 in
private lemma ps_seven {k : ℕ} (a : Parts 7) :
    ps (caterpillar a) k = sevenSum (fun i c => blockWeight (a i) c) := by
  rw [ps_spine_sum]
  simp_rw [seven_good]
  unfold sevenSum
  iterate 7
    rw [sum_finfun_succ]
    apply Finset.sum_congr rfl
    intro _ _
  simp [Fin.prod_univ_succ, mul_assoc]
  rfl

set_option maxHeartbeats 12000000 in
private lemma ps3_equal : ps (caterpillar witnessA) 3 = ps (caterpillar witnessB) 3 := by
  rw [ps_eight, ps_seven]
  norm_num [eightSum, sevenSum, Fin.sum_univ_succ, witnessA, witnessB,
    blockWeight, leafSum_eq, Fin.cons]
  ring

set_option maxHeartbeats 4000000 in
private lemma ps2_A : ps (caterpillar witnessA) 2 = Polynomial.X ^ 8 + Polynomial.X ^ 10 := by
  rw [ps_eight]
  norm_num [eightSum, Fin.sum_univ_succ, witnessA, blockWeight, leafSum_eq, Fin.cons]
  ring

set_option maxHeartbeats 4000000 in
private lemma ps2_B : ps (caterpillar witnessB) 2 = 2 * Polynomial.X ^ 9 := by
  rw [ps_seven]
  norm_num [sevenSum, Fin.sum_univ_succ, witnessB, blockWeight, leafSum_eq, Fin.cons]
  ring


private def twoNeighbors {V : Type*} (G : SimpleGraph V) (x : V) : Prop :=
  ∃ u v : V, u ≠ v ∧ G.Adj x u ∧ G.Adj x v

private lemma leaf_neighbor {l : ℕ} {a : Parts l} {x y : Vertex a}
    (hx : x.2.val ≠ 0) (h : (caterpillar a).Adj x y) :
    y.1 = x.1 ∧ y.2.val = 0 := by
  rcases h with ⟨_, h | h⟩
  · rcases h with ⟨_, h, _⟩ | ⟨h, _, _⟩ <;> exact (hx h).elim
  · rcases h with ⟨hi, hy, _⟩ | ⟨hy, h, _⟩
    · exact ⟨hi, hy⟩
    · exact (hx h).elim

private lemma root_ext {l : ℕ} {a : Parts l} {x y : Vertex a}
    (h : x.1 = y.1) (hx : x.2.val = 0) (hy : y.2.val = 0) : x = y := by
  rcases x with ⟨i,r⟩
  rcases y with ⟨j,s⟩
  dsimp at h hx hy
  subst j
  congr 1
  exact Fin.ext (hx.trans hy.symm)

private lemma nonleaf_root {l : ℕ} {a : Parts l} {x : Vertex a}
    (h : twoNeighbors (caterpillar a) x) : x.2.val = 0 := by
  by_contra hx
  rcases h with ⟨u,v,huv,hu,hv⟩
  have h1 := leaf_neighbor hx hu
  have h2 := leaf_neighbor hx hv
  exact huv (root_ext (h1.1.trans h2.1.symm) h1.2 h2.2)

private lemma iso_twoNeighbors {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {x : V} (h : twoNeighbors G x) : twoNeighbors H (e x) := by
  rcases h with ⟨u,v,huv,hu,hv⟩
  exact ⟨e u,e v,fun h => huv (e.injective h),e.map_adj hu,e.map_adj hv⟩

private instance {l : ℕ} (a : Parts l) : DecidableRel (edgeRel a) :=
  fun u v => inferInstanceAs (Decidable
    ((u.1 = v.1 ∧ u.2.val = 0 ∧ v.2.val ≠ 0) ∨
      (u.2.val = 0 ∧ v.2.val = 0 ∧ u.1.val + 1 = v.1.val)))

private instance {l : ℕ} (a : Parts l) : DecidableRel (caterpillar a).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (edgeRel a)).Adj)

private lemma witness_roots : ∀ i : Fin 8,
    twoNeighbors (caterpillar witnessA) ⟨i,⟨0,(witnessA i).pos⟩⟩ := by
  decide

private lemma no_iso_short {l : ℕ} (a : Parts l) (hl : l < 8) :
    ¬ Nonempty (caterpillar witnessA ≃g caterpillar a) := by
  rintro ⟨e⟩
  let f : Fin 8 → Fin l := fun i => (e ⟨i,⟨0,(witnessA i).pos⟩⟩).1
  have hf : Function.Injective f := by
    intro i j hij
    have hi := nonleaf_root (iso_twoNeighbors e (witness_roots i))
    have hj := nonleaf_root (iso_twoNeighbors e (witness_roots j))
    have he := e.injective (root_ext hij hi hj)
    exact congrArg Sigma.fst he
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

private lemma outside_list : ¬ listed witnessA witnessB := by
  rintro (⟨h,_⟩ | ⟨h,_⟩ | ⟨j,⟨h,_⟩ | ⟨h,_⟩⟩)
  · exact no_iso_short baseA (by decide) h
  · exact no_iso_short baseB (by decide) h
  · exact no_iso_short (alpha j) (by decide) h
  · exact no_iso_short (beta j) (by decide) h

/-- The second, exhaustive-pairs assertion in Remark 3.11 is false. -/
theorem result : ¬ claim := by
  intro h
  apply outside_list
  apply h 18 (by decide) 8 7 witnessA witnessB
  · right
    constructor
    · decide
    · intro i hi
      fin_cases i <;> norm_num [witnessA, Fin.cons] at *
  · right
    constructor
    · decide
    · intro i hi
      fin_cases i <;> norm_num [witnessB, Fin.cons] at *
  · norm_num [witnessA, Fin.sum_univ_succ, Fin.cons]
  · norm_num [witnessB, Fin.sum_univ_succ, Fin.cons]
  · rw [ne_eq, ordinary_eq_iff, ps2_A, ps2_B]
    intro he
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 8) he
    norm_num [Polynomial.coeff_X_pow] at hc
  · exact (ordinary_eq_iff _ _ 3).2 ps3_equal

end Trureturing.OpenProblems.BinghamCaterpillarUniquenessRefutation


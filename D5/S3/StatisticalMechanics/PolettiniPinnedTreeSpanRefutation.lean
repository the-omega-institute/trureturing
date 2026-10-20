/- GID: D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.claim; result=D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.result; claim=D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.claim
   digest: Triangle pins on unit-rate K4 refute the proposed tree-span dimension. -/

/-
admission_basis: open-problem-resolution (#19157; Refuted)
escape_witness: none
Direct frozen dependencies: none (only pinned Mathlib is imported).
fourth_to_third: proof_shape: bind-only; escape_witness: none; consumers: reaches_third.
reaches_third: proof_shape: bind-only; escape_witness: none; consumers: tree_iff.
tree_iff: proof_shape: bind-only; escape_witness: none; consumers: tau_eq_count.
catalog_cases: proof_shape: bind-only; escape_witness: none; consumers: tree_catalog_iff.
tree_catalog_iff: proof_shape: bind-only; escape_witness: none; consumers: tau_eq_count.
tau_eq_count: proof_shape: bind-only; escape_witness: none; consumers: tau_relation.
count_relation: proof_shape: bind-only; escape_witness: none; consumers: tau_relation.
tau_relation: proof_shape: bind-only; escape_witness: none; consumers: tau_dependent.
rates_nonneg: proof_shape: bind-only; escape_witness: none; consumers: result.
rates_irreducible: proof_shape: bind-only; escape_witness: none; consumers: result.
pins_valid: proof_shape: bind-only; escape_witness: none; consumers: result.
pins_injective: proof_shape: bind-only; escape_witness: none; consumers: result.
deleted_irreducible: proof_shape: bind-only; escape_witness: none; consumers: result.
tau_dependent: proof_shape: bind-only; escape_witness: none; consumers: span_finrank_le_three.
span_finrank_le_three: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; consumers: external conjecture settlement.
The source declarations follow issue #19157, with the type aliases Status and Rates
expanded to Option Bool and Fin N → Fin N → ℝ, and the namespace follows this file.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
Literature completeness: ASSUMED-UNVERIFIED; the full journal text is not checked.
-/

import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Sym.Sym2

open scoped BigOperators

/-! Binding conventions for M. Polettini, P. E. Harunari, S. Dal Cengio and V. Lecomte, "Coplanarity of rooted
spanning-tree vectors", arXiv:2407.16093v1 (Lett. Math. Phys. 2025), Section 2.1 (rooted spanning trees, the
conditioned rooted spanning tree polynomial) and the conjecture of the Introduction and Conclusions. -/

noncomputable section
open scoped Classical

namespace D5.S3.StatisticalMechanics.PolettiniPinnedTreeSpanRefutation


/-- The graph is irreducible: there is a path of nonzero weight between any two vertices. -/
def Irreducible {N : ℕ} (r : (Fin N → Fin N → ℝ)) : Prop :=
  ∀ x y, Relation.ReflTransGen (fun a b => 0 < r a b) x y

/-- A spanning tree rooted at `x`, every edge directed along the unique path to the root: each vertex `v ≠ x` has
one outgoing tree edge `v → p v` (an edge of the graph), and following the tree edges from any vertex reaches `x`. -/
def IsRootedTree {N : ℕ} (r : (Fin N → Fin N → ℝ)) (x : Fin N) (p : Fin N → Fin N) : Prop :=
  p x = x ∧ (∀ v, v ≠ x → 0 < r v (p v)) ∧ ∀ v, ∃ k, p^[k] v = x

/-- The tree `p` rooted at `x` contains the oriented edge `u → v`. -/
def Contains {N : ℕ} (x : Fin N) (p : Fin N → Fin N) (u v : Fin N) : Prop :=
  u ≠ x ∧ p u = v

/-- The tree `p` rooted at `x` has status `s` on the pinned edge `(u, v)`. -/
def HasStatus {N : ℕ} (x : Fin N) (p : Fin N → Fin N) (e : Fin N × Fin N) : (Option Bool) → Prop
  | none => ¬ Contains x p e.1 e.2 ∧ ¬ Contains x p e.2 e.1
  | some true => Contains x p e.1 e.2 ∧ ¬ Contains x p e.2 e.1
  | some false => Contains x p e.2 e.1 ∧ ¬ Contains x p e.1 e.2

/-- The spanning-tree vector `τ_x ∈ ℝ^{3^n}` of the deletion-constriction through the pinned edges `e_1, …, e_n`:
its `s`-coordinate is the conditioned rooted spanning tree polynomial `τ_x^{∖A ∖∖ B}` (Definition 1), the sum of the
products of the rates over the trees rooted at `x` with status `s_i` on each pinned edge `e_i`. -/
def tau {N n : ℕ} (r : (Fin N → Fin N → ℝ)) (pins : Fin n → Fin N × Fin N) (x : Fin N) : (Fin n → (Option Bool)) → ℝ :=
  fun s => ∑ p ∈ Finset.univ.filter (fun p : Fin N → Fin N =>
      IsRootedTree r x p ∧ ∀ i, HasStatus x p (pins i) (s i)),
    ∏ v ∈ Finset.univ.erase x, r v (p v)

/-- The rates after deleting every pinned edge in both directions. -/
def deletePins {N n : ℕ} (r : (Fin N → Fin N → ℝ)) (pins : Fin n → Fin N × Fin N) : (Fin N → Fin N → ℝ) :=
  fun a b => if ∃ i, (pins i = (a, b) ∨ pins i = (b, a)) then 0 else r a b

/-- The conjecture: "the `3^n`-vectors representing the deletion-constriction through `n` reversible edges span a
`n + 1` dimensional space". Stated for nonnegative rates, an irreducible graph, `n` distinct pinned reversible edges
(both directions of positive weight), and an irreducible graph after deleting all of them. -/
def claim : Prop :=
  ∀ (N n : ℕ) (r : (Fin N → Fin N → ℝ)) (pins : Fin n → Fin N × Fin N),
    (∀ a b, 0 ≤ r a b) → Irreducible r →
    (∀ i, (pins i).1 ≠ (pins i).2 ∧ 0 < r (pins i).1 (pins i).2 ∧ 0 < r (pins i).2 (pins i).1) →
    Function.Injective (fun i => Sym2.mk (pins i)) →
    Irreducible (deletePins r pins) →
    Module.finrank ℝ (Submodule.span ℝ (Set.range (tau r pins))) = n + 1

end D5.S3.StatisticalMechanics.PolettiniPinnedTreeSpanRefutation

set_option maxRecDepth 10000
set_option maxHeartbeats 0
attribute [-instance] Classical.propDecidable

namespace D5.S3.StatisticalMechanics.PolettiniPinnedTreeSpanRefutation

private def unitRates : (Fin 4 → Fin 4 → ℝ) := fun a b => if a = b then 0 else 1

private def trianglePins : Fin 3 → Fin 4 × Fin 4 := ![(0, 1), (1, 2), (2, 0)]

private theorem fourth_to_third : ∀ (p : Fin 4 → Fin 4) (x : Fin 4),
    p x = x → ∀ v, p^[4] v = x → p^[3] v = x := by
  have table : ∀ a b c d x v : Fin 4,
      (![a,b,c,d] : Fin 4 → Fin 4) x = x →
      (![a,b,c,d] : Fin 4 → Fin 4)^[4] v = x →
      (![a,b,c,d] : Fin 4 → Fin 4)^[3] v = x := by
    decide +kernel
  intro p x hx v h4
  have hp : p = ![p 0,p 1,p 2,p 3] := List.ofFn_inj.mp rfl
  have ht := table (p 0) (p 1) (p 2) (p 3) x v
  simp only [← hp] at ht
  exact ht hx h4

private theorem reaches_third (p : Fin 4 → Fin 4) (x : Fin 4) (hx : p x = x)
    (v : Fin 4) (h : ∃ k, p^[k] v = x) : p^[3] v = x := by
  obtain ⟨k, hk⟩ := h
  by_contra h3
  have hclosed : Set.MapsTo p {w | p^[3] w ≠ x} {w | p^[3] w ≠ x} := by
    intro w hw hpw
    apply hw
    apply fourth_to_third p x hx w
    simpa only [Function.iterate_succ_apply] using hpw
  have hknot := hclosed.iterate k h3
  change p^[3] (p^[k] v) ≠ x at hknot
  rw [hk] at hknot
  exact hknot (Function.iterate_fixed hx 3)

private theorem tree_iff (x : Fin 4) (p : Fin 4 → Fin 4) :
    IsRootedTree unitRates x p ↔ p x = x ∧ ∀ v, p^[3] v = x := by
  constructor
  · intro h
    exact ⟨h.1, fun v => reaches_third p x h.1 v (h.2.2 v)⟩
  · rintro ⟨hx, h3⟩
    refine ⟨hx, ?_, fun v => ⟨3, h3 v⟩⟩
    intro v hv
    have hne : v ≠ p v := by
      intro heq
      have hfix : p v = v := heq.symm
      have hh : p^[3] v = v := Function.iterate_fixed hfix 3
      exact hv (hh.symm.trans (h3 v))
    simp [unitRates, hne]

private instance statusDecidable (x : Fin 4) (p : Fin 4 → Fin 4)
    (e : Fin 4 × Fin 4) (s : (Option Bool)) : Decidable (HasStatus x p e s) := by
  cases s with
  | none => unfold HasStatus Contains; infer_instance
  | some b => cases b <;> unfold HasStatus Contains <;> infer_instance

private def parentTrees : Fin 4 → List (Fin 4 → Fin 4) :=
  ![
    [![0,0,0,0],
     ![0,0,0,1],
     ![0,0,0,2],
     ![0,0,1,0],
     ![0,0,1,1],
     ![0,0,1,2],
     ![0,0,3,0],
     ![0,0,3,1],
     ![0,2,0,0],
     ![0,2,0,1],
     ![0,2,0,2],
     ![0,2,3,0],
     ![0,3,0,0],
     ![0,3,0,2],
     ![0,3,1,0],
     ![0,3,3,0]],
    [![1,1,0,0],
     ![1,1,0,1],
     ![1,1,0,2],
     ![1,1,1,0],
     ![1,1,1,1],
     ![1,1,1,2],
     ![1,1,3,0],
     ![1,1,3,1],
     ![2,1,1,0],
     ![2,1,1,1],
     ![2,1,1,2],
     ![2,1,3,1],
     ![3,1,0,1],
     ![3,1,1,1],
     ![3,1,1,2],
     ![3,1,3,1]],
    [![1,2,2,0],
     ![1,2,2,1],
     ![1,2,2,2],
     ![1,3,2,2],
     ![2,0,2,0],
     ![2,0,2,1],
     ![2,0,2,2],
     ![2,2,2,0],
     ![2,2,2,1],
     ![2,2,2,2],
     ![2,3,2,0],
     ![2,3,2,2],
     ![3,0,2,2],
     ![3,2,2,1],
     ![3,2,2,2],
     ![3,3,2,2]],
    [![1,2,3,3],
     ![1,3,0,3],
     ![1,3,1,3],
     ![1,3,3,3],
     ![2,0,3,3],
     ![2,2,3,3],
     ![2,3,1,3],
     ![2,3,3,3],
     ![3,0,0,3],
     ![3,0,1,3],
     ![3,0,3,3],
     ![3,2,0,3],
     ![3,2,3,3],
     ![3,3,0,3],
     ![3,3,1,3],
     ![3,3,3,3]]]

private theorem catalog_cases : ∀ a b c d x : Fin 4,
    ((![a,b,c,d] : Fin 4 → Fin 4) x = x ∧
      ∀ v, (![a,b,c,d] : Fin 4 → Fin 4)^[3] v = x) ↔
      (![a,b,c,d] : Fin 4 → Fin 4) ∈ (parentTrees x).toFinset := by
  decide +kernel

private theorem tree_catalog_iff (x : Fin 4) (p : Fin 4 → Fin 4) :
    p ∈ (parentTrees x).toFinset ↔ p x = x ∧ ∀ v, p^[3] v = x := by
  have hp : p = ![p 0,p 1,p 2,p 3] := List.ofFn_inj.mp rfl
  have ht := catalog_cases (p 0) (p 1) (p 2) (p 3) x
  simp only [← hp] at ht
  exact ht.symm

private def treeCount (x : Fin 4) (s : Fin 3 → (Option Bool)) : ℕ :=
  ((parentTrees x).toFinset.filter fun p =>
    ∀ i, HasStatus x p (trianglePins i) (s i)).card

private theorem tau_eq_count (x : Fin 4) (s : Fin 3 → (Option Bool)) :
    tau unitRates trianglePins x s = (treeCount x s : ℝ) := by
  classical
  unfold tau treeCount
  calc
    _ = ∑ p ∈ (parentTrees x).toFinset.filter (fun p =>
        ∀ i, HasStatus x p (trianglePins i) (s i)),
        ∏ v ∈ Finset.univ.erase x, unitRates v (p v) := by
      apply Finset.sum_congr
      · ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, tree_iff,
          tree_catalog_iff]
      · intro p hp
        rfl
    _ = ∑ p ∈ (parentTrees x).toFinset.filter (fun p =>
        ∀ i, HasStatus x p (trianglePins i) (s i)), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hx, h3⟩ := (tree_catalog_iff x p).mp (Finset.mem_filter.mp hp).1
      apply Finset.prod_eq_one
      intro v hv
      have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
      have htree := (tree_iff x p).mpr ⟨hx, h3⟩
      have hne : v ≠ p v := by
        intro heq
        have hpv := htree.2.1 v hvx
        simp only [unitRates, ite_eq_left heq, lt_self_iff_false] at hpv
      simp [unitRates, hne]
    _ = _ := by simp

private theorem count_relation : ∀ s : Fin 3 → (Option Bool),
    treeCount 0 s + treeCount 1 s + treeCount 2 s = 3 * treeCount 3 s := by
  decide +kernel
private theorem tau_relation :
    tau unitRates trianglePins 0 + tau unitRates trianglePins 1 +
      tau unitRates trianglePins 2 = (3 : ℝ) • tau unitRates trianglePins 3 := by
  funext s
  change tau unitRates trianglePins 0 s + tau unitRates trianglePins 1 s +
    tau unitRates trianglePins 2 s = 3 * tau unitRates trianglePins 3 s
  simp only [tau_eq_count]
  have hh := congrArg (fun n : ℕ => (n : ℝ)) (count_relation s)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hh

private theorem rates_nonneg : ∀ a b, 0 ≤ unitRates a b := by
  intro a b
  simp only [unitRates]
  split <;> norm_num
private theorem rates_irreducible : Irreducible unitRates := by
  intro x y
  by_cases h : x = y
  · subst y
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (by simp [unitRates, h])
private theorem pins_valid : ∀ i, (trianglePins i).1 ≠ (trianglePins i).2 ∧
    0 < unitRates (trianglePins i).1 (trianglePins i).2 ∧
    0 < unitRates (trianglePins i).2 (trianglePins i).1 := by
  intro i
  fin_cases i <;> norm_num [trianglePins, unitRates]
private theorem pins_injective : Function.Injective (fun i => Sym2.mk (trianglePins i)) := by
  decide +kernel
private theorem deleted_irreducible : Irreducible (deletePins unitRates trianglePins) := by
  intro x y
  have to_center : ∀ a : Fin 4,
      Relation.ReflTransGen (fun a b => 0 < deletePins unitRates trianglePins a b) a 3 := by
    intro a
    fin_cases a
    · exact Relation.ReflTransGen.single (by norm_num [deletePins, trianglePins, unitRates, Fin.exists_fin_succ])
    · exact Relation.ReflTransGen.single (by norm_num [deletePins, trianglePins, unitRates, Fin.exists_fin_succ])
    · exact Relation.ReflTransGen.single (by norm_num [deletePins, trianglePins, unitRates, Fin.exists_fin_succ])
    · exact Relation.ReflTransGen.refl
  have from_center : ∀ b : Fin 4,
      Relation.ReflTransGen (fun a b => 0 < deletePins unitRates trianglePins a b) 3 b := by
    intro b
    fin_cases b
    · exact Relation.ReflTransGen.single (by norm_num [deletePins, trianglePins, unitRates, Fin.exists_fin_succ])
    · exact Relation.ReflTransGen.single (by norm_num [deletePins, trianglePins, unitRates, Fin.exists_fin_succ])
    · exact Relation.ReflTransGen.single (by norm_num [deletePins, trianglePins, unitRates, Fin.exists_fin_succ])
    · exact Relation.ReflTransGen.refl
  exact (to_center x).trans (from_center y)
private theorem tau_dependent : ¬ LinearIndependent ℝ (tau unitRates trianglePins) := by
  intro hlin
  have hz : ∑ i : Fin 4, (![1,1,1,-3] : Fin 4 → ℝ) i • tau unitRates trianglePins i = 0 := by
    funext s
    have hs := congrFun tau_relation s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, add_zero, one_mul]
    change tau unitRates trianglePins 0 s +
      (tau unitRates trianglePins 1 s +
        (tau unitRates trianglePins 2 s + -3 * tau unitRates trianglePins 3 s)) = 0
    linarith
  have hh := Fintype.linearIndependent_iff.mp hlin (![1,1,1,-3] : Fin 4 → ℝ) hz 0
  norm_num at hh
private theorem span_finrank_le_three :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (tau unitRates trianglePins))) ≤ 3 := by
  have hb : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (tau unitRates trianglePins))) ≤ 4 := by
    simpa only [Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := ℝ) (tau unitRates trianglePins))
  have hn : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (tau unitRates trianglePins))) ≠ 4 := by
    intro hd
    apply tau_dependent
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa only [Fintype.card_fin, Set.finrank] using hd.symm
  omega
/-- The spanning-tree dimension conjecture fails for a unit-weight K4 with the triangle pinned. -/
theorem result : ¬ D5.S3.StatisticalMechanics.PolettiniPinnedTreeSpanRefutation.claim := by
  intro h
  have hdim := h 4 3 unitRates trianglePins rates_nonneg rates_irreducible
    pins_valid pins_injective deleted_irreducible
  have hb := span_finrank_le_three
  omega
end D5.S3.StatisticalMechanics.PolettiniPinnedTreeSpanRefutation

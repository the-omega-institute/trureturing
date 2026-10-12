/- GID: D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence
   mirror-E: none(waiver:all-n-super-catalan-weighted-path-identity)
   anchors: []
   utility: none
   digest: The weighted path-table sum equals the next super Catalan number for every n. -/
/-
result
proof_shape: content
escape_witness: totalPaths_closed, the all-n binomial column formula obtained by tree induction.
admission_basis: open-problem-resolution (#14721; Proved)
Direct frozen dependencies: none (only pinned Mathlib imports).
Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/14755 (source.residual_requires_open; compiled Reg mirror retained).
Utility: none; all identities are general in n and no finite computation is retained.

Private theorem classifications and live consumers:
grow_node: proof_shape: bind-only; consumers: paths_grow_zero, paths_grow_succ, good_grow,
  totalPaths_grow_succ, totalPaths_grow_zero
pathsFrom_node: proof_shape: bind-only; consumers: pathsFrom_sum
tree_induction: proof_shape: bind-only; consumers: good_grow, totalPaths_grow_succ,
  totalPaths_grow_zero, totalPaths_short, pathsFrom_sum
list_sum_finset: proof_shape: bind-only; consumers: paths_grow_succ, totalPaths_grow_succ,
  totalPaths_grow_zero, pathsFrom_sum
good_child: proof_shape: bind-only; consumers: paths_grow_succ, totalPaths_grow_succ,
  totalPaths_grow_zero, totalPaths_short, pathsFrom_sum
good_integral: proof_shape: bind-only; consumers: additions_cast, weighted_factor
good_short: proof_shape: bind-only; consumers: totalPaths_short
paths_grow_zero: proof_shape: bind-only; consumers: paths_grow_succ, totalPaths_grow_zero
additions_cast: proof_shape: bind-only; consumers: paths_grow_succ, totalPaths_grow_zero
paths_grow_succ: proof_shape: content; consumers: good_grow, totalPaths_grow_succ
weighted_factor: proof_shape: bind-only; consumers: good_grow
good_leaf: proof_shape: bind-only; consumers: good_grow, good_G
good_grow: proof_shape: content; consumers: good_G
good_G: proof_shape: content; consumers: totalPaths_closed, column_closed
totalPaths_node: proof_shape: bind-only; consumers: totalPaths_leaf, totalPaths_grow_succ,
  totalPaths_grow_zero, totalPaths_short, pathsFrom_sum
totalPaths_leaf: proof_shape: bind-only; consumers: totalPaths_grow_succ, totalPaths_grow_zero,
  totalPaths_closed
totalPaths_grow_succ: proof_shape: content; consumers: totalPaths_closed
totalPaths_grow_zero: proof_shape: content; consumers: totalPaths_closed
totalPaths_short: proof_shape: bind-only; consumers: totalPaths_closed
hockey: proof_shape: bind-only; consumers: totalPaths_closed, result
central_step: proof_shape: bind-only; consumers: totalPaths_closed, result
totalPaths_closed: proof_shape: content; consumers: column_closed
pathsFrom_sum: proof_shape: bind-only; consumers: column_closed
S_zero: proof_shape: bind-only; consumers: result
column_closed: proof_shape: content; consumers: result
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp

noncomputable section

namespace D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence

inductive Tree where
  | node (label : ℕ) (children : List Tree)

def paths : Tree → ℕ → ℕ → ℕ
  | .node a _, 0, k => if a = k then 1 else 0
  | .node _ cs, r + 1, k => (cs.map (fun c => paths c r k)).sum
termination_by structural _ r _ => r

def grow (n : ℕ) (t : Tree) : Tree :=
  Tree.rec (motive_1 := fun _ => Tree) (motive_2 := fun _ => List Tree)
    (fun a cs gs => .node a (gs ++
      List.replicate (∑ r ∈ Finset.range (n + 1), paths (.node a cs) r n * 2 / 2 ^ r)
        (.node (n + 1) []))) [] (fun _ _ g gs => g :: gs) t

def G : ℕ → Tree
  | 0 => .node 0 []
  | n + 1 => grow n (G n)

def pathsFrom (t : Tree) (r v k : ℕ) : ℕ :=
  Tree.rec (motive_1 := fun _ => ℕ) (motive_2 := fun _ => List ℕ)
    (fun a cs ps => (if a = v then paths (.node a cs) r k else 0) + ps.sum)
    [] (fun _ _ p ps => p :: ps) t

def K (r v n : ℕ) := pathsFrom (G n) r v n

def S (m n : ℕ) : ℚ := ((2 * m).factorial * (2 * n).factorial : ℚ) /
  (m.factorial * n.factorial * (m + n).factorial)

def claim : Prop := ∀ n : ℕ, S 0 (n + 1) =
  ∑ r ∈ Finset.range (n + 1), (2 / 2 ^ r : ℚ) *
    ∑ v ∈ Finset.range (n + 1), (K r v n : ℚ)

@[simp]
private theorem grow_node (n a : ℕ) (cs : List Tree) :
    grow n (.node a cs) = .node a (cs.map (grow n) ++
      List.replicate (∑ r ∈ Finset.range (n + 1), paths (.node a cs) r n * 2 / 2 ^ r)
        (.node (n + 1) [])) := by
  simp only [grow]
  congr 2
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons]; congr 1

@[simp]
private theorem pathsFrom_node (a r v k : ℕ) (cs : List Tree) :
    pathsFrom (.node a cs) r v k = (if a = v then paths (.node a cs) r k else 0) +
      (cs.map (fun c => pathsFrom c r v k)).sum := by
  simp only [pathsFrom]
  congr 1
  congr 1
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons]; congr 1

private theorem tree_induction {P : Tree → Prop}
    (step : ∀ a cs, (∀ c ∈ cs, P c) → P (.node a cs)) (t : Tree) : P t :=
  Tree.rec (motive_1 := P) (motive_2 := fun cs => ∀ c ∈ cs, P c)
    step (by simp) (fun c cs hc hcs d hd => by
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hcs d hd) t

private theorem list_sum_finset {α β : Type*} (cs : List α) (I : Finset β)
    (f : α → β → ℚ) :
    (cs.map (fun c => ∑ i ∈ I, f c i)).sum =
      ∑ i ∈ I, (cs.map (fun c => f c i)).sum := by
  exact Multiset.sum_map_sum (m := (cs : Multiset α)) (s := I) (f := f)

private inductive Good (n : ℕ) : Tree → Prop where
  | node (a : ℕ) (cs : List Tree)
      (bound : a ≤ n)
      (integral : ∀ r, 2 ^ r ∣ paths (.node a cs) r n)
      (short : ∀ r, n < r → paths (.node a cs) r n = 0)
      (children : ∀ c ∈ cs, Good n c) : Good n (.node a cs)

private theorem good_child {n a : ℕ} {cs : List Tree} (h : Good n (.node a cs))
    {c : Tree} (hc : c ∈ cs) : Good n c := by
  cases h with | node _ _ _ _ _ children => exact children c hc

private theorem good_integral {n : ℕ} {t : Tree} (h : Good n t) (r : ℕ) :
    2 ^ r ∣ paths t r n := by
  cases h with | node _ _ _ integral _ _ => exact integral r

private theorem good_short {n : ℕ} {t : Tree} (h : Good n t) (r : ℕ) (hr : n < r) :
    paths t r n = 0 := by
  cases h with | node _ _ _ _ short _ => exact short r hr

private theorem paths_grow_zero {n : ℕ} {t : Tree} (h : Good n t) :
    paths (grow n t) 0 (n + 1) = 0 := by
  cases h with | node a cs bound _ _ _ =>
    simp [paths, show a ≠ n + 1 by omega]

private theorem additions_cast {n : ℕ} {t : Tree} (h : Good n t) :
    ((∑ i ∈ Finset.range (n + 1), paths t i n * 2 / 2 ^ i : ℕ) : ℚ) =
      ∑ i ∈ Finset.range (n + 1), (2 / 2 ^ i : ℚ) * paths t i n := by
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_div_charZero ((good_integral h i).mul_right 2)]
  push_cast
  ring

private theorem paths_grow_succ {n : ℕ} {t : Tree} (h : Good n t) (r : ℕ) :
    (paths (grow n t) (r + 1) (n + 1) : ℚ) =
      ∑ i ∈ Finset.range (n + 1), (2 / 2 ^ i : ℚ) * paths t (r + i) n := by
  induction r generalizing t with
  | zero =>
    cases t with | node a cs =>
      rw [grow_node, paths]
      simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append,
        List.map_replicate]
      have hz : (cs.map (fun c => paths (grow n c) 0 (n + 1))).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact paths_grow_zero (good_child h hc)
      rw [hz]
      simp only [paths, List.sum_replicate, nsmul_eq_mul, zero_add]
      simpa using additions_cast h
  | succ r ih =>
    cases t with | node a cs =>
      rw [grow_node, paths]
      simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append,
        List.map_replicate,
        paths, List.map_nil, List.sum_nil, List.sum_replicate, nsmul_eq_mul, mul_zero, add_zero]
      rw [Nat.cast_list_sum, List.map_map, Function.comp_def]
      have hh : cs.map (fun c => (paths (grow n c) (r + 1) (n + 1) : ℚ)) =
          cs.map (fun c => ∑ i ∈ Finset.range (n + 1),
            (2 / 2 ^ i : ℚ) * paths c (r + i) n) := by
        apply List.map_congr_left
        intro c hc
        exact ih (good_child h hc)
      rw [hh, list_sum_finset]
      apply Finset.sum_congr rfl
      intro i hi
      rw [List.sum_map_mul_left]
      congr 1
      rw [show r + 1 + i = (r + i) + 1 by omega, paths,
        Nat.cast_list_sum, List.map_map, Function.comp_def]


private theorem weighted_factor {n : ℕ} {t : Tree} (h : Good n t) (r : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (2 / 2 ^ i : ℚ) * paths t (r + i) n) =
      (2 ^ (r + 1) : ℚ) *
        ((∑ i ∈ Finset.range (n + 1), paths t (r + i) n / 2 ^ (r + i) : ℕ) : ℚ) := by
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_div_charZero (good_integral h (r + i))]
  push_cast
  rw [pow_add, pow_succ]
  field_simp
  ring

private theorem good_leaf (n : ℕ) : Good n (.node n []) := by
  constructor
  · rfl
  · intro r; cases r <;> simp [paths]
  · intro r hr; cases r <;> simp_all [paths]
  · simp

private theorem good_grow {n : ℕ} {t : Tree} (h : Good n t) :
    Good (n + 1) (grow n t) := by
  induction t using tree_induction with
  | step a cs ih =>
    have hh := h
    cases hh with | node _ _ bound integral short children =>
      rw [grow_node]
      apply Good.node
      · omega
      · intro r
        cases r with
        | zero => simp
        | succ r =>
          refine ⟨∑ i ∈ Finset.range (n + 1), paths (.node a cs) (r + i) n / 2 ^ (r + i), ?_⟩
          have eq := paths_grow_succ h r
          rw [weighted_factor h, grow_node] at eq
          exact_mod_cast eq
      · intro r hr
        cases r with
        | zero => omega
        | succ r =>
          have eq := paths_grow_succ h r
          have hz : (∑ i ∈ Finset.range (n + 1),
              (2 / 2 ^ i : ℚ) * paths (.node a cs) (r + i) n) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            rw [short (r + i) (by omega)]
            simp
          rw [hz, grow_node] at eq
          exact_mod_cast eq
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          exact ih d hd (children d hd)
        · have eq := (List.mem_replicate.mp hc).2
          rw [eq]
          exact good_leaf (n + 1)

private theorem good_G (n : ℕ) : Good n (G n) := by
  induction n with
  | zero => exact good_leaf 0
  | succ n ih => exact good_grow ih

private def totalPaths (t : Tree) (r k : ℕ) : ℚ :=
  Tree.rec (motive_1 := fun _ => ℚ) (motive_2 := fun _ => List ℚ)
    (fun a cs ps => (paths (.node a cs) r k : ℚ) + ps.sum)
    [] (fun _ _ p ps => p :: ps) t

private theorem totalPaths_node (a r k : ℕ) (cs : List Tree) :
    totalPaths (.node a cs) r k = (paths (.node a cs) r k : ℚ) +
      (cs.map (fun c => totalPaths c r k)).sum := by
  simp only [totalPaths]
  congr 1
  congr 1
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons]; congr 1

private theorem totalPaths_leaf (a r k : ℕ) :
    totalPaths (.node a []) r k = (paths (.node a []) r k : ℚ) := by
  rw [totalPaths_node]
  simp

private theorem totalPaths_grow_succ {n : ℕ} {t : Tree} (h : Good n t) (r : ℕ) :
    totalPaths (grow n t) (r + 1) (n + 1) =
      ∑ i ∈ Finset.range (n + 1), (2 / 2 ^ i : ℚ) * totalPaths t (r + i) n := by
  induction t using tree_induction with
  | step a cs ih =>
    rw [grow_node, totalPaths_node]
    have hp := paths_grow_succ h r
    rw [grow_node] at hp
    rw [hp]
    simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append,
      List.map_replicate, totalPaths_leaf, paths, List.map_nil, List.sum_nil,
      Nat.cast_zero, List.sum_replicate, nsmul_eq_mul, mul_zero, add_zero]
    have hh : cs.map (fun c => totalPaths (grow n c) (r + 1) (n + 1)) =
        cs.map (fun c => ∑ i ∈ Finset.range (n + 1),
          (2 / 2 ^ i : ℚ) * totalPaths c (r + i) n) := by
      apply List.map_congr_left
      intro c hc
      exact ih c hc (good_child h hc)
    rw [hh, list_sum_finset, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [List.sum_map_mul_left, totalPaths_node, mul_add]

private theorem totalPaths_grow_zero {n : ℕ} {t : Tree} (h : Good n t) :
    totalPaths (grow n t) 0 (n + 1) =
      ∑ i ∈ Finset.range (n + 1), (2 / 2 ^ i : ℚ) * totalPaths t i n := by
  induction t using tree_induction with
  | step a cs ih =>
    rw [grow_node, totalPaths_node]
    have hp := paths_grow_zero h
    rw [grow_node] at hp
    rw [hp]
    simp only [Nat.cast_zero, zero_add, List.map_append, List.map_map,
      Function.comp_def, List.sum_append, List.map_replicate, totalPaths_leaf,
      paths, ite_true, Nat.cast_one, List.sum_replicate, nsmul_eq_mul, mul_one]
    rw [additions_cast h]
    have hh : cs.map (fun c => totalPaths (grow n c) 0 (n + 1)) =
        cs.map (fun c => ∑ i ∈ Finset.range (n + 1),
          (2 / 2 ^ i : ℚ) * totalPaths c i n) := by
      apply List.map_congr_left
      intro c hc
      exact ih c hc (good_child h hc)
    rw [hh, list_sum_finset, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [List.sum_map_mul_left, totalPaths_node, mul_add]
    ring


private theorem totalPaths_short {n : ℕ} {t : Tree} (h : Good n t)
    (r : ℕ) (hr : n < r) : totalPaths t r n = 0 := by
  induction t using tree_induction with
  | step a cs ih =>
    rw [totalPaths_node, good_short h r hr]
    simp only [Nat.cast_zero, zero_add]
    apply List.sum_eq_zero
    intro q hq
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
    exact ih c hc (good_child h hc)

private theorem hockey (n r : ℕ) (hr : r ≤ n) :
    (∑ i ∈ Finset.range (n - r + 1), (2 * n - (r + i)).choose n) =
      (2 * n - r + 1).choose (n + 1) := by
  have eq : (∑ i ∈ Finset.range (n - r + 1), (2 * n - (r + i)).choose n) =
      ∑ i ∈ Finset.range (n - r + 1), (n + (n - r + 1 - 1 - i)).choose n := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    congr 1
    omega
  rw [eq, Finset.sum_range_reflect (fun j => (n + j).choose n)]
  simp_rw [Nat.add_comm n]
  rw [Nat.sum_range_add_choose]
  congr 1 <;> omega

private theorem central_step (n : ℕ) :
    2 * (2 * n + 1).choose (n + 1) = (2 * (n + 1)).choose (n + 1) := by
  have hs := Nat.choose_succ_succ' (2 * n + 1) n
  rw [← Nat.choose_symm_half n] at hs
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
  omega

private theorem totalPaths_closed (n r : ℕ) (hr : r ≤ n) :
    totalPaths (G n) r n = (2 ^ r : ℚ) * ((2 * n - r).choose n : ℚ) := by
  induction n generalizing r with
  | zero =>
    have : r = 0 := by omega
    subst r
    simp [G, totalPaths_leaf, paths]
  | succ n ih =>
    cases r with
    | zero =>
      rw [G, totalPaths_grow_zero (good_G n)]
      have hh : (∑ i ∈ Finset.range (n + 1), (2 / 2 ^ i : ℚ) * totalPaths (G n) i n) =
          2 * ((∑ i ∈ Finset.range (n + 1), (2 * n - i).choose n : ℕ) : ℚ) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i (by simpa using Finset.mem_range.mp hi)]
        field_simp
      rw [hh]
      have hs := hockey n 0 (Nat.zero_le n)
      simp only [Nat.sub_zero, zero_add] at hs
      rw [hs]
      have hc := central_step n
      simp only [pow_zero, Nat.sub_zero, one_mul]
      exact_mod_cast hc
    | succ r =>
      have hr' : r ≤ n := by omega
      rw [G, totalPaths_grow_succ (good_G n)]
      have ht : (∑ i ∈ Finset.range (n + 1),
          (2 / 2 ^ i : ℚ) * totalPaths (G n) (r + i) n) =
          ∑ i ∈ Finset.range (n - r + 1),
            (2 / 2 ^ i : ℚ) * totalPaths (G n) (r + i) n := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro i hi hin
        rw [totalPaths_short (good_G n) (r + i) (by
          have := Finset.mem_range.mp hi
          have : n - r + 1 ≤ i := by simpa [Finset.mem_range] using hin
          omega)]
        simp
      rw [ht]
      have hh : (∑ i ∈ Finset.range (n - r + 1),
          (2 / 2 ^ i : ℚ) * totalPaths (G n) (r + i) n) =
          (2 ^ (r + 1) : ℚ) *
            ((∑ i ∈ Finset.range (n - r + 1), (2 * n - (r + i)).choose n : ℕ) : ℚ) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hir : r + i ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        rw [ih (r + i) hir, pow_add, pow_succ]
        field_simp
      rw [hh, hockey n r hr']
      rw [show 2 * (n + 1) - (r + 1) = 2 * n - r + 1 by omega]

private theorem pathsFrom_sum {n : ℕ} {t : Tree} (h : Good n t) (r k : ℕ) :
    (∑ v ∈ Finset.range (n + 1), (pathsFrom t r v k : ℚ)) = totalPaths t r k := by
  induction t using tree_induction with
  | step a cs ih =>
    have hb : a ≤ n := by cases h with | node _ _ bound _ _ _ => exact bound
    simp only [pathsFrom_node, Nat.cast_add]
    rw [Finset.sum_add_distrib]
    have hroot : (∑ v ∈ Finset.range (n + 1),
        ((if a = v then paths (.node a cs) r k else 0 : ℕ) : ℚ)) =
        (paths (.node a cs) r k : ℚ) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b hb hba
        simp [Ne.symm hba]
      · intro ha
        exact (ha (Finset.mem_range.mpr (by omega))).elim
    rw [hroot, totalPaths_node]
    congr 1
    have hcast : ∀ v, (((cs.map (fun c => pathsFrom c r v k)).sum : ℕ) : ℚ) =
        (cs.map (fun c => (pathsFrom c r v k : ℚ))).sum := by
      intro v
      rw [Nat.cast_list_sum]
      simp only [List.map_map, Function.comp_def]
    simp_rw [hcast]
    rw [← list_sum_finset]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact ih c hc (good_child h hc)

private theorem S_zero (n : ℕ) : S 0 n = ((2 * n).choose n : ℚ) := by
  rw [Nat.cast_choose ℚ (show n ≤ 2 * n by omega)]
  simp [S, show 2 * n - n = n by omega]

private theorem column_closed (n r : ℕ) (hr : r ≤ n) :
    (∑ v ∈ Finset.range (n + 1), (K r v n : ℚ)) =
      (2 ^ r : ℚ) * ((2 * n - r).choose n : ℚ) := by
  simp only [K]
  rw [pathsFrom_sum (good_G n)]
  exact totalPaths_closed n r hr

theorem result : claim := by
  intro n
  rw [S_zero]
  have hh : (∑ i ∈ Finset.range (n + 1), (2 / 2 ^ i : ℚ) *
      ∑ v ∈ Finset.range (n + 1), (K i v n : ℚ)) =
      2 * ((∑ i ∈ Finset.range (n + 1), (2 * n - i).choose n : ℕ) : ℚ) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [column_closed n i (by simpa using Finset.mem_range.mp hi)]
    field_simp
  rw [hh]
  have hs := hockey n 0 (Nat.zero_le n)
  simp only [Nat.sub_zero, zero_add] at hs
  rw [hs]
  exact_mod_cast (central_step n).symm

end D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence

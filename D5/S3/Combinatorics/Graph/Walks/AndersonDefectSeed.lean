/- GID: D5/S3/Combinatorics/Graph/Walks/AndersonDefectSeed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/AndersonDefectSeed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: The actual Anderson defect geometry supplies adjacent diagonal units. -/

/-
proof_shape: defect_diagonal_seed: content; defect_bounds: bind-only.
admission_basis: escape-witness.
escape_witness: the unique negative edge and unequal actual positive runs
  isolate two actual adjacent diagonal units on the live path to defect_diagonal_seed.
defect_bounds consumers: defect_diagonal_seed and the actual nodal construction
  in AndersonDefectFamily.
Direct frozen dependencies: none (pinned Mathlib only).
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic

set_option autoImplicit false
open Matrix
open scoped Fin.NatCast
namespace D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed

/-- The fixed site at which the last periodic block is changed. -/
def defectSite (r m : ℕ) : ℕ := (m - 1) * r + 1

/-- The actual sign word, interpreted in the coefficient ring. -/
def signWord {K : Type*} [Ring K] (r m : ℕ) (i : Fin (r * m)) : K :=
  if i.val % r = 0 ∨ i.val = defectSite r m then -1 else 1

theorem defect_bounds (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    defectSite r m + 1 < r * m := by
  have he : (m - 1) * r + r = r * m := by
    calc
      (m - 1) * r + r = ((m - 1) + 1) * r := by ring
      _ = m * r := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
      _ = r * m := Nat.mul_comm _ _
  dsimp [defectSite]
  omega

private lemma negative_consecutive (r m x : ℕ) (hr : 3 ≤ r) :
    ((x % r = 0 ∨ x = defectSite r m) ∧
      ((x + 1) % r = 0 ∨ x + 1 = defectSite r m)) ↔ x = (m - 1) * r := by
  have hq : defectSite r m % r = 1 := by
    simp [defectSite, Nat.add_mod, Nat.mod_eq_of_lt (show 1 < r by omega)]
  constructor
  · rintro ⟨hx | hx, hy | hy⟩
    · have hh := Nat.add_mod x 1 r
      rw [hx, Nat.mod_eq_of_lt (show 1 < r by omega)] at hh
      simp only [zero_add, Nat.mod_eq_of_lt (show 1 < r by omega)] at hh
      omega
    · dsimp [defectSite] at hy
      omega
    · rw [hx] at hy
      have hh := Nat.add_mod (defectSite r m) 1 r
      rw [hq, Nat.mod_eq_of_lt (show 1 < r by omega)] at hh
      change (defectSite r m + 1) % r = 2 % r at hh
      rw [Nat.mod_eq_of_lt (show 2 < r by omega)] at hh
      omega
    · omega
  · intro hx
    subst x
    exact ⟨Or.inl (by simp), Or.inr rfl⟩

private lemma negative_last (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ¬ ((r * m - 1) % r = 0 ∨ r * m - 1 = defectSite r m) := by
  have hL : 0 < r * m := Nat.mul_pos (by omega) (by omega)
  have hq := defect_bounds r m hr hm
  rintro (h | h)
  · have hh := Nat.add_mod (r * m - 1) 1 r
    rw [Nat.sub_add_cancel hL, Nat.mul_mod_right, h,
      Nat.mod_eq_of_lt (show 1 < r by omega)] at hh
    simp only [zero_add, Nat.mod_eq_of_lt (show 1 < r by omega)] at hh
    omega
  · omega

private lemma negative_oriented_edge (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m)
    (a b : Fin (r * m))
    (ha : a.val % r = 0 ∨ a.val = defectSite r m)
    (hb : b.val % r = 0 ∨ b.val = defectSite r m)
    (hab : (b - a).val = 1) :
    a.val = (m - 1) * r ∧ b.val = defectSite r m := by
  have hL : 0 < r * m := Nat.mul_pos (by omega) (by omega)
  by_cases hle : a ≤ b
  · rw [Fin.sub_val_of_le hle] at hab
    have he : b.val = a.val + 1 := by omega
    have hp := (negative_consecutive r m a.val hr).mp ⟨ha, by simpa [he] using hb⟩
    exact ⟨hp, by dsimp [defectSite]; omega⟩
  · have hh : b < a := lt_of_not_ge hle
    rw [Fin.coe_sub_iff_lt.mpr hh] at hab
    have halast : a.val = r * m - 1 := by omega
    exact (negative_last r m hr hm (by simpa [halast] using ha)).elim

set_option maxHeartbeats 1000000 in
-- Finite matrix and cycle-coordinate normalization uses this local proof budget.
private lemma defect_pair_projection (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    let p : Fin (r * m) := ⟨(m - 1) * r, by have := defect_bounds r m hr hm; dsimp [defectSite] at *; omega⟩
    let q : Fin (r * m) := ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩
    Matrix.single p p (1 : ℝ) + Matrix.single q q (1 : ℝ) ∈
      Algebra.adjoin ℝ {(SimpleGraph.cycleGraph (r * m)).lapMatrix ℝ,
        Matrix.diagonal (signWord r m)} := by
  classical
  dsimp only
  let L := r * m
  have hL : 3 ≤ L := by dsimp [L]; nlinarith
  let p : Fin L := ⟨(m - 1) * r, by have := defect_bounds r m hr hm; dsimp [L, defectSite] at *; omega⟩
  let q : Fin L := ⟨defectSite r m, by have := defect_bounds r m hr hm; dsimp [L] at *; omega⟩
  let G := SimpleGraph.cycleGraph L
  let B := Algebra.adjoin ℝ {G.lapMatrix ℝ, Matrix.diagonal (signWord r m)}
  let A := G.adjMatrix ℝ
  let N : Matrix (Fin L) (Fin L) ℝ := Matrix.diagonal
    (fun i => if i.val % r = 0 ∨ i.val = defectSite r m then 1 else 0)
  have hV : Matrix.diagonal (signWord r m) ∈ B := Algebra.subset_adjoin (by simp)
  have hN : N ∈ B := by
    have h := B.smul_mem (B.sub_mem B.one_mem hV) (1 / 2 : ℝ)
    convert h using 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [N, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.one_apply_eq, smul_eq_mul, signWord]
      split_ifs <;> norm_num
    · simp [N, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, hij, Ne.symm hij]
  have hdeg : G.degMatrix ℝ = (2 : ℝ) • (1 : Matrix (Fin L) (Fin L) ℝ) := by
    obtain ⟨n, hn⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
    dsimp [G]
    rw [hn]
    ext i j
    simp [SimpleGraph.degMatrix, SimpleGraph.cycleGraph_degree_three_le,
      Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply]
  have hA : A ∈ B := by
    have hD : G.lapMatrix ℝ ∈ B := Algebra.subset_adjoin (by simp)
    convert B.sub_mem (B.smul_mem B.one_mem (2 : ℝ)) hD using 1
    dsimp [A]
    rw [SimpleGraph.lapMatrix, hdeg]
    abel
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p,q,defectSite] at this; omega
  have edge : ∀ i j : Fin L,
      (i.val % r = 0 ∨ i.val = defectSite r m) ∧
      (j.val % r = 0 ∨ j.val = defectSite r m) ∧ G.Adj i j ↔
      (i = p ∧ j = q) ∨ (i = q ∧ j = p) := by
    intro i j
    constructor
    · rintro ⟨hi,hj,hij⟩
      rcases SimpleGraph.cycleGraph_adj'.mp hij with h | h
      · obtain ⟨hj',hi'⟩ := negative_oriented_edge r m hr hm j i hj hi h
        exact Or.inr ⟨Fin.ext hi', Fin.ext hj'⟩
      · obtain ⟨hi',hj'⟩ := negative_oriented_edge r m hr hm i j hi hj h
        exact Or.inl ⟨Fin.ext hi', Fin.ext hj'⟩
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · refine ⟨Or.inl (by simp [p]), Or.inr rfl, ?_⟩
        apply SimpleGraph.cycleGraph_adj'.mpr
        right
        rw [Fin.sub_val_of_le (show p ≤ q by change (m - 1) * r ≤ defectSite r m; dsimp [defectSite]; omega)]
        simp [p,q,defectSite]
      · refine ⟨Or.inr rfl, Or.inl (by simp [p]), ?_⟩
        apply SimpleGraph.cycleGraph_adj'.mpr
        left
        rw [Fin.sub_val_of_le (show p ≤ q by change (m - 1) * r ≤ defectSite r m; dsimp [defectSite]; omega)]
        simp [p,q,defectSite]
  have hW : N * A * N = Matrix.single p q 1 + Matrix.single q p 1 := by
    ext i j
    have he : (N * A * N) i j =
        if (i.val % r = 0 ∨ i.val = defectSite r m) ∧
          (j.val % r = 0 ∨ j.val = defectSite r m) ∧ G.Adj i j then 1 else 0 := by
      simp only [N, Matrix.diagonal_mul, Matrix.mul_diagonal, A,
        SimpleGraph.adjMatrix_apply]
      by_cases hi : i.val % r = 0 ∨ i.val = defectSite r m
      <;> by_cases hj : j.val % r = 0 ∨ j.val = defectSite r m
      <;> by_cases ha : G.Adj i j
      <;> simp only [hi,hj,ha,ite_true,ite_false,true_and,false_and,and_true,and_false,
        zero_mul,mul_zero,one_mul,mul_one]
    rw [he]
    simp only [edge i j]
    simp only [Matrix.add_apply, Matrix.single, Matrix.of_apply]
    by_cases h1 : i = p ∧ j = q <;> by_cases h2 : i = q ∧ j = p
    · exact (hpq (h1.1.symm.trans h2.1)).elim
    all_goals simp [Matrix.single, eq_comm, h1, h2, hpq, Ne.symm hpq]
  have hWmem := B.mul_mem (B.mul_mem hN hA) hN
  rw [hW] at hWmem
  have hD := B.mul_mem hWmem hWmem
  simpa [add_mul, mul_add, Matrix.single_mul_single_of_ne, hpq, hpq.symm,
    add_comm, p, q, B, G, L] using hD

private lemma filtered_transport {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hs : A.IsSymm) (f : n → ℝ) (a b : n)
    (hcol : ∀ i, f i * A i a = if i = b then 1 else 0) :
    Matrix.diagonal f * A * Matrix.single a a 1 * A * Matrix.diagonal f =
      Matrix.single b b 1 := by
  have hleft : Matrix.diagonal f * A * Matrix.single a a 1 = Matrix.single b a 1 := by
    ext i j
    by_cases hj : j = a
    · subst j
      simp only [Matrix.mul_single_apply_same, mul_one, Matrix.diagonal_mul, hcol]
      simp [Matrix.single, eq_comm]
    · rw [Matrix.mul_single_apply_of_ne (1 : ℝ) a a i j hj]
      simp [Matrix.single, Ne.symm hj]
  have hright : Matrix.single a a 1 * A * Matrix.diagonal f = Matrix.single a b 1 := by
    simpa only [Matrix.transpose_mul, Matrix.diagonal_transpose,
      show Aᵀ = A from hs, Matrix.transpose_single, mul_assoc] using
        congrArg Matrix.transpose hleft
  calc
    Matrix.diagonal f * A * Matrix.single a a 1 * A * Matrix.diagonal f =
        (Matrix.diagonal f * A * Matrix.single a a 1) *
          (Matrix.single a a 1 * A * Matrix.diagonal f) := by
      symm
      calc
        _ = (Matrix.diagonal f * A) * (Matrix.single a a 1 * Matrix.single a a 1) *
            (A * Matrix.diagonal f) := by noncomm_ring
        _ = _ := by simp [mul_assoc]
    _ = Matrix.single b b 1 := by rw [hleft, hright]; simp

private lemma filtered_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (_hs : A.IsSymm) (f : n → ℝ) (a : n)
    (hcol : ∀ i, f i * A i a = 0) :
    Matrix.diagonal f * A * Matrix.single a a 1 * A * Matrix.diagonal f = 0 := by
  have hleft : Matrix.diagonal f * A * Matrix.single a a 1 = 0 := by
    ext i j
    by_cases hj : j = a
    · subst j
      simp only [Matrix.mul_single_apply_same, mul_one, Matrix.diagonal_mul, hcol,
        Matrix.zero_apply]
    · rw [Matrix.mul_single_apply_of_ne (1 : ℝ) a a i j hj]
      rfl
  rw [hleft, zero_mul, zero_mul]

private lemma cycle_neighbors (L : ℕ) (hL : 3 ≤ L) [NeZero L] (i a : Fin L) :
    (SimpleGraph.cycleGraph L).Adj i a ↔ i = a - 1 ∨ i = a + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
  have h := congrArg (fun s => i ∈ s) (SimpleGraph.cycleGraph_neighborSet (v := a))
  simpa [SimpleGraph.mem_neighborSet, SimpleGraph.adj_comm] using h

private lemma cycle_filtered_column (L : ℕ) (hL : 3 ≤ L) [NeZero L]
    (f : Fin L → ℝ) (a b c : Fin L)
    (hneighbors : (b = a - 1 ∧ c = a + 1) ∨ (b = a + 1 ∧ c = a - 1))
    (hbc : b ≠ c) (hb : f b = 1) (hc : f c = 0) :
    ∀ i, f i * (SimpleGraph.cycleGraph L).adjMatrix ℝ i a = if i = b then 1 else 0 := by
  intro i
  have hadj : (SimpleGraph.cycleGraph L).Adj i a ↔ i = b ∨ i = c := by
    rw [cycle_neighbors L hL]
    rcases hneighbors with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> tauto
  by_cases hib : i = b
  · subst i
    simp [SimpleGraph.adjMatrix_apply, hadj, hb]
  · by_cases hic : i = c
    · subst i
      simp [SimpleGraph.adjMatrix_apply, hadj, hc, hib]
    · simp [SimpleGraph.adjMatrix_apply, hadj, hib, hic]

private def armLeft (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) (j : ℕ) : Fin (r * m) :=
  ⟨((m - 1) * r - j) % (r * m), Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega))⟩

private def armRight (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) (j : ℕ) : Fin (r * m) :=
  ⟨(defectSite r m + j) % (r * m), Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega))⟩

private lemma arms_values (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    (∀ j, j ≤ r → (armLeft r m hr hm j).val = (m - 1) * r - j) ∧
    (∀ j, j ≤ r - 2 → (armRight r m hr hm j).val = defectSite r m + j) ∧
    armRight r m hr hm (r - 1) =
      ⟨0, Nat.mul_pos (by omega) (by omega)⟩ := by
  have hb := defect_bounds r m hr hm
  have hpr : r ≤ (m - 1) * r := by
    calc
      r = 1 * r := by simp
      _ ≤ (m - 1) * r := Nat.mul_le_mul_right r (by omega)
  have hL : (m - 1) * r + r = r * m := by
    calc
      _ = ((m - 1) + 1) * r := by ring
      _ = m * r := by rw [Nat.sub_add_cancel (show 1 ≤ m by omega)]
      _ = _ := Nat.mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    dsimp [armLeft]
    apply Nat.mod_eq_of_lt
    dsimp [defectSite] at hb
    omega
  · intro j hj
    dsimp [armRight]
    apply Nat.mod_eq_of_lt
    dsimp [defectSite] at *
    omega
  · apply Fin.ext
    change (defectSite r m + (r - 1)) % (r * m) = 0
    have he : defectSite r m + (r - 1) = r * m := by dsimp [defectSite]; omega
    rw [he, Nat.mod_self]

private lemma arms_signs (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    (∀ j, 1 ≤ j → j ≤ r - 1 →
      signWord (K := ℝ) r m (armLeft r m hr hm j) = 1) ∧
    (∀ j, 1 ≤ j → j ≤ r - 2 →
      signWord (K := ℝ) r m (armRight r m hr hm j) = 1) := by
  have hvals := arms_values r m hr hm
  have hpr : r ≤ (m - 1) * r := by
    calc
      r = 1 * r := by simp
      _ ≤ (m - 1) * r := Nat.mul_le_mul_right r (by omega)
  have hp : (m - 1) * r = (m - 2) * r + r := by
    have he : m - 1 = (m - 2) + 1 := by omega
    rw [he]
    ring
  constructor
  · intro j hj hjr
    have he : (m - 1) * r - j = (m - 2) * r + (r - j) := by omega
    have hrem : ((m - 1) * r - j) % r = r - j := by
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show r - j < r by omega)]
    simp only [signWord, hvals.1 j (by omega), hrem]
    rw [if_neg]
    dsimp [defectSite]
    omega
  · intro j hj hjr
    have hrem : (defectSite r m + j) % r = j + 1 := by
      have he : defectSite r m + j = (m - 1) * r + (j + 1) := by dsimp [defectSite]; omega
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show j + 1 < r by omega)]
    simp only [signWord, hvals.2.1 j hjr, hrem]
    rw [if_neg]
    omega

private lemma arm_left_neighbors (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m)
    [NeZero (r * m)] (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r - 1) :
    armLeft r m hr hm (j + 1) = armLeft r m hr hm j - 1 ∧
    armLeft r m hr hm (j - 1) = armLeft r m hr hm j + 1 := by
  have hpr : r ≤ (m - 1) * r := by
    calc
      r = 1 * r := by simp
      _ ≤ (m - 1) * r := Nat.mul_le_mul_right r (by omega)
  have h1 : (m - 1) * r - j = ((m - 1) * r - (j + 1)) + 1 := by omega
  have h2 : (m - 1) * r - (j - 1) = ((m - 1) * r - j) + 1 := by omega
  constructor
  · change (((m - 1) * r - (j + 1) : ℕ) : Fin (r * m)) =
      (((m - 1) * r - j : ℕ) : Fin (r * m)) - 1
    rw [h1]
    push_cast
    abel
  · change (((m - 1) * r - (j - 1) : ℕ) : Fin (r * m)) =
      (((m - 1) * r - j : ℕ) : Fin (r * m)) + 1
    rw [h2]
    push_cast
    rfl

private lemma arm_right_neighbors (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m)
    [NeZero (r * m)] (j : ℕ) (hj : 1 ≤ j) :
    armRight r m hr hm (j + 1) = armRight r m hr hm j + 1 ∧
    armRight r m hr hm (j - 1) = armRight r m hr hm j - 1 := by
  constructor
  · change ((defectSite r m + (j + 1) : ℕ) : Fin (r * m)) =
      ((defectSite r m + j : ℕ) : Fin (r * m)) + 1
    push_cast
    abel
  · have h : defectSite r m + j = defectSite r m + (j - 1) + 1 := by omega
    change ((defectSite r m + (j - 1) : ℕ) : Fin (r * m)) =
      ((defectSite r m + j : ℕ) : Fin (r * m)) - 1
    rw [h]
    push_cast
    abel

set_option maxHeartbeats 1000000 in
-- Finite matrix and cycle-coordinate normalization uses this local proof budget.
/-- The unequal actual positive runs separate two adjacent diagonal units. -/
theorem defect_diagonal_seed (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ∃ j : Fin (r * m),
      Matrix.single j j (1 : ℝ) ∈ Algebra.adjoin ℝ
        {(SimpleGraph.cycleGraph (r * m)).lapMatrix ℝ, Matrix.diagonal (signWord r m)} ∧
      Matrix.single (j + ⟨1, by have := defect_bounds r m hr hm; omega⟩)
        (j + ⟨1, by have := defect_bounds r m hr hm; omega⟩) (1 : ℝ) ∈
        Algebra.adjoin ℝ {(SimpleGraph.cycleGraph (r * m)).lapMatrix ℝ,
          Matrix.diagonal (signWord r m)} := by
  classical
  let L := r * m
  have hL : 3 ≤ L := by dsimp [L]; nlinarith
  letI : NeZero L := ⟨by omega⟩
  let l := armLeft r m hr hm
  let u := armRight r m hr hm
  let A := (SimpleGraph.cycleGraph L).adjMatrix ℝ
  let B := Algebra.adjoin ℝ {(SimpleGraph.cycleGraph L).lapMatrix ℝ,
    Matrix.diagonal (signWord r m)}
  let plus : Fin L → ℝ := fun i => (1 + signWord r m i) / 2
  let P := Matrix.diagonal plus
  let F : ℕ → Matrix (Fin L) (Fin L) ℝ := fun j => Matrix.single (l j) (l j) 1 +
    if j < r - 1 then Matrix.single (u j) (u j) 1 else 0
  have vals := arms_values r m hr hm
  have signs := arms_signs r m hr hm
  have hpr : r ≤ (m - 1) * r := by
    calc
      r = 1 * r := by simp
      _ ≤ (m - 1) * r := Nat.mul_le_mul_right r (by omega)
  have cross (i j : ℕ) (hi : i ≤ r) (hj : j ≤ r - 2) : l i ≠ u j := by
    intro h
    have hh := congrArg Fin.val h
    rw [vals.1 i hi, vals.2.1 j hj] at hh
    dsimp [defectSite] at hh
    omega
  have hplusl (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r - 1) : plus (l j) = 1 := by
    dsimp [plus,l]
    rw [signs.1 j hj hjr]
    norm_num
  have hplusu (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r - 2) : plus (u j) = 1 := by
    dsimp [plus,u]
    rw [signs.2 j hj hjr]
    norm_num
  have hplusl0 : plus (l 0) = 0 := by simp [plus,l,signWord,armLeft, Nat.mod_eq_of_lt
    (show (m - 1) * r < r * m by have := defect_bounds r m hr hm; dsimp [defectSite] at *; omega)]
  have hplusu0 : plus (u 0) = 0 := by
    dsimp [plus]
    have hv := vals.2.1 0 (by omega)
    simp only [Nat.add_zero] at hv
    simp [signWord,u,hv]
  have hplusuend : plus (u (r - 1)) = 0 := by
    dsimp [plus,u]
    rw [vals.2.2]
    simp [signWord]
  have hP : P ∈ B := by
    have hV : Matrix.diagonal (signWord r m) ∈ B := Algebra.subset_adjoin (by simp)
    have h := B.smul_mem (B.add_mem B.one_mem hV) (1 / 2 : ℝ)
    convert h using 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [P,plus,Matrix.smul_apply,div_eq_mul_inv]
      ring
    · simp [P,Matrix.diagonal,hij,Ne.symm hij,Matrix.one_apply_ne hij]
  have hA : A ∈ B := by
    have hD : (SimpleGraph.cycleGraph L).lapMatrix ℝ ∈ B := Algebra.subset_adjoin (by simp)
    have hd : (SimpleGraph.cycleGraph L).degMatrix ℝ =
        (2 : ℝ) • (1 : Matrix (Fin L) (Fin L) ℝ) := by
      obtain ⟨n, hn⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
      rw [hn]
      ext i j
      simp [SimpleGraph.degMatrix,SimpleGraph.cycleGraph_degree_three_le,
        Matrix.diagonal,Matrix.one_apply,Matrix.smul_apply]
    convert B.sub_mem (B.smul_mem B.one_mem (2 : ℝ)) hD using 1
    dsimp [A]
    rw [SimpleGraph.lapMatrix, hd]
    abel
  have hsym : A.IsSymm := SimpleGraph.isSymm_adjMatrix _
  have hF0 : F 0 ∈ B := by
    have h := defect_pair_projection r m hr hm
    simpa [F,l,u,armLeft,armRight, Nat.mod_eq_of_lt,
      show (m - 1) * r < r * m by have := defect_bounds r m hr hm; dsimp [defectSite] at *; omega,
      show defectSite r m < r * m by have := defect_bounds r m hr hm; omega,
      show 0 < r - 1 by omega] using h
  have baseL : l 1 = l 0 - 1 ∧ u 0 = l 0 + 1 := by
    constructor
    · change (((m - 1) * r - 1 : ℕ) : Fin L) = (((m - 1) * r : ℕ) : Fin L) - 1
      have h : (m - 1) * r = ((m - 1) * r - 1) + 1 := by omega
      rw [h]
      push_cast
      abel
    · change ((defectSite r m : ℕ) : Fin L) = (((m - 1) * r : ℕ) : Fin L) + 1
      simp [defectSite,Nat.cast_add]
  have baseU : u 1 = u 0 + 1 ∧ l 0 = u 0 - 1 := by
    constructor
    · change ((defectSite r m + 1 : ℕ) : Fin L) = ((defectSite r m : ℕ) : Fin L) + 1
      push_cast
      rfl
    · rw [baseL.2]
      abel
  have hF1 : F 1 ∈ B := by
    have h := B.mul_mem (B.mul_mem (B.mul_mem (B.mul_mem hP hA) hF0) hA) hP
    have h1 := filtered_transport A hsym plus (l 0) (l 1)
      (cycle_filtered_column L hL plus (l 0) (l 1) (u 0) (Or.inl baseL)
        (cross 1 0 (by omega) (by omega)) (hplusl 1 (by omega) (by omega)) hplusu0)
    have h2 := filtered_transport A hsym plus (u 0) (u 1)
      (cycle_filtered_column L hL plus (u 0) (u 1) (l 0) (Or.inr baseU)
        (Ne.symm (cross 0 1 (by omega) (by omega)))
        (hplusu 1 (by omega) (by omega)) hplusl0)
    simpa only [F, show 0 < r - 1 by omega, show 1 < r - 1 by omega, ite_true,
      mul_add, add_mul, P, h1, h2] using h
  have step (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r - 2)
      (hprev : F (j - 1) ∈ B) (hcur : F j ∈ B) : F (j + 1) ∈ B := by
    let f : Fin L → ℝ := fun i => plus i *
      (1 - (if i = l (j - 1) then 1 else 0) - (if i = u (j - 1) then 1 else 0))
    have hQ : Matrix.diagonal f ∈ B := by
      have heq : Matrix.diagonal f = P * (1 - F (j - 1)) := by
        ext i k
        dsimp only [P]
        simp only [Matrix.diagonal_mul, Matrix.sub_apply, Matrix.one_apply,
          F, show j - 1 < r - 1 by omega, ite_true, Matrix.add_apply]
        by_cases hik : i = k
        · subst k
          simp only [Matrix.diagonal_apply_eq,ite_true,Matrix.single,Matrix.of_apply,and_self]
          dsimp only [f]
          simp only [eq_comm]
          ring
        · have hl0 : ¬ (i = l (j - 1) ∧ k = l (j - 1)) := by
            rintro ⟨h1,h2⟩
            exact hik (h1.trans h2.symm)
          have hu0 : ¬ (i = u (j - 1) ∧ k = u (j - 1)) := by
            rintro ⟨h1,h2⟩
            exact hik (h1.trans h2.symm)
          simp [f,Matrix.single,Matrix.diagonal_apply,hik,Ne.symm hik,eq_comm,hl0,hu0]
      rw [heq]
      exact B.mul_mem hP (B.sub_mem B.one_mem hprev)

    have hl := arm_left_neighbors r m hr hm j hj (by omega)
    have hu := arm_right_neighbors r m hr hm j hj
    have hll : l (j + 1) ≠ l (j - 1) := by
      intro h
      have hh := congrArg Fin.val h
      rw [vals.1 _ (by omega), vals.1 _ (by omega)] at hh
      omega
    have huu : u (j + 1) ≠ u (j - 1) := by
      intro h
      have hh := congrArg Fin.val h
      by_cases hje : j + 1 ≤ r - 2
      · rw [vals.2.1 _ hje, vals.2.1 _ (by omega)] at hh
        omega
      · have he : j + 1 = r - 1 := by omega
        dsimp only [u] at hh
        rw [he, vals.2.2, vals.2.1 _ (by omega)] at hh
        simp only [Fin.mk_zero] at hh
        dsimp [defectSite] at hh
        omega
    have flold : f (l (j - 1)) = 0 := by
      simp [f,cross (j - 1) (j - 1) (by omega) (by omega)]
    have fuold : f (u (j - 1)) = 0 := by
      simp [f,Ne.symm (cross (j - 1) (j - 1) (by omega) (by omega))]
    have flnew : f (l (j + 1)) = 1 := by
      simp [f,hll,cross (j + 1) (j - 1) (by omega) (by omega),
        hplusl (j + 1) (by omega) (by omega)]
    have hltrans := filtered_transport A hsym f (l j) (l (j + 1))
      (cycle_filtered_column L hL f (l j) (l (j + 1)) (l (j - 1))
        (Or.inl hl) hll flnew flold)
    have h := B.mul_mem (B.mul_mem (B.mul_mem (B.mul_mem hQ hA) hcur) hA) hQ
    by_cases hje : j + 1 < r - 1
    · have funew : f (u (j + 1)) = 1 := by
        simp [f,huu,Ne.symm (cross (j - 1) (j + 1) (by omega) (by omega)),
          hplusu (j + 1) (by omega) (by omega)]
      have hutrans := filtered_transport A hsym f (u j) (u (j + 1))
        (cycle_filtered_column L hL f (u j) (u (j + 1)) (u (j - 1))
          (Or.inr hu) huu funew fuold)
      simpa only [F,show j < r - 1 by omega,hje,ite_true,mul_add,add_mul,
        hltrans,hutrans] using h
    · have he : j + 1 = r - 1 := by omega
      have funew : f (u (j + 1)) = 0 := by simp [f,he,hplusuend]
      have hzero : ∀ i, f i * A i (u j) = 0 := by
        intro i
        have hadj : (SimpleGraph.cycleGraph L).Adj i (u j) ↔
            i = u (j + 1) ∨ i = u (j - 1) := by
          rw [cycle_neighbors L hL,←hu.1,←hu.2]
          tauto
        by_cases hi : i = u (j + 1)
        · subst i
          simp [funew]
        · by_cases hi' : i = u (j - 1)
          · subst i
            simp [fuold]
          · simp [A,SimpleGraph.adjMatrix_apply,hadj,hi,hi']
      have hutrans := filtered_zero A hsym f (u j) hzero
      simpa only [F,show j < r - 1 by omega,hje,ite_true,ite_false,mul_add,add_mul,
        hltrans,hutrans,add_zero] using h
  have allF : ∀ j, j ≤ r - 1 → F j ∈ B := by
    apply Nat.twoStepInduction
    · intro _
      exact hF0
    · intro _
      exact hF1
    · intro j h0 h1 hj
      have he : j + 2 = (j + 1) + 1 := by omega
      rw [he]
      apply step (j + 1) (by omega) (by omega)
      · simpa using h0 (by omega)
      · exact h1 (by omega)
  have hX : Matrix.single (l (r - 1)) (l (r - 1)) (1 : ℝ) ∈ B := by
    simpa [F] using allF (r - 1) (by omega)
  let n : Fin L → ℝ := fun i => 1 - plus i
  have hN : Matrix.diagonal n ∈ B := by
    convert B.sub_mem B.one_mem hP using 1
    ext i j
    by_cases hij : i = j <;> simp [n,P,Matrix.diagonal,Matrix.one_apply,hij]
  have hln := arm_left_neighbors r m hr hm (r - 1) (by omega) (by omega)
  have hy : n (l r) = 1 := by
    have hrem : ((m - 1) * r - r) % r = 0 := by
      have he : m - 1 = (m - 2) + 1 := by omega
      rw [he]
      simp [Nat.add_mul]
    simp [n,plus,signWord,l,vals.1 r (by omega),hrem]
  have hc : n (l ((r - 1) - 1)) = 0 := by
    simp [n,hplusl ((r - 1) - 1) (by omega) (by omega)]
  have hne : l r ≠ l ((r - 1) - 1) := by
    intro h
    have hh := congrArg Fin.val h
    rw [vals.1 _ (by omega), vals.1 _ (by omega)] at hh
    omega
  have hcol := cycle_filtered_column L hL n (l (r - 1)) (l r) (l ((r - 1) - 1))
    (Or.inl (by simpa [show (r - 1) + 1 = r by omega] using hln)) hne hy hc
  have hY := B.mul_mem (B.mul_mem (B.mul_mem (B.mul_mem hN hA) hX) hA) hN
  rw [filtered_transport A hsym n (l (r - 1)) (l r) hcol] at hY
  refine ⟨l r,hY,?_⟩
  have he : l r + (⟨1, by omega⟩ : Fin L) = l (r - 1) := by
    have hp : (m - 1) * r - (r - 1) = ((m - 1) * r - r) + 1 := by omega
    change (((m - 1) * r - r : ℕ) : Fin L) + (⟨1, by omega⟩ : Fin L) =
      (((m - 1) * r - (r - 1) : ℕ) : Fin L)
    rw [hp]
    have hone : (⟨1, by omega⟩ : Fin L) = 1 := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (show 1 < L by omega)]
    rw [hone]
    push_cast
    rfl
  simpa only [he] using hX


end D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed

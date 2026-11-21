/- GID: D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank-three signed-coordinate quotient Cayley graphs contain four-cliques at unbounded row counts. -/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The fixed-rank stabilization conjecture for standardized Abelian Cayley graphs. -/

namespace D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement

/-- Integer span of the columns of the Heuberger matrix. -/
def relations {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℤ) :
    AddSubgroup (Fin m → ℤ) :=
  M.mulVecLin.range.toAddSubgroup

private abbrev Vertex {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℤ) :=
  (Fin m → ℤ) ⧸ relations M

def generators {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℤ) :
    Set (Vertex M) :=
  {s | ∃ i : Fin m,
    let e := QuotientAddGroup.mk' (relations M) (Pi.single i 1)
    s = e ∨ s = -e}

/-- Whether zero occurs among the signed coordinate cosets. -/
def HasLoops {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℤ) : Prop :=
  0 ∈ generators M

private def graph {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℤ) : SimpleGraph (Vertex M) :=
  SimpleGraph.addCayley (generators M)

/-- Source bipartiteness, including the absence of loops. -/
def IsBipartite {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℤ) : Prop :=
  ¬ HasLoops M ∧ (graph M).IsBipartite

/-- Source chromatic number, with infinity assigned to looped graphs. -/
noncomputable def chromaticNumber {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℤ) : ℕ∞ := by
  classical
  exact if HasLoops M then ⊤ else (graph M).chromaticNumber

/-- Krebs–Leyva, arXiv:2511.03028v1, Conjecture 1.2 (printed page 3). -/
def claim : Prop :=
  ∀ r : ℕ, 0 < r →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ M : Matrix (Fin m) (Fin r) ℤ,
        (∀ i : Fin m, ∃ j : Fin r, M i j ≠ 0) →
        ¬ IsBipartite M → ¬ HasLoops M → chromaticNumber M = 3

private def rowCount (k : ℕ) : ℕ := 4 * (k + 1) + 3

/-- The columns are e₂ - 2e₁, e₃ - 3e₁, and 4e₁ + ∑ j fⱼ. -/
private def family (k : ℕ) : Matrix (Fin (rowCount k)) (Fin 3) ℤ :=
  fun i =>
    if i.val = 0 then ![-2, -3, 4]
    else if i.val = 1 then ![1, 0, 0]
    else if i.val = 2 then ![0, 1, 0]
    else ![0, 0, (i.val : ℤ) - 2]

private def row (k : ℕ) (i : Fin 5) : Fin (rowCount k) :=
  ⟨i.val, by unfold rowCount; omega⟩

private def axis (k : ℕ) (i : Fin (rowCount k)) : Vertex (family k) :=
  QuotientAddGroup.mk' (relations (family k)) (Pi.single i 1)

private theorem mulVec_family (k : ℕ) (a : Fin 3 → ℤ) (i : Fin (rowCount k)) :
    (family k).mulVecLin a i =
      if i.val = 0 then -2 * a 0 - 3 * a 1 + 4 * a 2
      else if i.val = 1 then a 0
      else if i.val = 2 then a 1
      else ((i.val : ℤ) - 2) * a 2 := by
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  unfold family
  split_ifs <;> simp
  omega

private theorem family_noZeroRows (k : ℕ) : ∀ i, ∃ j, family k i j ≠ 0 := by
  intro i
  by_cases h0 : i.val = 0
  · exact ⟨0, by simp [family, h0]⟩
  by_cases h1 : i.val = 1
  · exact ⟨0, by simp [family, h1]⟩
  by_cases h2 : i.val = 2
  · exact ⟨1, by simp [family, h2]⟩
  refine ⟨2, ?_⟩
  simp [family, h0, h1, h2]
  omega

private theorem axis_ne_zero (k : ℕ) (i : Fin (rowCount k)) : axis k i ≠ 0 := by
  intro hz
  have hm : Pi.single i (1 : ℤ) ∈ relations (family k) := by
    rw [← QuotientAddGroup.ker_mk' (relations (family k))]
    exact hz
  obtain ⟨a, ha⟩ : ∃ a, (family k).mulVecLin a = Pi.single i 1 := hm
  have h0 := congrFun ha (row k 0)
  have h1 := congrFun ha (row k 1)
  have h2 := congrFun ha (row k 2)
  have h3 := congrFun ha (row k 3)
  have h4 := congrFun ha (row k 4)
  simp [mulVec_family, row, Pi.single_apply, Fin.ext_iff] at h0 h1 h2 h3 h4
  have hc : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 := by
    split_ifs at h0 h1 h2 h3 h4 <;> omega
  have ha0 : a = 0 := by
    funext j
    fin_cases j
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2
  subst a
  simpa using congrFun ha i

private theorem family_loopless (k : ℕ) : ¬ HasLoops (family k) := by
  rintro ⟨i, hi | hi⟩
  · exact axis_ne_zero k i hi.symm
  · exact axis_ne_zero k i (neg_eq_zero.mp hi.symm)

private theorem first_columns (k : ℕ) (j : Fin 2) :
    (family k).mulVecLin (Pi.single j.castSucc 1) =
      Pi.single (row k ⟨j.val + 1, by omega⟩) 1 -
        (j.val + 2) • Pi.single (row k 0) 1 := by
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  funext i
  fin_cases j <;>
    simp [Matrix.col_apply, family, Pi.single_apply, Fin.ext_iff, row, Pi.sub_apply] <;>
    split_ifs <;> norm_num <;> omega

private theorem axis_eq_nsmul (k : ℕ) (d : Fin 3) :
    (d.val + 1) • axis k (row k 0) = axis k (row k ⟨d.val, by omega⟩) := by
  by_cases hd : d.val = 0
  · have hd' : d = 0 := Fin.ext hd
    subst d
    simp
  let j : Fin 2 := ⟨d.val - 1, by omega⟩
  have hj : j.val + 1 = d.val := by dsimp [j]; omega
  have hmul : j.val + 2 = d.val + 1 := by omega
  have hm : (family k).mulVecLin (Pi.single j.castSucc 1) ∈ relations (family k) :=
    ⟨_, rfl⟩
  rw [first_columns, hmul] at hm
  have hr : row k ⟨j.val + 1, by omega⟩ = row k ⟨d.val, by omega⟩ := Fin.ext hj
  rw [hr, ← QuotientAddGroup.ker_mk' (relations (family k))] at hm
  change QuotientAddGroup.mk' _ (_ - _) = 0 at hm
  rw [map_sub, map_nsmul, sub_eq_zero] at hm
  exact hm.symm

/-- Four vertices in the actual source quotient. -/
private def cliqueVertex (k : ℕ) (i : Fin 4) : Vertex (family k) :=
  i.val • axis k (row k 0)

private theorem clique_adj_of_lt (k : ℕ) {i j : Fin 4} (h : i.val < j.val) :
    (graph (family k)).Adj (cliqueVertex k i) (cliqueVertex k j) := by
  let d : Fin 3 := ⟨j.val - i.val - 1, by omega⟩
  let t := row k (⟨d.val, by omega⟩ : Fin 5)
  have ht : i.val + (d.val + 1) = j.val := by dsimp [d]; omega
  have hstep : cliqueVertex k i + axis k t = cliqueVertex k j := by
    change i.val • axis k (row k 0) + axis k t = j.val • axis k (row k 0)
    rw [← axis_eq_nsmul k d, ← add_nsmul, ht]
  apply (SimpleGraph.addCayley_adj' _ _ _).2
  refine ⟨?_, axis k t, ⟨t, Or.inl rfl⟩, Or.inl hstep⟩
  intro he
  rw [← he] at hstep
  exact axis_ne_zero k t (by simpa using hstep)

private theorem family_clique (k : ℕ) :
    Pairwise fun i j : Fin 4 => (graph (family k)).Adj (cliqueVertex k i) (cliqueVertex k j) := by
  intro i j hij
  rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
  · exact clique_adj_of_lt k h
  · exact (clique_adj_of_lt k h).symm

private theorem graph_chromatic_lower (k : ℕ) : 4 ≤ (graph (family k)).chromaticNumber := by
  exact SimpleGraph.le_chromaticNumber_of_pairwise_adj (n := 4) (by simp)
    (cliqueVertex k) (family_clique k)

private theorem family_nonbipartite (k : ℕ) : ¬ IsBipartite (family k) := by
  intro h
  have hh := (graph_chromatic_lower k).trans h.2.chromaticNumber_le
  norm_num at hh

private theorem family_chromatic_lower (k : ℕ) : 4 ≤ chromaticNumber (family k) := by
  simpa only [chromaticNumber, ite_eq_right (family_loopless k)] using graph_chromatic_lower k

private theorem cofinal_counterexamples (m₀ : ℕ) :
    ∃ m : ℕ, m₀ ≤ m ∧ ∃ M : Matrix (Fin m) (Fin 3) ℤ,
      (∀ i, ∃ j, M i j ≠ 0) ∧ ¬ IsBipartite M ∧ ¬ HasLoops M ∧ 4 ≤ chromaticNumber M :=
  ⟨rowCount m₀, by unfold rowCount; omega, family m₀, family_noZeroRows m₀,
    family_nonbipartite m₀, family_loopless m₀, family_chromatic_lower m₀⟩

/-- The rank-three family refutes the full stabilization conjecture. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨m₀, h⟩ := h 3 (by decide)
  obtain ⟨m, hdim, M, hrows, hbip, hloop, hchrom⟩ := cofinal_counterexamples m₀
  rw [h m hdim M hrows hbip hloop] at hchrom
  norm_num at hchrom

end D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement

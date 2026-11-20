/- GID: D5/S3/Quantum/Dynamics/WeldedColumnEvolution
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/WeldedColumnEvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized column vectors intertwine a welded-tree walk and its weighted path. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap

/-! Normalized graph columns and the corresponding weighted path evolution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.WeldedColumnEvolution

open _root_.Matrix
open scoped Matrix.Norms.Operator

private theorem exp_entry {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) (v w : V) :
    NormedSpace.exp A v w = ∑' k : ℕ, (Nat.factorial k : ℚ)⁻¹ • (A ^ k) v w := by
  rw [NormedSpace.exp_eq_tsum_rat]
  let eval : Matrix V V ℂ →+ ℂ :=
    { toFun := fun M => M v w, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hContinuous : Continuous eval := continuous_apply_apply v w
  have hSum := (NormedSpace.expSeries_summable' (𝕂 := ℚ) A).hasSum.map eval hContinuous
  exact hSum.tsum_eq.symm

private theorem exp_diagonal_blocks {V Q : Type*}
    [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (A : Matrix V V ℂ) (B : Matrix Q Q ℂ) :
    NormedSpace.exp (fromBlocks A 0 0 B) =
      fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp B) := by
  ext (v | q) (w | r) <;>
    simp [exp_entry, fromBlocks_diagonal_pow]

private theorem exp_intertwines {V Q : Type*}
    [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (A : Matrix V V ℂ) (B : Matrix Q Q ℂ) (C : Matrix V Q ℂ)
    (h : A * C = C * B) :
    NormedSpace.exp A * C = C * NormedSpace.exp B := by
  let diag : Matrix (V ⊕ Q) (V ⊕ Q) ℂ := fromBlocks A 0 0 B
  let upper : Matrix (V ⊕ Q) (V ⊕ Q) ℂ := fromBlocks 0 C 0 0
  have hc : Commute diag upper := by
    change diag * upper = upper * diag
    simp [diag, upper, fromBlocks_multiply, h]
  have he := hc.exp_left.eq
  rw [show diag = fromBlocks A 0 0 B from rfl, exp_diagonal_blocks] at he
  simpa [upper, fromBlocks_multiply] using congrArg toBlocks₁₂ he


open D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open scoped BigOperators

abbrev Column (d : ℕ) := Fin (2 * (d + 1) - 1 + 1)

/-- The depth in the nearer of the two binary trees. -/
def columnDepth (d : ℕ) (i : Column d) : ℕ :=
  min i.val (2 * d + 1 - i.val)

/-- Neighbor counts towards the root, children and central weld. -/
def columnDegree (d : ℕ) (i j : Column d) : ℕ :=
  if i.val + 1 = j.val then
    if i.val ≤ d then 2 else 1
  else if j.val + 1 = i.val then
    if j.val < d then 1 else 2
  else 0

private noncomputable def columnWeight (d : ℕ) (i : Column d) : ℝ :=
  (Real.sqrt 2 ^ columnDepth d i)⁻¹

/-- Each column is supported precisely on the original vertices of that level. -/
noncomputable def normalizedColumns {V : Type*} {d : ℕ}
    (column : V → Column d) : Matrix V (Column d) ℂ :=
  fun v j => if column v = j then (columnWeight d j : ℂ) else 0

private theorem centralDefect_entry (d : ℕ) (i j : Column d) :
    centralDefect (d + 1) (by omega) i j =
      if i.val + 1 = j.val then (if i.val = d then Real.sqrt 2 else 1)
      else if j.val + 1 = i.val then (if j.val = d then Real.sqrt 2 else 1)
      else 0 := by
  by_cases hu : i.val + 1 = j.val
  · have hl : j.val + 1 ≠ i.val := by omega
    simp [centralDefect, jacobiMatrix, upperBand, centralEdges, hu, hl]
  · simp [centralDefect, jacobiMatrix, upperBand, centralEdges, hu]

private theorem column_action_scalar (d : ℕ) (i j : Column d) :
    (Real.sqrt 2)⁻¹ * (columnDegree d i j : ℝ) * columnWeight d j =
      columnWeight d i * centralDefect (d + 1) (by omega) i j := by
  have hp : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [centralDefect_entry]
  by_cases hu : i.val + 1 = j.val
  · by_cases hlt : i.val < d
    · have hd : columnDepth d j = columnDepth d i + 1 := by
        unfold columnDepth
        omega
      have hle : i.val ≤ d := by omega
      have hne : i.val ≠ d := by omega
      simp [columnWeight, columnDegree, hu, hle, hne, hd, pow_succ] <;> field_simp [hp.ne'] <;> nlinarith [hs]
    · by_cases heq : i.val = d
      · have hd : columnDepth d j = columnDepth d i := by
          unfold columnDepth
          omega
        have hcentral : d + 1 = j.val := by omega
        simp [columnWeight, columnDegree, heq, hcentral, hd] <;> field_simp [hp.ne'] <;> nlinarith [hs]
      · have hng : ¬ i.val ≤ d := by omega
        have hd : columnDepth d i = columnDepth d j + 1 := by
          unfold columnDepth
          omega
        simp [columnWeight, columnDegree, hu, heq, hng, hd, pow_succ] <;> field_simp [hp.ne'] <;> nlinarith [hs]
  · by_cases hl : j.val + 1 = i.val
    · by_cases hlt : j.val < d
      · have hd : columnDepth d i = columnDepth d j + 1 := by
          unfold columnDepth
          omega
        have hne : j.val ≠ d := by omega
        simp [columnWeight, columnDegree, hu, hl, hlt, hne, hd, pow_succ] <;> field_simp [hp.ne'] <;> nlinarith [hs]
      · by_cases heq : j.val = d
        · have hd : columnDepth d j = columnDepth d i := by
            unfold columnDepth
            omega
          have hcentral : d + 1 = i.val := by omega
          have hforward : i.val + 1 ≠ d := by omega
          simp [columnWeight, columnDegree, heq, hcentral, hforward, hd] <;> field_simp [hp.ne'] <;> nlinarith [hs]
        · have hd : columnDepth d j = columnDepth d i + 1 := by
            unfold columnDepth
            omega
          simp [columnWeight, columnDegree, hu, hl, hlt, heq, hd, pow_succ] <;> field_simp [hp.ne'] <;> nlinarith [hs]
    · simp [columnDegree, hu, hl]

private theorem adjacency_mul_columns {V : Type*} [Fintype V]
    (d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (col : V → Column d)
    (hdegree : ∀ v j,
      ((G.neighborFinset v).filter (fun w => col w = j)).card = columnDegree d (col v) j) :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • G.adjMatrix ℂ * normalizedColumns col =
      normalizedColumns col * (centralDefect (d + 1) (by omega)).map Complex.ofReal := by
  classical
  ext v j
  simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.mul_apply, SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← G.neighborFinset_eq_filter]
  simp only [normalizedColumns, Matrix.map_apply]
  have hsum : (∑ w ∈ G.neighborFinset v,
      if col w = j then (columnWeight d j : ℂ) else 0) =
        (columnDegree d (col v) j : ℂ) * (columnWeight d j : ℂ) := by
    rw [← Finset.sum_filter, Finset.sum_const, hdegree, nsmul_eq_mul]
  rw [hsum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← mul_assoc]
  exact_mod_cast (column_action_scalar d (col v) j)


private theorem normalized_columns_isometry {V : Type*} [Fintype V] {d : ℕ}
    (col : V → Column d)
    (hsize : ∀ j, (Finset.univ.filter (fun v => col v = j)).card = 2 ^ columnDepth d j) :
    (normalizedColumns col)ᴴ * normalizedColumns col = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hsum :
        (∑ v, (normalizedColumns col)ᴴ i v * normalizedColumns col v i) =
          ∑ v, if col v = i then (columnWeight d i : ℂ) * (columnWeight d i : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : col v = i <;> simp [Matrix.conjTranspose_apply, normalizedColumns, hv]
    rw [hsum, ← Finset.sum_filter, Finset.sum_const, hsize, nsmul_eq_mul]
    have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hp : 0 < Real.sqrt (2 : ℝ) := by positivity
    have hpow : (Real.sqrt (2 : ℝ) ^ columnDepth d i) ^ 2 =
        (2 : ℝ) ^ columnDepth d i := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hs]
    have hweight : (2 : ℝ) ^ columnDepth d i *
        (columnWeight d i * columnWeight d i) = 1 := by
      rw [← hpow]
      simp only [columnWeight, pow_two]
      field_simp [pow_ne_zero _ hp.ne']
    exact_mod_cast hweight
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : col v = i
    · simp [Matrix.conjTranspose_apply, normalizedColumns, hv, hij]
    · simp [Matrix.conjTranspose_apply, normalizedColumns, hv]

private theorem endpoint_entry_of_intertwining {V : Type*} [Fintype V] {d : ℕ}
    (col : V → Column d)
    (hsize : ∀ j, (Finset.univ.filter (fun v => col v = j)).card = 2 ^ columnDepth d j)
    (A : Matrix V V ℂ) (B : Matrix (Column d) (Column d) ℂ)
    (h : A * normalizedColumns col = normalizedColumns col * B)
    (x y : V) (hx : col x = 0) (hy : col y = Fin.last _) :
    A y x = B (Fin.last _) 0 := by
  classical
  have hzero : columnDepth d (0 : Column d) = 0 := by simp [columnDepth]
  have hlast : columnDepth d (Fin.last (2 * (d + 1) - 1)) = 0 := by
    simp only [columnDepth, Fin.val_last]
    omega
  have hcard := hsize 0
  rw [hzero, pow_zero] at hcard
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have he : x = v := by
    have hm : x ∈ Finset.univ.filter (fun u => col u = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    rw [hv] at hm
    exact Finset.mem_singleton.mp hm
  have hentry := congrArg (fun M : Matrix V (Column d) ℂ => M y 0) h
  change (A * normalizedColumns col) y 0 = (normalizedColumns col * B) y 0 at hentry
  simp only [Matrix.mul_apply, normalizedColumns, columnWeight, hzero, hy, pow_zero,
    inv_one, Complex.ofReal_one, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul] at hentry
  rw [← Finset.sum_filter, hv, Finset.sum_singleton, ← he] at hentry
  simpa [Finset.sum_ite_eq, hlast] using hentry

/-- The normalized columns of a two-tree weld with the binary neighbor profile are orthonormal.
Their actual time evolution intertwines with the central square-root-two defect path. -/
theorem central_defect_column_evolution {V : Type*} [Fintype V] [DecidableEq V]
    (d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (col : V → Column d)
    (hsize : ∀ j, (Finset.univ.filter (fun v => col v = j)).card = 2 ^ columnDepth d j)
    (hdegree : ∀ v j,
      ((G.neighborFinset v).filter (fun w => col w = j)).card = columnDegree d (col v) j)
    (t : ℝ) :
    let Q := normalizedColumns col
    let H := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • G.adjMatrix ℂ
    let J := (centralDefect (d + 1) (by omega)).map Complex.ofReal
    let U := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
    let P := NormedSpace.exp ((-Complex.I * (t : ℂ)) • J)
    Qᴴ * Q = 1 ∧ U * Q = Q * P ∧
      ∀ x y, col x = 0 → col y = Fin.last _ → U y x = P (Fin.last _) 0 := by
  dsimp only
  refine ⟨normalized_columns_isometry col hsize, ?_⟩
  have hAction := adjacency_mul_columns d G col hdegree
  let phase := -Complex.I * (t : ℂ)
  have hTime :
      NormedSpace.exp (phase • ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • G.adjMatrix ℂ)) *
          normalizedColumns col =
        normalizedColumns col *
          NormedSpace.exp (phase • (centralDefect (d + 1) (by omega)).map Complex.ofReal) := by
    apply exp_intertwines
    rw [Matrix.smul_mul, Matrix.mul_smul, hAction]
  exact ⟨hTime, endpoint_entry_of_intertwining col hsize _ _ hTime⟩

end D5.S3.Quantum.Dynamics.WeldedColumnEvolution

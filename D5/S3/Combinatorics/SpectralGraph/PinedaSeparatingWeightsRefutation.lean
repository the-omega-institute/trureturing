/- GID: D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.claim
   digest: Weighted paths refute the three universal separating-weight analogues. -/

/- Judgement form.
   admission_basis: open-problem-resolution (#33474; Refuted).
   Direct frozen dependencies: AlbrightKemenyEdgeDerivativeRefutation.normLap,
   module statement ID sha256:c0b89b4b6882605547b15450771019bb0238a86bd1aa67e9cc670937ce0db860.
   Certified-instance utility: the two path supports and their weighted eigenvectors refute claim.
   normalized_refuted: proof_shape: content; escape_witness: normalized_witness constructs the
   square-root-degree-scaled vector at eigenvalue one for every positive weighting.
   adjacency_refuted: proof_shape: content; escape_witness: adjacency_witness constructs a
   nonzero null vector with interior zero coordinates for every positive weighting.
   directed_refuted: proof_shape: content; escape_witness: outPath_arborescence constructs the
   required spanning out-tree and directed_witness finds a vanishing-coordinate right eigenvector.
   result: proof_shape: content after expanding all three branch proofs; escape_witness: the
   three support-specific eigenvector constructions on its disjunction-elimination branches.
-/

import D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! A five-vertex path and a three-vertex out-path obstruct the separating-weight analogues
in Pineda Montoya, Gallego González, Porras Barrera and Rúa Muñoz, Question 7.5. -/

namespace D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation

open Matrix
open D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation (normLap)

private def Positive {E : Type} (w : E → ℝ) : Prop := ∀ e, 0 < w e

private noncomputable def weightedAdj {n : ℕ} (G : SimpleGraph (Fin n))
    (w : G.edgeSet → ℝ) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if h : G.Adj i j then w ⟨s(i, j), h⟩ else 0

private theorem weightedAdj_of_adj {n : ℕ} {G : SimpleGraph (Fin n)} (w : G.edgeSet → ℝ)
    {i j : Fin n} (h : G.Adj i j) :
    weightedAdj G w i j = w ⟨s(i, j), h⟩ := dite_eq_left h

private theorem weightedAdj_of_not_adj {n : ℕ} {G : SimpleGraph (Fin n)}
    (w : G.edgeSet → ℝ) {i j : Fin n} (h : ¬ G.Adj i j) :
    weightedAdj G w i j = 0 := dite_eq_right h

private def Arc {n : ℕ} (G : Digraph (Fin n)) :=
  {ij : Fin n × Fin n // G.Adj ij.1 ij.2}

@[instance_reducible] private def graphQuiver {n : ℕ} (G : Digraph (Fin n)) : Quiver (Fin n) where
  Hom i j := PLift (G.Adj i j)

private def HasSpanningOutArborescence {n : ℕ} (G : Digraph (Fin n)) : Prop :=
  ∃ T : Digraph (Fin n), T ≤ G ∧ Nonempty (@Quiver.Arborescence (Fin n) (graphQuiver T))

/-- Rows receive arcs. In particular the entry at (i,j) reads the weight on j → i. -/
private noncomputable def receivingAdj {n : ℕ} (G : Digraph (Fin n))
    (w : Arc G → ℝ) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if h : G.Adj j i then w ⟨(j, i), h⟩ else 0

private theorem receivingAdj_of_arc {n : ℕ} {G : Digraph (Fin n)} (w : Arc G → ℝ)
    {i j : Fin n} (h : G.Adj j i) :
    receivingAdj G w i j = w ⟨(j, i), h⟩ := dite_eq_left h

private theorem receivingAdj_of_not_arc {n : ℕ} {G : Digraph (Fin n)} (w : Arc G → ℝ)
    {i j : Fin n} (h : ¬ G.Adj j i) :
    receivingAdj G w i j = 0 := dite_eq_right h

private noncomputable def receivingLap {n : ℕ} (G : Digraph (Fin n))
    (w : Arc G → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => ∑ j, receivingAdj G w i j) - receivingAdj G w

private noncomputable def complexified {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  M.map Complex.ofReal

private def Separating {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (S3Mode : K → (Fin n → K) → Prop) : Prop :=
  M.charpoly.Separable ∧
  (∀ lam x, Module.End.HasEigenvector M.mulVecLin lam x → ∀ i, x i ≠ 0) ∧
  (∀ lam x, Module.End.HasEigenvector M.mulVecLin lam x →
    S3Mode lam x → Function.Injective x)

private def PolynomialCertificate {E : Type} (sep : (E → ℝ) → Prop) : Prop :=
  ∃ (degree : ℕ) (P : MvPolynomial E ℤ), P ≠ 0 ∧ P.IsHomogeneous degree ∧
    ∀ w, Positive w → (sep w ↔ MvPolynomial.eval₂ (Int.castRingHom ℝ) w P ≠ 0)

private def normalizedSep {n : ℕ} (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℝ) : Prop :=
  Separating (normLap (weightedAdj G w))
    (fun _ x => ∑ i, Real.sqrt (∑ j, weightedAdj G w i j) * x i = 0)

/-- The adjacency S3 modes exclude the top eigenvalue (the Perron eigenvalue at positive weights). -/
private def adjacencySep {n : ℕ} (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℝ) : Prop :=
  Separating (weightedAdj G w)
    (fun lam _ => ∃ μ, Module.End.HasEigenvalue (weightedAdj G w).mulVecLin μ ∧ lam < μ)

/-- S3 excludes the constant zero-eigenvalue mode and uses complex right eigenvectors. -/
private def directedSep {n : ℕ} (G : Digraph (Fin n)) (w : Arc G → ℝ) : Prop :=
  Separating (complexified (receivingLap G w)) (fun lam _ => lam ≠ 0)

def NormalizedClaim : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ G : SimpleGraph (Fin n), G.Connected →
    ∃ (degree : ℕ) (P : MvPolynomial (G.edgeSet) ℤ), P ≠ 0 ∧ P.IsHomogeneous degree ∧
      ∀ w, Positive w → (normalizedSep G w ↔ MvPolynomial.eval₂ (Int.castRingHom ℝ) w P ≠ 0)

def AdjacencyClaim : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ G : SimpleGraph (Fin n), G.Connected →
    ∃ (degree : ℕ) (P : MvPolynomial (G.edgeSet) ℤ), P ≠ 0 ∧ P.IsHomogeneous degree ∧
      ∀ w, Positive w → (adjacencySep G w ↔ MvPolynomial.eval₂ (Int.castRingHom ℝ) w P ≠ 0)

def DirectedClaim : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ G : Digraph (Fin n), (∀ i, ¬ G.Adj i i) →
    HasSpanningOutArborescence G →
    ∃ (degree : ℕ) (P : MvPolynomial (Arc G) ℤ), P ≠ 0 ∧ P.IsHomogeneous degree ∧
      ∀ w, Positive w → (directedSep G w ↔ MvPolynomial.eval₂ (Int.castRingHom ℝ) w P ≠ 0)

/-- Question 7.5 asks whether any of the three universal analogues holds. -/
def claim : Prop := NormalizedClaim ∨ AdjacencyClaim ∨ DirectedClaim

private theorem no_polynomial_certificate {E : Type} {sep : (E → ℝ) → Prop}
    (fails : ∀ w, Positive w → ¬ sep w) : ¬ PolynomialCertificate sep := by
  rintro ⟨_, P, hP, _, hcert⟩
  let cast := Int.castRingHom ℝ
  have hzero : MvPolynomial.map cast P = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ))
      (fun _ => Set.Ioi_infinite _)
    intro w hw
    have hwpos : Positive w := fun e => hw e (Set.mem_univ e)
    rw [MvPolynomial.eval_map, map_zero]
    by_contra h
    exact fails w hwpos ((hcert w hwpos).2 h)
  exact hP (MvPolynomial.map_injective _ Int.cast_injective (by simpa only [map_zero] using hzero))

private theorem eigenvector_of_mulVec {K : Type} [Field K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {lam : K} {x : Fin n → K}
    (hx : x ≠ 0) (heq : M *ᵥ x = lam • x) : Module.End.HasEigenvector M.mulVecLin lam x :=
  Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr heq, hx⟩

private theorem not_separating {K : Type} [Field K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {S3Mode : K → (Fin n → K) → Prop}
    {lam : K} {i : Fin n} {x : Fin n → K}
    (hEigen : Module.End.HasEigenvector M.mulVecLin lam x) (hi : x i = 0) : ¬ Separating M S3Mode :=
  fun h => h.2.1 lam x hEigen i hi

private def edge01 : (SimpleGraph.pathGraph 5).edgeSet :=
  ⟨s(0, 1), SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩

private def edge12 : (SimpleGraph.pathGraph 5).edgeSet :=
  ⟨s(1, 2), SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩

private def edge23 : (SimpleGraph.pathGraph 5).edgeSet :=
  ⟨s(2, 3), SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩

private def edge34 : (SimpleGraph.pathGraph 5).edgeSet :=
  ⟨s(3, 4), SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩

private theorem path_edges (e : (SimpleGraph.pathGraph 5).edgeSet) :
    e = edge01 ∨ e = edge12 ∨ e = edge23 ∨ e = edge34 := by
  obtain ⟨pair, h⟩ := e
  revert h
  induction pair using Sym2.inductionOn with
  | _ i j =>
    intro h
    have hadj : (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) :=
      SimpleGraph.pathGraph_adj.mp (show (SimpleGraph.pathGraph 5).Adj i j from h)
    fin_cases i <;> fin_cases j <;>
      first
      | exact False.elim ((by decide : ¬ _) hadj)
      | exact Or.inl (Subtype.ext rfl)
      | exact Or.inl (Subtype.ext Sym2.eq_swap)
      | exact Or.inr (Or.inl (Subtype.ext rfl))
      | exact Or.inr (Or.inl (Subtype.ext Sym2.eq_swap))
      | exact Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))
      | exact Or.inr (Or.inr (Or.inl (Subtype.ext Sym2.eq_swap)))
      | exact Or.inr (Or.inr (Or.inr (Subtype.ext rfl)))
      | exact Or.inr (Or.inr (Or.inr (Subtype.ext Sym2.eq_swap)))

private def pathEntries (a b c d : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, a, 0, 0, 0;
     a, 0, b, 0, 0;
     0, b, 0, c, 0;
     0, 0, c, 0, d;
     0, 0, 0, d, 0]

private theorem weighted_path_entries (w : (SimpleGraph.pathGraph 5).edgeSet → ℝ) :
    weightedAdj (SimpleGraph.pathGraph 5) w = pathEntries (w edge01) (w edge12) (w edge23) (w edge34) := by
  ext i j
  by_cases h : (SimpleGraph.pathGraph 5).Adj i j
  · rw [weightedAdj_of_adj w h]
    generalize he : (⟨s(i, j), h⟩ : (SimpleGraph.pathGraph 5).edgeSet) = e
    rcases path_edges e with hEdge | hEdge | hEdge | hEdge
    all_goals
      rw [hEdge] at he ⊢
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | have hp := congrArg Subtype.val he
          change (s(_, _) : Sym2 (Fin 5)) = _ at hp
          exact False.elim ((by decide : ¬ _) hp)
  · rw [weightedAdj_of_not_adj w h]
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact False.elim (h (by rw [SimpleGraph.pathGraph_adj]; decide))

private theorem path_degrees (a b c d : ℝ) :
    (fun i => ∑ j, pathEntries a b c d i j) = ![a, a + b, b + c, c + d, d] := by
  funext i
  fin_cases i <;> simp [pathEntries, Fin.sum_univ_succ]

private theorem normalized_path_entries (a b c d : ℝ) :
    normLap (pathEntries a b c d) = 1 -
      pathEntries (a / (Real.sqrt a * Real.sqrt (a + b)))
        (b / (Real.sqrt (a + b) * Real.sqrt (b + c)))
        (c / (Real.sqrt (b + c) * Real.sqrt (c + d)))
        (d / (Real.sqrt (c + d) * Real.sqrt d)) := by
  unfold normLap
  congr 1
  ext i j
  have hi := congrFun (path_degrees a b c d) i
  have hj := congrFun (path_degrees a b c d) j
  change (∑ k, pathEntries a b c d i k) = _ at hi
  change (∑ k, pathEntries a b c d j k) = _ at hj
  rw [Matrix.of_apply, hi, hj]
  fin_cases i <;> fin_cases j <;> simp [pathEntries, mul_comm]

private theorem normalized_weighted_path_entries (w : (SimpleGraph.pathGraph 5).edgeSet → ℝ) :
    let a := w edge01
    let b := w edge12
    let c := w edge23
    let d := w edge34
    normLap (weightedAdj (SimpleGraph.pathGraph 5) w) = 1 -
      pathEntries (a / (Real.sqrt a * Real.sqrt (a + b)))
        (b / (Real.sqrt (a + b) * Real.sqrt (b + c)))
        (c / (Real.sqrt (b + c) * Real.sqrt (c + d)))
        (d / (Real.sqrt (c + d) * Real.sqrt d)) := by
  dsimp only
  rw [weighted_path_entries, normalized_path_entries]

private def pathMode (a b c d : ℝ) : Fin 5 → ℝ := ![b * d, 0, -(a * d), 0, a * c]

private theorem pathMode_ne_zero {a b c d : ℝ} (hb : b ≠ 0) (hd : d ≠ 0) :
    pathMode a b c d ≠ 0 := by
  intro h
  exact mul_ne_zero hb hd (congrFun h 0)

private theorem path_mulVec_mode (a b c d : ℝ) :
    pathEntries a b c d *ᵥ pathMode a b c d = 0 := by
  funext i
  fin_cases i <;>
    simp [pathEntries, pathMode, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem adjacency_witness (w : (SimpleGraph.pathGraph 5).edgeSet → ℝ) (hw : Positive w) :
    ∃ x, Module.End.HasEigenvector (weightedAdj (SimpleGraph.pathGraph 5) w).mulVecLin 0 x ∧
      x 1 = 0 ∧ x 3 = 0 := by
  rw [weighted_path_entries]
  exact ⟨pathMode _ _ _ _, eigenvector_of_mulVec
    (pathMode_ne_zero (hw edge12).ne' (hw edge34).ne')
    (by rw [path_mulVec_mode, zero_smul]), rfl, rfl⟩

private theorem normalized_witness (w : (SimpleGraph.pathGraph 5).edgeSet → ℝ) (hw : Positive w) :
    ∃ y, Module.End.HasEigenvector (normLap (weightedAdj (SimpleGraph.pathGraph 5) w)).mulVecLin 1 y ∧ y 1 = 0 ∧ y 3 = 0 := by
  let a := w edge01
  let b := w edge12
  let c := w edge23
  let d := w edge34
  have ha : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 (hw edge01)).ne'
  have hab : Real.sqrt (a + b) ≠ 0 := (Real.sqrt_pos.2 (add_pos (hw edge01) (hw edge12))).ne'
  have hbc : Real.sqrt (b + c) ≠ 0 := (Real.sqrt_pos.2 (add_pos (hw edge12) (hw edge23))).ne'
  have hcd : Real.sqrt (c + d) ≠ 0 := (Real.sqrt_pos.2 (add_pos (hw edge23) (hw edge34))).ne'
  have hd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.2 (hw edge34)).ne'
  let y : Fin 5 → ℝ := ![Real.sqrt a * (b * d), 0, Real.sqrt (b + c) * (-(a * d)), 0,
    Real.sqrt d * (a * c)]
  have hy : y ≠ 0 := fun h =>
    mul_ne_zero ha (mul_ne_zero (hw edge12).ne' (hw edge34).ne') (congrFun h 0)
  rw [normalized_weighted_path_entries]
  refine ⟨y, eigenvector_of_mulVec hy ?_, rfl, rfl⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, one_smul]
  apply sub_eq_self.mpr
  change pathEntries (a / (Real.sqrt a * Real.sqrt (a + b)))
    (b / (Real.sqrt (a + b) * Real.sqrt (b + c)))
    (c / (Real.sqrt (b + c) * Real.sqrt (c + d)))
    (d / (Real.sqrt (c + d) * Real.sqrt d)) *ᵥ y = 0
  funext i
  fin_cases i <;> simp [pathEntries, y, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp [ha, hab, hbc, hcd, hd] <;> ring

private def outPath : Digraph (Fin 3) := ⟨fun i j => i.val + 1 = j.val⟩

private theorem outPath_adj (i j : Fin 3) :
    outPath.Adj i j ↔ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by
  change (i.val + 1 = j.val) ↔ _
  fin_cases i <;> fin_cases j <;> decide

private theorem outPath_loopless (i : Fin 3) : ¬ outPath.Adj i i := by
  change ¬ i.val + 1 = i.val
  omega

private def arc01 : Arc outPath := ⟨(0, 1), rfl⟩
private def arc12 : Arc outPath := ⟨(1, 2), rfl⟩

private theorem outPath_arcs (e : Arc outPath) : e = arc01 ∨ e = arc12 := by
  obtain ⟨⟨i, j⟩, h⟩ := e
  rcases (outPath_adj i j).mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

@[instance_reducible] private noncomputable def outPath_arborescence :
    @Quiver.Arborescence (Fin 3) (graphQuiver outPath) := by
  letI : Quiver (Fin 3) := graphQuiver outPath
  refine Quiver.arborescenceMk 0 Fin.val ?_ ?_ ?_
  · intro i j e
    have h : i.val + 1 = j.val := e.down
    omega
  · intro i j k e f
    have he : i.val + 1 = k.val := e.down
    have hf : j.val + 1 = k.val := f.down
    have hij : i = j := Fin.ext (by omega)
    subst j
    have hArrow : e = f := Subsingleton.elim (α := PLift (outPath.Adj i k)) e f
    exact ⟨rfl, heq_of_eq hArrow⟩
  · intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr ⟨0, ⟨PLift.up arc01.property⟩⟩
    · exact Or.inr ⟨1, ⟨PLift.up arc12.property⟩⟩

private theorem outPath_spanning : HasSpanningOutArborescence outPath :=
  ⟨outPath, le_rfl, ⟨outPath_arborescence⟩⟩

private theorem receiving_adj_entries (w : Arc outPath → ℝ) :
    receivingAdj outPath w = !![0, 0, 0; w arc01, 0, 0; 0, w arc12, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
    | rw [receivingAdj_of_not_arc w (by rw [outPath_adj]; decide)]
      rfl
    | rw [receivingAdj_of_arc w (by rw [outPath_adj]; decide)]
      generalize he : (⟨(_, _), _⟩ : Arc outPath) = e
      rcases outPath_arcs e with h | h
      all_goals
        first
        | rw [h]; rfl
        | exact False.elim ((by decide : ¬ _) (congrArg Subtype.val (he.trans h)))

private theorem receiving_lap_entries (w : Arc outPath → ℝ) :
    receivingLap outPath w = !![0, 0, 0; -w arc01, w arc01, 0; 0, -w arc12, w arc12] := by
  unfold receivingLap
  rw [receiving_adj_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Fin.sum_univ_succ]

private theorem directed_witness (w : Arc outPath → ℝ) :
    ∃ x, Module.End.HasEigenvector (complexified (receivingLap outPath w)).mulVecLin (w arc12 : ℂ) x ∧
      x 0 = 0 ∧ x 1 = 0 := by
  refine ⟨Pi.single 2 1, eigenvector_of_mulVec ?_ ?_, by simp, by simp⟩
  · intro h
    simpa using congrFun h (2 : Fin 3)
  · rw [Matrix.mulVec_single_one, complexified, receiving_lap_entries]
    funext i
    fin_cases i <;> simp [Matrix.col, Matrix.map_apply]

theorem normalized_refuted : ¬ NormalizedClaim := by
  intro h
  apply no_polynomial_certificate (sep := normalizedSep (SimpleGraph.pathGraph 5)) _
    (h 5 (by decide) (SimpleGraph.pathGraph 5) (SimpleGraph.connected_pathGraph_add_one 4))
  intro w hw
  obtain ⟨y, hy, hzero, _⟩ := normalized_witness w hw
  exact not_separating hy hzero

theorem adjacency_refuted : ¬ AdjacencyClaim := by
  intro h
  apply no_polynomial_certificate (sep := adjacencySep (SimpleGraph.pathGraph 5)) _
    (h 5 (by decide) (SimpleGraph.pathGraph 5) (SimpleGraph.connected_pathGraph_add_one 4))
  intro w hw
  obtain ⟨x, hx, hzero, _⟩ := adjacency_witness w hw
  exact not_separating hx hzero

theorem directed_refuted : ¬ DirectedClaim := by
  intro h
  apply no_polynomial_certificate (sep := directedSep outPath) _
    (h 3 (by decide) outPath outPath_loopless outPath_spanning)
  intro w _
  obtain ⟨x, hx, hzero, _⟩ := directed_witness w
  exact not_separating hx hzero

theorem result : ¬ claim := by
  rintro (h | h | h)
  · exact normalized_refuted h
  · exact adjacency_refuted h
  · exact directed_refuted h

end D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation

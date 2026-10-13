/- GID: D5/S3/Quantum/Contextuality/EightVertexQutritBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/EightVertexQutritBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both eight-vertex graphs have sharp qutrit value three and minimum dimension four. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators RealInnerProductSpace

namespace D5.S3.Quantum.Contextuality.EightVertexQutritBound

abbrev Vertex := Fin 8
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

private def fromEdges (edges : Finset (Vertex × Vertex)) : SimpleGraph Vertex :=
  SimpleGraph.fromRel (fun i j => (i, j) ∈ edges)

/-- The Wagner graph, with the labels of Table VI. -/
def W : SimpleGraph Vertex := fromEdges
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0),
   (0, 4), (1, 5), (2, 6), (3, 7)}

/-- The graph in row five of Table VI; the name specifies its table rank. -/
def G5 : SimpleGraph Vertex := fromEdges
  {(0, 3), (0, 5), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7),
   (3, 6), (3, 7), (4, 7), (5, 7)}

private instance : DecidableRel W.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)
private instance : DecidableRel G5.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

noncomputable section

/-- Only normalization and edge orthogonality are imposed. -/
def Realizes {d : ℕ} (G : SimpleGraph Vertex) (v : Vertex → E d) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ (∀ i j, G.Adj i j → ⟪v i, v j⟫ = 0)

def overlapSq {d : ℕ} (ψ x : E d) : ℝ := ⟪ψ, x⟫ ^ 2

def score {d : ℕ} (v : Vertex → E d) (ψ : E d) : ℝ := ∑ i, overlapSq ψ (v i)

def UpperBound (G : SimpleGraph Vertex) (d : ℕ) (c : ℝ) : Prop :=
  ∀ v : Vertex → E d, Realizes G v → ∀ ψ, score v ψ ≤ c * ‖ψ‖ ^ 2

def UnitScores (G : SimpleGraph Vertex) (d : ℕ) : Set ℝ :=
  {t | ∃ v : Vertex → E d, Realizes G v ∧ ∃ ψ, ‖ψ‖ = 1 ∧ score v ψ = t}

def eta (G : SimpleGraph Vertex) (d : ℕ) : ℝ := sSup (UnitScores G d)

def HasViolation (G : SimpleGraph Vertex) (d : ℕ) : Prop :=
  ∃ v : Vertex → E d, Realizes G v ∧
    ∃ ψ, ‖ψ‖ = 1 ∧ (G.indepNum : ℝ) < score v ψ

private def RayEq {d : ℕ} (x y : E d) : Prop := x = y ∨ x = -y

private theorem rayEq_symm {d : ℕ} {x y : E d} (h : RayEq x y) : RayEq y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [h, neg_neg]

private theorem overlapSq_eq_of_rayEq {d : ℕ} {x y : E d}
    (h : RayEq x y) (ψ : E d) : overlapSq ψ x = overlapSq ψ y := by
  unfold overlapSq
  rcases h with h | h <;> rw [h]
  rw [inner_neg_right, neg_sq]

private theorem orthogonal_iff_of_rayEq {d : ℕ} {x y z : E d}
    (h : RayEq x y) : ⟪x, z⟫ = 0 ↔ ⟪y, z⟫ = 0 := by
  rcases h with h | h <;> rw [h]
  rw [inner_neg_left, neg_eq_zero]

private theorem rayEq_of_unit_smul {d : ℕ} {x y : E d}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (h : ∃ r : ℝ, r • x = y) : RayEq x y := by
  obtain ⟨r, hr⟩ := h
  have hn := congrArg norm hr
  rw [norm_smul, hx, hy, mul_one, Real.norm_eq_abs] at hn
  have hs : r ^ 2 = 1 := by nlinarith [sq_abs r]
  rcases sq_eq_one_iff.mp hs with h1 | h1
  · left
    simpa only [h1, one_smul] using hr
  · right
    have hneg : -x = y := by simpa only [h1, neg_one_smul] using hr
    rw [← hneg, neg_neg]

private theorem rayEq_of_common_perp {a c b d : E 3}
    (hac : LinearIndependent ℝ ![a, c]) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hab : ⟪a, b⟫ = 0) (hcb : ⟪c, b⟫ = 0)
    (had : ⟪a, d⟫ = 0) (hcd : ⟪c, d⟫ = 0) : RayEq b d := by
  let K := Submodule.span ℝ (Set.range ![a, c])
  have hK : Module.finrank ℝ K = 2 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hac
  have hdim : Module.finrank ℝ Kᗮ = 1 := by
    have hsum := K.finrank_add_finrank_orthogonal
    rw [hK, finrank_euclideanSpace_fin] at hsum
    omega
  have mem (x : E 3) (hax : ⟪a, x⟫ = 0) (hcx : ⟪c, x⟫ = 0) : x ∈ Kᗮ := by
    have h : K ⟂ (ℝ ∙ x) := by
      apply Submodule.isOrtho_span.mpr
      rintro u ⟨i, rfl⟩ _ rfl
      fin_cases i <;> assumption
    exact h.ge (Submodule.mem_span_singleton_self x)
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one hdim
    (x := (⟨b, mem b hab hcb⟩ : Kᗮ))
    (fun h => hb0 (congrArg Subtype.val h)) (⟨d, mem d had hcd⟩ : Kᗮ)
  exact rayEq_of_unit_smul hb hd ⟨r, congrArg Subtype.val hr⟩

private theorem square {a b c d : E 3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hab : ⟪a, b⟫ = 0) (hbc : ⟪b, c⟫ = 0)
    (hcd : ⟪c, d⟫ = 0) (hda : ⟪d, a⟫ = 0) : RayEq a c ∨ RayEq b d := by
  by_cases h : RayEq a c
  · exact Or.inl h
  · right
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    have hac : LinearIndependent ℝ ![a, c] :=
      (LinearIndependent.pair_iff' ha0).mpr fun r hr =>
        h (rayEq_of_unit_smul ha hc ⟨r, hr⟩)
    exact rayEq_of_common_perp hac hb hd hab
      (by rwa [real_inner_comm]) (by rwa [real_inner_comm]) hcd

private theorem orthonormal_two {d : ℕ} {a b : E d}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ = 0) :
    Orthonormal ℝ ![a, b] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ha, hb, hab, real_inner_comm, inner_self_eq_norm_sq_to_K]

private theorem orthonormal_three {a b c : E 3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : ⟪a, b⟫ = 0) (hac : ⟪a, c⟫ = 0) (hbc : ⟪b, c⟫ = 0) :
    Orthonormal ℝ ![a, b, c] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ha, hb, hc, hab, hac, hbc, real_inner_comm, inner_self_eq_norm_sq_to_K]

private theorem force_third_ray {a b c x : E 3}
    (hON : Orthonormal ℝ ![a, b, c]) (hx : ‖x‖ = 1)
    (hxa : ⟪x, a⟫ = 0) (hxb : ⟪x, b⟫ = 0) : RayEq x c := by
  have ha : ‖a‖ = 1 := hON.norm_eq_one 0
  have hb : ‖b‖ = 1 := hON.norm_eq_one 1
  have hc : ‖c‖ = 1 := hON.norm_eq_one 2
  have hab : ⟪a, b⟫ = 0 := hON.inner_eq_zero (i := 0) (j := 1) (by decide)
  have hac : ⟪a, c⟫ = 0 := hON.inner_eq_zero (i := 0) (j := 2) (by decide)
  have hbc : ⟪b, c⟫ = 0 := hON.inner_eq_zero (i := 1) (j := 2) (by decide)
  exact rayEq_of_common_perp (orthonormal_two ha hb hab).linearIndependent hx hc
    (by rwa [real_inner_comm]) (by rwa [real_inner_comm]) hac hbc

private theorem parseval_three {a b c : E 3}
    (hON : Orthonormal ℝ ![a, b, c]) (ψ : E 3) :
    overlapSq ψ a + overlapSq ψ b + overlapSq ψ c = ‖ψ‖ ^ 2 := by
  let B := basisOfOrthonormalOfCardEqFinrank hON (by simp)
  have hB : (B : Fin 3 → E 3) = ![a, b, c] :=
    coe_basisOfOrthonormalOfCardEqFinrank hON _
  have hb : Orthonormal ℝ B := by rw [hB]; exact hON
  have hcoe : ((B.toOrthonormalBasis hb) : Fin 3 → E 3) = ![a, b, c] := by
    rw [Module.Basis.coe_toOrthonormalBasis]
    exact hB
  have h := (B.toOrthonormalBasis hb).sum_sq_inner_left ψ
  rw [hcoe] at h
  simpa only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, overlapSq.eq_1, add_assoc] using h

private theorem bessel_pair {d : ℕ} {x y : E d}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫ = 0) (ψ : E d) :
    overlapSq ψ x + overlapSq ψ y ≤ ‖ψ‖ ^ 2 := by
  have h := (orthonormal_two hx hy hxy).sum_inner_products_le ψ (s := Finset.univ)
  simpa only [Finset.sum_const_zero, Finset.sum_ite_irrel,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, Real.norm_eq_abs, sq_abs, real_inner_comm,
    overlapSq] using h

private def PairDecomposition (G : SimpleGraph Vertex) (v : Vertex → E 3) : Prop :=
  ∃ i j, G.Adj i j ∧ ∀ ψ,
    score v ψ = 2 * ‖ψ‖ ^ 2 + overlapSq ψ (v i) + overlapSq ψ (v j)

private theorem bound_of_pairDecomposition {G : SimpleGraph Vertex} {v : Vertex → E 3}
    (hv : Realizes G v) (hD : PairDecomposition G v) :
    ∀ ψ, score v ψ ≤ 3 * ‖ψ‖ ^ 2 := by
  obtain ⟨i, j, hij, hscore⟩ := hD
  intro ψ
  have h := bessel_pair (hv.1 i) (hv.1 j) (hv.2 i j hij) ψ
  rw [hscore]
  linarith

private theorem w_pairDecomposition {v : Vertex → E 3} (hv : Realizes W v) :
    PairDecomposition W v := by
  have edges : W.Adj 0 1 ∧ W.Adj 1 2 ∧ W.Adj 2 3 ∧ W.Adj 3 4 ∧
      W.Adj 4 5 ∧ W.Adj 5 6 ∧ W.Adj 6 7 ∧ W.Adj 7 0 ∧
      W.Adj 0 4 ∧ W.Adj 1 5 ∧ W.Adj 2 6 ∧ W.Adj 3 7 := by
    constructor
    · rw [W, fromEdges, SimpleGraph.fromRel_adj]
      decide
    · decide
  obtain ⟨e01, e12, e23, e34, e45, e56, e67, e70, e04, e15, e26, e37⟩ := edges
  have h01 := hv.2 0 1 e01
  have h12 := hv.2 1 2 e12
  have h23 := hv.2 2 3 e23
  have h34 := hv.2 3 4 e34
  have h45 := hv.2 4 5 e45
  have h56 := hv.2 5 6 e56
  have h67 := hv.2 6 7 e67
  have h70 := hv.2 7 0 e70
  have h04 := hv.2 0 4 e04
  have h15 := hv.2 1 5 e15
  have h26 := hv.2 2 6 e26
  have h37 := hv.2 3 7 e37
  have s1 := square (hv.1 0) (hv.1 1) (hv.1 5) (hv.1 4)
    h01 h15 (by rwa [real_inner_comm]) (by rwa [real_inner_comm])
  have s2 := square (hv.1 2) (hv.1 3) (hv.1 7) (hv.1 6)
    h23 h37 (by rwa [real_inner_comm]) (by rwa [real_inner_comm])
  rcases s1 with h05 | h14 <;> rcases s2 with h27 | h36
  · have h02 : ⟪v 0, v 2⟫ = 0 := by
      rw [real_inner_comm]
      exact (orthogonal_iff_of_rayEq (rayEq_symm h27)).mp h70
    have h06 : ⟪v 0, v 6⟫ = 0 := (orthogonal_iff_of_rayEq h05).mpr h56
    have hON := orthonormal_three (hv.1 0) (hv.1 2) (hv.1 6) h02 h06 h26
    have h16 := force_third_ray hON (hv.1 1) (by rwa [real_inner_comm]) h12
    refine ⟨3, 4, e34, fun ψ => ?_⟩
    have hp := parseval_three hON ψ
    have q05 := overlapSq_eq_of_rayEq h05 ψ
    have q27 := overlapSq_eq_of_rayEq h27 ψ
    have q16 := overlapSq_eq_of_rayEq h16 ψ
    simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]
    linarith
  · have h03 : ⟪v 0, v 3⟫ = 0 := by
      rw [real_inner_comm]
      apply (orthogonal_iff_of_rayEq h36).mpr
      rw [real_inner_comm]
      exact (orthogonal_iff_of_rayEq h05).mpr h56
    have hON := orthonormal_three (hv.1 0) (hv.1 3) (hv.1 7) h03
      (by rwa [real_inner_comm]) h37
    have h47 := force_third_ray hON (hv.1 4)
      (by rwa [real_inner_comm]) (by rwa [real_inner_comm])
    refine ⟨1, 2, e12, fun ψ => ?_⟩
    have hp := parseval_three hON ψ
    have q05 := overlapSq_eq_of_rayEq h05 ψ
    have q36 := overlapSq_eq_of_rayEq h36 ψ
    have q47 := overlapSq_eq_of_rayEq h47 ψ
    simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]
    linarith
  · have h17 : ⟪v 1, v 7⟫ = 0 := by
      rw [real_inner_comm]
      apply (orthogonal_iff_of_rayEq h27).mp
      rwa [real_inner_comm]
    have h13 : ⟪v 1, v 3⟫ = 0 :=
      (orthogonal_iff_of_rayEq h14).mpr (by rwa [real_inner_comm])
    have hON := orthonormal_three (hv.1 1) (hv.1 7) (hv.1 3) h17 h13
      (by rwa [real_inner_comm])
    have h03 := force_third_ray hON (hv.1 0) h01 (by rwa [real_inner_comm])
    refine ⟨5, 6, e56, fun ψ => ?_⟩
    have hp := parseval_three hON ψ
    have q14 := overlapSq_eq_of_rayEq h14 ψ
    have q27 := overlapSq_eq_of_rayEq h27 ψ
    have q03 := overlapSq_eq_of_rayEq h03 ψ
    simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]
    linarith
  · have h13 : ⟪v 1, v 3⟫ = 0 :=
      (orthogonal_iff_of_rayEq h14).mpr (by rwa [real_inner_comm])
    have hON := orthonormal_three (hv.1 1) (hv.1 3) (hv.1 2) h13 h12
      (by rwa [real_inner_comm])
    have h53 : ⟪v 5, v 3⟫ = 0 := by
      rw [real_inner_comm]
      exact (orthogonal_iff_of_rayEq h36).mpr (by rwa [real_inner_comm])
    have h52 := force_third_ray hON (hv.1 5) (by rwa [real_inner_comm]) h53
    refine ⟨7, 0, e70, fun ψ => ?_⟩
    have hp := parseval_three hON ψ
    have q14 := overlapSq_eq_of_rayEq h14 ψ
    have q36 := overlapSq_eq_of_rayEq h36 ψ
    have q52 := overlapSq_eq_of_rayEq h52 ψ
    simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]
    linarith

private theorem w_upper_three : UpperBound W 3 3 := by
  intro v hv
  exact bound_of_pairDecomposition hv (w_pairDecomposition hv)

private theorem g5_pairDecomposition {v : Vertex → E 3} (hv : Realizes G5 v) :
    PairDecomposition G5 v := by
  have edges : G5.Adj 0 3 ∧ G5.Adj 0 5 ∧ G5.Adj 1 4 ∧ G5.Adj 1 5 ∧
      G5.Adj 1 6 ∧ G5.Adj 2 5 ∧ G5.Adj 2 6 ∧ G5.Adj 2 7 ∧
      G5.Adj 3 6 ∧ G5.Adj 3 7 ∧ G5.Adj 4 7 ∧ G5.Adj 5 7 := by
    constructor
    · rw [G5, fromEdges, SimpleGraph.fromRel_adj]
      decide
    · decide
  obtain ⟨e03, e05, e14, e15, e16, e25, e26, e27, e36, e37, e47, e57⟩ := edges
  have h03 := hv.2 0 3 e03
  have h05 := hv.2 0 5 e05
  have h14 := hv.2 1 4 e14
  have h15 := hv.2 1 5 e15
  have h16 := hv.2 1 6 e16
  have h25 := hv.2 2 5 e25
  have h26 := hv.2 2 6 e26
  have h27 := hv.2 2 7 e27
  have h36 := hv.2 3 6 e36
  have h37 := hv.2 3 7 e37
  have h47 := hv.2 4 7 e47
  have h57 := hv.2 5 7 e57
  have hON := orthonormal_three (hv.1 2) (hv.1 5) (hv.1 7) h25 h27 h57
  have s1 := square (hv.1 1) (hv.1 5) (hv.1 2) (hv.1 6)
    h15 (by rwa [real_inner_comm]) h26 (by rwa [real_inner_comm])
  rcases s1 with h12 | h56
  · have h42 : ⟪v 4, v 2⟫ = 0 := by
      rw [real_inner_comm]
      exact (orthogonal_iff_of_rayEq h12).mp h14
    have hON' := orthonormal_three (hv.1 2) (hv.1 7) (hv.1 5) h27 h25
      (by rwa [real_inner_comm])
    have h45 := force_third_ray hON' (hv.1 4) h42 h47
    have s2 := square (hv.1 0) (hv.1 3) (hv.1 7) (hv.1 5)
      h03 h37 (by rwa [real_inner_comm]) (by rwa [real_inner_comm])
    rcases s2 with h07 | h35
    · refine ⟨3, 6, e36, fun ψ => ?_⟩
      have hp := parseval_three hON ψ
      have q12 := overlapSq_eq_of_rayEq h12 ψ
      have q45 := overlapSq_eq_of_rayEq h45 ψ
      have q07 := overlapSq_eq_of_rayEq h07 ψ
      simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]
      linarith
    · have h62 : ⟪v 6, v 2⟫ = 0 := by
        rw [real_inner_comm]
        exact (orthogonal_iff_of_rayEq h12).mp h16
      have h65 : ⟪v 6, v 5⟫ = 0 := by
        rw [real_inner_comm]
        exact (orthogonal_iff_of_rayEq h35).mp h36
      have h67 := force_third_ray hON (hv.1 6) h62 h65
      refine ⟨0, 5, e05, fun ψ => ?_⟩
      have hp := parseval_three hON ψ
      have q12 := overlapSq_eq_of_rayEq h12 ψ
      have q45 := overlapSq_eq_of_rayEq h45 ψ
      have q35 := overlapSq_eq_of_rayEq h35 ψ
      have q67 := overlapSq_eq_of_rayEq h67 ψ
      simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]
      linarith
  · have h35 : ⟪v 3, v 5⟫ = 0 := by
      rw [real_inner_comm]
      exact (orthogonal_iff_of_rayEq h56).mpr (by rwa [real_inner_comm])
    have hON' := orthonormal_three (hv.1 5) (hv.1 7) (hv.1 2) h57
      (by rwa [real_inner_comm]) (by rwa [real_inner_comm])
    have h32 := force_third_ray hON' (hv.1 3) h35 h37
    have h02 : ⟪v 0, v 2⟫ = 0 := by
      rw [real_inner_comm]
      exact (orthogonal_iff_of_rayEq h32).mp (by rwa [real_inner_comm])
    have h07 := force_third_ray hON (hv.1 0) h02 h05
    refine ⟨1, 4, e14, fun ψ => ?_⟩
    have hp := parseval_three hON ψ
    have q56 := overlapSq_eq_of_rayEq h56 ψ
    have q32 := overlapSq_eq_of_rayEq h32 ψ
    have q07 := overlapSq_eq_of_rayEq h07 ψ
    simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]
    linarith

private theorem g5_upper_three : UpperBound G5 3 3 := by
  intro v hv
  exact bound_of_pairDecomposition hv (g5_pairDecomposition hv)

private theorem attained_of_coloring {G : SimpleGraph Vertex} (color : Vertex → Fin 3)
    (hproper : ∀ i j, G.Adj i j → color i ≠ color j)
    (hcount : (Finset.univ.filter (fun i => color i = 0)).card = 3) :
    3 ∈ UnitScores G 3 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  refine ⟨fun i => b (color i), ⟨fun i => b.orthonormal.norm_eq_one _, ?_⟩,
    b 0, b.orthonormal.norm_eq_one 0, ?_⟩
  · intro i j hij
    exact b.orthonormal.inner_eq_zero (hproper i j hij)
  · unfold score overlapSq
    have hi (i : Vertex) : ⟪b 0, b (color i)⟫ ^ 2 = if color i = 0 then 1 else 0 := by
      by_cases h : color i = 0
      · rw [h, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one]; norm_num
      · rw [if_neg h, b.orthonormal.inner_eq_zero (Ne.symm h)]; norm_num
    simp_rw [hi]
    rw [Finset.sum_boole, hcount]
    norm_num

private theorem normalize_orthogonal {d : ℕ} {u v : E d} (huv : ⟪u, v⟫ = 0) :
    ⟪NormedSpace.normalize u, NormedSpace.normalize v⟫ = 0 := by
  unfold NormedSpace.normalize
  rw [real_inner_smul_left, real_inner_smul_right, huv, mul_zero, mul_zero]

private theorem overlapSq_normalize {d : ℕ} {p u : E d}
    (hp : 0 < ⟪p, p⟫) (hu : 0 < ⟪u, u⟫) :
    overlapSq (NormedSpace.normalize p) (NormedSpace.normalize u) =
      ⟪p, u⟫ ^ 2 / (⟪p, p⟫ * ⟪u, u⟫) := by
  unfold overlapSq NormedSpace.normalize
  rw [norm_eq_sqrt_real_inner p, norm_eq_sqrt_real_inner u]
  rw [real_inner_smul_left, real_inner_smul_right]
  simp only [mul_pow, inv_pow, Real.sq_sqrt hp.le, Real.sq_sqrt hu.le]
  rw [div_eq_mul_inv, mul_inv]
  ring

private theorem normalized_witness {G : SimpleGraph Vertex} {d : ℕ} {t : ℝ}
    (u : Vertex → E d) (p : E d)
    (hu : ∀ i, 0 < ⟪u i, u i⟫) (hp : 0 < ⟪p, p⟫)
    (hEdges : ∀ i j, G.Adj i j → ⟪u i, u j⟫ = 0)
    (hValue : (∑ i, ⟪p, u i⟫ ^ 2 / (⟪p, p⟫ * ⟪u i, u i⟫)) = t) :
    t ∈ UnitScores G d := by
  refine ⟨fun i => NormedSpace.normalize (u i),
    ⟨fun i => NormedSpace.norm_normalize (real_inner_self_pos.mp (hu i)), ?_⟩,
    NormedSpace.normalize p, NormedSpace.norm_normalize (real_inner_self_pos.mp hp), ?_⟩
  · intro i j hij
    exact normalize_orthogonal (hEdges i j hij)
  · rw [score.eq_1]
    simp_rw [overlapSq_normalize hp (hu _)]
    exact hValue

private def embedToThree {d : ℕ} (hd : d ≤ 3) : E d →ₗᵢ[ℝ] E 3 := by
  let bd := EuclideanSpace.basisFun (Fin d) ℝ
  let b3 := EuclideanSpace.basisFun (Fin 3) ℝ
  let f : Fin d → Fin 3 := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hd⟩
  have hf : Function.Injective f := fun i j h => Fin.ext (congrArg (fun k : Fin 3 => k.val) h)
  let L := bd.toBasis.constr ℝ (fun i => b3 (f i))
  refine L.isometryOfOrthonormal (v := bd.toBasis) bd.orthonormal ?_
  have heq : L ∘ bd.toBasis = fun i => b3 (f i) := by
    funext i
    exact bd.toBasis.constr_basis ℝ _ i
  rw [heq]
  exact b3.orthonormal.comp f hf

private theorem upperBound_pullback {G : SimpleGraph Vertex} {d e : ℕ} {c : ℝ}
    (J : E d →ₗᵢ[ℝ] E e) (h : UpperBound G e c) : UpperBound G d c := by
  intro v hv ψ
  have hj : Realizes G (fun i => J (v i)) := by
    refine ⟨fun i => (J.norm_map _).trans (hv.1 i), ?_⟩
    intro i j hij
    rw [J.inner_map_map]
    exact hv.2 i j hij
  have hs := h _ hj (J ψ)
  simpa only [score, overlapSq, J.inner_map_map, J.norm_map] using hs

private theorem unitScores_bddAbove (G : SimpleGraph Vertex) (d : ℕ) :
    BddAbove (UnitScores G d) := by
  refine ⟨8, ?_⟩
  rintro t ⟨v, hv, ψ, hψ, rfl⟩
  have hi (i : Vertex) : overlapSq ψ (v i) ≤ 1 := by
    have h := abs_real_inner_le_norm ψ (v i)
    rw [hψ, hv.1 i, mul_one] at h
    unfold overlapSq
    nlinarith [sq_abs ⟪ψ, v i⟫, abs_nonneg ⟪ψ, v i⟫]
  calc
    score v ψ ≤ ∑ _i : Vertex, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hi i)
    _ = 8 := by norm_num

private theorem eta_eq_of_upper_attained {G : SimpleGraph Vertex} {d : ℕ} {c : ℝ}
    (hU : UpperBound G d c) (hA : c ∈ UnitScores G d) : eta G d = c := by
  apply IsGreatest.csSup_eq
  refine ⟨hA, ?_⟩
  rintro t ⟨v, hv, ψ, hψ, rfl⟩
  simpa only [hψ, one_pow, mul_one] using hU v hv ψ

private theorem lt_eta_of_mem {G : SimpleGraph Vertex} {d : ℕ} {t c : ℝ}
    (ht : t ∈ UnitScores G d) (hct : c < t) : c < eta G d :=
  hct.trans_le (le_csSup (unitScores_bddAbove G d) ht)

private theorem minimum_dimension_four {G : SimpleGraph Vertex}
    (hα : G.indepNum = 3) (hLow : ∀ d : ℕ, d ≤ 3 → UpperBound G d 3)
    (hFour : HasViolation G 4) : IsLeast {d : ℕ | HasViolation G d} 4 := by
  refine ⟨hFour, ?_⟩
  rintro d ⟨v, hv, ψ, hψ, hgt⟩
  by_contra h
  have hd : d ≤ 3 := by omega
  have hs := hLow d hd v hv ψ
  rw [hψ, one_pow, mul_one] at hs
  rw [hα] at hgt
  norm_num at hgt
  exact (not_lt_of_ge hs) hgt

/-- Sharp qutrit value, independence number, and least dimension of a violation. -/
def Settled (G : SimpleGraph Vertex) : Prop :=
  G.indepNum = 3 ∧
  (∀ d : ℕ, d ≤ 3 → UpperBound G d 3) ∧
  IsGreatest (UnitScores G 3) 3 ∧ eta G 3 = 3 ∧ 3 < eta G 4 ∧
  IsLeast {d : ℕ | HasViolation G d} 4

def claim : Prop := Settled W ∧ Settled G5

private theorem settled_of_certificates {G : SimpleGraph Vertex}
    (hα : G.indepNum = 3) (h3 : UpperBound G 3 3) (hAttained : 3 ∈ UnitScores G 3)
    (hFour : ∃ t ∈ UnitScores G 4, 3 < t) : Settled G := by
  have hLow (d : ℕ) (hd : d ≤ 3) : UpperBound G d 3 :=
    upperBound_pullback (embedToThree hd) h3
  have hGreatest : IsGreatest (UnitScores G 3) 3 := by
    refine ⟨hAttained, ?_⟩
    rintro t ⟨v, hv, ψ, hψ, rfl⟩
    simpa only [hψ, one_pow, mul_one] using h3 v hv ψ
  obtain ⟨t, ht, hgt⟩ := hFour
  have hViolation : HasViolation G 4 := by
    obtain ⟨v, hv, ψ, hψ, hs⟩ := ht
    refine ⟨v, hv, ψ, hψ, ?_⟩
    rw [hs, hα]
    exact_mod_cast hgt
  exact ⟨hα, hLow, hGreatest, eta_eq_of_upper_attained h3 hAttained,
    lt_eta_of_mem ht hgt, minimum_dimension_four hα hLow hViolation⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Finite independent-set enumeration and exact coordinate arithmetic share this budget.
/-- Both eight-vertex graphs have sharp qutrit value three and least violation dimension four. -/
theorem result : claim := by
  have hαW : W.indepNum = 3 := by
    have hi : W.IsIndepSet ({0, 3, 5} : Finset Vertex) := by decide
    have hc : ∀ s : Finset Vertex, W.IsIndepSet s → s.card ≤ 3 := by decide
    have hm : W.IsMaximumIndepSet ({0, 3, 5} : Finset Vertex) :=
      ⟨hi, fun s hs => by simpa using hc s hs⟩
    simpa using (W.maximumIndepSet_card_eq_indepNum _ hm).symm
  have hαG5 : G5.indepNum = 3 := by
    have hi : G5.IsIndepSet ({1, 2, 3} : Finset Vertex) := by decide
    have hc : ∀ s : Finset Vertex, G5.IsIndepSet s → s.card ≤ 3 := by decide
    have hm : G5.IsMaximumIndepSet ({1, 2, 3} : Finset Vertex) :=
      ⟨hi, fun s hs => by simpa using hc s hs⟩
    simpa using (G5.maximumIndepSet_card_eq_indepNum _ hm).symm
  have hAW : 3 ∈ UnitScores W 3 := by
    let color : Vertex → Fin 3 := ![0, 1, 2, 0, 1, 0, 1, 2]
    have hp : ∀ i j, W.Adj i j → color i ≠ color j := by decide
    have hc : (Finset.univ.filter (fun i => color i = 0)).card = 3 := by decide
    exact attained_of_coloring color hp hc
  have hAG5 : 3 ∈ UnitScores G5 3 := by
    let color : Vertex → Fin 3 := ![2, 0, 0, 0, 1, 1, 1, 2]
    have hp : ∀ i j, G5.Adj i j → color i ≠ color j := by decide
    have hc : (Finset.univ.filter (fun i => color i = 0)).card = 3 := by decide
    exact attained_of_coloring color hp hc
  have h4W : ∃ t ∈ UnitScores W 4, 3 < t := by
    let u : Vertex → E 4 := fun i => WithLp.toLp 2
      (![![20, 15, 0, 0], ![9, -12, -12, 16], ![12, 16, 9, 12], ![20, -15, 0, 0],
         ![0, 0, -15, 20], ![16, 12, 12, 9], ![-12, 9, 16, -12], ![0, 0, 15, 20]] i)
    let p : E 4 := WithLp.toLp 2 ![4, 0, 0, 3]
    have hn : ∀ i, ⟪u i, u i⟫ = 625 := by
      intro i; fin_cases i <;>
        norm_num [u, EuclideanSpace.inner_toLp_toLp, dotProduct,
          EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    have hp : ⟪p, p⟫ = 25 := by
      norm_num [p, EuclideanSpace.inner_toLp_toLp, dotProduct,
        EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    have hpu : ∀ i, ⟪p, u i⟫ = (![80, 84, 84, 80, 60, 91, -84, 60] : Vertex → ℝ) i := by
      intro i; fin_cases i <;>
        norm_num [u, p, EuclideanSpace.inner_toLp_toLp, dotProduct,
          EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    have he : ∀ i j, W.Adj i j → ⟪u i, u j⟫ = 0 := by
      intro i j hij; fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd hij (by decide)
        | norm_num [u, EuclideanSpace.inner_toLp_toLp, dotProduct,
            Fin.sum_univ_succ, EuclideanSpace.norm_sq_eq]
    refine ⟨49449 / 15625, ?_, by norm_num⟩
    apply normalized_witness u p (fun i => by rw [hn]; norm_num) (by rw [hp]; norm_num) he
    simp_rw [hpu, hn, hp]
    norm_num [Fin.sum_univ_succ]
  have h4G5 : ∃ t ∈ UnitScores G5 4, 3 < t := by
    let u : Vertex → E 4 := fun i => WithLp.toLp 2
      (![![19, 5, -13, 0], ![-2, 5, 29, -15], ![0, 0, 0, -1], ![8, -20, 4, -15],
         ![2, 31, 1, 12], ![2, -5, 1, 0], ![-5, -2, 0, 0], ![-1, 0, 2, 0]] i)
    let p : E 4 := WithLp.toLp 2 ![1, 2, -2, 1]
    have hn : ∀ i, ⟪u i, u i⟫ =
        (![555, 1095, 1, 705, 1110, 30, 29, 5] : Vertex → ℝ) i := by
      intro i; fin_cases i <;>
        norm_num [u, EuclideanSpace.inner_toLp_toLp, dotProduct,
          EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    have hp : ⟪p, p⟫ = 10 := by
      norm_num [p, EuclideanSpace.inner_toLp_toLp, dotProduct,
        EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    have hpu : ∀ i, ⟪p, u i⟫ = (![55, -65, -1, -55, 74, -10, -9, -5] : Vertex → ℝ) i := by
      intro i; fin_cases i <;>
        norm_num [u, p, EuclideanSpace.inner_toLp_toLp, dotProduct,
          EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    have he : ∀ i j, G5.Adj i j → ⟪u i, u j⟫ = 0 := by
      intro i j hij; fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd hij (by decide)
        | norm_num [u, EuclideanSpace.inner_toLp_toLp, dotProduct,
            Fin.sum_univ_succ, EuclideanSpace.norm_sq_eq]
    have hu : ∀ i, 0 < ⟪u i, u i⟫ := by
      intro i; rw [hn]; fin_cases i <;> norm_num
    refine ⟨846537181 / 276109725, ?_, by norm_num⟩
    apply normalized_witness u p hu (by rw [hp]; norm_num) he
    simp_rw [hpu, hn, hp]
    norm_num [Fin.sum_univ_succ]
  exact ⟨settled_of_certificates hαW w_upper_three hAW h4W,
    settled_of_certificates hαG5 g5_upper_three hAG5 h4G5⟩

end

end D5.S3.Quantum.Contextuality.EightVertexQutritBound

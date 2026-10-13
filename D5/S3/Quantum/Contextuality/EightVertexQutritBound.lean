/- GID: D5/S3/Quantum/Contextuality/EightVertexQutritBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/EightVertexQutritBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Wagner and rank-five eight-vertex graphs have qutrit score at most three. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators RealInnerProductSpace

namespace D5.S3.Quantum.Contextuality.EightVertexQutritBound

abbrev Vertex := Fin 8
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

private def fromEdges (edges : Finset (Vertex × Vertex)) : SimpleGraph Vertex where
  Adj i j := i ≠ j ∧ ((i, j) ∈ edges ∨ (j, i) ∈ edges)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance (edges : Finset (Vertex × Vertex)) : DecidableRel (fromEdges edges).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∈ edges ∨ _ ∈ edges)))

/-- The Wagner graph, with the labels of Table VI. -/
def W : SimpleGraph Vertex := fromEdges
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0),
   (0, 4), (1, 5), (2, 6), (3, 7)}

/-- The graph in row five of Table VI; the name specifies its table rank. -/
def G5 : SimpleGraph Vertex := fromEdges
  {(0, 3), (0, 5), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7),
   (3, 6), (3, 7), (4, 7), (5, 7)}

instance : DecidableRel W.Adj := inferInstanceAs (DecidableRel (fromEdges _).Adj)
instance : DecidableRel G5.Adj := inferInstanceAs (DecidableRel (fromEdges _).Adj)

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
    apply (K.mem_orthogonal x).mpr
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      fin_cases i <;> assumption
    | zero => exact inner_zero_left _
    | add u w _ _ hu hw => rw [inner_add_left, hu, hw, zero_add]
    | smul r u _ hu => rw [real_inner_smul_left, hu, mul_zero]
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
  let b := basisOfOrthonormalOfCardEqFinrank hON (by simp)
  have hb : Orthonormal ℝ b := by
    simpa only [b, coe_basisOfOrthonormalOfCardEqFinrank] using hON
  have h := (b.toOrthonormalBasis hb).sum_sq_inner_left ψ
  simpa only [Module.Basis.coe_toOrthonormalBasis, b,
    coe_basisOfOrthonormalOfCardEqFinrank, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    overlapSq, add_assoc] using h

private theorem bessel_pair {d : ℕ} {x y : E d}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫ = 0) (ψ : E d) :
    overlapSq ψ x + overlapSq ψ y ≤ ‖ψ‖ ^ 2 := by
  have h := (orthonormal_two hx hy hxy).sum_inner_products_le ψ (s := Finset.univ)
  simpa only [Finset.mem_univ, Finset.sum_const_zero, Finset.sum_ite_irrel,
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
      W.Adj 0 4 ∧ W.Adj 1 5 ∧ W.Adj 2 6 ∧ W.Adj 3 7 := by decide
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
      G5.Adj 3 6 ∧ G5.Adj 3 7 ∧ G5.Adj 4 7 ∧ G5.Adj 5 7 := by decide
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

end

end D5.S3.Quantum.Contextuality.EightVertexQutritBound

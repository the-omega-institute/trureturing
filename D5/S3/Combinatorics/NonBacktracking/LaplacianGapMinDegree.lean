/- GID: D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Non-backtracking gap is bounded by the reciprocal minimum-degree excess. -/

/- Judgement form.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15386.
   proof_shape: result: content (same-delivery symmetric-pencil crossing is inlined); Arc: content-free source definition; nbTransition: content-free source definition; nbGap: content-free source definition; claim: bind-only source statement.
   escape_witness: none
   admission_basis: open-problem-resolution (#15268; Proved)
   Owner declaration identities (producing Lean report; public API re-pin): D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue (statement_id sha256:db7411fc038dde55051b605a75e04c276d83ca7452caed40cdd2030bacb1f2ad); D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner (statement_id sha256:f65fbfeb07a19a6b00f0d2cbf90c03cabdaaea7530d966173716ea7d506cfae3); D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le (statement_id sha256:914d96cba49b1649c8d13bfe19d14cc7ba7385bd42ae1eee1e570b770e1600f6).
   Private theorem count: each private theorem is consumed on result's live proof path; private proposition-valued definitions are absent.
-/

import D5.S3.Combinatorics.NonBacktracking.HermitianPencilCrossing
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.Matrix.Permutation

noncomputable section
open scoped BigOperators
namespace D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

@[reducible] def Arc {n : ℕ} (G : SimpleGraph (Fin n)) :=
  {p : Fin n × Fin n // G.Adj p.1 p.2}

private instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Fintype (Arc G) :=
  inferInstanceAs (Fintype {p : Fin n × Fin n // G.Adj p.1 p.2})

private instance {n : ℕ} (G : SimpleGraph (Fin n)) : DecidableEq (Arc G) :=
  inferInstanceAs (DecidableEq {p : Fin n × Fin n // G.Adj p.1 p.2})

def nbTransition {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Arc G) (Arc G) ℝ := fun a b =>
  if a.1.2 = b.1.1 ∧ b.1.2 ≠ a.1.1 then
    1 / ((G.degree a.1.2 : ℝ) - 1) else 0

def nbGap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  sInf {r : ℝ | ∃ μ ∈ spectrum ℂ ((nbTransition G).map (algebraMap ℝ ℂ)), r = ‖μ‖}

def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < n → 2 ≤ G.minDegree →
    ¬ Nonempty (G ≃g SimpleGraph.cycleGraph n) →
    nbGap G ≤ 1 / ((G.minDegree : ℝ) - 1)

end D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

open scoped BigOperators
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private def arcDartEquiv : Arc G ≃ G.Dart where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.toProd, a.adj⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def reverse : Equiv.Perm (Arc G) where
  toFun a := ⟨a.1.swap, a.2.symm⟩
  invFun a := ⟨a.1.swap, a.2.symm⟩
  left_inv a := by apply Subtype.ext; exact Prod.swap_swap _
  right_inv a := by apply Subtype.ext; exact Prod.swap_swap _

@[simp] private theorem reverse_reverse (a : Arc G) : reverse G (reverse G a) = a :=
  (reverse G).left_inv a




private def R (K : Type*) [Zero K] [One K] : Matrix (Arc G) (Arc G) K :=
  (reverse G).permMatrix K

variable {K : Type*}

private theorem R_mul [Semiring K] (A : Matrix (Arc G) (Arc G) K) :
    R G K * A = fun a b => A (reverse G a) b := by
  exact PEquiv.toMatrix_toPEquiv_mul (reverse G) A


private theorem R_sq [Semiring K] : R G K * R G K = 1 := by
  have he : reverse G * reverse G = 1 := by apply Equiv.ext; intro a; exact reverse_reverse G a
  rw [R, ← Matrix.permMatrix_mul, he, Matrix.permMatrix_one]


private theorem R_mulVec [CommRing K] (x : Arc G → K) :
    R G K *ᵥ x = x ∘ reverse G :=
  Matrix.permMatrix_mulVec _

private def tailDegree (K : Type*) [NatCast K] [Sub K] [One K] (a : Arc G) : K :=
  (G.degree a.1.1 : K) - 1

private def C (K : Type*) [Zero K] [One K] : Matrix (Arc G) (Arc G) K :=
  fun a b => if a.1.1 = b.1.1 then 1 else 0

private def T (K : Type*) [Ring K] : Matrix (Arc G) (Arc G) K :=
  C G K - Matrix.diagonal (tailDegree G K)

private def S (K : Type*) [Field K] : Matrix (Arc G) (Arc G) K :=
  Matrix.diagonal (fun a => (tailDegree G K a)⁻¹) * (C G K - 1)



private theorem arc_card : Fintype.card (Arc G) = 2 * G.edgeFinset.card := by
  rw [Fintype.card_congr (arcDartEquiv G)]
  exact G.dart_card_eq_twice_card_edges

private def tailFiberEquiv (v : Fin n) : {a : Arc G // a.1.1 = v} ≃ G.neighborSet v where
  toFun a := ⟨a.1.1.2, by change G.Adj v a.1.1.2; simpa only [← a.2] using a.1.2⟩
  invFun w := ⟨⟨(v, w.1), w.2⟩, rfl⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext a.2.symm rfl
  right_inv _ := rfl

private theorem tail_fiber_card (v : Fin n) :
    Fintype.card {a : Arc G // a.1.1 = v} = G.degree v := by
  rw [Fintype.card_congr (tailFiberEquiv G v)]
  exact G.card_neighborSet_eq_degree v

private theorem C_row_sum [Semiring K] (a : Arc G) :
    ∑ b, C G K a b = (G.degree a.1.1 : K) := by
  simp only [C]
  have hc := tail_fiber_card G a.1.1
  simpa [Fintype.card_subtype, eq_comm] using congrArg (fun k : ℕ => (k : K)) hc

private theorem C_sq [Semiring K] :
    C G K * C G K = Matrix.diagonal (fun a => (G.degree a.1.1 : K)) * C G K := by
  ext a b
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, C]
  by_cases hab : a.1.1 = b.1.1
  · simpa +contextual [C, hab, eq_comm] using C_row_sum (K := K) G a
  · simp only [hab, ite_false, mul_zero]
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with hac hcb <;> try simp
    exact (hab (hac.trans hcb)).elim

private theorem diagonal_C_comm [Semiring K] (f : Fin n → K) :
    Matrix.diagonal (fun a : Arc G => f a.1.1) * C G K =
      C G K * Matrix.diagonal (fun a : Arc G => f a.1.1) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, C]
  by_cases h : a.1.1 = b.1.1 <;> simp [h]

private theorem RS_eq_transition : R G ℝ * S G ℝ = nbTransition G := by
  have hf (a : Arc G) : (reverse G a).1.1 = a.1.2 := rfl
  rw [R_mul]
  ext a b
  simp only [S, Matrix.diagonal_mul, Matrix.sub_apply, C, hf, tailDegree,
    Matrix.one_apply, nbTransition]
  by_cases ht : a.1.2 = b.1.1
  · by_cases hh : b.1.2 = a.1.1
    · have he : reverse G a = b := by apply Subtype.ext; exact Prod.ext ht hh.symm
      simp [ht, hh, he] <;> rfl
    · have he : reverse G a ≠ b := by intro h; exact hh (congrArg (fun c : Arc G => c.1.2) h).symm
      simp [ht, hh, he, one_div] <;> rfl
  · have he : reverse G a ≠ b := by intro h; exact ht (congrArg (fun c : Arc G => c.1.1) h)
    simp [ht, he] <;> rfl


private theorem tailDegree_ne_zero [Field K] [CharZero K]
    (hdeg : 2 ≤ G.minDegree) (a : Arc G) : tailDegree G K a ≠ 0 := by
  have hd : 2 ≤ G.degree a.1.1 := hdeg.trans (G.minDegree_le_degree _)
  dsimp [tailDegree]
  apply sub_ne_zero.mpr
  exact_mod_cast (show G.degree a.1.1 ≠ 1 by omega)

private theorem T_mul_C_sub_one [Ring K] :
    T G K * (C G K - 1) = Matrix.diagonal (tailDegree G K) := by
  have hd : Matrix.diagonal (fun a : Arc G => (G.degree a.1.1 : K)) =
      Matrix.diagonal (tailDegree G K) + 1 := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    ext a
    simp [tailDegree]
  have hcc := C_sq (K := K) G
  rw [hd, add_mul, one_mul] at hcc
  calc
    T G K * (C G K - 1) =
        C G K * C G K - C G K - Matrix.diagonal (tailDegree G K) * C G K +
          Matrix.diagonal (tailDegree G K) := by unfold T; noncomm_ring
    _ = Matrix.diagonal (tailDegree G K) := by rw [hcc]; abel

private theorem T_mul_S [Field K] [CharZero K] (hdeg : 2 ≤ G.minDegree) :
    T G K * S G K = 1 := by
  let E := Matrix.diagonal (fun a : Arc G => (tailDegree G K a)⁻¹)
  have heC : E * C G K = C G K * E := by
    exact diagonal_C_comm G (fun v => ((G.degree v : K) - 1)⁻¹)
  have heD : Matrix.diagonal (tailDegree G K) * E = E * Matrix.diagonal (tailDegree G K) := by
    dsimp [E]
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    ext a
    exact mul_comm _ _
  have heT : T G K * E = E * T G K := by
    dsimp [T]
    rw [sub_mul, mul_sub, ← heC, heD]
  calc
    T G K * S G K = (T G K * E) * (C G K - 1) := by rw [S, mul_assoc]
    _ = E * (T G K * (C G K - 1)) := by rw [heT, mul_assoc]
    _ = E * Matrix.diagonal (tailDegree G K) := by rw [T_mul_C_sub_one]
    _ = 1 := by
      dsimp [E]
      rw [Matrix.diagonal_mul_diagonal]
      have he : (fun a : Arc G => (tailDegree G K a)⁻¹ * tailDegree G K a) =
          (fun _ => 1) := by
        funext a
        exact inv_mul_cancel₀ (tailDegree_ne_zero (K := K) G hdeg a)
      rw [he, Matrix.diagonal_one]

private theorem S_mul_T [Field K] [CharZero K] (hdeg : 2 ≤ G.minDegree) :
    S G K * T G K = 1 :=
  mul_eq_one_comm.mp (T_mul_S G hdeg)

private theorem S_mul_one [Field K] [CharZero K] (hdeg : 2 ≤ G.minDegree) :
    S G K *ᵥ (fun _ => 1) = fun _ => 1 := by
  rw [S, ← Matrix.mulVec_mulVec]
  ext a
  rw [Matrix.mulVec_diagonal]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
  change (tailDegree G K a)⁻¹ * ((∑ b, C G K a b * 1) - 1) = 1
  simp only [mul_one, C_row_sum]
  exact inv_mul_cancel₀ (tailDegree_ne_zero (K := K) G hdeg a)


end D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

open Matrix
open scoped BigOperators InnerProductSpace
open Module (finrank)
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

@[reducible] private def Orient := {a : Arc G // a.1.1 < a.1.2}
private instance : Fintype (Orient G) := inferInstanceAs (Fintype {a : Arc G // a.1.1 < a.1.2})

private theorem reverse_orient (a : Arc G) (h : ¬ a.1.1 < a.1.2) :
    (reverse G a).1.1 < (reverse G a).1.2 := by
  exact lt_of_le_of_ne (le_of_not_gt h) a.2.ne.symm

private def orientEquiv : Arc G ≃ Orient G ⊕ Orient G where
  toFun a := if h : a.1.1 < a.1.2 then Sum.inl ⟨a,h⟩ else Sum.inr ⟨reverse G a,reverse_orient G a h⟩
  invFun s := s.elim Subtype.val (fun a => reverse G a.1)
  left_inv a := by
    dsimp
    split_ifs <;> simp
  right_inv s := by
    cases s with
    | inl a => simp [a.2]
    | inr a =>
      have hf : (reverse G a.1).1.1 = a.1.1.2 := rfl
      have hs : (reverse G a.1).1.2 = a.1.1.1 := rfl
      simp [hf, hs, a.2.le]

private theorem arc_card_orient : Fintype.card (Arc G) = 2 * Fintype.card (Orient G) := by
  rw [Fintype.card_congr (orientEquiv G), Fintype.card_sum]
  omega

private def skewMap : (Orient G → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Arc G) where
  toFun f := WithLp.toLp 2 (fun a => if h : a.1.1 < a.1.2 then f ⟨a,h⟩
    else -f ⟨reverse G a, reverse_orient G a h⟩)
  map_add' f g := by
    apply PiLp.ext; intro a
    dsimp
    split_ifs <;> simp [add_comm]
  map_smul' c f := by
    apply PiLp.ext; intro a
    dsimp
    split_ifs <;> simp [mul_neg]

private theorem skewMap_injective : Function.Injective (skewMap G) := by
  intro f g he
  funext a
  have hh := congrArg (fun x : EuclideanSpace ℂ (Arc G) => x a.1) he
  simpa [skewMap, a.2] using hh

private def Vminus : Submodule ℂ (EuclideanSpace ℂ (Arc G)) := (skewMap G).range

private theorem Vminus_finrank : finrank ℂ (Vminus G) = Fintype.card (Orient G) := by
  rw [Vminus, LinearMap.finrank_range_of_inj (skewMap_injective G)]
  exact Module.finrank_fintype_fun_eq_card ℂ

private theorem Vminus_reverse (x : EuclideanSpace ℂ (Arc G)) (hx : x ∈ Vminus G) :
    R G ℂ *ᵥ ⇑x = -⇑x := by
  obtain ⟨f, rfl⟩ := hx
  have hf (a : Arc G) : (reverse G a).1.1 = a.1.2 := rfl
  have hs (a : Arc G) : (reverse G a).1.2 = a.1.1 := rfl
  rw [R_mulVec]
  funext a
  by_cases ha : a.1.1 < a.1.2
  · have hn : ¬ a.1.2 < a.1.1 := not_lt_of_gt ha
    simp [skewMap, Function.comp_apply, hf, hs, ha, hn]
  · have hr : a.1.2 < a.1.1 := reverse_orient G a ha
    simp [skewMap, Function.comp_apply, hf, hs, ha, hr]

private def tailSum : EuclideanSpace ℂ (Arc G) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x v := ∑ a : Arc G, if a.1.1 = v then x a else 0
  map_add' x y := by
    funext v
    change (∑ a : Arc G, if a.1.1 = v then x a + y a else 0) =
      (∑ a : Arc G, if a.1.1 = v then x a else 0) + ∑ a : Arc G, if a.1.1 = v then y a else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  map_smul' c x := by funext v; simp [Finset.mul_sum, mul_ite]

private def W : Submodule ℂ (EuclideanSpace ℂ (Arc G)) := (tailSum G).ker

private theorem W_finrank_lower : Fintype.card (Arc G) ≤ finrank ℂ (W G) + n := by
  have hr := (tailSum G).finrank_range_add_finrank_ker
  have hl := Submodule.finrank_le ((tailSum G).range)
  simp only [finrank_euclideanSpace, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr hl
  dsimp [W]
  omega

private theorem W_C_zero (x : EuclideanSpace ℂ (Arc G)) (hx : x ∈ W G) :
    C G ℂ *ᵥ ⇑x = 0 := by
  have hh : tailSum G x = 0 := hx
  funext a
  have ha := congrFun hh a.1.1
  simpa [tailSum, Matrix.mulVec, dotProduct, C, ite_mul, eq_comm] using ha

end D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

open Matrix
open scoped BigOperators InnerProductSpace
open Module (finrank)
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private def q (A : Matrix (Arc G) (Arc G) ℂ) (x : EuclideanSpace ℂ (Arc G)) : ℝ :=
  (star ⇑x ⬝ᵥ (A *ᵥ ⇑x)).re

private theorem inner_matrix (A : Matrix (Arc G) (Arc G) ℂ) (x : EuclideanSpace ℂ (Arc G)) :
    RCLike.re ⟪Matrix.toEuclideanLin A x,x⟫_ℂ = q G A x := by
  rw [inner_re_symm, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

private theorem q_sub (A B : Matrix (Arc G) (Arc G) ℂ) (x : EuclideanSpace ℂ (Arc G)) :
    q G (A-B) x = q G A x - q G B x := by
  simp [q, Matrix.sub_mulVec, dotProduct_sub]

private theorem q_real_smul (A : Matrix (Arc G) (Arc G) ℂ) (x : EuclideanSpace ℂ (Arc G)) (t : ℝ) :
    q G ((t:ℂ) • A) x = t * q G A x := by
  simp [q, Matrix.smul_mulVec, dotProduct_smul]

private theorem q_diagonal (w : Arc G → ℝ) (x : EuclideanSpace ℂ (Arc G)) :
    q G (Matrix.diagonal (fun a => (w a : ℂ))) x = ∑ a, w a * ‖x a‖ ^ 2 := by
  simp only [q, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_left_comm]
  change ((w a : ℂ) * (starRingEnd ℂ (x a) * x a)).re = _
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

private theorem C_mulVec_tailSum (x : EuclideanSpace ℂ (Arc G)) :
    C G ℂ *ᵥ ⇑x = fun a => tailSum G x a.1.1 := by
  funext a
  simp [C, tailSum, Matrix.mulVec, dotProduct, ite_mul, eq_comm]

private theorem q_C (x : EuclideanSpace ℂ (Arc G)) :
    q G (C G ℂ) x = ∑ v, ‖tailSum G x v‖ ^ 2 := by
  rw [q, C_mulVec_tailSum]
  have hs : (∑ a : Arc G, star (x a) * tailSum G x a.1.1) =
      ∑ v, star (tailSum G x v) * tailSum G x v := by
    calc
      _ = ∑ v, ∑ a : Arc G with a.1.1 = v, star (x a) * tailSum G x a.1.1 :=
        (Finset.sum_fiberwise Finset.univ (fun a : Arc G => a.1.1)
          (fun a => star (x a) * tailSum G x a.1.1)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        change (∑ a : Arc G with a.1.1 = v, star (x a) * tailSum G x a.1.1) =
          star (∑ a : Arc G, if a.1.1 = v then x a else 0) * tailSum G x v
        rw [star_sum, Finset.sum_mul, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : a.1.1 = v <;> simp [h]
  change (∑ a : Arc G, star (x a) * tailSum G x a.1.1).re = _
  rw [hs, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro v _
  change (starRingEnd ℂ (tailSum G x v) * tailSum G x v).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem diagonal_tailDegree_complex : Matrix.diagonal (tailDegree G ℂ) =
    Matrix.diagonal (fun a : Arc G => (((G.degree a.1.1 : ℝ)-1):ℂ)) := by
  apply congrArg Matrix.diagonal
  funext a
  simp only [tailDegree]
  push_cast
  rfl

private theorem q_T (x : EuclideanSpace ℂ (Arc G)) :
    q G (T G ℂ) x = (∑ v, ‖tailSum G x v‖ ^ 2) -
      ∑ a, ((G.degree a.1.1 : ℝ) - 1) * ‖x a‖ ^ 2 := by
  rw [T, q_sub, q_C]
  have hq := q_diagonal G (fun a => (G.degree a.1.1 : ℝ)-1) x
  push_cast at hq
  rw [diagonal_tailDegree_complex]
  push_cast
  rw [hq]

private theorem q_T_lower (x : EuclideanSpace ℂ (Arc G)) :
    -((G.maxDegree : ℝ)-1) * ‖x‖ ^ 2 ≤ q G (T G ℂ) x := by
  rw [q_T, EuclideanSpace.norm_sq_eq]
  have hp : 0 ≤ ∑ v, ‖tailSum G x v‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : (∑ a : Arc G, ((G.degree a.1.1 : ℝ)-1) * ‖x a‖ ^ 2) ≤
      ((G.maxDegree : ℝ)-1) * ∑ a, ‖x a‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    gcongr
    exact_mod_cast G.degree_le_maxDegree a.1.1
  linarith

private theorem q_T_W_upper (x : EuclideanSpace ℂ (Arc G)) (hx : x ∈ W G) :
    q G (T G ℂ) x ≤ -((G.minDegree : ℝ)-1) * ‖x‖ ^ 2 := by
  have hz : q G (C G ℂ) x = 0 := by simp [q, W_C_zero G x hx]
  rw [T, q_sub, hz]
  have hd : ((G.minDegree : ℝ)-1) * ∑ a : Arc G, ‖x a‖ ^ 2 ≤
      ∑ a, ((G.degree a.1.1 : ℝ)-1) * ‖x a‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    gcongr
    exact_mod_cast G.minDegree_le_degree a.1.1
  have hq := q_diagonal G (fun a => (G.degree a.1.1 : ℝ)-1) x
  push_cast at hq
  rw [diagonal_tailDegree_complex]
  push_cast
  rw [hq, EuclideanSpace.norm_sq_eq]
  linarith


private theorem R_norm (x : EuclideanSpace ℂ (Arc G)) :
    ‖Matrix.toEuclideanLin (R G ℂ) x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ a : Arc G, ‖(R G ℂ *ᵥ ⇑x) a‖ ^ 2) = ∑ a, ‖x a‖ ^ 2
  rw [R_mulVec]
  exact Equiv.sum_comp (reverse G) (fun a => ‖x a‖ ^ 2)

private theorem q_R_abs (x : EuclideanSpace ℂ (Arc G)) : |q G (R G ℂ) x| ≤ ‖x‖ ^ 2 := by
  rw [← inner_matrix]
  calc
    _ ≤ ‖⟪Matrix.toEuclideanLin (R G ℂ) x,x⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖Matrix.toEuclideanLin (R G ℂ) x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ = ‖x‖ ^ 2 := by rw [R_norm]; ring

private theorem q_one (x : EuclideanSpace ℂ (Arc G)) : q G (1 : Matrix (Arc G) (Arc G) ℂ) x = ‖x‖ ^ 2 := by
  have hh := q_diagonal G (fun _ => 1) x
  simpa [Matrix.diagonal_one, EuclideanSpace.norm_sq_eq] using hh

private theorem q_R_Vminus (x : EuclideanSpace ℂ (Arc G)) (hx : x ∈ Vminus G) :
    q G (R G ℂ) x = -‖x‖ ^ 2 := by
  have hh := q_one G x
  simp only [q, Matrix.one_mulVec] at hh
  simp only [q, Vminus_reverse G x hx, dotProduct_neg, Complex.neg_re]
  rw [hh]

private theorem pencil_left_nonpos (hdeg : 2 ≤ G.minDegree)
    (x : EuclideanSpace ℂ (Arc G)) (hx : x ∈ W G) :
    RCLike.re ⟪Matrix.toEuclideanLin
      (T G ℂ - (((G.minDegree : ℝ)-1):ℂ) • R G ℂ) x,x⟫_ℂ ≤ 0 := by
  rw [inner_matrix, q_sub]
  have hs := q_real_smul G (R G ℂ) x ((G.minDegree:ℝ)-1)
  push_cast at hs ⊢
  rw [hs]
  have hT := q_T_W_upper G x hx
  have hR := (abs_le.mp (q_R_abs G x)).1
  have ha : 0 ≤ (G.minDegree : ℝ)-1 := by
    have hd : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast hdeg
    linarith
  nlinarith

private theorem pencil_right_pos (x : EuclideanSpace ℂ (Arc G)) (hx : x ∈ Vminus G) (hx0 : x ≠ 0) :
    0 < RCLike.re ⟪Matrix.toEuclideanLin
      (T G ℂ - (G.maxDegree:ℂ) • R G ℂ) x,x⟫_ℂ := by
  rw [inner_matrix]
  have he : (G.maxDegree:ℂ) = ((G.maxDegree:ℝ):ℂ) := by norm_cast
  rw [he, q_sub, q_real_smul, q_R_Vminus G x hx]
  have hT := q_T_lower G x
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  nlinarith

private theorem R_hermitian : (R G ℂ).IsHermitian := by
  change (R G ℂ)ᴴ = R G ℂ
  simp [R, show (reverse G)⁻¹ = reverse G from rfl]

private theorem T_hermitian : (T G ℂ).IsHermitian := by
  apply Matrix.IsHermitian.sub
  · ext a b
    simp [C, Matrix.conjTranspose_apply, eq_comm]
  · rw [Matrix.isHermitian_diagonal_iff]
    intro a
    simp [tailDegree, IsSelfAdjoint]


end D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

open Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem eigenpair_mem_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r : ℂ) (x : ι → ℂ) (hx : x ≠ 0) (he : A *ᵥ x = r • x) :
    r ∈ spectrum ℂ A := by
  rw [← Matrix.spectrum_toLin']
  exact (Module.End.hasEigenvalue_of_hasEigenvector
    (f := Matrix.toLin' A) ⟨Module.End.mem_eigenspace_iff.mpr he, hx⟩).mem_spectrum

private theorem transition_complex :
    (nbTransition G).map (algebraMap ℝ ℂ) = R G ℂ * S G ℂ := by
  rw [← RS_eq_transition]
  ext a b
  simp [R_mul, S, Matrix.diagonal_mul, C, tailDegree, Matrix.one_apply]
  split_ifs <;> simp_all

private theorem nbGap_le_norm_eigenpair (r : ℂ) (x : Arc G → ℂ) (hx : x ≠ 0)
    (he : (nbTransition G).map (algebraMap ℝ ℂ) *ᵥ x = r • x) :
    nbGap G ≤ ‖r‖ := by
  apply csInf_le
  · exact ⟨0, by rintro y ⟨z, hz, rfl⟩; exact norm_nonneg _⟩
  · exact ⟨r, eigenpair_mem_spectrum _ _ x hx he, rfl⟩

private theorem arc_nonempty (hn : 0 < n) (hdeg : 2 ≤ G.minDegree) : Nonempty (Arc G) := by
  let v : Fin n := ⟨0,hn⟩
  have hd : 0 < G.degree v := lt_of_lt_of_le (by omega) (hdeg.trans (G.minDegree_le_degree v))
  have hc : 0 < Fintype.card (G.neighborSet v) := by rwa [G.card_neighborSet_eq_degree]
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hc
  exact ⟨⟨(v,w.1),w.2⟩⟩

private theorem nbGap_le_one (hn : 0 < n) (hdeg : 2 ≤ G.minDegree) : nbGap G ≤ 1 := by
  letI := arc_nonempty G hn hdeg
  have hz : (fun _ : Arc G => (1 : ℂ)) ≠ 0 := by
    intro h
    have hh := congrFun h (Classical.choice (arc_nonempty G hn hdeg))
    norm_num at hh
  have he : (nbTransition G).map (algebraMap ℝ ℂ) *ᵥ (fun _ => 1) =
      (1 : ℂ) • (fun _ : Arc G => 1) := by
    rw [transition_complex, ← Matrix.mulVec_mulVec, S_mul_one G hdeg, R_mulVec]
    funext a
    simp
  simpa using nbGap_le_norm_eigenpair G 1 _ hz he

private theorem pencil_to_eigenpair (hdeg : 2 ≤ G.minDegree) (t : ℝ) (ht : 0 < t)
    (x : Arc G → ℂ) (hx : x ≠ 0) (he : (T G ℂ - (t:ℂ) • R G ℂ) *ᵥ x = 0) :
    ∃ y : Arc G → ℂ, y ≠ 0 ∧
      (nbTransition G).map (algebraMap ℝ ℂ) *ᵥ y = ((1/t : ℝ):ℂ) • y := by
  have hTx : T G ℂ *ᵥ x = (t:ℂ) • (R G ℂ *ᵥ x) := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, sub_eq_zero] using he
  have hST : S G ℂ *ᵥ (T G ℂ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, S_mul_T G hdeg, Matrix.one_mulVec]
  have hS : S G ℂ *ᵥ (R G ℂ *ᵥ x) = (t:ℂ)⁻¹ • x := by
    rw [hTx, Matrix.mulVec_smul] at hST
    calc
      _ = (t:ℂ)⁻¹ • ((t:ℂ) • (S G ℂ *ᵥ (R G ℂ *ᵥ x))) := by
        rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht.ne'), one_smul]
      _ = (t:ℂ)⁻¹ • x := by rw [hST]
  refine ⟨R G ℂ *ᵥ x, ?_, ?_⟩
  · intro h
    have hR := congrArg (fun z => R G ℂ *ᵥ z) h
    rw [Matrix.mulVec_mulVec, R_sq, Matrix.one_mulVec, Matrix.mulVec_zero] at hR
    exact hx hR
  · rw [transition_complex, ← Matrix.mulVec_mulVec, hS, Matrix.mulVec_smul]
    simp

end D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

open Matrix
open scoped BigOperators InnerProductSpace
open Module (finrank)
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private theorem orient_card_gt (hn : 0 < n) (hdeg : 3 ≤ G.minDegree) :
    n < Fintype.card (Orient G) := by
  have hc := arc_card G
  have ho := arc_card_orient G
  have hh := G.sum_degrees_eq_twice_card_edges
  have hl : (∑ v : Fin n, 3) ≤ ∑ v : Fin n, G.degree v :=
    Finset.sum_le_sum fun v _ => hdeg.trans (G.minDegree_le_degree v)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hl
  norm_cast at hl
  omega

private theorem pencil_graph_singular (hn : 0 < n) (hdeg : 3 ≤ G.minDegree) :
    ∃ t ∈ Set.Ico ((G.minDegree : ℝ)-1) (G.maxDegree : ℝ),
      ∃ x : Arc G → ℂ, x ≠ 0 ∧ (T G ℂ - (t:ℂ) • R G ℂ) *ᵥ x = 0 := by
  let m := Fintype.card (Orient G)
  have hm : n < m := orient_card_gt G hn hdeg
  have hc : Fintype.card (Arc G) = 2*m := arc_card_orient G
  let k : Fin (Fintype.card (Arc G)) := ⟨m-1, by omega⟩
  have hk : (k : ℕ)+1 = m := by dsimp [k]; omega
  have hw := W_finrank_lower G
  have hv : finrank ℂ (Vminus G) = (k : ℕ)+1 := by rw [Vminus_finrank, hk]
  have hl : finrank ℂ (W G) + (k : ℕ) + 1 > Fintype.card (Arc G) := by omega
  have hab : (G.minDegree : ℝ)-1 ≤ G.maxDegree := by
    have hd : (G.minDegree : ℝ) ≤ G.maxDegree := by exact_mod_cast G.minDegree_le_maxDegree
    linarith
  exact D5.S3.Combinatorics.NonBacktracking.HermitianPencilCrossing.pencil_singular_of_subspaces (T G ℂ) (R G ℂ) (T_hermitian G) (R_hermitian G)
    _ _ hab k (W G) (Vminus G) hl hv
    (by simpa only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
      using pencil_left_nonpos G (by omega)) (by
      intro x hx hx0
      simpa only [Complex.ofReal_natCast] using pencil_right_pos G x hx hx0)

private theorem positive_small_eigenpair (hn : 0 < n) (hdeg : 3 ≤ G.minDegree) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / ((G.minDegree : ℝ)-1) ∧
      ∃ x : Arc G → ℂ, x ≠ 0 ∧
        (nbTransition G).map (algebraMap ℝ ℂ) *ᵥ x = (r:ℂ) • x := by
  obtain ⟨t, ht, x, hx, he⟩ := pencil_graph_singular G hn hdeg
  have hd : (3 : ℝ) ≤ G.minDegree := by exact_mod_cast hdeg
  have ha : 0 < (G.minDegree : ℝ)-1 := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  obtain ⟨y,hy,hPy⟩ := pencil_to_eigenpair G (by omega) t ht0 x hx he
  refine ⟨1/t, one_div_pos.mpr ht0, one_div_le_one_div_of_le ha ht.1, y, hy, hPy⟩


end D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

namespace D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

theorem result : claim := by
  intro n G inst hn hdeg _hcycle
  by_cases hd : G.minDegree = 2
  · convert nbGap_le_one G hn hdeg using 1 <;> norm_num [hd]
  · have hd3 : 3 ≤ G.minDegree := by omega
    obtain ⟨r, hr, hb, x, hx, he⟩ := positive_small_eigenpair G hn hd3
    have hg := nbGap_le_norm_eigenpair G (r : ℂ) x hx he
    have hnorm : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    rw [hnorm] at hg
    exact hg.trans hb

end D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree

/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.FieldTheory.Minpoly.Field]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim; claim=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim; result=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result
   digest: Conjecture B.1 for the literal planar diagram algebra at loop fugacity zero. -/
import D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineDiagrams
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineAction
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineEdges
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineHornerData
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineHorner
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Basic.Complex.Basic

/-! The quantified family uses the full noncrossing diagram basis and literal path concatenation. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.StatisticalMechanics.PonciniRasmussenMinpolyRefutation
open D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra

/-- Poncini–Rasmussen Conjecture B.1 with its original quantifier and Hamiltonian. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ((minpoly ℂ (h ℂ n)).natDegree : ℚ) =
      ((3 : ℚ)^((n+1)/2) + (-1 : ℚ)^n * 3^((n-1)/2))/2

open scoped BigOperators Polynomial
open PonciniRasmussenNineDiagrams PonciniRasmussenNineAction PonciniRasmussenNineHorner

private def liftVector (b : Fin 4862 → TL ℂ 9) (v : Fin 8192 → Int) : TL ℂ 9 :=
  ∑ i : Fin 4862, v ⟨i.val,by omega⟩ • b i

private theorem h_lift (b : Fin 4862 → TL ℂ 9) (v : Fin 8192 → Int)
    (T : Fin 8 → Fin 4862 → Fin 4863)
    (hb : ∀ g i, (generator g : TL ℂ 9) * b i =
      if ht : (T g i).val < 4862 then b ⟨(T g i).val,ht⟩ else 0) :
    h ℂ 9 * liftVector b v =
      -(∑ i : Fin 4862, ∑ g : Fin 8,
        if ht : (T g i).val < 4862 then v ⟨i.val,by omega⟩ • b ⟨(T g i).val,ht⟩ else 0) := by
  unfold h liftVector
  rw [neg_mul, Finset.sum_mul]
  simp only [Finset.mul_sum, mul_zsmul, hb]
  rw [Finset.sum_comm]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro g hg
  rw [mul_smul_comm, hb]
  split_ifs <;> simp only [smul_zero]

private theorem lift_step (b : Fin 4862 → TL ℂ 9) (v : Fin 8192 → Int) (c : Int)
    (hunit : b ⟨4861,by omega⟩ = 1) :
    liftVector b (fun i => v i + if i.val == 4861 then c else 0) =
      liftVector b v + c • (1 : TL ℂ 9) := by
  unfold liftVector
  simp only [add_zsmul, Finset.sum_add_distrib]
  apply congrArg (fun z => (∑ i : Fin 4862, v ⟨i.val,by omega⟩ • b i) + z)
  simp only [beq_iff_eq]
  have hh : ∀ i : Fin 4862,
      ((if i.val = 4861 then c else 0) • b i) =
        if i = ⟨4861,by omega⟩ then c • (1 : TL ℂ 9) else 0 := by
    intro i
    by_cases hi : i.val = 4861
    · have h : i = ⟨4861,by omega⟩ := Fin.ext hi
      rw [ite_eq_left hi, ite_eq_left h, h, hunit]
    · rw [ite_eq_right hi, ite_eq_right (show i ≠ ⟨4861,by omega⟩ from fun h => hi (congrArg Fin.val h)), zero_zsmul]
  simp_rw [hh]
  simp

private def polynomialFromCoefficients (cs : List Int) : ℂ[X] :=
  cs.foldl (fun p (c : Int) => Polynomial.X*p + Polynomial.C (c : ℂ)) 0

private theorem fold_aeval (cs : List Int) : ∀ p : ℂ[X],
    Polynomial.aeval (h ℂ 9) (cs.foldl (fun p (c : Int) => Polynomial.X*p + Polynomial.C (c : ℂ)) p) =
      cs.foldl (fun a c => h ℂ 9*a + c • (1 : TL ℂ 9)) (Polynomial.aeval (h ℂ 9) p) := by
  induction cs with
  | nil => intro p; rfl
  | cons c cs ih =>
    intro p
    simp only [List.foldl_cons]
    rw [ih]
    apply congrArg (fun a => cs.foldl (fun a c => h ℂ 9*a + c • (1 : TL ℂ 9)) a)
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    simp

private theorem fold_lift (b : Fin 4862 → TL ℂ 9) (H : (Fin 8192 → Int) → Fin 8192 → Int)
    (hb : b ⟨4861,by omega⟩ = 1)
    (hH : ∀ v, liftVector b (H v) = h ℂ 9 * liftVector b v)
    (cs : List Int) : ∀ v,
    liftVector b (cs.foldl (fun v c => fun i => H v i + if i.val == 4861 then c else 0) v) =
      cs.foldl (fun a c => h ℂ 9*a + c • (1 : TL ℂ 9)) (liftVector b v) := by
  induction cs with
  | nil => intro v; rfl
  | cons c cs ih =>
    intro v
    simp only [List.foldl_cons, ih]
    rw [lift_step b (H v) c hb, hH]

private theorem polynomial_annihilates
    (b : Fin 4862 → TL ℂ 9) (H : (Fin 8192 → Int) → Fin 8192 → Int)
    (hb : b ⟨4861,by omega⟩ = 1)
    (hH : ∀ v, liftVector b (H v) = h ℂ 9 * liftVector b v)
    (cs : List Int)
    (hc : cs.foldl (fun v c => fun i => H v i + if i.val == 4861 then c else 0) (fun _ => 0) =
      (fun _ => 0)) :
    Polynomial.aeval (h ℂ 9) (polynomialFromCoefficients cs) = 0 := by
  have hz : liftVector b (fun _ => 0) = 0 := by simp [liftVector]
  have hh := fold_lift b H hb hH cs (fun _ => 0)
  rw [hc, hz] at hh
  rw [polynomialFromCoefficients, fold_aeval]
  simpa only [map_zero] using hh.symm

private def basisDiagram (i : Fin 4862) : TL ℂ 9 := MonoidAlgebra.single (diagram i) 1

private theorem sparse_lift (v : Fin 8192 → Int) :
    liftVector basisDiagram (sparseHamiltonian v) = h ℂ 9 * liftVector basisDiagram v := by
  rw [h_lift basisDiagram v transition (fun g i => generator_basis g i)]
  exact PonciniRasmussenNineEdges.sparse_sum basisDiagram v

private def annihilator : ℂ[X] := polynomialFromCoefficients annihilatorCoefficients

private theorem annihilator_aeval : Polynomial.aeval (h ℂ 9) annihilator = 0 :=
  polynomial_annihilates basisDiagram sparseHamiltonian unit_basis sparse_lift
    annihilatorCoefficients annihilation

private theorem annihilator_monic : annihilator.Monic := by
  unfold annihilator polynomialFromCoefficients annihilatorCoefficients
  simp only [List.foldl_cons, List.foldl_nil, mul_zero, zero_add, Int.cast_one, Int.cast_zero, Int.cast_neg]
  monicity!

private theorem annihilator_degree : annihilator.natDegree = 57 := by
  unfold annihilator polynomialFromCoefficients annihilatorCoefficients
  simp only [List.foldl_cons, List.foldl_nil, mul_zero, zero_add, Int.cast_one, Int.cast_zero, Int.cast_neg]
  compute_degree!

private theorem minpoly_nine_bound : (minpoly ℂ (h ℂ 9)).natDegree ≤ 57 := by
  rw [← annihilator_degree]
  exact Polynomial.natDegree_le_natDegree
    (minpoly.min ℂ (h ℂ 9) annihilator_monic annihilator_aeval)

/-- The degree-57 annihilator contradicts the conjectured degree 81 at nine strands. -/
theorem result : ¬ claim := by
  intro hc
  have hc9 := hc 9 (by omega)
  norm_num at hc9
  have hb := minpoly_nine_bound
  have hbq : ((minpoly ℂ (h ℂ 9)).natDegree : ℚ) ≤ 57 := by exact_mod_cast hb
  linarith

#print axioms result
end D5.S3.StatisticalMechanics.PonciniRasmussenMinpolyRefutation

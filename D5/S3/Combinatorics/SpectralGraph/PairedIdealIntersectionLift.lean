/- GID: D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: Exact paired support intertwining with the actual ideal graph. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
import Mathlib.Tactic

/-! Paired support construction from the public Nikandish unit-exponent source,
revision b93becea662a746badeadba42fdc3d3eb3db9382. Independently authored proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Finset Matrix
open scoped Classical Kronecker
namespace D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions

/-- Two equal distinguished exponents and two arbitrary tail exponents. -/
def pairExponents (a b c : ℕ) : Fin 4 → ℕ := ![a,a,b,c]

/-- The two tail support indicators, in the tensor-factor order. -/
def tailIndex (S : Finset (Fin 4)) : Fin 2 × Fin 2 :=
  (if 2 ∈ S then 1 else 0, if 3 ∈ S then 1 else 0)

/-- Antisymmetric values on the two paired families, zero on all other cells. -/
def pairedValue (h : Fin 2 × Fin 2 → ℝ) (S : Finset (Fin 4)) : ℝ :=
  if 0 ∈ S ∧ 1 ∉ S then h (tailIndex S)
  else if 1 ∈ S ∧ 0 ∉ S then -h (tailIndex S) else 0

/-- A concrete cell in the positive member of each pair. -/
def pairedCell (q : Fin 2 × Fin 2) : Finset (Fin 4) :=
  insert 0 ((if q.1 = 0 then ∅ else {2}) ∪ (if q.2 = 0 then ∅ else {3}))

private lemma support_univ : (univ : Finset (Finset (Fin 4))) = {∅,{0},{1},{0,1},{2},{0,2},{1,2},{0,1,2},{3},{0,3},{1,3},{0,1,3},{2,3},{0,2,3},{1,2,3},{0,1,2,3}} := by
  decide

private lemma sum_support (f : Finset (Fin 4) → ℝ) :
    (∑ S, f S) = f ∅+(f ({0})+(f ({1})+(f ({0,1})+(f ({2})+(f ({0,2})+(f ({1,2})+(f ({0,1,2})+(f ({3})+(f ({0,3})+(f ({1,3})+(f ({0,1,3})+(f ({2,3})+(f ({0,2,3})+(f ({1,2,3})+(f ({0,1,2,3})))))))))))))))) := by
  rw [support_univ]
  simp (disch := decide) only [sum_insert,sum_singleton]

private lemma tail_pairedCell (q : Fin 2 × Fin 2) : tailIndex (pairedCell q) = q := by
  rcases q with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide

private lemma pairedValue_cell (h : Fin 2 × Fin 2 → ℝ) (q : Fin 2 × Fin 2) :
    pairedValue h (pairedCell q) = h q := by
  rw [pairedValue, if_pos]
  · rw [tail_pairedCell]
  · rcases q with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> decide

private lemma pairedCell_nonempty (q : Fin 2 × Fin 2) : (pairedCell q).Nonempty :=
  ⟨0,mem_insert_self ..⟩

private lemma pairedCell_ne_univ (q : Fin 2 × Fin 2) : pairedCell q ≠ univ := by
  intro he
  have hh : (1 : Fin 4) ∈ pairedCell q := he.symm ▸ mem_univ 1
  rcases q with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [pairedCell] at hh

/-- The positive paired cell witnesses injectivity, for every tail vector. -/
theorem paired_lift_nonzero (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Fin 2 × Fin 2 → ℝ) (hh : h ≠ 0) :
    supportLift (pairExponents a b c) (pairedValue h) ≠ 0 := by
  have hk (i : Fin 4) : 0 < pairExponents a b c i := by
    fin_cases i <;> simp [pairExponents] <;> assumption
  obtain ⟨q,hq⟩ : ∃ q, h q ≠ 0 := Function.ne_iff.mp hh
  apply support_lift_nonzero _ hk _ (pairedCell q) (pairedCell_nonempty q)
    (pairedCell_ne_univ q)
  rwa [pairedValue_cell]

/-- Equal positive weights of the paired cells give exact zero total vertex sum. -/
theorem paired_lift_sum (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Fin 2 × Fin 2 → ℝ) :
    (∑ e : BoxVertex (pairExponents a b c),
      supportLift (pairExponents a b c) (pairedValue h) e) = 0 := by
  have hk (i : Fin 4) : 0 < pairExponents a b c i := by
    fin_cases i <;> simp [pairExponents] <;> assumption
  rw [show (∑ e : BoxVertex (pairExponents a b c),
      supportLift (pairExponents a b c) (pairedValue h) e) =
      ∑ S, supportWeight (pairExponents a b c) S * pairedValue h S from
    support_lift_sum _ hk _ (by simp [pairedValue]) (by simp [pairedValue])]
  rw [sum_support]
  simp [supportWeight,pairExponents,pairedValue,tailIndex]

/-- The full paired complement action, including every zero cell and both
removed endpoints. This is an exact intertwining with the source tensor. -/
theorem paired_support_action (a b c : ℕ) (h : Fin 2 × Fin 2 → ℝ)
    (S : Finset (Fin 4)) :
    supportComplementOp (pairExponents a b c) (pairedValue h) S =
      pairedValue ((tensorK (a : ℝ) (b : ℝ) (c : ℝ)-1)*ᵥ h) S := by
  have hn0 : ({0} : Finset (Fin 4)) ≠ univ := by decide
  have hn1 : ({1} : Finset (Fin 4)) ≠ univ := by decide
  have hn2 : ({0,1} : Finset (Fin 4)) ≠ univ := by decide
  have hn3 : ({2} : Finset (Fin 4)) ≠ univ := by decide
  have hn4 : ({0,2} : Finset (Fin 4)) ≠ univ := by decide
  have hn5 : ({1,2} : Finset (Fin 4)) ≠ univ := by decide
  have hn6 : ({0,1,2} : Finset (Fin 4)) ≠ univ := by decide
  have hn7 : ({3} : Finset (Fin 4)) ≠ univ := by decide
  have hn8 : ({0,3} : Finset (Fin 4)) ≠ univ := by decide
  have hn9 : ({1,3} : Finset (Fin 4)) ≠ univ := by decide
  have hn10 : ({0,1,3} : Finset (Fin 4)) ≠ univ := by decide
  have hn11 : ({2,3} : Finset (Fin 4)) ≠ univ := by decide
  have hn12 : ({0,2,3} : Finset (Fin 4)) ≠ univ := by decide
  have hn13 : ({1,2,3} : Finset (Fin 4)) ≠ univ := by decide
  have hS : S ∈ (univ : Finset (Finset (Fin 4))) := mem_univ S
  rw [support_univ] at hS
  simp only [mem_insert,mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [supportComplementOp,sum_support] <;>
    simp [supportWeight,pairExponents,
      hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,Matrix.one_apply,
      pairedValue,tailIndex,tensorK,E,F,kroneckerMap_apply,mulVec,dotProduct,
      Fintype.sum_prod_type,Fin.sum_univ_succ] <;> ring


/-- A paired tensor eigenvector gives a nonzero actual ideal-graph eigenvector.
There is no nonzero assumption on the intermediate complement eigenvalue. -/
theorem actual_paired_eigenvalue (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (e : ℝ) (h : Fin 2 × Fin 2 → ℝ) (hh : h ≠ 0)
    (he : tensorK (a : ℝ) (b : ℝ) (c : ℝ)*ᵥ h=e • h) :
    HasActualEigenvalue (modulus p (pairExponents a b c))
      (((((a+1)^2*(b+1)*(c+1))-2 : ℕ) : ℝ)+1-e) := by
  have hk (i : Fin 4) : 0 < pairExponents a b c i := by
    fin_cases i <;> simp [pairExponents] <;> assumption
  have hlap : (supportGraph (pairExponents a b c))ᶜ.lapMatrix ℝ *ᵥ
      supportLift (pairExponents a b c) (pairedValue h) =
      (e-1) • supportLift (pairExponents a b c) (pairedValue h) := by
    ext x
    rw [support_complement_intertwining _ hk,paired_support_action]
    rw [sub_mulVec,he,one_mulVec]
    simp only [supportLift,pairedValue,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    split_ifs <;> ring
  have hhactual := actual_eigenvalue_of_support p hp hinj (pairExponents a b c) hk
    (e-1) (supportLift (pairExponents a b c) (pairedValue h))
    (paired_lift_nonzero a b c ha hb hc h hh) (paired_lift_sum a b c ha hb hc h) hlap
  have hprod : (∏ i, (pairExponents a b c i+1))=(a+1)^2*(b+1)*(c+1) := by
    simp [pairExponents,Fin.prod_univ_succ]
    ring
  rw [hprod] at hhactual
  convert hhactual using 1 <;> ring

end D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift

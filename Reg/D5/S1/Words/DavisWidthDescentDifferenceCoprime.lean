import D5.S1.Words.DavisWidthDescentDifferenceCoprime
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime
open _root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime
open LaurentPolynomial
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LaurentPolynomial Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n k => G n k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n k : Nat, 1 ≤ k → k < n → Nat.Coprime k n →
    r.readout () n k = (n : LaurentPolynomial Int) * T (1 - (k : Int)) * eulerian (n - 1)

theorem eulerian_one : eulerian 1 = 1 := by
  have h : widthDescents 1 (Equiv.refl (Fin 1)) = 0 := by decide +kernel
  simp only [eulerian, Fintype.sum_unique]
  change T (widthDescents 1 (Equiv.refl (Fin 1)) : Int) = 1
  rw [h]
  rfl

theorem eulerian_two : eulerian 2 = T 0 + T 1 := by
  have h0 : widthDescents 1 (Equiv.refl (Fin 2)) = 0 := by decide +kernel
  have h1 : widthDescents 1 (Equiv.swap (0 : Fin 2) 1) = 1 := by decide +kernel
  rw [eulerian, ← Equiv.Perm.decomposeFin.symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, h0, h1]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 2 1 (by decide) (by decide) (by decide)
  change (0 : LaurentPolynomial Int) = 2 * T (1 - (1 : Int)) * eulerian 1 at hf
  simp only [eulerian_one, sub_self, T_zero, mul_one] at hf
  have hc := congrArg (fun p : LaurentPolynomial Int => p.coeff 0) hf
  norm_num [AddMonoidAlgebra.natCast_def] at hc

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨3, 1, 2, ?_⟩
  change G 3 1 ≠ G 3 2
  rw [_root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime.result
    3 1 (by decide) (by decide) (by decide),
    _root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime.result
    3 2 (by decide) (by decide) (by decide)]
  norm_num only
  rw [eulerian_two]
  intro h
  have hc := congrArg (fun p : LaurentPolynomial Int => p.coeff (-1)) h
  change
    (AddMonoidAlgebra.single (0 : Int) (3 : Int) * AddMonoidAlgebra.single 0 1 *
      (AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single 1 1)).coeff (-1) =
    (AddMonoidAlgebra.single (0 : Int) (3 : Int) * AddMonoidAlgebra.single (-1) 1 *
      (AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single 1 1)).coeff (-1) at hc
  norm_num only [T, mul_add, AddMonoidAlgebra.natCast_def,
    AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single, Finsupp.add_apply, Finsupp.single_apply] at hc
  norm_num at hc

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime.result in arena
  readout via (realize signature (fun _ n k => G n k) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime
    «definition» := some {
      owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime
      name := `D5.S1.Words.DavisWidthDescentDifferenceCoprime.claim }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime

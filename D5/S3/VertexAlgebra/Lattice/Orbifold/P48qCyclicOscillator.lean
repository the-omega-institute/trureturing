/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCyclicOscillator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qCyclicOscillator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recognition of a cyclic P48q oscillator space from its Weyl relations. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedFockIrreducibility
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import OmegaBuild.Commands

/-! Cyclic oscillator recognition for the polynomial Fock model of P48q. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCyclicOscillator

open P48qThirdTwistedField (Fock Mode)
open P48qTwistedFockIrreducibility (applyPartials exists_constant_derivative_word)
open MvPolynomial
open scoped IsMulCommutative

/-- Evaluating polynomials in the commuting creators on a nonzero vacuum
embeds the native Fock space and intertwines its coordinate Weyl action. -/
theorem exists_cyclic_intertwiner {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A D : Mode → Module.End ℂ M) (w : M)
    (hA : ∀ i j, Commute (A i) (A j))
    (hWeyl : ∀ i j, ⁅D i, A j⁆ = if i = j then 1 else 0)
    (hw : w ≠ 0) (hVac : ∀ i, D i w = 0) :
    ∃ F : Fock →ₗ[ℂ] M, Function.Injective F ∧ F 1 = w ∧
      (∀ i P, F (X i * P) = A i (F P)) ∧
      (∀ i P, F (pderiv i P) = D i (F P)) := by
  classical
  let S : Subalgebra ℂ (Module.End ℂ M) := Algebra.adjoin ℂ (Set.range A)
  let : IsMulCommutative S :=
    Algebra.isMulCommutative_adjoin ℂ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hA i j)
  let generators (i : Mode) : S := ⟨A i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  let eval : Fock →ₐ[ℂ] Module.End ℂ M := S.val.comp (aeval generators)
  let F : Fock →ₗ[ℂ] M := (LinearMap.applyₗ (R := ℂ) w).comp eval.toLinearMap
  have eval_X (i : Mode) : eval (X i) = A i := by
    change S.val (aeval generators (X i)) = A i
    rw [aeval_X]
    rfl
  have F_C (c : ℂ) : F (C c) = c • w := by
    change eval (C c) w = c • w
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rfl
  have F_one : F 1 = w := by
    change eval 1 w = w
    rw [map_one]
    rfl
  have F_X (i : Mode) (P : Fock) : F (X i * P) = A i (F P) := by
    change eval (X i * P) w = A i (eval P w)
    rw [map_mul, eval_X]
    rfl
  have F_deriv (i : Mode) (P : Fock) : F (pderiv i P) = D i (F P) := by
    induction P using MvPolynomial.induction_on with
    | C c => simp [F_C, hVac]
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P j hP =>
      have h := DFunLike.congr_fun (hWeyl i j) (F P)
      change D i (A j (F P)) - A j (D i (F P)) =
        (if i = j then (1 : Module.End ℂ M) else 0) (F P) at h
      rw [pderiv_mul, map_add, mul_comm (pderiv i P) (X j), F_X, hP,
        mul_comm P (X j), F_X, sub_eq_iff_eq_add.mp h]
      by_cases hij : i = j
      · subst j
        simp [add_comm]
      · simp [hij, pderiv_X_of_ne (Ne.symm hij)]
  refine ⟨F, (injective_iff_map_eq_zero F).2 ?_, F_one, F_X, F_deriv⟩
  intro P hP
  by_contra hne
  have word_zero (word : List Mode) (Q : Fock) (hQ : F Q = 0) :
      F (applyPartials word Q) = 0 := by
    induction word generalizing Q with
    | nil => exact hQ
    | cons j word ih => exact ih _ (by rw [F_deriv, hQ, map_zero])
  obtain ⟨word, _, c, hc, hword⟩ := exists_constant_derivative_word P hne
  have h := word_zero word P hP
  rw [hword, F_C] at h
  exact smul_ne_zero hc hw h

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCyclicOscillator

#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCyclicOscillator.exists_cyclic_intertwiner

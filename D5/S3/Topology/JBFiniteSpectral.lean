/- GID: D5/S3/Topology/JBFiniteSpectral
   generality: G
   mirror-B: D5/B/S3/Topology/JBFiniteSpectral
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: Finite-dimensional six-law real JB algebras supply spectral resolutions on their original carrier. -/

module

public import D5.S3.Topology.JBSquareDefect
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.JBFiniteSpectral

open JBAlgebra JBComplexification JBSquareDefect
open scoped BigOperators

section Commutative

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
  [SquareLaws R] [CompleteSpace R]

/-- Real restriction of an actual complex character. -/
private def realCharacter (φ : WeakDual.characterSpace ℂ (Complexification R)) : R →ₐ[ℝ] ℝ where
  toFun r := (φ (QuadraticAlgebra.C r)).re
  map_zero' := by simp
  map_one' := by simp
  map_add' r s := by simp
  map_mul' r s := by
    apply Complex.ofReal_injective
    simp only [real_character_value, Complex.ofReal_mul, QuadraticAlgebra.C_mul, map_mul]
  commutes' t := by
    change (φ (QuadraticAlgebra.C (algebraMap ℝ R t))).re = t
    rw [Algebra.algebraMap_eq_smul_one, real_character_scalar, Complex.ofReal_re]

private theorem character_ext (r s : R)
    (h : ∀ φ : WeakDual.characterSpace ℂ (Complexification R),
      realCharacter φ r = realCharacter φ s) : r = s := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← real_gelfand_norm]
  have hz : gelfandStarTransform (Complexification R) (QuadraticAlgebra.C (r - s)) = 0 := by
    ext φ
    change φ (QuadraticAlgebra.C (r - s)) = 0
    rw [QuadraticAlgebra.C_sub, map_sub, sub_eq_zero]
    rw [← real_character_value r φ, ← real_character_value s φ]
    exact congrArg Complex.ofReal (h φ)
  rw [hz, norm_zero]

/-- An annihilator's distinct real roots suffice; unrealized roots give zero projections. -/
private theorem commutative_spectral [FiniteDimensional ℝ R] (a : R) :
    ∃ (n : ℕ) (e : Fin n → R) (r : Fin n → ℝ),
      (∀ i, e i * e i = e i) ∧ ∑ i, e i = 1 ∧
      ∑ i, r i • e i = a ∧ ∑ i, (r i * r i) • e i = a * a := by
  classical
  by_cases hR : Subsingleton R
  · letI := hR
    refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    all_goals exact Subsingleton.elim _ _
  letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
  let p := minpoly ℝ a
  have hp : p ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)
  let roots := p.roots.toFinset
  let e : roots → R := fun i => Polynomial.aeval a (Lagrange.basis roots id i.val)
  have hroot (φ : WeakDual.characterSpace ℂ (Complexification R)) :
      realCharacter φ a ∈ roots := by
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    change Polynomial.eval (realCharacter φ a) p = 0
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]
    simp only [p, minpoly.aeval, map_zero]
  have heval (φ : WeakDual.characterSpace ℂ (Complexification R)) (i : roots) :
      realCharacter φ (e i) = if i.val = realCharacter φ a then 1 else 0 := by
    rw [show realCharacter φ (e i) =
        Polynomial.eval (realCharacter φ a) (Lagrange.basis roots id i.val) from
      (Polynomial.aeval_algHom_apply (realCharacter φ) a _).symm]
    split_ifs with hi
    · rw [← hi]
      exact Lagrange.eval_basis_self (fun _ _ _ _ h => h) i.property
    · exact Lagrange.eval_basis_of_ne hi (hroot φ)
  have hid (i : roots) : e i * e i = e i := by
    apply character_ext
    intro φ
    rw [map_mul, heval]
    split_ifs <;> norm_num
  have horth (i j : roots) (hij : i ≠ j) : e i * e j = 0 := by
    apply character_ext
    intro φ
    rw [map_mul, map_zero, heval, heval]
    split_ifs with hi hj
    · exact False.elim (hij (Subtype.ext (hi.trans hj.symm)))
    all_goals norm_num
  have hsum : ∑ i, e i = 1 := by
    apply character_ext
    intro φ
    rw [map_sum, map_one]
    let j : roots := ⟨realCharacter φ a, hroot φ⟩
    have hv (i : roots) : realCharacter φ (e i) = if i = j then 1 else 0 := by
      simpa only [j, Subtype.ext_iff] using heval φ i
    simp only [hv]
    simp
  have hlin : ∑ i, i.val • e i = a := by
    apply character_ext
    intro φ
    rw [map_sum]
    let j : roots := ⟨realCharacter φ a, hroot φ⟩
    have hv (i : roots) : realCharacter φ (e i) = if i = j then 1 else 0 := by
      simpa only [j, Subtype.ext_iff] using heval φ i
    simp only [map_smul, hv]
    simp [j]
  have hsq : ∑ i, (i.val * i.val) • e i = a * a := by
    rw [← hlin, Finset.sum_mul]
    have hterm (i : roots) : (i.val • e i) * (∑ j, j.val • e j) =
        (i.val * i.val) • e i := by
      rw [Finset.mul_sum]
      calc
        _ = ∑ j, if j = i then (i.val * i.val) • e i else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp [smul_mul_smul_comm, hid]
          · simp [smul_mul_smul_comm, horth i j (Ne.symm hji), hji]
        _ = _ := by simp
    simp only [hterm]
  let b : Fin (Fintype.card roots) ≃ roots := (Fintype.equivFin roots).symm
  refine ⟨Fintype.card roots, fun i => e (b i), fun i => (b i).val,
    fun i => hid (b i), ?_, ?_, ?_⟩
  · exact (b.sum_comp e).trans hsum
  · exact (b.sum_comp (fun i => i.val • e i)).trans hlin
  · exact (b.sum_comp (fun i => (i.val * i.val) • e i)).trans hsq

end Commutative

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}

/-- Actual spectral resolutions from the six JB laws and finite dimensionality,
with the original product, unit and norm and no supplied spectral data. -/
theorem finite_spectral_resolutions (A : Data X S u) : HasFiniteSpectralResolutions S u := by
  letI : CompleteSpace X := FiniteDimensional.complete ℝ X
  intro a
  let R := Generated A a
  letI : FiniteDimensional ℝ R :=
    inferInstanceAs (FiniteDimensional ℝ ↥(generated S u a))
  have ha : a ∈ generated S u a := by
    have h : npow S u a 1 ∈ generated S u a :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
    simpa only [npow, A.symm a u, A.unit_mul] using h
  let ar : R := ⟨a, ha⟩
  obtain ⟨n, e, r, hid, hunit, hlin, hsq⟩ := commutative_spectral ar
  let inc : R →ₗ[ℝ] X := (generated S u a).subtype
  refine ⟨n, fun i => inc (e i), r, ?_, ?_, ?_, ?_⟩
  · intro i
    exact congrArg inc (hid i)
  · simpa only [map_sum] using congrArg inc hunit
  · simpa only [map_sum, map_smul] using congrArg inc hlin
  · simpa only [map_sum, map_smul] using congrArg inc hsq

#print axioms finite_spectral_resolutions

end D5.S3.Topology.JBFiniteSpectral

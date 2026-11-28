/- GID: D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CosetActions/TwistedGradedCorner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nondegenerate inverse-degree products force one-dimensional saturated grades. -/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OmegaBuild.Commands

/-!
The homogeneous spanning argument comes from Davydov–Simmons, *On Lagrangian algebras in
group-theoretical modular categories*, [Lemma 2.14](https://arxiv.org/abs/1603.04650).
Here the grading group is fixed in advance. Equality of the total dimension with its order
then forces every grade to occur.
-/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.FiniteGroups.CosetActions.TwistedGradedCorner

open scoped BigOperators

variable {K B : Type*} [Group K] [AddCommGroup B] [Module ℂ B]
variable {grade : K → Submodule ℂ B} {μ : B →ₗ[ℂ] B →ₗ[ℂ] B} {e : B}
variable {α : K → K → K → ℂˣ}

section Multiplication

variable (mul_mem : ∀ {g h : K} {x y : B},
  x ∈ grade g → y ∈ grade h → μ x y ∈ grade (g * h))
variable (unit_grade : grade 1 = Submodule.span ℂ {e})
variable (pairing : ∀ {g : K} {x : B}, x ∈ grade g → x ≠ 0 →
  ∃ y ∈ grade g⁻¹, μ x y ≠ 0)
variable (twisted_assoc : ∀ {g h k : K} {x y z : B},
  x ∈ grade g → y ∈ grade h → z ∈ grade k →
    (α g h k : ℂ) • μ (μ x y) z = μ x (μ y z))
variable (left_unit : ∀ x : B, μ e x = x) (right_unit : ∀ x : B, μ x e = x)

include mul_mem unit_grade pairing in
private theorem exists_inverse_product {g : K} {x : B} (hx : x ∈ grade g) (hx₀ : x ≠ 0) :
    ∃ y ∈ grade g⁻¹, ∃ t : ℂ, t ≠ 0 ∧ μ x y = t • e := by
  obtain ⟨y, hy, hxy⟩ := pairing hx hx₀
  have hmem : μ x y ∈ grade 1 := by simpa only [mul_inv_cancel] using mul_mem hx hy
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (unit_grade ▸ hmem)
  refine ⟨y, hy, t, ?_, ht.symm⟩
  intro ht₀
  exact hxy (by rw [← ht, ht₀, zero_smul])

include mul_mem unit_grade pairing twisted_assoc left_unit right_unit in
/-- Any nonzero homogeneous vector spans its grade. -/
theorem grade_eq_span_singleton {g : K} {a : B} (ha : a ∈ grade g) (ha₀ : a ≠ 0) :
    grade g = Submodule.span ℂ {a} := by
  obtain ⟨b, hb, t, ht₀, hab⟩ := exists_inverse_product mul_mem unit_grade pairing ha ha₀
  apply le_antisymm _ ((Submodule.span_singleton_le_iff_mem _ _).mpr ha)
  intro c hc
  have hbc_mem : μ b c ∈ grade 1 := by simpa only [inv_mul_cancel] using mul_mem hb hc
  obtain ⟨u, hbc⟩ := Submodule.mem_span_singleton.mp (unit_grade ▸ hbc_mem)
  have h := twisted_assoc ha hb hc
  rw [hab, map_smul, LinearMap.smul_apply, left_unit, ← hbc, map_smul, right_unit, smul_smul] at h
  have hs : (↑(α g g⁻¹ g) : ℂ) * t ≠ 0 := mul_ne_zero (Units.ne_zero _) ht₀
  have hsmul : ((↑(α g g⁻¹ g) : ℂ) * t) • c ∈ Submodule.span ℂ {a} :=
    Submodule.mem_span_singleton.mpr ⟨u, h.symm⟩
  exact (Submodule.smul_mem_iff _ hs).mp hsmul

include mul_mem unit_grade pairing twisted_assoc right_unit in
/-- Multiplication of two nonzero homogeneous vectors gives a nonzero vector. -/
theorem homogeneous_mul_ne_zero {g h : K} {x y : B}
    (hx : x ∈ grade g) (hy : y ∈ grade h) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) : μ x y ≠ 0 := by
  obtain ⟨z, hz, t, ht₀, hyz⟩ := exists_inverse_product mul_mem unit_grade pairing hy hy₀
  intro hxy
  have h := twisted_assoc hx hy hz
  rw [hxy, map_zero, LinearMap.zero_apply, smul_zero, hyz, map_smul, right_unit] at h
  exact smul_ne_zero ht₀ hx₀ h.symm

include mul_mem unit_grade pairing twisted_assoc left_unit right_unit in
/-- Under the inverse-degree pairing and twisted associativity hypotheses, an
internal grading of total dimension `|K|` has a line in every degree. -/
theorem finrank_grade_eq_one [Fintype K] [DecidableEq K]
    (decomposition : DirectSum.IsInternal grade) (dimension : Module.finrank ℂ B = Fintype.card K)
    (g : K) : Module.finrank ℂ (grade g) = 1 := by
  have : FiniteDimensional ℂ B := Module.finite_of_finrank_pos (by
    rw [dimension]
    exact Fintype.card_pos)
  have hle (h : K) : Module.finrank ℂ (grade h) ≤ 1 := by
    by_cases hbot : grade h = ⊥
    · rw [hbot, finrank_bot]
      exact Nat.zero_le _
    · obtain ⟨a, ha, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      rw [grade_eq_span_singleton mul_mem unit_grade pairing twisted_assoc left_unit right_unit
        ha ha₀, finrank_span_singleton ha₀]
  have hsum : (∑ h : K, Module.finrank ℂ (grade h)) = Fintype.card K := by
    rw [← Module.finrank_directSum, (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap grade) decomposition).finrank_eq, dimension]
  by_contra hne
  have hlt : (∑ h : K, Module.finrank ℂ (grade h)) < ∑ _ : K, (1 : ℕ) :=
    Finset.sum_lt_sum (fun h _ => hle h) ⟨g, Finset.mem_univ g, (hle g).lt_of_ne hne⟩
  simp [hsum] at hlt

end Multiplication

#print axioms grade_eq_span_singleton
#print axioms homogeneous_mul_ne_zero
#print axioms finrank_grade_eq_one

end D5.S3.FiniteGroups.CosetActions.TwistedGradedCorner

/- GID: D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover
   generality: I
   mirror-B: D5/B/S3/Quantum/Masking/HyperdiskRegularSubsetCover
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.claim; result=D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.result; claim=D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.claim
   digest: A regular subset of a four-dimensional hyperdisk has no finite hyperdisk cover. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Ding and Hu, arXiv:1909.11256v3, Definitions 1 and 4 and the second open
question in the conclusion. Pure states are unit vectors, including their global
phases. A cover consists of hyperdisks contained in the regular subset. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover

/-- The full coefficient-modulus level set of unit vectors in the source definition. -/
def IsHyperdisk {n : ℕ} (s : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∃ (m : ℕ) (φ : Fin m → EuclideanSpace ℂ (Fin n)) (r : Fin m → ℝ),
    Orthonormal ℂ φ ∧ Submodule.span ℂ (Set.range φ) = Submodule.span ℂ s ∧
      (∀ j, 0 < r j) ∧ s = {ψ | ‖ψ‖ = 1 ∧ ∀ j, ‖⟪φ j, ψ⟫_ℂ‖ = r j}

/-- Definition 4: intersection with the linear span of the subset. -/
def IsRegularSubset {n : ℕ} (c s : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  IsHyperdisk s ∧ ((Submodule.span ℂ c : Set _) ∩ s = c)

/-- The finite-cover question for regular subsets of hyperdisks. -/
def claim : Prop :=
  ∀ (n : ℕ) (s c : Set (EuclideanSpace ℂ (Fin n))), IsRegularSubset c s →
    ∃ (k : ℕ) (h : Fin k → Set (EuclideanSpace ℂ (Fin n))),
      (∀ i, IsHyperdisk (h i) ∧ h i ⊆ c) ∧ c = ⋃ i, h i

private def radii : Fin 4 → ℝ := fun j => ![1, 2, 3, 4] j / Real.sqrt 30

private def constraint : EuclideanSpace ℂ (Fin 4) →ₗ[ℂ] ℂ where
  toFun x := 6 * x 0 + 3 * x 1 + 2 * x 2 + 3 * x 3
  map_add' x y := by simp only [PiLp.add_apply]; ring
  map_smul' a x := by simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def ambient : Set (EuclideanSpace ℂ (Fin 4)) :=
  {x | ‖x‖ = 1 ∧ ∀ j, ‖x j‖ = radii j}

private def counterexample : Set (EuclideanSpace ℂ (Fin 4)) :=
  (LinearMap.ker constraint : Set _) ∩ ambient

private def parameter (a : ℕ) : ℝ := -1 / 2 - 1 / (4 * ((a : ℝ) + 1))

private def phases (t : ℝ) : Fin 4 → ℂ :=
  let z : ℂ := (t : ℂ) + Complex.I * (Real.sqrt (1 - t ^ 2) : ℂ)
  let w : ℂ := -2 - z
  let q : ℝ := 5 + 4 * t
  let k : ℂ := (Real.sqrt ((4 - q) / q) : ℂ)
  ![z, w * (1 + Complex.I * k) / 2, w * (1 - Complex.I * k) / 2, 1]

private def family (a : ℕ) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun j => (radii j : ℂ) * phases (parameter a) j)

private lemma radii_pos (j : Fin 4) : 0 < radii j := by
  sorry

private lemma coordinate_norm (x : EuclideanSpace ℂ (Fin 4))
    (hx : ∀ j, ‖x j‖ = radii j) : ‖x‖ = 1 := by
  sorry

private lemma ambient_span : Submodule.span ℂ ambient = ⊤ := by
  sorry

private lemma ambient_hyperdisk : IsHyperdisk ambient := by
  refine ⟨4, fun j => EuclideanSpace.single j 1, radii,
    EuclideanSpace.orthonormal_single, ?_, radii_pos, ?_⟩
  · sorry
  · ext x
    simp only [ambient, Set.mem_setOf_eq, EuclideanSpace.inner_single_left,
      map_one, one_mul]

private lemma regular : IsRegularSubset counterexample ambient := by
  refine ⟨ambient_hyperdisk, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨(Submodule.span_le.mpr (fun y hy => hy.1)) hx.1, hx.2⟩
  · intro x hx
    exact ⟨Submodule.subset_span hx, hx.2⟩

private lemma parameter_bounds (a : ℕ) : -(3 : ℝ) / 4 ≤ parameter a ∧
    parameter a ≤ -(1 : ℝ) / 2 := by
  sorry

private lemma phases_unit (t : ℝ) (ht : -(3 : ℝ) / 4 ≤ t ∧ t ≤ -(1 : ℝ) / 2) :
    (∀ j, ‖phases t j‖ = 1) ∧
      phases t 0 + phases t 1 + phases t 2 + 2 * phases t 3 = 0 := by
  sorry

private lemma family_mem (a : ℕ) : family a ∈ counterexample := by
  sorry

private lemma family_ray_injective (a b : ℕ) (u : ℂ)
    (h : family a = u • family b) : a = b := by
  sorry

private lemma constant_modulus {m : ℕ} (a : Fin m → ℂ) (r : ℝ)
    (h : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) → ‖∑ p, a p * u p‖ = r) :
    ∀ p q, p ≠ q → a p = 0 ∨ a q = 0 := by
  sorry

private lemma phase_state {m : ℕ} (φ : Fin m → EuclideanSpace ℂ (Fin 4))
    (r : Fin m → ℝ) (ho : Orthonormal ℂ φ) (hr : ∀ p, 0 < r p)
    (x : EuclideanSpace ℂ (Fin 4)) (hx : ‖x‖ = 1)
    (hcoeff : ∀ p, ‖⟪φ p, x⟫_ℂ‖ = r p)
    (hspan : x ∈ Submodule.span ℂ (Set.range φ))
    (u : Fin m → ℂ) (hu : ∀ p, ‖u p‖ = 1) :
    ‖∑ p, ((r p : ℂ) * u p) • φ p‖ = 1 ∧
      ∀ p, ‖⟪φ p, ∑ q, ((r q : ℂ) * u q) • φ q⟫_ℂ‖ = r p := by
  sorry

private lemma disjoint_generators {m : ℕ}
    (φ : Fin m → EuclideanSpace ℂ (Fin 4)) (r : Fin m → ℝ)
    (ho : Orthonormal ℂ φ) (hr : ∀ p, 0 < r p)
    (hs : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) →
      (∑ p, ((r p : ℂ) * u p) • φ p) ∈ counterexample) :
    ∀ j p q, p ≠ q → φ p j = 0 ∨ φ q j = 0 := by
  sorry

private lemma block_obstruction {m : ℕ}
    (φ : Fin m → EuclideanSpace ℂ (Fin 4)) (r : Fin m → ℝ)
    (ho : Orthonormal ℂ φ) (hr : ∀ p, 0 < r p)
    (hd : ∀ j p q, p ≠ q → φ p j = 0 ∨ φ q j = 0)
    (hs : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) →
      (∑ p, ((r p : ℂ) * u p) • φ p) ∈ counterexample) : m ≤ 1 := by
  sorry

private lemma hyperdisk_single_ray (h : Set (EuclideanSpace ℂ (Fin 4)))
    (hh : IsHyperdisk h) (hc : h ⊆ counterexample)
    (x : EuclideanSpace ℂ (Fin 4)) (hx : x ∈ h)
    (y : EuclideanSpace ℂ (Fin 4)) (hy : y ∈ h) : ∃ u : ℂ, x = u • y := by
  sorry

/-- The registered four-coordinate regular subset refutes the finite-cover question. -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨k, h, hh, hcover⟩ := hclaim 4 ambient counterexample regular
  have hmem (a : ℕ) : ∃ i, family a ∈ h i := by
    have ha := family_mem a
    rw [hcover] at ha
    exact Set.mem_iUnion.mp ha
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨u, hu⟩ := hyperdisk_single_ray (h (f a)) (hh (f a)).1 (hh (f a)).2
      (family a) (hf a) (family b) (hab ▸ hf b)
    exact family_ray_injective a b u hu
  haveI : Finite ℕ := Finite.of_injective f hinj
  exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) Set.finite_univ

end D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover

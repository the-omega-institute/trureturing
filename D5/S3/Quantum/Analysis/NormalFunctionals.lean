/- GID: D5/S3/Quantum/Analysis/NormalFunctionals
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NormalFunctionals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The closed Banach subspace of arbitrary-directed order-normal functionals. -/

/-
admission_basis: escape-witness
escape_witness: isClosed_setOf_isOrderNormal
isClosed_setOf_isOrderNormal: proof_shape: content; consumer: normalDual_completeSpace,
  NormalL1Realization.exists_normal_L1_extension through its Banach codomain.
isOrderNormal_of_domination: proof_shape: content; consumer:
  NormalL1Realization.continuous_normal_of_unit.
normal_zero, normal_add, normal_smul: consumed subspace-construction helpers.
utility none: arbitrary-space analytic closure and domination, without a finite
certificate, enumeration, numerical checker or bounded reduction.
-/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Tactic

/-! # Arbitrary-directed order-normal continuous functionals -/

noncomputable section

open Set
open scoped ComplexOrder

namespace D5.S3.Quantum.Analysis.NormalFunctionals

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]

/-- Normality along every nonempty upward-directed set of positive elements
having an actual least upper bound. The estimate holds on an entire tail. -/
def IsOrderNormal (φ : StrongDual ℂ A) : Prop :=
  ∀ (s : Set A) (a : A), s.Nonempty → DirectedOn (· ≤ ·) s →
    (∀ x ∈ s, 0 ≤ x) → IsLUB s a →
    ∀ ε : ℝ, 0 < ε → ∃ b ∈ s, ∀ x ∈ s, b ≤ x → ‖φ (a - x)‖ < ε

private theorem normal_zero : IsOrderNormal (0 : StrongDual ℂ A) := by
  intro s a hs _ _ _ ε hε
  obtain ⟨b, hb⟩ := hs
  exact ⟨b, hb, by simpa using fun x (_ : x ∈ s) (_ : b ≤ x) => hε⟩

private theorem normal_add {φ ψ : StrongDual ℂ A}
    (hφ : IsOrderNormal φ) (hψ : IsOrderNormal ψ) : IsOrderNormal (φ + ψ) := by
  intro s a hs hd hp ha ε hε
  obtain ⟨b, hb, hbt⟩ := hφ s a hs hd hp ha (ε / 2) (by positivity)
  obtain ⟨c, hc, hct⟩ := hψ s a hs hd hp ha (ε / 2) (by positivity)
  obtain ⟨d, hdmem, hbd, hcd⟩ := hd b hb c hc
  refine ⟨d, hdmem, ?_⟩
  intro x hx hdx
  exact (norm_add_le _ _).trans_lt (by
    simpa using add_lt_add (hbt x hx (hbd.trans hdx)) (hct x hx (hcd.trans hdx)))

private theorem normal_smul (z : ℂ) {φ : StrongDual ℂ A}
    (hφ : IsOrderNormal φ) : IsOrderNormal (z • φ) := by
  intro s a hs hd hp ha ε hε
  obtain ⟨b, hb, hbt⟩ := hφ s a hs hd hp ha (ε / (‖z‖ + 1)) (by positivity)
  refine ⟨b, hb, ?_⟩
  intro x hx hbx
  change ‖z • φ (a - x)‖ < ε
  rw [norm_smul]
  have ht := hbt x hx hbx
  have hh := (lt_div_iff₀ (by positivity : 0 < ‖z‖ + 1)).mp ht
  nlinarith [norm_nonneg (φ (a - x))]

/-- The actual complex subspace of the continuous dual defined by order-normality. -/
def normalDual : Submodule ℂ (StrongDual ℂ A) where
  carrier := {φ | IsOrderNormal φ}
  zero_mem' := normal_zero
  add_mem' := normal_add
  smul_mem' := normal_smul

variable [StarOrderedRing A]

/-- Dual-norm limits preserve arbitrary-directed order-normality. -/
theorem isClosed_setOf_isOrderNormal :
    IsClosed {φ : StrongDual ℂ A | IsOrderNormal φ} := by
  rw [← closure_subset_iff_isClosed]
  intro φ hφ s a hs hd hp ha ε hε
  obtain ⟨ψ, hψ, hdist⟩ := Metric.mem_closure_iff.mp hφ
    (ε / (2 * (‖a‖ + 1))) (by positivity)
  obtain ⟨b, hb, hbt⟩ := hψ s a hs hd hp ha (ε / 2) (by positivity)
  refine ⟨b, hb, ?_⟩
  intro x hx hbx
  have hxa : x ≤ a := ha.1 hx
  have hnorm : ‖a - x‖ ≤ ‖a‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self a (hp x hx))
      (sub_nonneg.mpr hxa)
  have hdif : ‖φ - ψ‖ * (2 * (‖a‖ + 1)) < ε := by
    rw [dist_eq_norm] at hdist
    exact (lt_div_iff₀ (by positivity)).mp hdist
  calc
    ‖φ (a - x)‖ = ‖(φ - ψ) (a - x) + ψ (a - x)‖ := by simp
    _ ≤ ‖(φ - ψ) (a - x)‖ + ‖ψ (a - x)‖ := norm_add_le _ _
    _ ≤ ‖φ - ψ‖ * ‖a‖ + ‖ψ (a - x)‖ := by
      gcongr
      exact ((φ - ψ).le_opNorm _).trans (by gcongr)
    _ < ε := by
      have ht := hbt x hx hbx
      nlinarith [norm_nonneg (φ - ψ)]

/-- The restricted dual norm makes the normal-functional space complete. -/
instance normalDual_completeSpace : CompleteSpace (normalDual (A := A)) :=
  isClosed_setOf_isOrderNormal.completeSpace_coe

/-- Positive domination preserves normality, including zero domination constants. -/
theorem isOrderNormal_of_domination (S : StrongDual ℂ A) (hS : IsOrderNormal S)
    (c : ℝ) (hc : 0 ≤ c) (φ : StrongDual ℂ A)
    (hφ : ∀ a : A, 0 ≤ a → 0 ≤ φ a ∧ φ a ≤ (c : ℂ) * S a) :
    IsOrderNormal φ := by
  intro s a hs hd hp ha ε hε
  obtain ⟨b, hb, hbt⟩ := hS s a hs hd hp ha (ε / (c + 1)) (by positivity)
  refine ⟨b, hb, ?_⟩
  intro x hx hbx
  have hax : 0 ≤ a - x := sub_nonneg.mpr (ha.1 hx)
  have hv := hφ (a - x) hax
  have hle : ‖φ (a - x)‖ ≤ c * ‖S (a - x)‖ := by
    have hr := (Complex.le_def.mp hv.2).1
    have hn := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hv.1)
    simp only [Complex.ofReal_re] at hn
    rw [← hn]
    calc
      _ ≤ ((c : ℂ) * S (a - x)).re := hr
      _ = c * (S (a - x)).re := by simp
      _ ≤ c * ‖S (a - x)‖ := mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hc
  have ht := (lt_div_iff₀ (by positivity : 0 < c + 1)).mp (hbt x hx hbx)
  nlinarith [norm_nonneg (S (a - x))]

#print axioms isClosed_setOf_isOrderNormal
#print axioms isOrderNormal_of_domination

end D5.S3.Quantum.Analysis.NormalFunctionals

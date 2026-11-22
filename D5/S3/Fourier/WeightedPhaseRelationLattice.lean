/- GID: D5/S3/Fourier/WeightedPhaseRelationLattice
   generality: G
   mirror-B: D5/B/S3/Fourier/WeightedPhaseRelationLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Fourier/TorusOrbitClosure]
   utility: none
   digest: The complete integer relation lattice controls weighted common-time phase deficit. -/

import D5.S3.Fourier.TorusOrbitClosure
import Mathlib.Analysis.Real.Cardinality

/-! The real-time phase orbit closure is the annihilator of its integer relations. -/

open Set
open scoped BigOperators

namespace D5.S3.Fourier.WeightedPhaseRelationLattice

private theorem exists_nonresonant_step {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ s ∈ Ioo (0 : ℝ) 1, ∀ (k : J → ℤ) (m : ℤ),
      (∑ j, (k j : ℝ) * γ j) * s = (m : ℝ) * (2 * Real.pi) →
        (∑ j, (k j : ℝ) * γ j) = 0 := by
  let dot (k : J → ℤ) : ℝ := ∑ j, (k j : ℝ) * γ j
  let bad : (J → ℤ) × ℤ → ℝ := fun p => (p.2 : ℝ) * (2 * Real.pi) / dot p.1
  have hcount : (range bad).Countable := countable_range bad
  have hnot : ¬ Ioo (0 : ℝ) 1 ⊆ range bad := by
    intro hsub
    exact (not_le_of_gt zero_lt_one) (Cardinal.Real.Ioo_countable_iff.mp (hcount.mono hsub))
  obtain ⟨s, hs, hgood⟩ := not_subset.mp hnot
  refine ⟨s, hs, fun k m h => ?_⟩
  by_contra hne
  apply hgood
  refine ⟨(k, m), ?_⟩
  change (m : ℝ) * (2 * Real.pi) / dot k = s
  exact (div_eq_iff hne).2 (by simpa [dot, mul_comm s] using h.symm)

private theorem circle_character_exp {J : Type*} [Fintype J] (k : J → ℤ) (θ : J → ℝ) :
    (∏ j, Circle.exp (θ j) ^ k j) = Circle.exp (∑ j, (k j : ℝ) * θ j) := by
  simp_rw [← Circle.exp_intCast_mul]
  exact (map_sum Circle.expHom _ _).symm

private theorem mem_closure_real_phase_orbit {J : Type*} [Fintype J]
    (γ : J → ℝ) (z : J → Circle) :
    z ∈ closure (range (fun (t : ℝ) (j : J) => Circle.exp (γ j * t))) ↔
      ∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 → (∏ j, z j ^ k j) = 1 := by
  let orbit (t : ℝ) (j : J) := Circle.exp (γ j * t)
  change z ∈ closure (range orbit) ↔ _
  have hchar (k : J → ℤ) (t : ℝ) :
      (∏ j, orbit t j ^ k j) = Circle.exp ((∑ j, (k j : ℝ) * γ j) * t) := by
    simp only [orbit, circle_character_exp, ← mul_assoc, ← Finset.sum_mul]
  constructor
  · intro hz k hk
    have hc : Continuous (fun w : J → Circle => ∏ j, w j ^ k j) := by
      exact continuous_finsetProd _ fun j _ => (continuous_apply j).zpow (k j)
    apply closure_minimal (t := {w | (∏ j, w j ^ k j) = 1}) ?_
      (isClosed_eq hc continuous_const) hz
    rintro _ ⟨t, rfl⟩
    change (∏ j, orbit t j ^ k j) = 1
    rw [hchar, hk, zero_mul, Circle.exp_zero]
  · intro hz
    obtain ⟨s, _, hs⟩ := exists_nonresonant_step γ
    have hd : z ∈ closure (range (fun n : ℕ => orbit s ^ n)) := by
      apply (D5.S3.Fourier.TorusOrbitClosure.result (orbit s) z).2
      intro k hk
      rw [hchar] at hk
      obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hk
      exact hz k (hs k m hm)
    refine closure_mono ?_ hd
    rintro _ ⟨n, rfl⟩
    refine ⟨(n : ℝ) * s, ?_⟩
    funext j
    change Circle.exp (γ j * ((n : ℝ) * s)) = Circle.exp (γ j * s) ^ n
    rw [mul_left_comm, Circle.exp_natCast_mul]

/-- The real-time orbit closure is the common kernel of exactly the zero-dot-product
integer characters. -/
theorem closure_real_phase_orbit {J : Type*} [Fintype J] (γ : J → ℝ) :
    closure (range (fun (t : ℝ) (j : J) => Circle.exp (γ j * t))) =
      {p | ∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 → (∏ j, p j ^ k j) = 1} := by
  ext p
  exact mem_closure_real_phase_orbit γ p

#print axioms closure_real_phase_orbit

end D5.S3.Fourier.WeightedPhaseRelationLattice

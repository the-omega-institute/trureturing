/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The faithful GHZ--Mermin minimum is the exact Staircase for every n >= 3. -/
/-
proof_shape: result: content
escape_witness: qFree_walsh_square, parity_fiber_cancellation and finite_overlap_lower_bound lie on the live upper/lower-bound proof paths.
admission_basis: open-problem-resolution (#13111; Proved)
Direct frozen dependencies: none.
Same-delivery content dependencies: odd_construction, even_construction, staircase_lower.
The transitive frozen closure uses DataProcessing.total_variation_channel_le.
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.QuantumBounds.MerminMeasurementDependence.Construction

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.QuantumBounds.MerminMeasurementDependence.AlaiStaircase
open D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section

def classicalS (n : ℕ) : ℝ := ((ratio n : ℝ)+1)/(2*(ratio n : ℝ))

def attainableF (n : ℕ) : Set ℝ :=
  {z | ∃ rho : Setting n → Strategy n → ℝ, Faithful rho ∧ F rho=z}

def Fmin (n : ℕ) : ℝ := sInf (attainableF n)

def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    Fmin n = (ratio n : ℝ)/(2*((ratio n : ℝ)+1)) ∧
    Fmin n = 1/(4*classicalS n) ∧ Fmin n*classicalS n=1/4 ∧
    (∃ rho : Setting n → Strategy n → ℝ, Faithful rho ∧ F rho=Fmin n) ∧
    (∀ rho : Setting n → Strategy n → ℝ, Faithful rho → Fmin n ≤ F rho)

theorem result : claim := by
  intro n hn
  obtain ⟨k,hk,he⟩ : ∃ k : ℕ, 1 ≤ k ∧ (n=2*k+1 ∨ n=2*k+2) := by
    refine ⟨(n-1)/2,?_,?_⟩ <;> omega
  have hatt : ∃ rho : Setting n → Strategy n → ℝ, Faithful rho ∧ F rho=floorValue n := by
    rcases he with he | he
    · subst n
      exact odd_construction k hk
    · subst n
      exact even_construction k hk
  obtain ⟨rho,hfaith,hF⟩ := hatt
  have hbound := staircase_lower n hn
  have hmem : floorValue n ∈ attainableF n := ⟨rho,hfaith,hF⟩
  have hbelow : ∀ z ∈ attainableF n, floorValue n ≤ z := by
    rintro z ⟨p,hp,rfl⟩
    exact hbound p hp
  have hbdd : BddBelow (attainableF n) := ⟨floorValue n,hbelow⟩
  have hne : (attainableF n).Nonempty := ⟨floorValue n,hmem⟩
  have hmin : Fmin n=floorValue n :=
    le_antisymm (csInf_le hbdd hmem) (le_csInf hne hbelow)
  have hR : (ratio n : ℝ) ≠ 0 := by unfold ratio;positivity
  have hR1 : (ratio n : ℝ)+1 ≠ 0 := by unfold ratio;positivity
  refine ⟨hmin,?_,?_,⟨rho,hfaith,hF.trans hmin.symm⟩,?_⟩
  · rw [hmin]
    unfold floorValue classicalS
    field_simp
    ring
  · rw [hmin]
    unfold floorValue classicalS
    field_simp
    ring
  · intro p hp
    rw [hmin]
    exact hbound p hp
end
end D5.S3.QuantumBounds.MerminMeasurementDependence.AlaiStaircase

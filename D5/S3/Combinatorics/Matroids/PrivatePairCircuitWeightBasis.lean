/- GID: D5/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Private pairs give distinct zero-weight intersections for overlapping faces. -/

module

public import D5.S3.Combinatorics.Matroids.MembershipCircuitWeightBasis

/-! Simultaneous weight coordinates for faces with private pairs. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PrivatePairCircuitWeightBasis

open Finset MembershipCircuitWeightBasis

set_option autoImplicit false

/-- If every face has two distinct indices belonging to no other face, an
integral change of basis preserves all faces and the pivot while separating
the faces by their intersections with the zero-weight indices. -/
theorem exists_private_pair_weight_basis {I J : Type*} [Finite I] [DecidableEq I]
    (F : J → Finset I) (root : I) (hroot : ∀ t, root ∉ F t)
    (hprivate : ∀ t, ∃ i ∈ F t, ∃ j ∈ F t, i ≠ j ∧
      ∀ s ≠ t, i ∉ F s ∧ j ∉ F s)
    (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) :
    ∃ (b : Module.Basis I ℤ (I → ℤ)) (w : I → ℕ) (A : Finset I),
      (∀ i, b.equivFun (fun j => (weight j : ℤ)) i = (w i : ℤ)) ∧
      (∀ i ∈ A, w i = 0) ∧ root ∉ A ∧ Function.Injective (fun t => F t ∩ A) ∧
      (∀ t, ∀ i ∈ F t, ∀ j ∉ F t, b i j = 0 ∧ b.equivFun (Pi.single i 1) j = 0) ∧
      (∀ j ≠ root, b.equivFun (Pi.single root 1) j = 0) := by
  classical
  refine exists_membership_separating_weight_basis F root hroot ?_ weight hweight
  intro s t hne
  obtain ⟨i, hi, j, hj, hij, hother⟩ := hprivate s
  refine ⟨i, j, hij, ?_, Or.inl ⟨hi, (hother t hne.symm).1⟩⟩
  intro u
  by_cases hu : u = s
  · subst u
    simp [hi, hj]
  · obtain ⟨hiU, hjU⟩ := hother u hu
    simp [hiU, hjU]

end D5.S3.Combinatorics.Matroids.PrivatePairCircuitWeightBasis

/- GID: D5/S3/QuadraticForms/AxialInnerLieConverseRefutation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/AxialInnerLieConverseRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/AxialInnerLieConverseRefutation.claim; result=D5/S3/QuadraticForms/AxialInnerLieConverseRefutation.result; claim=D5/S3/QuadraticForms/AxialInnerLieConverseRefutation.claim
   digest: A primitive axial algebra with a proper scalar ideal has simple selected-axis inner Lie algebra. -/

/- proof_shape: result: content
   admission_basis: open-problem-resolution (issue #35124)
   escape_witness: actual eigenspaces and both inclusions of the selected-axis Lie span
   Direct frozen dependencies: OrthogonalLieStructure, LieRadicalTransfer. -/

import D5.S3.QuadraticForms.OrthogonalLieStructure
import OmegaMath.Algebra.RationalSpinFactor
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
The converse in Gorshkov–Shpectorov, Problem 3.20 (journal Problem 2.20).
The rational spin factor with three vector coordinates has a scalar direct
summand adjoined as an additional axis. The literal selected-axis Lie span is
the zero extension of the standard orthogonal Lie algebra acting on the vector
coordinates.

The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

open scoped Matrix
open LieAlgebra
open OmegaMath.RationalSpinFactor
open D5.S3.QuadraticForms

namespace D5.S3.QuadraticForms.AxialInnerLieConverseRefutation

variable {n : Type*} [Fintype n]

private theorem scalar_ideal :
    let I : Submodule ℚ (B n) := ℚ ∙ z
    (∀ a x, x ∈ I → left a x ∈ I) ∧ I ≠ ⊥ ∧ I ≠ ⊤ := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a.2 * t, ?_⟩
    change (a.2 * t) • z = product a (t • (z : B n))
    simp [z, product]
  · intro h
    have hz : (z : B n) ∈ (⊥ : Submodule ℚ (B n)) :=
      h ▸ Submodule.mem_span_singleton_self z
    have hz' := congrArg Prod.snd ((Submodule.mem_bot ℚ).mp hz)
    norm_num [z] at hz'
  · intro h
    have hu : (unitSpin : B n) ∈ ℚ ∙ z := h.symm ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu
    have ht' := congrArg (fun x : B n => x.1.1) ht
    norm_num [z, unitSpin] at ht'

private theorem simple_selected : IsSimple ℚ (selectedLie left (chosen : Set (B (Fin 3)))) := by
  let : IsSimple ℚ (Orthogonal.so (Fin 3) ℚ) :=
    OrthogonalLieStructure.isSimple_of_card_ne_four (by decide) (by decide)
  exact LieRadicalTransfer.isSimple_of_equiv chosenLieEquiv

/-- The finite-dimensional rational primitive Jordan-half instance of the
printed universal converse. In the universal assertion take the field to be
`ℚ`, the fusion law to be Jordan half, and the chosen generating axes to be
`X`. The eigenspaces used here are independent by
`Module.End.eigenspaces_iSupIndep`. Closure under all left multiplications is
the ideal condition by commutativity. -/
def claim : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℚ A] [FiniteDimensional ℚ A]
    (L : A →ₗ[ℚ] Module.End ℚ A) (X : Set A),
    (∀ a b, L a b = L b a) → (∀ a ∈ X, IsAxis L a) → Generates L X →
      IsSimple ℚ (selectedLie L X) → AlgebraSimple L

theorem result : ¬ claim := by
  intro h
  have simple := h (B (Fin 3)) left chosen product_comm chosen_axes chosen_generates simple_selected
  obtain ⟨hI, hbot, htop⟩ := (scalar_ideal (n := Fin 3))
  exact (simple _ hI).elim hbot htop

end D5.S3.QuadraticForms.AxialInnerLieConverseRefutation

/- GID: D5/S3/Quantum/Matrix/CrossSpeciesConsensus
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CrossSpeciesConsensus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared irreducibility makes equivariant Hermitian observables real scalar matrices. -/

import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Matrix.CrossSpeciesConsensus

variable {G n : Type*} [Group G] [Fintype n] [DecidableEq n]

/-- The linear representation induced by the supplied common matrix action. -/
def matrixRepresentation (U : G →* Matrix n n ℂ) : Representation ℂ G (n → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp U

/-- Conditional Schur theorem: irreducibility and equivariance are explicit hypotheses. -/
theorem equivariant_selfAdjoint_eq_smul_id_of_irreducible
    (U : G →* Matrix n n ℂ)
    (h_irreducible : Representation.IsIrreducible (matrixRepresentation U))
    (A : Matrix n n ℂ) (h_selfAdjoint : A.IsHermitian)
    (h_equivariant : ∀ g : G, A * U g = U g * A) :
    ∃ r : ℝ, A = (r : ℂ) • (1 : Matrix n n ℂ) := by
  classical
  let ρ := matrixRepresentation U
  let f : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := Matrix.toLinAlgEquiv' A
      isIntertwining' := fun g => by
        change Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' (U g) =
          Matrix.toLinAlgEquiv' (U g) * Matrix.toLinAlgEquiv' A
        simpa only [map_mul] using congrArg Matrix.toLinAlgEquiv' (h_equivariant g) }
  haveI : Representation.IsIrreducible ρ := h_irreducible
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  have h_linear : c • (1 : Module.End ℂ (n → ℂ)) = Matrix.toLinAlgEquiv' A := by
    exact congrArg Representation.IntertwiningMap.toLinearMap hc
  have h_scalar : c • (1 : Matrix n n ℂ) = A := by
    apply Matrix.toLinAlgEquiv'.injective
    simpa only [map_smul, map_one] using h_linear
  rcases isEmpty_or_nonempty n with h_empty | h_nonempty
  · exact ⟨0, Subsingleton.elim _ _⟩
  · obtain ⟨i⟩ := h_nonempty
    have hc_real : star c = c := by
      simpa only [← h_scalar, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        using h_selfAdjoint.apply i i
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hc_real
    exact ⟨r, by rw [← h_scalar, hr]⟩

/-- Every trace-one probe has the same real reading of the common equivariant observable. -/
theorem cross_species_consensus {Species : Type*}
    (U : G →* Matrix n n ℂ)
    (h_irreducible : Representation.IsIrreducible (matrixRepresentation U))
    (A : Matrix n n ℂ) (h_selfAdjoint : A.IsHermitian)
    (h_equivariant : ∀ g : G, A * U g = U g * A)
    (probe : Species → Matrix n n ℂ)
    (h_normalized : ∀ s, Matrix.trace (probe s) = 1) :
    ∃ r : ℝ, A = (r : ℂ) • (1 : Matrix n n ℂ) ∧
      (∀ s, (Matrix.trace (probe s * A)).re = r) ∧
      ∀ s t, (Matrix.trace (probe s * A)).re = (Matrix.trace (probe t * A)).re := by
  obtain ⟨r, hA⟩ := equivariant_selfAdjoint_eq_smul_id_of_irreducible
    U h_irreducible A h_selfAdjoint h_equivariant
  have h_reading (s : Species) : (Matrix.trace (probe s * A)).re = r := by
    rw [hA, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, h_normalized s]
    simp
  exact ⟨r, hA, h_reading, fun s t => (h_reading s).trans (h_reading t).symm⟩

end D5.S3.Quantum.Matrix.CrossSpeciesConsensus

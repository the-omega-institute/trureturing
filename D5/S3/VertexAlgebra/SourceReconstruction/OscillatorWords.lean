/- GID: D5/S3/VertexAlgebra/SourceReconstruction/OscillatorWords
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceReconstruction/OscillatorWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-charge original source generation by finite oscillator occurrence words. -/

import D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeAllStateField LatticeAllStateReconstruction
open LatticeHalfFockOriginalMixedIterate LatticeHalfFockAllStateCurrentCommutator
open MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

def unitCurrent (D : LatticeData) (colour : Fin D.rank) : VertexOperator ℂ (Carrier D) :=
  sourceCurrent D (Pi.single colour 1)

theorem unitCurrent_mode (D : LatticeData) (colour : Fin D.rank) (mode : ℤ) :
    (unitCurrent D colour)[[mode]] = neutralMode D colour mode := by
  classical
  simp [unitCurrent, sourceCurrent_mode, Pi.single_apply]

theorem negative_current_single (D : LatticeData) (colour : Fin D.rank)
    (degree : ℕ) (charge : Charge D) (polynomial : Oscillator D) :
    ((unitCurrent D colour)[[-(degree : ℤ) - 1]]) (Finsupp.single charge polynomial) =
      Finsupp.single charge (X (colour, degree) * polynomial) := by
  rw [unitCurrent_mode, neutralMode_single, neutralPolynomialMode_negative]
  rfl

def oscillatorWord (D : LatticeData) (charge : Charge D) : List (Index D) → Carrier D
  | [] => Finsupp.single charge 1
  | index :: tail => ((unitCurrent D index.1)[[-(index.2 : ℤ) - 1]])
      (oscillatorWord D charge tail)

theorem oscillatorWord_eq (D : LatticeData) (charge : Charge D) (word : List (Index D)) :
    oscillatorWord D charge word =
      Finsupp.single charge ((word.map (fun index => (X index : Oscillator D))).prod) := by
  induction word with
  | nil => rfl
  | cons index tail inductionHypothesis =>
    rw [oscillatorWord, inductionHypothesis, negative_current_single]
    rfl

theorem finite_source_expansion (D : LatticeData) (state : Carrier D) :
    state = ∑ charge ∈ state.support,
      ∑ exponent ∈ ((basisMonomials (Index D) ℂ).repr (state charge)).support,
        ((basisMonomials (Index D) ℂ).repr (state charge) exponent) •
          oscillatorWord D charge (occurrences D exponent) := by
  classical
  simp_rw [oscillatorWord_eq, occurrences_product, Finsupp.smul_single,
    ← Finsupp.single_finsetSum]
  conv_lhs => rw [← Finsupp.sum_single state]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro charge member
  congr 1
  exact ((basisMonomials (Index D) ℂ).linearCombination_repr (state charge)).symm

def oscillatorWordSpan (D : LatticeData) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ (Set.range (fun pair : Charge D × List (Index D) =>
    oscillatorWord D pair.1 pair.2))

theorem oscillatorWordSpan_eq_top (D : LatticeData) : oscillatorWordSpan D = ⊤ := by
  classical
  apply top_unique
  intro state member
  rw [finite_source_expansion D state]
  apply Submodule.sum_mem
  intro charge chargeMember
  apply Submodule.sum_mem
  intro exponent exponentMember
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(charge, occurrences D exponent), rfl⟩

end
end D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords

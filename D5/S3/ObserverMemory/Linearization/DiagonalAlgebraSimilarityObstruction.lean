/- GID: D5/S3/ObserverMemory/Linearization/DiagonalAlgebraSimilarityObstruction
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Linearization/DiagonalAlgebraSimilarityObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Similar transition matrices need not admit a diagonal-algebra-preserving similarity. -/

import D5.S3.ObserverMemory.InverseLimits.FunctionGraphLinearSimilarity

/- Library-search audit trail (2026-08-22):
   * Exact repository hits `tauA`, `tauB`,
     `same_trace_rank_spectra_not_function_graph_conjugate`, and
     `transition_matrices_linearly_similar` supply the canonical source maps, the graph
     obstruction, and the integral similarity certificate; all are applied directly.
   * Exact pinned-Mathlib hits `Matrix.map_mul`, `Matrix.mul_diagonal`,
     `Matrix.diagonal_mul`, `Equiv.ofBijective`, and
     `Finite.injective_iff_surjective` are applied below.
   * Repository and pinned-Mathlib searches found no theorem packaging the concrete
     complex similarity with the diagonal-algebra normalizer obstruction. -/

noncomputable section

namespace D5.S3.ObserverMemory.Linearization.DiagonalAlgebraSimilarityObstruction

open D5.S3.ObserverMemory.InverseLimits.FunctionGraphSpectrumCollision
open D5.S3.ObserverMemory.InverseLimits.FunctionGraphLinearSimilarity

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev ComplexMatrixEight := Matrix (Fin 8) (Fin 8) Complex

/-- The complex transition matrix whose column at a state is the basis vector at its image. -/
def complexTransitionMatrix (update : Fin 8 -> Fin 8) : ComplexMatrixEight :=
  fun target source => if update source = target then 1 else 0

/-- Two complex matrices are similar when an explicit change of basis and its inverse
intertwine them. -/
def LinearlySimilar (first second : ComplexMatrixEight) : Prop :=
  ∃ change inverse : ComplexMatrixEight,
    change * inverse = 1 ∧ inverse * change = 1 ∧
      first * change = change * second

/-- A similarity preserves the standard diagonal algebra when conjugation in both directions
sends every diagonal matrix to another diagonal matrix. -/
def DiagonalAlgebraPreservingSimilarity
    (first second : ComplexMatrixEight) : Prop :=
  ∃ change inverse : ComplexMatrixEight,
    change * inverse = 1 ∧ inverse * change = 1 ∧
      first * change = change * second ∧
      (∀ diagonal : Fin 8 -> Complex, ∃ transported : Fin 8 -> Complex,
        change * Matrix.diagonal diagonal * inverse = Matrix.diagonal transported) ∧
      (∀ diagonal : Fin 8 -> Complex, ∃ transported : Fin 8 -> Complex,
        inverse * Matrix.diagonal diagonal * change = Matrix.diagonal transported)

private def integerMatrixToComplex :
    Matrix (Fin 8) (Fin 8) Int →* ComplexMatrixEight where
  toFun matrix := matrix.map (Int.castRingHom Complex)
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' first second := by
    exact Matrix.map_mul

private theorem integer_transition_maps_to_complex (update : Fin 8 -> Fin 8) :
    integerMatrixToComplex (transitionMatrix update) =
      complexTransitionMatrix update := by
  ext i j
  simp [integerMatrixToComplex, transitionMatrix, complexTransitionMatrix]

private theorem complex_transition_matrices_similar :
    LinearlySimilar (complexTransitionMatrix tauA)
      (complexTransitionMatrix tauB) := by
  rcases transition_matrices_linearly_similar with ⟨change, change_unit, intertwines⟩
  rcases change_unit with ⟨unit, rfl⟩
  refine ⟨integerMatrixToComplex (unit : Matrix (Fin 8) (Fin 8) Int),
    integerMatrixToComplex (↑(unit⁻¹) : Matrix (Fin 8) (Fin 8) Int), ?_, ?_, ?_⟩
  · rw [← map_mul]
    simp
  · rw [← map_mul]
    simp
  · have mapped := congrArg integerMatrixToComplex intertwines
    simpa only [map_mul, integer_transition_maps_to_complex] using mapped

private theorem diagonal_preservation_induces_conjugacy
    {firstUpdate secondUpdate : Fin 8 -> Fin 8}
    (change inverse : ComplexMatrixEight)
    (inverse_change : inverse * change = 1)
    (intertwines : complexTransitionMatrix firstUpdate * change =
      change * complexTransitionMatrix secondUpdate)
    (diagonal_forward : ∀ diagonal : Fin 8 -> Complex,
      ∃ transported : Fin 8 -> Complex,
        change * Matrix.diagonal diagonal * inverse = Matrix.diagonal transported) :
    ∃ relabeling : Equiv.Perm (Fin 8),
      Function.Semiconj relabeling secondUpdate firstUpdate := by
  have column_nonzero (source : Fin 8) : ∃ target, change target source ≠ 0 := by
    by_contra no_entry
    have column_zero : ∀ target, change target source = 0 := by
      intro target
      by_contra nonzero
      exact no_entry ⟨target, nonzero⟩
    have product_zero : (inverse * change) source source = 0 := by
      simp [Matrix.mul_apply, column_zero]
    have zero_eq_one : (0 : Complex) = 1 := by
      calc
        0 = (inverse * change) source source := product_zero.symm
        _ = 1 := by rw [inverse_change]; simp
    exact zero_ne_one zero_eq_one
  let row : Fin 8 -> Fin 8 := fun source => Classical.choose (column_nonzero source)
  have row_nonzero (source : Fin 8) : change (row source) source ≠ 0 :=
    Classical.choose_spec (column_nonzero source)
  have row_exclusive (source other : Fin 8) (different : other ≠ source) :
      change (row source) other = 0 := by
    let coordinate : Fin 8 -> Complex := fun index => if index = source then 1 else 0
    rcases diagonal_forward coordinate with ⟨transported, conjugates⟩
    have commutes :
        change * Matrix.diagonal coordinate = Matrix.diagonal transported * change := by
      calc
        change * Matrix.diagonal coordinate =
            (change * Matrix.diagonal coordinate) * 1 := (mul_one _).symm
        _ = (change * Matrix.diagonal coordinate) * (inverse * change) := by
          rw [inverse_change]
        _ = (change * Matrix.diagonal coordinate * inverse) * change := by
          simp only [mul_assoc]
        _ = Matrix.diagonal transported * change := by rw [conjugates]
    have diagonal_entry := congrFun₂ commutes (row source) source
    have transported_one : transported (row source) = 1 := by
      apply mul_right_cancel₀ (row_nonzero source)
      simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, coordinate] using
        diagonal_entry.symm
    have off_diagonal_entry := congrFun₂ commutes (row source) other
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, coordinate, different,
      transported_one] using off_diagonal_entry.symm
  have row_injective : Function.Injective row := by
    intro source other same_row
    by_contra different
    apply row_nonzero other
    rw [← same_row]
    exact row_exclusive source other (Ne.symm different)
  have row_surjective : Function.Surjective row :=
    Finite.injective_iff_surjective.mp row_injective
  have column_exclusive (source target : Fin 8) (different : target ≠ row source) :
      change target source = 0 := by
    obtain ⟨other, rfl⟩ := row_surjective target
    have source_ne_other : source ≠ other := by
      intro same_source
      subst other
      exact different rfl
    exact row_exclusive other source source_ne_other
  have row_intertwines (source : Fin 8) :
      firstUpdate (row source) = row (secondUpdate source) := by
    by_contra different
    have left_zero :
        (complexTransitionMatrix firstUpdate * change)
            (row (secondUpdate source)) source = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro index _
      by_cases is_row : index = row source
      · subst index
        simp [complexTransitionMatrix, different]
      · rw [column_exclusive source index is_row]
        simp
    have right_entry :
        (change * complexTransitionMatrix secondUpdate)
            (row (secondUpdate source)) source =
          change (row (secondUpdate source)) (secondUpdate source) := by
      simp [complexTransitionMatrix, Matrix.mul_apply]
    have matrix_entry :=
      congrFun₂ intertwines (row (secondUpdate source)) source
    rw [left_zero, right_entry] at matrix_entry
    exact row_nonzero (secondUpdate source) matrix_entry.symm
  let relabeling : Equiv.Perm (Fin 8) :=
    Equiv.ofBijective row ⟨row_injective, row_surjective⟩
  refine ⟨relabeling, ?_⟩
  intro source
  change row (secondUpdate source) = firstUpdate (row source)
  exact (row_intertwines source).symm

/-- The two canonical eight-state transition matrices are similar over the complex numbers,
but no similarity between them preserves the standard diagonal algebra. -/
theorem same_linear_class_without_diagonal_algebra_similarity :
    LinearlySimilar (complexTransitionMatrix tauA)
        (complexTransitionMatrix tauB) ∧
      ¬ DiagonalAlgebraPreservingSimilarity
        (complexTransitionMatrix tauA) (complexTransitionMatrix tauB) := by
  refine ⟨complex_transition_matrices_similar, ?_⟩
  rintro ⟨change, inverse, _, inverse_change, intertwines,
    diagonal_forward, _⟩
  rcases diagonal_preservation_induces_conjugacy change inverse inverse_change
      intertwines diagonal_forward with ⟨relabeling, semiconj_reverse⟩
  have semiconj_forward : Function.Semiconj relabeling.symm tauA tauB := by
    intro state
    obtain ⟨source, rfl⟩ := relabeling.surjective state
    rw [← semiconj_reverse source]
    simp
  have no_conjugacy :
      ¬ ∃ relabeling : Equiv.Perm (Fin 8),
        Function.Semiconj relabeling tauA tauB := by
    have collision := same_trace_rank_spectra_not_function_graph_conjugate
    aesop
  exact no_conjugacy ⟨relabeling.symm, semiconj_forward⟩

#print axioms same_linear_class_without_diagonal_algebra_similarity

end D5.S3.ObserverMemory.Linearization.DiagonalAlgebraSimilarityObstruction

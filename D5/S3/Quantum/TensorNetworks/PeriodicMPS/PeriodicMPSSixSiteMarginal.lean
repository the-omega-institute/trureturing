/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMarginal
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMarginal
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCoordinates]
   utility: none
   digest: The adjacent six-site marginal restricts to the five independent-set coordinates. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCoordinates

/-! The literal adjacent two-site marginal and the independent-set slice. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMarginal

open Matrix
open PeriodicMPSParentIntersection (Bond Word)
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSSixSiteCoordinates
open scoped ComplexConjugate
open private traceWord_eq_of_rotate from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCoordinates

def prefixBits : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m := 2) (n := 2)).symm

private def suffixWords : Fin 16 → Word 4 :=
  ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1],
    ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 1, 1],
    ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1],
    ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 1, 1]]

private noncomputable def suffixEquiv : Fin 16 ≃ Word 4 :=
  Equiv.ofBijective suffixWords (by decide)

/-- Index of the cyclic necklace represented by each prefix and suffix. -/
def necklaceTable : Matrix (Fin 4) (Fin 16) (Fin 14) :=
  !![0, 1, 1, 2, 1, 3, 2, 4, 1, 5, 3, 6, 2, 7, 4, 8;
    1, 3, 5, 7, 3, 9, 6, 10, 2, 6, 7, 11, 4, 10, 8, 12;
    1, 2, 3, 4, 5, 6, 7, 8, 3, 7, 9, 10, 6, 11, 10, 12;
    2, 4, 6, 8, 7, 10, 11, 12, 4, 8, 10, 12, 8, 12, 12, 13]

/-- The adjacent two-site amplitude flattening in lexicographic order. -/
def flatten {R : Type*} (p : Fin 14 → R) : Matrix (Fin 4) (Fin 16) R :=
  fun i j => p (necklaceTable i j)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- The reindexing table is checked by enumerating the 64 prefix and suffix pairs.
private theorem table_rotate : ∀ (i : Fin 4) (j : Fin 16), ∃ r : Fin 6,
    (List.ofFn (Fin.append ![(prefixBits i).1, (prefixBits i).2] (suffixWords j))).rotate r.val =
      List.ofFn (necklaces (necklaceTable i j)) := by decide

theorem flatten_necklaces (A : Fin 2 → Bond) :
    (PeriodicMPSParentIntersection.twoFlattening A 2).submatrix prefixBits suffixEquiv =
      flatten (traceWord 2 2 6 A ∘ necklaces) := by
  ext i j
  obtain ⟨r, h⟩ := table_rotate i j
  exact traceWord_eq_of_rotate A h

/-- Two-site marginal readout on the same prefix order as the flattening. -/
noncomputable def gram (p : Fin 14 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  flatten p * (flatten p).conjTranspose

/-- The trace-coordinate Gram is the literal adjacent marginal. -/
theorem flatten_gram (A : Fin 2 → Bond) :
    (PeriodicMPSTwoSiteAmbiguity.rawTwo A 2).submatrix prefixBits prefixBits =
      gram (traceWord 2 2 6 A ∘ necklaces) := by
  rw [gram, ← flatten_necklaces, PeriodicMPSTwoSiteAmbiguity.rawTwo,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

/-- The five allowed coefficients with no cyclically adjacent ones. -/
def independentSlice (a b c d e : ℂ) : Fin 14 → ℂ :=
  ![a, b, 0, c, 0, d, 0, 0, 0, e, 0, 0, 0, 0]

/-- Zero adjacent-ones probability restricts the full amplitude to the
independent-set slice. -/
theorem supported_of_corner_zero (p : Fin 14 → ℂ) (h : gram p 3 3 = 0) :
    p = independentSlice (p 0) (p 1) (p 3) (p 5) (p 9) := by
  have hs : ∑ j : Fin 16, Complex.normSq (flatten p 3 j) = 0 := by
    have hc := congrArg Complex.re h
    simpa [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj] using hc
  have hz (j : Fin 16) : flatten p 3 j = 0 :=
    Complex.normSq_eq_zero.mp <| (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Complex.normSq_nonneg (flatten p 3 k))).mp hs j (Finset.mem_univ _)
  have h₂ : p 2 = 0 := hz 0
  have h₄ : p 4 = 0 := hz 1
  have h₆ : p 6 = 0 := hz 2
  have h₇ : p 7 = 0 := hz 4
  have h₈ : p 8 = 0 := hz 3
  have h₁₀ : p 10 = 0 := hz 5
  have h₁₁ : p 11 = 0 := hz 6
  have h₁₂ : p 12 = 0 := hz 7
  have h₁₃ : p 13 = 0 := hz 15
  funext i
  fin_cases i <;> simp [independentSlice, h₂, h₄, h₆, h₇, h₈, h₁₀, h₁₁, h₁₂, h₁₃]

/-- Every nonzero actual state with zero adjacent-ones probability has a
traceless and singular second tensor. -/
theorem trace_det_second_eq_zero (A : Fin 2 → Bond) (hne : traceWord 2 2 6 A ≠ 0)
    (h : gram (traceWord 2 2 6 A ∘ necklaces) 3 3 = 0) :
    (A 1).trace = 0 ∧ (A 1).det = 0 := by
  let p := traceWord 2 2 6 A ∘ necklaces
  let t := (A 0).trace
  let s := (A 1).trace
  let d := (A 0).det
  let e := (A 1).det
  let k := (A 0 * A 1).trace
  have hp : p = coordinates (t ^ 2) (t * s) (s ^ 2) d e k := trace_word_necklaces A
  have hsupport := supported_of_corner_zero p h
  have hs : coordinates (s ^ 2) (s * t) (t ^ 2) e d k = p ∘ swappedIndex := by
    rw [mul_comm s t, coordinates_swap, ← hp]
  have hback : p = coordinates (s ^ 2) (s * t) (t ^ 2) e d k ∘ swappedIndex := by
    rw [hp, mul_comm t s, coordinates_swap]
  have hz : coordinates (s ^ 2) (s * t) (t ^ 2) e d k ≠ 0 := by
    intro he
    have hp₀ : p = 0 := by rw [hback, he]; rfl
    apply hne
    have hp₁ : p = (0 : ℂ) • p := by rw [hp₀, zero_smul]
    simpa only [zero_smul] using traceWord_smul_of_necklaces A A 0 hp₁
  apply trace_det_eq_zero_of_first_three_zero hz
  · exact (congrFun hs 0).trans (congrFun hsupport 13)
  · exact (congrFun hs 1).trans (congrFun hsupport 12)
  · exact (congrFun hs 2).trans (congrFun hsupport 8)

/-- Explicit entries on the independent-set slice used for the special fiber. -/
theorem independent_gram (a b c d e : ℂ) :
    let G := gram (independentSlice a b c d e)
    G 0 0 = a * conj a + 4 * (b * conj b) + 2 * (c * conj c) + d * conj d ∧
    G 0 1 = a * conj b + 2 * (b * conj c) + b * conj d + c * conj e ∧
    G 1 1 = b * conj b + 2 * (c * conj c) + d * conj d + e * conj e ∧
    G 1 2 = b * conj b + c * conj d + d * conj c ∧
    G 3 3 = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gram, flatten, independentSlice, necklaceTable, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> ring

/-- Coordinates with the alternating triple fixed to one. -/
def nilpotentRay (x y : ℂ) : Fin 14 → ℂ :=
  independentSlice (x ^ 3 - 6 * x ^ 2 * y + 9 * x * y ^ 2 - 2 * y ^ 3)
    (x ^ 2 - 3 * x * y + y ^ 2) (x - y) x 1

/-- A nondegenerate zero-corner fiber is represented by the nilpotent ray chart. -/
theorem exists_nilpotentRay (A : Fin 2 → Bond) (hne : traceWord 2 2 6 A ≠ 0)
    (h₀ : gram (traceWord 2 2 6 A ∘ necklaces) 3 3 = 0)
    (h₁ : gram (traceWord 2 2 6 A ∘ necklaces) 1 1 ≠ 0) :
    ∃ x y gain : ℂ, gain ≠ 0 ∧ traceWord 2 2 6 A ∘ necklaces = gain • nilpotentRay x y := by
  obtain ⟨hs, he⟩ := trace_det_second_eq_zero A hne h₀
  let t := (A 0).trace
  let d := (A 0).det
  let k := (A 0 * A 1).trace
  have hp : traceWord 2 2 6 A ∘ necklaces = coordinates (t ^ 2) 0 0 d 0 k := by
    rw [trace_word_necklaces, hs, he, mul_zero, zero_pow (by decide : 2 ≠ 0)]
  have hk : k ≠ 0 := by
    intro hz
    rw [hp, nilpotent_coordinates, hz] at h₁
    apply h₁
    simp [gram, flatten, necklaceTable, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]
  have hscale := coordinates_scale k (t ^ 2 / k) 0 0 (d / k) 0 1
  rw [mul_div_cancel₀ _ hk, mul_div_cancel₀ _ hk, mul_zero, mul_one] at hscale
  refine ⟨t ^ 2 / k, d / k, k ^ 3, pow_ne_zero _ hk, hp.trans (hscale.trans ?_)⟩
  rw [nilpotent_coordinates]
  simp [nilpotentRay, independentSlice]

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMarginal

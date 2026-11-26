/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace]
   utility: none
   digest: Homogeneous trace coordinates of binary bond-two periodic states on five sites. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity

/-! The trace covector and determinant pencil give the eight necklace amplitudes. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates

open Matrix
open PeriodicMPSParentIntersection (Bond Word)
open UniformMPSExpectedDimensionRefutation (traceWord)

/-- Cyclic representatives for the eight binary necklaces of length five. -/
def necklaces : Fin 8 → Word 5 :=
  ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0],
    ![1, 1, 1, 0, 0], ![1, 1, 0, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 1]]

/-- The necklace traces in the homogeneous coordinates of two 2 by 2 matrices. -/
def coordinates {R : Type*} [CommRing R] (t s d e k : R) : Fin 8 → R :=
  ![t ^ 5 - 5 * d * t ^ 3 + 5 * d ^ 2 * t,
    (t ^ 3 - 2 * d * t) * k + (d ^ 2 - d * t ^ 2) * s,
    s * (t ^ 2 - d) * k - e * t ^ 3 - d * s ^ 2 * t + 3 * d * e * t,
    t * k ^ 2 - d * s * k - d * e * t,
    (s ^ 2 - e) * k * t - d * s ^ 3 - s * e * t ^ 2 + 3 * s * d * e,
    s * k ^ 2 - e * k * t - d * e * s,
    (s ^ 3 - 2 * s * e) * k + e ^ 2 * t - s ^ 2 * e * t,
    s ^ 5 - 5 * e * s ^ 3 + 5 * e ^ 2 * s]

/-- The two antisymmetric necklace differences recover the trace direction wherever
the first difference is nonzero. -/
theorem trace_direction {R : Type*} [CommRing R] (t s d e k : R) :
    let p := coordinates t s d e k
    t * (p 4 - p 5) = s * (p 2 - p 3) := by
  simp [coordinates]
  ring

/-- On a trace-aligned fiber the amplitudes, after removing the trace factor, are
quadratic in the square of the trace and the three determinant-pencil coefficients. -/
def aligned {R : Type*} [CommRing R] (x y z w : R) : Fin 8 → R :=
  ![-x ^ 2 + 3 * x * y - y ^ 2, z * y, x * w, z ^ 2 + y * w - x * w,
    z * w, z * w, w ^ 2, 0]

theorem aligned_trace {R : Type*} [CommRing R] (t d e k : R) :
    coordinates t 0 d e k =
      t • aligned (3 * d - t ^ 2) (2 * d - t ^ 2) (-k) e := by
  funext i
  fin_cases i <;>
    simp [coordinates, aligned, Pi.smul_apply, smul_eq_mul] <;> ring

set_option maxHeartbeats 2000000 in
-- The eight degree-five matrix traces are expanded in the eight matrix entries.
/-- The literal periodic trace-word amplitudes are the homogeneous coordinate polynomials. -/
theorem trace_word_necklaces (A : Fin 2 → Bond) :
    traceWord 2 2 5 A ∘ necklaces =
      coordinates (A 0).trace (A 1).trace (A 0).det (A 1).det (A 0 * A 1).trace := by
  funext i
  fin_cases i <;>
    simp [traceWord, necklaces, coordinates, List.ofFn_succ, List.ofFn_zero, Matrix.trace,
      Matrix.diag, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The quadratic map is undefined precisely at the binary quadratic roots on the line
where the last two source coordinates vanish. -/
theorem aligned_eq_zero_iff {R : Type*} [Field R] (x y z w : R) :
    aligned x y z w = 0 ↔ w = 0 ∧ z = 0 ∧ -x ^ 2 + 3 * x * y - y ^ 2 = 0 := by
  constructor
  · intro h
    have hw₂ := congrFun h (6 : Fin 8)
    change w ^ 2 = 0 at hw₂
    have hw : w = 0 := sq_eq_zero_iff.mp hw₂
    have hz : z = 0 := sq_eq_zero_iff.mp (by simpa [aligned, hw] using congrFun h 3)
    exact ⟨hw, hz, by simpa [aligned] using congrFun h 0⟩
  · rintro ⟨rfl, rfl, h⟩
    funext i
    fin_cases i <;> simp [aligned, h]

/-- On the chart with nonzero last source coordinate, the indicated three
projective amplitude coordinates reconstruct the remaining source ratios. -/
theorem aligned_inverse {R : Type*} [Field R] (x y z w : R) (hw : w ≠ 0) :
    let p := aligned x y z w
    p 2 / p 6 = x / w ∧ p 4 / p 6 = z / w ∧
      p 3 / p 6 - (p 4 / p 6) ^ 2 + p 2 / p 6 = y / w := by
  simp only [aligned]
  change x * w / w ^ 2 = x / w ∧ z * w / w ^ 2 = z / w ∧
    (z ^ 2 + y * w - x * w) / w ^ 2 - (z * w / w ^ 2) ^ 2 + x * w / w ^ 2 = y / w
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
  ring

/-- Every complex tuple of the two traces, two determinants and the mixed trace
has an actual binary bond-two presentation. -/
theorem exists_trace_coordinates (t s d e k : ℂ) :
    ∃ A : Fin 2 → Bond, (A 0).trace = t ∧ (A 1).trace = s ∧
      (A 0).det = d ∧ (A 1).det = e ∧ (A 0 * A 1).trace = k := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4 * e) (n := 2) (by decide)
  let r := (s + u) / 2
  have hr : r * (s - r) = e := by
    dsimp [r]
    calc
      (s + u) / 2 * (s - (s + u) / 2) = (s ^ 2 - u ^ 2) / 4 := by ring
      _ = e := by rw [hu]; ring
  refine ⟨![!![0, -d; 1, t], !![r, k - t * (s - r); 0, s - r]], ?_⟩
  simp [Matrix.trace, Matrix.diag, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hr]

/-- Common scaling of the two physical tensors acts with weight five on the amplitudes. -/
theorem coordinates_scale {R : Type*} [CommRing R] (z t s d e k : R) :
    coordinates (z * t) (z * s) (z ^ 2 * d) (z ^ 2 * e) (z ^ 2 * k) =
      z ^ 5 • coordinates t s d e k := by
  funext i
  fin_cases i <;> simp [coordinates, Pi.smul_apply, smul_eq_mul] <;> ring

private def prefixBits : Fin 4 ≃ Fin 2 × Fin 2 :=
  (finProdFinEquiv (m := 2) (n := 2)).symm

private def suffixWords : Fin 8 → Word 3 :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1],
    ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]]

private noncomputable def suffixEquiv : Fin 8 ≃ Word 3 := Equiv.ofBijective suffixWords (by decide)

/-- The flattening indexed by the standard binary prefixes and suffixes. -/
def flatten {R : Type*} (p : Fin 8 → R) : Matrix (Fin 4) (Fin 8) R :=
  !![p 0, p 1, p 1, p 2, p 1, p 3, p 2, p 4;
    p 1, p 3, p 3, p 5, p 2, p 5, p 4, p 6;
    p 1, p 2, p 3, p 4, p 3, p 5, p 5, p 6;
    p 2, p 4, p 5, p 6, p 4, p 6, p 6, p 7]

private lemma traceWord_rotate (A : Fin 2 → Bond) (a b c d e : Fin 2) :
    traceWord 2 2 5 A ![a, b, c, d, e] = traceWord 2 2 5 A ![b, c, d, e, a] := by
  change (A a * (A b * (A c * (A d * (A e * 1))))).trace =
    (A b * (A c * (A d * (A e * (A a * 1))))).trace
  simpa only [mul_one, Matrix.mul_assoc] using
    Matrix.trace_mul_comm (A a) (A b * (A c * (A d * A e)))

/-- The trace-coordinate flattening is the actual periodic amplitude flattening. -/
theorem flatten_necklaces (A : Fin 2 → Bond) :
    (PeriodicMPSParentIntersection.twoFlattening A 1).submatrix prefixBits suffixEquiv =
      flatten (traceWord 2 2 5 A ∘ necklaces) := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact (traceWord_rotate A 0 0 0 0 1).trans ((traceWord_rotate A 0 0 0 1 0).trans ((traceWord_rotate A 0 0 1 0 0).trans ((traceWord_rotate A 0 1 0 0 0))))
  · exact (traceWord_rotate A 0 0 0 1 0).trans ((traceWord_rotate A 0 0 1 0 0).trans ((traceWord_rotate A 0 1 0 0 0)))
  · exact (traceWord_rotate A 0 0 0 1 1).trans ((traceWord_rotate A 0 0 1 1 0).trans ((traceWord_rotate A 0 1 1 0 0)))
  · exact (traceWord_rotate A 0 0 1 0 0).trans ((traceWord_rotate A 0 1 0 0 0))
  · exact (traceWord_rotate A 0 0 1 0 1).trans ((traceWord_rotate A 0 1 0 1 0))
  · exact (traceWord_rotate A 0 0 1 1 0).trans ((traceWord_rotate A 0 1 1 0 0))
  · exact (traceWord_rotate A 0 0 1 1 1).trans ((traceWord_rotate A 0 1 1 1 0))
  · exact (traceWord_rotate A 0 1 0 0 0)
  · exact (traceWord_rotate A 0 1 0 0 1).trans ((traceWord_rotate A 1 0 0 1 0).trans ((traceWord_rotate A 0 0 1 0 1).trans ((traceWord_rotate A 0 1 0 1 0))))
  · exact (traceWord_rotate A 0 1 0 1 0)
  · exact (traceWord_rotate A 0 1 0 1 1).trans ((traceWord_rotate A 1 0 1 1 0).trans ((traceWord_rotate A 0 1 1 0 1)))
  · exact (traceWord_rotate A 0 1 1 0 0)
  · exact (traceWord_rotate A 0 1 1 0 1)
  · exact (traceWord_rotate A 0 1 1 1 0)
  · exact (traceWord_rotate A 0 1 1 1 1)
  · rfl
  · exact (traceWord_rotate A 1 0 0 0 1).trans ((traceWord_rotate A 0 0 0 1 1).trans ((traceWord_rotate A 0 0 1 1 0).trans ((traceWord_rotate A 0 1 1 0 0))))
  · exact (traceWord_rotate A 1 0 0 1 0).trans ((traceWord_rotate A 0 0 1 0 1).trans ((traceWord_rotate A 0 1 0 1 0)))
  · exact (traceWord_rotate A 1 0 0 1 1).trans ((traceWord_rotate A 0 0 1 1 1).trans ((traceWord_rotate A 0 1 1 1 0)))
  · rfl
  · exact (traceWord_rotate A 1 0 1 0 1).trans ((traceWord_rotate A 0 1 0 1 1).trans ((traceWord_rotate A 1 0 1 1 0).trans ((traceWord_rotate A 0 1 1 0 1))))
  · exact (traceWord_rotate A 1 0 1 1 0).trans ((traceWord_rotate A 0 1 1 0 1))
  · exact (traceWord_rotate A 1 0 1 1 1).trans ((traceWord_rotate A 0 1 1 1 1))
  · rfl
  · exact (traceWord_rotate A 1 1 0 0 1).trans ((traceWord_rotate A 1 0 0 1 1).trans ((traceWord_rotate A 0 0 1 1 1).trans ((traceWord_rotate A 0 1 1 1 0))))
  · rfl
  · exact (traceWord_rotate A 1 1 0 1 1).trans ((traceWord_rotate A 1 0 1 1 1).trans ((traceWord_rotate A 0 1 1 1 1)))
  · rfl
  · exact (traceWord_rotate A 1 1 1 0 1).trans ((traceWord_rotate A 1 1 0 1 1).trans ((traceWord_rotate A 1 0 1 1 1).trans ((traceWord_rotate A 0 1 1 1 1))))
  · rfl
  · rfl

/-- The literal two-site marginal is the Hermitian Gram of the trace-coordinate flattening. -/
theorem flatten_gram (A : Fin 2 → Bond) :
    (PeriodicMPSTwoSiteAmbiguity.rawTwo A 1).submatrix prefixBits prefixBits =
      flatten (traceWord 2 2 5 A ∘ necklaces) *
      (flatten (traceWord 2 2 5 A ∘ necklaces)).conjTranspose := by
  rw [← flatten_necklaces, PeriodicMPSTwoSiteAmbiguity.rawTwo,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates

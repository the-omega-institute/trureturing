/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCoordinates
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCoordinates
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates]
   utility: none
   digest: Cubic coordinates of the six-site periodic binary bond-two amplitudes. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates
import Mathlib.Data.List.Rotate

/-! Six-letter traces are cubic in the squared trace covector and the determinant pencil. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCoordinates

open Matrix
open PeriodicMPSParentIntersection (Bond Word)
open UniformMPSExpectedDimensionRefutation (traceWord)

/-- Cyclic representatives for the fourteen binary necklaces on six sites. -/
def necklaces : Fin 14 → Word 6 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 1], ![0, 0, 1, 0, 1, 1], ![0, 0, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 0, 1, 1],
    ![0, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1]]

/-- In the order used here the first three entries are the components of the squared
trace covector. The remaining entries are the two determinants and the mixed trace. -/
def coordinates {R : Type*} [CommRing R] (T S U d e k : R) : Fin 14 → R :=
  ![T ^ 3 - 6 * T ^ 2 * d + 9 * T * d ^ 2 - 2 * d ^ 3,
    -S * T * d + 2 * S * d ^ 2 + T ^ 2 * k - 3 * T * d * k + d ^ 2 * k,
    S * T * k - 2 * S * d * k - T ^ 2 * e - T * U * d + 4 * T * d * e + U * d ^ 2 - 2 * d ^ 2
      * e,
    -S * d * k - T * d * e + T * k ^ 2 + 2 * d ^ 2 * e - d * k ^ 2,
    -S * T * e - S * U * d + 4 * S * d * e + T * U * k - T * e * k - U * d * k + d * e * k,
    -2 * S * d * k + T * k ^ 2 + U * d ^ 2 - 2 * d ^ 2 * e,
    S * k ^ 2 - T * e * k - U * d * k + d * e * k,
    S * k ^ 2 - T * e * k - U * d * k + d * e * k,
    S * U * k - 2 * S * e * k - T * U * e + T * e ^ 2 - U ^ 2 * d + 4 * U * d * e - 2 * d * e
      ^ 2,
    -3 * d * e * k + k ^ 3,
    -S * e * k - U * d * e + U * k ^ 2 + 2 * d * e ^ 2 - e * k ^ 2,
    -2 * S * e * k + T * e ^ 2 + U * k ^ 2 - 2 * d * e ^ 2,
    -S * U * e + 2 * S * e ^ 2 + U ^ 2 * k - 3 * U * e * k + e ^ 2 * k,
    U ^ 3 - 6 * U ^ 2 * e + 9 * U * e ^ 2 - 2 * e ^ 3]

set_option maxHeartbeats 4000000 in
-- Expand the fourteen degree-six traces in the eight matrix entries.
/-- The cubic coordinates at the trace invariants give the literal six-letter amplitudes. -/
theorem trace_word_necklaces (A : Fin 2 → Bond) :
    traceWord 2 2 6 A ∘ necklaces =
      coordinates ((A 0).trace ^ 2) ((A 0).trace * (A 1).trace) ((A 1).trace ^ 2)
        (A 0).det (A 1).det (A 0 * A 1).trace := by
  funext i
  fin_cases i <;>
    simp [traceWord, necklaces, coordinates, List.ofFn_succ, List.ofFn_zero, Matrix.trace,
      Matrix.diag, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The six-letter amplitude coordinates have degree three in the weight-two variables. -/
theorem coordinates_scale {R : Type*} [CommRing R] (a T S U d e k : R) :
    coordinates (a * T) (a * S) (a * U) (a * d) (a * e) (a * k) =
      a ^ 3 • coordinates T S U d e k := by
  funext i
  fin_cases i <;> simp [coordinates, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Switching the two physical symbols permutes the six-site necklaces. -/
def swappedIndex : Fin 14 → Fin 14 :=
  ![13, 12, 8, 10, 4, 11, 7, 6, 2, 9, 3, 5, 1, 0]

theorem coordinates_swap {R : Type*} [CommRing R] (T S U d e k : R) :
    coordinates U S T e d k = coordinates T S U d e k ∘ swappedIndex := by
  funext i
  fin_cases i <;> simp [coordinates, swappedIndex] <;> ring

/-- Empty-word coefficient in the trace-aligned chart with first trace one. -/
def vacuum {R : Type*} [CommRing R] (d : R) : R := 1 - 6 * d + 9 * d ^ 2 - 2 * d ^ 3

/-- The controlling trace identities in the chart with second trace zero. -/
theorem aligned_first_three {R : Type*} [CommRing R] (d e k : R) :
    coordinates 1 0 0 d e k 0 = vacuum d ∧
      coordinates 1 0 0 d e k 1 = (d ^ 2 - 3 * d + 1) * k ∧
      coordinates 1 0 0 d e k 2 = -(2 * d ^ 2 - 4 * d + 1) * e := by
  constructor
  · simp [coordinates, vacuum] <;> ring
  constructor <;> simp [coordinates] <;> ring

/-- The one- and two-letter normal directions are nondegenerate at the vacuum roots. -/
theorem controlling_factors_ne {d : ℂ} (hd : vacuum d = 0) :
    d ^ 2 - 3 * d + 1 ≠ 0 ∧ 2 * d ^ 2 - 4 * d + 1 ≠ 0 := by
  constructor
  · intro hz
    have he : (5 * d - 13) * vacuum d +
        (10 * d ^ 2 - 41 * d + 14) * (d ^ 2 - 3 * d + 1) = 1 := by unfold vacuum; ring
    simp [hd, hz] at he
  · intro hz
    have he : (20 * d - 34) * vacuum d +
        (20 * d ^ 2 - 84 * d + 35) * (2 * d ^ 2 - 4 * d + 1) = 1 := by unfold vacuum; ring
    simp [hd, hz] at he

/-- The aligned trace chart has exactly three base points on its determinant line. -/
theorem aligned_eq_zero_iff {d e k : ℂ} :
    coordinates 1 0 0 d e k = 0 ↔ vacuum d = 0 ∧ e = 0 ∧ k = 0 := by
  constructor
  · intro h
    obtain ⟨h₀, h₁, h₂⟩ := aligned_first_three d e k
    have hv : vacuum d = 0 := h₀.symm.trans (congrFun h 0)
    obtain ⟨hK, hE⟩ := controlling_factors_ne hv
    exact ⟨hv,
      (mul_eq_zero.mp (h₂.symm.trans (congrFun h 2))).resolve_left (neg_ne_zero.mpr hE),
      (mul_eq_zero.mp (h₁.symm.trans (congrFun h 1))).resolve_left hK⟩
  · rintro ⟨hd, rfl, rfl⟩
    funext i
    fin_cases i <;> simp [coordinates]
    simpa only [vacuum, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hd

/-- Vanishing trace covectors do not produce projective base points. -/
theorem traceless_eq_zero_iff {d e k : ℂ} :
    coordinates 0 0 0 d e k = 0 ↔ d = 0 ∧ e = 0 ∧ k = 0 := by
  constructor
  · intro h
    have hd : d = 0 := by
      have h₀ := congrFun h (0 : Fin 14)
      simp [coordinates, pow_eq_zero_iff] at h₀
      exact h₀
    have he : e = 0 := by
      have h₁ := congrFun h (13 : Fin 14)
      simp [coordinates, pow_eq_zero_iff] at h₁
      exact h₁
    have hk := congrFun h (9 : Fin 14)
    exact ⟨hd, he, by simpa [coordinates, hd, he, pow_eq_zero_iff] using hk⟩
  · rintro ⟨rfl, rfl, rfl⟩
    funext i
    fin_cases i <;> simp [coordinates]

/-- Subtracting the second trace times the first tensor makes the second tensor traceless.
These are the resulting coefficients of the first three trace words. -/
theorem adapted_first_three {R : Type*} [CommRing R] (s d e k : R) :
    let h := k - s * (1 - 2 * d)
    let j := e - s * (s - k) + s ^ 2 * d
    coordinates 1 s (s ^ 2) d e k 0 = vacuum d ∧
      coordinates 1 s (s ^ 2) d e k 1 = s * vacuum d + (d ^ 2 - 3 * d + 1) * h ∧
      coordinates 1 s (s ^ 2) d e k 2 =
        s ^ 2 * vacuum d + 2 * s * (d ^ 2 - 3 * d + 1) * h - (2 * d ^ 2 - 4 * d + 1) * j := by
  dsimp only
  constructor
  · simp [coordinates, vacuum] <;> ring
  constructor <;> simp [coordinates, vacuum] <;> ring

private theorem proportional_pencil_eq_zero {s d : ℂ} (hd : vacuum d = 0) :
    coordinates 1 s (s ^ 2) d (d * s ^ 2) ((1 - 2 * d) * s) = 0 := by
  let counts : Fin 14 → ℕ := ![0, 1, 2, 2, 3, 2, 3, 3, 4, 3, 4, 4, 5, 6]
  have h (i : Fin 14) :
      coordinates 1 s (s ^ 2) d (d * s ^ 2) ((1 - 2 * d) * s) i =
        s ^ counts i * vacuum d := by
    fin_cases i <;> simp [coordinates, counts, vacuum] <;> ring
  funext i
  rw [h i, hd, mul_zero]
  rfl

/-- Three trace words classify the base conics on the first trace chart. -/
theorem first_three_zero_iff {s d e k : ℂ} :
    (coordinates 1 s (s ^ 2) d e k 0 = 0 ∧ coordinates 1 s (s ^ 2) d e k 1 = 0 ∧
      coordinates 1 s (s ^ 2) d e k 2 = 0) ↔
      vacuum d = 0 ∧ e = d * s ^ 2 ∧ k = (1 - 2 * d) * s := by
  obtain ⟨h₀, h₁, h₂⟩ := adapted_first_three s d e k
  constructor
  · rintro ⟨hv, hk, he⟩
    rw [h₀] at hv
    obtain ⟨hK, hE⟩ := controlling_factors_ne hv
    rw [h₁, hv, mul_zero, zero_add] at hk
    have hm := (mul_eq_zero.mp hk).resolve_left hK
    rw [h₂, hv, hm, mul_zero, mul_zero, zero_add, zero_sub] at he
    have hj := (mul_eq_zero.mp (neg_eq_zero.mp he)).resolve_left hE
    have hk' : k = (1 - 2 * d) * s := by linear_combination hm
    refine ⟨hv, ?_, hk'⟩
    rw [hk'] at hj
    linear_combination hj
  · rintro ⟨hd, rfl, rfl⟩
    have h := proportional_pencil_eq_zero (s := s) hd
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩

theorem chart_eq_zero_iff {s d e k : ℂ} :
    coordinates 1 s (s ^ 2) d e k = 0 ↔
      vacuum d = 0 ∧ e = d * s ^ 2 ∧ k = (1 - 2 * d) * s := by
  constructor
  · intro h
    exact first_three_zero_iff.mp ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨hd, rfl, rfl⟩
    exact proportional_pencil_eq_zero hd

/-- For a nonzero six-letter amplitude, vanishing of the first three trace words
forces the first tensor to have zero trace and determinant. -/
theorem trace_det_eq_zero_of_first_three_zero {t s d e k : ℂ}
    (hne : coordinates (t ^ 2) (t * s) (s ^ 2) d e k ≠ 0)
    (h₀ : coordinates (t ^ 2) (t * s) (s ^ 2) d e k 0 = 0)
    (h₁ : coordinates (t ^ 2) (t * s) (s ^ 2) d e k 1 = 0)
    (h₂ : coordinates (t ^ 2) (t * s) (s ^ 2) d e k 2 = 0) : t = 0 ∧ d = 0 := by
  have ht : t = 0 := by
    by_contra hn
    let a := (t ^ 2)⁻¹
    have hscale := coordinates_scale a (t ^ 2) (t * s) (s ^ 2) d e k
    have ha₀ : a * t ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero _ hn)
    have ha₁ : a * (t * s) = s / t := by
      dsimp [a]
      field_simp
    have ha₂ : a * s ^ 2 = (s / t) ^ 2 := by
      rw [div_pow, div_eq_mul_inv, mul_comm]
    rw [ha₀, ha₁, ha₂] at hscale
    have hzero (i : Fin 14) (hi : coordinates (t ^ 2) (t * s) (s ^ 2) d e k i = 0) :
        coordinates 1 (s / t) ((s / t) ^ 2) (a * d) (a * e) (a * k) i = 0 :=
      (congrFun hscale i).trans (show a ^ 3 * coordinates (t ^ 2) (t * s) (s ^ 2)
        d e k i = 0 by rw [hi, mul_zero])
    have hz := chart_eq_zero_iff.mpr
      (first_three_zero_iff.mp ⟨hzero 0 h₀, hzero 1 h₁, hzero 2 h₂⟩)
    rw [hscale] at hz
    have ha : a ^ 3 ≠ 0 := pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hn))
    exact (smul_ne_zero ha hne) hz
  subst t
  exact ⟨rfl, by simpa [coordinates, pow_eq_zero_iff] using h₀⟩

/-- The empty word and the four nonempty independent-set necklaces constitute
the full six-site amplitude when the second tensor has zero trace and determinant. -/
theorem nilpotent_coordinates {R : Type*} [CommRing R] (T d k : R) :
    coordinates T 0 0 d 0 k =
      ![T ^ 3 - 6 * T ^ 2 * d + 9 * T * d ^ 2 - 2 * d ^ 3, (T ^ 2 - 3 * T * d + d ^ 2) * k,
        0, (T - d) * k ^ 2, 0, T * k ^ 2, 0, 0, 0, k ^ 3, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [coordinates] <;> ring

private theorem trace_rotate (l : List Bond) (n : ℕ) :
    (l.rotate n).prod.trace = l.prod.trace := by
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append, Matrix.trace_mul_comm,
    ← List.prod_append, List.take_append_drop]

private theorem traceWord_eq_of_rotate (A : Fin 2 → Bond) {u v : Word 6} {j : ℕ}
    (h : (List.ofFn u).rotate j = List.ofFn v) : traceWord 2 2 6 A u = traceWord 2 2 6 A v := by
  have he := congrArg (List.map A) h
  rw [List.map_rotate, List.map_ofFn, List.map_ofFn] at he
  change (List.ofFn (A ∘ u)).prod.trace = (List.ofFn (A ∘ v)).prod.trace
  rw [← he, trace_rotate]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Enumerate the rotations of the 64 six-letter words in the kernel.
private theorem exists_necklace :
    ∀ w : Word 6, ∃ i : Fin 14, ∃ j : Fin 6,
      (List.ofFn w).rotate j.val = List.ofFn (necklaces i) := by decide

/-- Equality on the six-site necklace amplitudes gives equality of all word amplitudes. -/
theorem traceWord_smul_of_necklaces (A B : Fin 2 → Bond) (a : ℂ)
    (h : traceWord 2 2 6 B ∘ necklaces = a • (traceWord 2 2 6 A ∘ necklaces)) :
    traceWord 2 2 6 B = a • traceWord 2 2 6 A := by
  funext w
  obtain ⟨i, j, he⟩ := exists_necklace w
  change traceWord 2 2 6 B w = a * traceWord 2 2 6 A w
  rw [traceWord_eq_of_rotate B he, traceWord_eq_of_rotate A he]
  exact congrFun h i

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCoordinates

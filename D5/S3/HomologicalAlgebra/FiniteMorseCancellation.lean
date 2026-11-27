/- GID: D5/S3/HomologicalAlgebra/FiniteMorseCancellation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FiniteMorseCancellation
   mirror-E: none(waiver:algebraic-inference)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLin]
   utility: none
   digest: Explicit finite polynomial chain contraction for a ranked signed matching. -/

import D5.S3.HomologicalAlgebra.FinitePerturbation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
An integral differential, with columns as inputs, is split into matched unit entries
and the remaining entries. A rank decreasing along unmatched downward and reversed
matched arrows bounds the finite perturbation polynomial. When all unmatched indices
have one size, the transferred differential vanishes by degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.HomologicalAlgebra.FiniteMorseCancellation

open Finset Matrix
open FinitePerturbation (Input inversePolynomial)

/-- A signed matching on an integral differential that lowers size by one. -/
structure Matching (F : Type*) [Fintype F] where
  d : F → ℕ
  mate : F → F
  D : Matrix F F ℤ
  involutive : Function.Involutive mate
  adjacent : ∀ j, mate j ≠ j → d (mate j) + 1 = d j ∨ d j + 1 = d (mate j)
  differential_sq : D * D = 0
  downward : ∀ i j, D i j ≠ 0 → d i + 1 = d j
  unit_entry : ∀ j, d (mate j) + 1 = d j → D (mate j) j ^ 2 = 1

namespace Matching

variable {F : Type*} [Fintype F] (m : Matching F)

abbrev Critical := {j : F // m.mate j = j}

variable [DecidableEq F]

/-- The matched downward part of the differential. -/
def A : Matrix F F ℤ :=
  Matrix.of fun i j => if i = m.mate j ∧ m.d i + 1 = m.d j then m.D i j else 0

/-- The upward matching uses the same sign as the downward differential entry. -/
def h : Matrix F F ℤ := m.A.transpose

def delta : Matrix F F ℤ := m.D - m.A

/-- Coordinate inclusion of the unmatched indices. -/
def i0 : Matrix F m.Critical ℤ := Matrix.of fun i j => if i = j.val then 1 else 0

/-- Coordinate restriction to the unmatched indices. -/
def p0 : Matrix m.Critical F ℤ := m.i0.transpose

private theorem A_entry {i j : F} (hne : m.A i j ≠ 0) :
    i = m.mate j ∧ m.d i + 1 = m.d j := by
  by_contra hn
  apply hne
  simp [A, hn]

private theorem A_off_column {i j : F} (hne : i ≠ m.mate j) : m.A i j = 0 := by
  simp [A, hne]

private theorem A_off_row {i j : F} (hne : j ≠ m.mate i) : m.A i j = 0 := by
  apply m.A_off_column
  intro hij
  apply hne
  rw [hij, m.involutive j]

/-- Multiplication by the matched differential acts on a single coordinate. -/
private theorem A_mul_apply {J : Type*} (B : Matrix F J ℤ) (i : F) (j : J) :
    (m.A * B) i j = m.A i (m.mate i) * B (m.mate i) j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_single (m.mate i)
    (fun l _ hne => by rw [m.A_off_row hne, zero_mul])
    (fun hmem => (hmem (Finset.mem_univ _)).elim)

private theorem h_mul_apply {J : Type*} (B : Matrix F J ℤ) (i : F) (j : J) :
    (m.h * B) i j = m.A (m.mate i) i * B (m.mate i) j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_single (m.mate i)
    (fun l _ hne => by rw [show m.h i l = m.A l i from rfl, m.A_off_column hne, zero_mul])
    (fun hmem => (hmem (Finset.mem_univ _)).elim)

private theorem A_sq : m.A * m.A = 0 := by
  ext i j
  rw [m.A_mul_apply, Matrix.zero_apply]
  by_cases hne : m.A i (m.mate i) = 0
  · rw [hne, zero_mul]
  · have hDown := (m.A_entry hne).2
    have hOther : m.A (m.mate i) j = 0 := by
      by_contra hn
      have hEntry := m.A_entry hn
      have hj : j = i := m.involutive.injective hEntry.1.symm
      subst j
      omega
    rw [hOther, mul_zero]

private theorem h_sq : m.h * m.h = 0 := by
  simpa only [h, Matrix.transpose_mul, Matrix.transpose_zero] using
    congrArg Matrix.transpose m.A_sq

private theorem p0_mul_apply {J : Type*} (B : Matrix F J ℤ) (i : m.Critical) (j : J) :
    (m.p0 * B) i j = B i.val j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i.val]
  · simp [p0, i0]
  · intro l _ hne
    simp [p0, i0, hne]
  · simp

private theorem mul_i0_apply {J : Type*} (B : Matrix J F ℤ) (i : J) (j : m.Critical) :
    (B * m.i0) i j = B i j.val := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j.val]
  · simp [i0]
  · intro l _ hne
    simp [i0, hne]
  · simp

private theorem i0_mul_p0_apply (i j : F) :
    (m.i0 * m.p0) i j = if i = j ∧ m.mate i = i then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : m.mate i = i
  · let c : m.Critical := ⟨i, hi⟩
    rw [Finset.sum_eq_single c]
    · simp [c, i0, p0, hi, eq_comm]
    · intro b _ hb
      have hne : i ≠ b.val := fun he => hb (Subtype.ext he.symm)
      simp [i0, hne]
    · simp
  · rw [ite_eq_right (fun h => hi h.2)]
    apply Finset.sum_eq_zero
    intro c _
    have hne : i ≠ c.val := by
      intro he
      exact hi (he ▸ c.property)
    simp [i0, hne]

private theorem p0_mul_i0 : m.p0 * m.i0 = 1 := by
  ext i j
  rw [m.p0_mul_apply, Matrix.one_apply]
  have he : i.val = j.val ↔ i = j := Subtype.val_inj
  simp [i0, he]

private theorem A_mul_i0 : m.A * m.i0 = 0 := by
  ext i j
  rw [m.mul_i0_apply, Matrix.zero_apply]
  by_contra hn
  have he := m.A_entry hn
  have hi := he.1.trans j.property
  have hd := he.2
  rw [hi] at hd
  omega

private theorem p0_mul_A : m.p0 * m.A = 0 := by
  ext i j
  rw [m.p0_mul_apply, Matrix.zero_apply]
  by_contra hn
  have he := m.A_entry hn
  have hj : j = i.val := m.involutive.injective (he.1.symm.trans i.property.symm)
  subst j
  omega

private theorem h_mul_i0 : m.h * m.i0 = 0 := by
  simpa only [h, p0, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
    using congrArg Matrix.transpose m.p0_mul_A

private theorem p0_mul_h : m.p0 * m.h = 0 := by
  simpa only [h, p0, Matrix.transpose_mul, Matrix.transpose_zero]
    using congrArg Matrix.transpose m.A_mul_i0

private theorem A_h_add_h_A : m.A * m.h + m.h * m.A = 1 - m.i0 * m.p0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, m.A_mul_apply, m.h_mul_apply,
    m.i0_mul_p0_apply, Matrix.one_apply]
  change m.A i (m.mate i) * m.A j (m.mate i) + m.A (m.mate i) i * m.A (m.mate i) j =
    (if i = j then 1 else 0) - (if i = j ∧ m.mate i = i then 1 else 0)
  by_cases hij : i = j
  · subst j
    by_cases hi : m.mate i = i
    · simp [A, hi]
    · obtain hUpper | hLower := m.adjacent i hi
      · have hNotLower : ¬m.d i + 1 = m.d (m.mate i) := by omega
        have hUnit := m.unit_entry i hUpper
        simpa [A, hi, m.involutive i, hUpper, hNotLower, pow_two] using hUnit
      · have hNotUpper : ¬m.d (m.mate i) + 1 = m.d i := by omega
        have hUnit := m.unit_entry (m.mate i) (by simpa only [m.involutive i] using hLower)
        simpa [A, hi, m.involutive i, hLower, hNotUpper, pow_two] using hUnit
  · have hne : j ≠ m.mate (m.mate i) := by simpa only [m.involutive i] using Ne.symm hij
    simp [m.A_off_column hne, m.A_off_row hne, hij]

private theorem exists_nonzero_mul_entry {L M N : Type*} [Fintype M]
    {B : Matrix L M ℤ} {E : Matrix M N ℤ} {i : L} {j : N} (hne : (B * E) i j ≠ 0) :
    ∃ l, B i l ≠ 0 ∧ E l j ≠ 0 := by
  rw [Matrix.mul_apply] at hne
  obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨l, left_ne_zero_of_mul hl, right_ne_zero_of_mul hl⟩

private theorem delta_entry {i j : F} (hne : m.delta i j ≠ 0) :
    i ≠ m.mate j ∧ m.D i j ≠ 0 := by
  have hd : m.D i j ≠ 0 := by
    intro hd
    apply hne
    simp [delta, A, hd]
  refine ⟨?_, hd⟩
  intro he
  apply hne
  subst i
  have hSize := m.downward (m.mate j) j hd
  simp [delta, A, hSize]

private theorem rank_mul (r : F → ℕ)
    (unmatched : ∀ i j, i ≠ m.mate j → m.D i j ≠ 0 → r i < r j)
    (matched : ∀ j, m.d j + 1 = m.d (m.mate j) → r (m.mate j) < r j)
    {i j : F} (hne : (m.h * m.delta) i j ≠ 0) : r i < r j := by
  obtain ⟨l, hl, hr⟩ := exists_nonzero_mul_entry hne
  have hUp := m.A_entry (show m.A l i ≠ 0 from hl)
  have hDown := m.delta_entry hr
  have hm : r i < r l := by
    obtain ⟨rfl, hSize⟩ := hUp
    simpa only [m.involutive i] using
      matched (m.mate i) (by simpa only [m.involutive i] using hSize)
  exact hm.trans (unmatched l j hDown.1 hDown.2)

private theorem rank_pow {B : Matrix F F ℤ} {r : F → ℕ}
    (decreases : ∀ i j, B i j ≠ 0 → r i < r j) (n : ℕ) {i j : F}
    (hne : (B ^ n) i j ≠ 0) : r i + n ≤ r j := by
  induction n generalizing i j with
  | zero =>
      have he : i = j := by simpa [Matrix.one_apply] using hne
      simp [he]
  | succ n ih =>
      rw [pow_succ] at hne
      obtain ⟨l, hl, hr⟩ := exists_nonzero_mul_entry hne
      have hn := ih hl
      have hlt := decreases l j hr
      omega

/-- A strict rank bound gives a nilpotence exponent for the perturbation polynomial. -/
private theorem perturbation_nilpotent (r : F → ℕ) (N : ℕ) (bound : ∀ j, r j < N)
    (unmatched : ∀ i j, i ≠ m.mate j → m.D i j ≠ 0 → r i < r j)
    (matched : ∀ j, m.d j + 1 = m.d (m.mate j) → r (m.mate j) < r j) :
    (m.h * m.delta) ^ N = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  by_contra hn
  have hpath := rank_pow (fun a b => m.rank_mul r unmatched matched (i := a) (j := b)) N hn
  have hb := bound j
  omega

/-- The coordinate retraction before adding the unmatched entries. -/
def perturbationInput : Input (R := ℤ) (U := m.Critical → ℤ) (V := F → ℤ) where
  d0 := Matrix.toLin' m.A
  h := Matrix.toLin' m.h
  delta := Matrix.toLin' m.delta
  i := Matrix.toLin' m.i0
  p := Matrix.toLin' m.p0
  d0_sq := by
    simpa only [Matrix.toLin'_mul, Module.End.mul_eq_comp, map_zero] using
      congrArg Matrix.toLin' m.A_sq
  pi := by
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_one] using congrArg Matrix.toLin' m.p0_mul_i0
  di := by
    simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' m.A_mul_i0
  pd := by
    simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' m.p0_mul_A
  contraction := by
    simpa only [map_add, map_sub, Matrix.toLin'_mul, Matrix.toLin'_one, Module.End.mul_eq_comp,
      Module.End.one_eq_id] using congrArg Matrix.toLin' m.A_h_add_h_A
  hh := by
    simpa only [Matrix.toLin'_mul, Module.End.mul_eq_comp, map_zero] using
      congrArg Matrix.toLin' m.h_sq
  hi := by
    simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' m.h_mul_i0
  ph := by
    simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' m.p0_mul_h
  perturbed_sq := by
    have he : m.A + m.delta = m.D := by simp [delta]
    change (Matrix.toLin' m.A + Matrix.toLin' m.delta) *
      (Matrix.toLin' m.A + Matrix.toLin' m.delta) = 0
    rw [← map_add, he, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, m.differential_sq, map_zero]


/-- The finite inverse of `1 + h * delta` for a valid nilpotence bound. -/
def K (N : ℕ) : Matrix F F ℤ := inversePolynomial (m.h * m.delta) N

/-- The finite inverse of `1 + delta * h` with the opposite nilpotence bound. -/
def J (N : ℕ) : Matrix F F ℤ := inversePolynomial (m.delta * m.h) (N + 1)

/-- The perturbed inclusion of the critical coordinates. -/
def I (N : ℕ) : Matrix F m.Critical ℤ := m.K N * m.i0

/-- The perturbed projection to the critical coordinates. -/
def P (N : ℕ) : Matrix m.Critical F ℤ := m.p0 * m.J N

/-- The signed homotopy that raises size by one. -/
def H (N : ℕ) : Matrix F F ℤ := m.K N * m.h

private theorem same_size_h_delta {i j : F} (hne : (m.h * m.delta) i j ≠ 0) :
    m.d i = m.d j := by
  obtain ⟨l, hl, hr⟩ := exists_nonzero_mul_entry hne
  exact (m.A_entry (show m.A l i ≠ 0 from hl)).2.symm.trans
    (m.downward l j (m.delta_entry hr).2)

private theorem same_size_delta_h {i j : F} (hne : (m.delta * m.h) i j ≠ 0) :
    m.d i = m.d j := by
  obtain ⟨l, hl, hr⟩ := exists_nonzero_mul_entry hne
  exact Nat.add_right_cancel ((m.downward i l (m.delta_entry hl).2).trans
    (m.A_entry (show m.A j l ≠ 0 from hr)).2.symm)

private theorem same_size_pow (B : Matrix F F ℤ)
    (preserves : ∀ i j, B i j ≠ 0 → m.d i = m.d j) (n : ℕ) {i j : F}
    (hne : (B ^ n) i j ≠ 0) : m.d i = m.d j := by
  induction n generalizing i j with
  | zero =>
      have he : i = j := by simpa [Matrix.one_apply] using hne
      rw [he]
  | succ n ih =>
      rw [pow_succ] at hne
      obtain ⟨l, hl, hr⟩ := exists_nonzero_mul_entry hne
      exact (ih hl).trans (preserves l j hr)

private theorem same_size_polynomial (B : Matrix F F ℤ)
    (preserves : ∀ i j, B i j ≠ 0 → m.d i = m.d j) (n : ℕ) {i j : F}
    (hne : inversePolynomial B n i j ≠ 0) : m.d i = m.d j := by
  simp only [inversePolynomial, Matrix.sum_apply] at hne
  obtain ⟨power, _, hpower⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact m.same_size_pow (-B) (by simpa only [Matrix.neg_apply, neg_ne_zero] using preserves)
    power hpower

private theorem inclusion_degree (N : ℕ) {i : F} {j : m.Critical}
    (hne : m.I N i j ≠ 0) : m.d i = m.d j.val := by
  rw [I, m.mul_i0_apply] at hne
  exact m.same_size_polynomial _ (fun _ _ => m.same_size_h_delta) N hne

private theorem projection_degree (N : ℕ) {i : m.Critical} {j : F}
    (hne : m.P N i j ≠ 0) : m.d i.val = m.d j := by
  rw [P, m.p0_mul_apply] at hne
  exact m.same_size_polynomial _ (fun _ _ => m.same_size_delta_h) (N + 1) hne

private theorem homotopy_degree (N : ℕ) {i j : F}
    (hne : m.H N i j ≠ 0) : m.d i = m.d j + 1 := by
  obtain ⟨l, hl, hr⟩ := exists_nonzero_mul_entry hne
  exact (m.same_size_polynomial _ (fun _ _ => m.same_size_h_delta) N hl).trans
    (m.A_entry (show m.A j l ≠ 0 from hr)).2.symm

private theorem transferred_matrix_zero (N k : ℕ)
    (critical_size : ∀ j, m.mate j = j → m.d j = k) :
    m.p0 * (m.delta * m.I N) = 0 := by
  ext i j
  rw [m.p0_mul_apply, Matrix.zero_apply]
  by_contra hn
  obtain ⟨l, hl, hr⟩ := exists_nonzero_mul_entry hn
  have hDown := m.downward i.val l (m.delta_entry hl).2
  have hSame := m.inclusion_degree N hr
  have hi := critical_size i.val i.property
  have hj := critical_size j.val j.property
  omega

private theorem toLin_polynomial (B : Matrix F F ℤ) (N : ℕ) :
    Matrix.toLin' (inversePolynomial B N) = inversePolynomial (Matrix.toLin' B) N := by
  change Matrix.toLinAlgEquiv' (inversePolynomial B N) =
    inversePolynomial (Matrix.toLinAlgEquiv' B) N
  simp only [inversePolynomial, map_sum, map_pow, map_neg]

private theorem toLin_K (N : ℕ) : Matrix.toLin' (m.K N) = m.perturbationInput.K N := by
  unfold K Input.K
  rw [toLin_polynomial, Matrix.toLin'_mul]
  rfl

private theorem toLin_J (N : ℕ) : Matrix.toLin' (m.J N) = m.perturbationInput.J N := by
  unfold J Input.J
  rw [toLin_polynomial, Matrix.toLin'_mul]
  rfl

private theorem toLin_I (N : ℕ) : Matrix.toLin' (m.I N) = m.perturbationInput.I N := by
  rw [I, Matrix.toLin'_mul, m.toLin_K]
  rfl

private theorem toLin_P (N : ℕ) : Matrix.toLin' (m.P N) = m.perturbationInput.P N := by
  rw [P, Matrix.toLin'_mul, m.toLin_J]
  rfl

private theorem toLin_H (N : ℕ) : Matrix.toLin' (m.H N) = m.perturbationInput.H N := by
  rw [H, Matrix.toLin'_mul, m.toLin_K]
  rfl

private theorem toLin_D : Matrix.toLin' m.D = m.perturbationInput.D := by
  change Matrix.toLin' m.D = Matrix.toLin' m.A + Matrix.toLin' m.delta
  rw [← map_add]
  congr 1
  simp [delta]

private theorem critical_inclusion (N : ℕ) (hN : 1 ≤ N) : m.p0 * m.I N = 1 := by
  have hp : m.p0 * m.K N = m.p0 := by
    rw [K, inversePolynomial, Matrix.mul_sum, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      rw [pow_succ', ← Matrix.mul_assoc, Matrix.mul_neg, ← Matrix.mul_assoc, m.p0_mul_h]
      simp
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hN))
  rw [I, ← Matrix.mul_assoc, hp, m.p0_mul_i0]

/-- The matrix identities and degree support of the explicit contraction. -/
structure Contraction (N : ℕ) : Prop where
  transferred_zero : m.p0 * (m.delta * m.I N) = 0
  inclusion_chain : m.D * m.I N = 0
  projection_chain : m.P N * m.D = 0
  retract : m.P N * m.I N = 1
  critical_coefficients : m.p0 * m.I N = 1
  homotopy : m.D * m.H N + m.H N * m.D = 1 - m.I N * m.P N
  inclusion_degree : ∀ i (j : m.Critical), m.I N i j ≠ 0 → m.d i = m.d j.val
  projection_degree : ∀ (i : m.Critical) j, m.P N i j ≠ 0 → m.d i.val = m.d j
  homotopy_degree : ∀ i j, m.H N i j ≠ 0 → m.d i = m.d j + 1

/-- A ranked signed matching with critical indices all of size `k` contracts
onto the critical coordinates, with the displayed finite polynomial formulas. -/
theorem finite_morse_cancellation (r : F → ℕ) (k N : ℕ) (positive : 1 ≤ N)
    (bound : ∀ j, r j < N)
    (unmatched : ∀ i j, i ≠ m.mate j → m.D i j ≠ 0 → r i < r j)
    (matched : ∀ j, m.d j + 1 = m.d (m.mate j) → r (m.mate j) < r j)
    (critical_size : ∀ j, m.mate j = j → m.d j = k) :
    m.Contraction N := by
  have nilpotent := m.perturbation_nilpotent r N bound unmatched matched
  have nilpotentLin : (m.perturbationInput.h * m.perturbationInput.delta) ^ N = 0 := by
    change (Matrix.toLin' m.h * Matrix.toLin' m.delta) ^ N = 0
    simpa only [Matrix.toLin'_pow, Matrix.toLin'_mul, Module.End.mul_eq_comp, map_zero] using
      congrArg Matrix.toLin' nilpotent
  have out := m.perturbationInput.finite_perturbation N positive nilpotentLin
  have transfer := m.transferred_matrix_zero N k critical_size
  have transferLin : m.perturbationInput.transferred N = 0 := by
    change (Matrix.toLin' m.p0).comp
      ((Matrix.toLin' m.delta).comp (m.perturbationInput.I N)) = 0
    simpa only [Matrix.toLin'_mul, m.toLin_I, map_zero] using congrArg Matrix.toLin' transfer
  refine ⟨transfer, ?_, ?_, ?_, m.critical_inclusion N positive, ?_, fun _ _ => m.inclusion_degree N,
    fun _ _ => m.projection_degree N, fun _ _ => m.homotopy_degree N⟩
  · apply Matrix.toLin'.injective
    simpa [Matrix.toLin'_mul, m.toLin_D, m.toLin_I, transferLin] using out.inclusion_chain
  · apply Matrix.toLin'.injective
    simpa [Matrix.toLin'_mul, m.toLin_D, m.toLin_P, transferLin] using out.projection_chain
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, m.toLin_P, m.toLin_I, Matrix.toLin'_one] using out.retract
  · apply Matrix.toLin'.injective
    simpa only [map_add, map_sub, Matrix.toLin'_mul, Matrix.toLin'_one, m.toLin_D, m.toLin_I,
      m.toLin_P, m.toLin_H, Module.End.mul_eq_comp, Module.End.one_eq_id] using out.homotopy

end Matching

end D5.S3.HomologicalAlgebra.FiniteMorseCancellation

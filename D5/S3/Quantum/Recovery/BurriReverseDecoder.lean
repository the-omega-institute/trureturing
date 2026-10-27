/- GID: D5/S3/Quantum/Recovery/BurriReverseDecoder
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReverseDecoder
   mirror-E: none(waiver:unfinished-actual-decoder-comparison)
   anchors: []
   utility: none
   digest: Explicit six-dimensional amplitude and literal source spaces for the reverse Burri instance. -/

import D5.S3.Quantum.Recovery.ReferencePetzChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

/-! The source environment is A times a copy of B, including its zero complement.
The active amplitude is the a=3 member of Burri's reverse-comparison construction.
The real four-parameter rotation keeps both polar blocks visible. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Recovery.BurriReverseDecoder

abbrev A := Fin 2
abbrev F := Fin 3
abbrev B := A × F
abbrev E := A × B
abbrev P := A × E

def sign (i : A) : ℝ := if i = 0 then 1 else -1
def amplitude (p q : B) : ℝ :=
  if p.2 = q.2 then
    if p.1 = q.1 then 3 else if p.2 = 0 then 1 else if p.2 = 1 then -1 else 0
  else if p.1 = q.1 ∧ ((p.2 = 0 ∧ q.2 = 2) ∨ (p.2 = 2 ∧ q.2 = 0))
    then sign p.1 else 0

def Y : Matrix B B ℂ := fun p q => amplitude p q
def rho : Matrix A A ℂ := (1 / 2 : ℂ) • 1
def output : Matrix B B ℂ := (1 / 62 : ℂ) • (Y * Y)

/-- The active source rotation, with no Hadamard radical in its entries. -/
def rotation (cp cm kp km : ℝ) (p q : B) : ℝ :=
  if p.2 = 0 ∧ q.2 = 0 then (cp + cm * sign p.1 * sign q.1) / 2
  else if p.2 = 2 ∧ q.2 = 2 then (cp * sign p.1 * sign q.1 + cm) / 2
  else if p.2 = 0 ∧ q.2 = 2 then
    (kp + km * sign p.1 * sign q.1) * sign q.1 / 2
  else if p.2 = 2 ∧ q.2 = 0 then
    -sign p.1 * (kp + km * sign p.1 * sign q.1) / 2
  else if p.2 = 1 ∧ q.2 = 1 ∧ p.1 = q.1 then 1 else 0

def activeU (cp cm kp km : ℝ) : Matrix B B ℂ :=
  fun p q => rotation cp cm kp km p q

/-- The prescribed active embedding into the literal twelve-dimensional E. -/
def embed (a : F) : E := (0, (0, a))
def active (e : E) : Prop := e.1 = 0 ∧ e.2.1 = 0

def V : Matrix (B × E) A ℂ := fun p i =>
  if active p.2 then Y (i, p.2.2.2) p.1 / (Real.sqrt 31 : ℂ) else 0
def noiseKraus (e : E) : Matrix B A ℂ := fun b i => V (b, e) i

/-- The fixed ancillary vector is |0> on R' times |0> on A'. -/
def ancilla (i j : A) : ℂ := if i = 0 ∧ j = 0 then 1 else 0
def prepare : Matrix P B ℂ := fun p b =>
  if p.2.2 = b then ancilla p.1 p.2.1 else 0
def sourceSwap : Equiv.Perm P where
  toFun p := (p.2.2.1, (p.2.1, (p.1, p.2.2.2)))
  invFun p := (p.2.2.1, (p.2.1, (p.1, p.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl
def W : Matrix P P ℂ := sourceSwap.permMatrix ℂ

def inject : Matrix P B ℂ := fun p b =>
  if active p.2 ∧ (p.1, p.2.2.2) = b then 1 else 0

/-- The active unitary is extended by identity on the unused eighteen coordinates. -/
def sourceU (cp cm kp km : ℝ) : Matrix P P ℂ := fun p q =>
  if active p.2 ∧ active q.2 then activeU cp cm kp km (p.1, p.2.2.2) (q.1, q.2.2.2)
  else if p = q then 1 else 0
def sourceKraus (cp cm kp km : ℝ) (e : E) : Matrix A P ℂ :=
  fun k p => (sourceU cp cm kp km * W) (k, e) p
def swKraus (cp cm kp km : ℝ) (e : E) : Matrix A B ℂ :=
  sourceKraus cp cm kp km e * prepare

/-- Environment-slice matrices, later identified with the ordinary Petz map. -/
def slice (e : E) : Matrix A B ℂ := fun i b =>
  if active e ∧ (i, e.2.2) = b then 1 else 0

private theorem root31 : (Real.sqrt 31) ^ 2 = 31 ∧ Real.sqrt 31 ≠ 0 :=
  ⟨Real.sq_sqrt (by norm_num), ne_of_gt (Real.sqrt_pos.2 (by norm_num))⟩

theorem amplitude_adjoint : Yᴴ = Y := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [Y, amplitude, sign, Matrix.conjTranspose_apply]

theorem noise_normalization : (∑ e : E, (noiseKraus e)ᴴ * noiseKraus e) = 1 := by
  obtain ⟨hs, hn⟩ := root31
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [noiseKraus, V, active, Y, amplitude, sign, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.ext_iff,
      Complex.div_re, Complex.div_im]
  all_goals field_simp <;> nlinarith

theorem noise_output : (∑ e : E, noiseKraus e * rho * (noiseKraus e)ᴴ) = output := by
  obtain ⟨hs, hn⟩ := root31
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [noiseKraus, V, active, Y, amplitude, sign, rho, output,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Complex.ext_iff, Complex.div_re, Complex.div_im]
  all_goals field_simp <;> nlinarith

theorem physical_channel : ∃ channel : QuantumChannel A B, ∀ T : Matrix A A ℂ,
    CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ e : E, noiseKraus e * T * (noiseKraus e)ᴴ :=
  finite_kraus_quantum_channel noiseKraus noise_normalization

theorem rotation_unitary (cp cm kp km : ℝ)
    (hp : cp ^ 2 + kp ^ 2 = 1) (hm : cm ^ 2 + km ^ 2 = 1) :
    (activeU cp cm kp km)ᴴ * activeU cp cm kp km = 1 ∧
    activeU cp cm kp km * (activeU cp cm kp km)ᴴ = 1 := by
  constructor <;> ext ⟨i, a⟩ ⟨j, b⟩
  all_goals fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [activeU, rotation, sign, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Complex.ext_iff, Complex.div_re, Complex.div_im]
  all_goals nlinarith

theorem source_injection : W * prepare = inject := by
  ext p b
  rw [Matrix.mul_apply]
  simp [W, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    sourceSwap, prepare, ancilla, inject, active, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three]
  rcases p with ⟨i, j, k, a⟩
  rcases b with ⟨l, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases a <;>
    fin_cases l <;> fin_cases b <;> norm_num

theorem supported_rows (cp cm kp km : ℝ) (e : E) (i : A) (b : B) :
    swKraus cp cm kp km e i b =
      if active e then activeU cp cm kp km (i, e.2.2) b else 0 := by
  have h : swKraus cp cm kp km e =
      (sourceU cp cm kp km * inject).submatrix (fun i => (i, e)) id := by
    unfold swKraus sourceKraus
    ext k q
    change ((sourceU cp cm kp km * W) * prepare) (k, e) q = _
    rw [Matrix.mul_assoc, source_injection]
    rfl
  rw [h]
  rcases e with ⟨j, k, a⟩
  rcases b with ⟨l, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases a <;>
    fin_cases l <;> fin_cases b <;>
    simp [Matrix.submatrix_apply, Matrix.mul_apply, sourceU, inject, active,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]

/-- The exact polynomial certificate before imposing either circle equation. -/
theorem gap_sos (cp cm kp km : ℝ) :
    108 - ((4 * cp + 2 * cm + kp + km) ^ 2 + 36 +
      (3 * cp + 3 * cm - (kp + km)) ^ 2) =
      16 * (cp - cm) ^ 2 + (cp - cm - (kp + km)) ^ 2 +
      14 * (kp + km) ^ 2 + (kp + km + 3 * (kp - km)) ^ 2 +
      9 * (kp - km) ^ 2 + 42 * (1 - cp ^ 2 - kp ^ 2) +
      30 * (1 - cm ^ 2 - km ^ 2) := by ring

theorem gap_positive (cp cm kp km : ℝ)
    (hp : cp ^ 2 + kp ^ 2 = 1) (hm : cm ^ 2 + km ^ 2 = 1)
    (hk : 0 < kp + km) :
    0 < 108 - ((4 * cp + 2 * cm + kp + km) ^ 2 + 36 +
      (3 * cp + 3 * cm - (kp + km)) ^ 2) := by
  rw [gap_sos]
  have hk2 : 0 < (kp + km) ^ 2 := sq_pos_of_pos hk
  nlinarith [sq_nonneg (cp - cm), sq_nonneg (cp - cm - (kp + km)),
    sq_nonneg (kp + km + 3 * (kp - km)), sq_nonneg (kp - km)]

#print axioms physical_channel
#print axioms rotation_unitary
#print axioms source_injection
#print axioms supported_rows
#print axioms gap_positive

end D5.S3.Quantum.Recovery.BurriReverseDecoder

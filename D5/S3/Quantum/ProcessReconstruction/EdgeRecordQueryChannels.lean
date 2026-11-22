/- GID: D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The hidden-input oracles act by basis measurement and diagonal preparation. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FinitePreparationChannel
import D5.S3.Quantum.Foundation.TraceNormTensorProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! The hidden-input oracle as basis measurement followed by diagonal preparation. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.EnvironmentRecords.HiddenInput

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FinitePreparationChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit
  (traceNorm_kronecker)

abbrev Bit := ZMod 2
abbrev Word (n : ℕ) := Fin n → Bit

def parity {n : ℕ} (y : Word n) : Bit := ∑ i, y i

theorem card_word (n : ℕ) : Fintype.card (Word n) = 2 ^ n := by simp

private theorem parity_cons {n : ℕ} (c : Bit) (w : Word n) :
    parity (Fin.cons c w) = c + parity w := by
  simp [parity, Fin.sum_univ_succ]

private def parityFiber {n : ℕ} (b : Bit) :
    Word n ≃ {y : Word (n + 1) // parity y = b} where
  toFun w := ⟨Fin.cons (b - parity w) w, by rw [parity_cons, sub_add_cancel]⟩
  invFun y := Fin.tail y.val
  left_inv w := Fin.tail_cons _ _
  right_inv y := by
    apply Subtype.ext
    have h := y.property
    rw [parity, Fin.sum_univ_succ] at h
    have hhead : b - parity (Fin.tail y.val) = y.val 0 := by
      apply (sub_eq_iff_eq_add).2
      exact h.symm
    change Fin.cons (b - parity (Fin.tail y.val)) (Fin.tail y.val) = y.val
    rw [hhead, Fin.cons_self_tail]

variable {n : ℕ}

/-- Uniform output probability on the words of length `n`. -/
def uniformMass (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- The marked row has doubled mass on the parity fiber. -/
def parityMass (b : Bit) (y : Word (n + 1)) : ℝ :=
  if parity y = b then 2 * uniformMass (n + 1) else 0

def markedMass (a : Word (n + 1)) (b : Bit) (x y : Word (n + 1)) : ℝ :=
  if x = a then parityMass b y else uniformMass (n + 1)

theorem uniformMass_nonneg (n : ℕ) : 0 ≤ uniformMass n := by
  unfold uniformMass
  positivity

private theorem sum_uniformMass (n : ℕ) : ∑ _ : Word n, uniformMass n = 1 := by
  simp [uniformMass, nsmul_eq_mul]

private theorem sum_parityMass (b : Bit) : ∑ y : Word (n + 1), parityMass b y = 1 := by
  classical
  unfold parityMass
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  rw [Finset.subtype_univ]
  rw [Finset.sum_const, Finset.card_univ, ← Fintype.card_congr (parityFiber b), card_word]
  simp [nsmul_eq_mul, uniformMass, pow_succ]

private def diagonalState {A : Type*} [Fintype A] [DecidableEq A] (p : A → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : DensityState A :=
  ⟨CStarMatrix.ofMatrix (diagonal fun i => (p i : ℂ)), by
    apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact (Matrix.PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (hp i)).nonneg, by
    change (diagonal fun i => (p i : ℂ)).trace = 1
    rw [Matrix.trace_diagonal]
    exact_mod_cast hs⟩

private def prepare {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (p : A → B → ℝ) (hp : ∀ x y, 0 ≤ p x y) (hs : ∀ x, ∑ y, p x y = 1) :
    A → DensityState B :=
  fun x => diagonalState (p x) (hp x) (hs x)

def uniformPrepared (n : ℕ) : Word n → DensityState (Word n) :=
  prepare (fun _ _ => uniformMass n) (fun _ _ => uniformMass_nonneg n)
    (fun _ => sum_uniformMass n)

def markedPrepared (a : Word (n + 1)) (b : Bit) : Word (n + 1) → DensityState (Word (n + 1)) :=
  prepare (markedMass a b) (fun x y => by
    unfold markedMass parityMass
    split_ifs <;> [exact mul_nonneg (by norm_num) (uniformMass_nonneg _); rfl;
      exact uniformMass_nonneg _]) (fun x => by
    by_cases hx : x = a
    · simpa only [markedMass, hx, ite_true] using sum_parityMass (n := n) b
    · simpa only [markedMass, hx, ite_false] using sum_uniformMass (n + 1))

def preparationChannel {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (p : A → DensityState B) :
    QuantumChannel A B :=
  (finite_preparation_quantum_channel p).choose

def uniformChannel (n : ℕ) : QuantumChannel (Word n) (Word n) :=
  preparationChannel (uniformPrepared n)

def markedChannel (a : Word (n + 1)) (b : Bit) : QuantumChannel (Word (n + 1)) (Word (n + 1)) :=
  preparationChannel (markedPrepared a b)

theorem uniformChannel_action (X : Matrix (Word n) (Word n) ℂ) :
    act (uniformChannel n) X = diagonal (fun _ => X.trace * (uniformMass n : ℂ)) := by
  have h := (finite_preparation_quantum_channel (uniformPrepared n)).choose_spec X
  change act (uniformChannel n) X = _ at h
  rw [h]
  ext y z
  by_cases hyz : y = z
  · subst z
    simp [uniformPrepared, prepare, diagonalState, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.trace, Finset.sum_mul]
  · simp [uniformPrepared, prepare, diagonalState, Matrix.sum_apply, Matrix.smul_apply, hyz]

theorem markedChannel_action (a : Word (n + 1)) (b : Bit)
    (X : Matrix (Word (n + 1)) (Word (n + 1)) ℂ) :
    act (markedChannel a b) X =
      diagonal (fun y => ∑ x, X x x * (markedMass a b x y : ℂ)) := by
  have h := (finite_preparation_quantum_channel (markedPrepared a b)).choose_spec X
  change act (markedChannel a b) X = _ at h
  rw [h]
  ext y z
  by_cases hyz : y = z
  · subst z
    simp [markedPrepared, prepare, diagonalState, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  · simp [markedPrepared, prepare, diagonalState, Matrix.sum_apply, Matrix.smul_apply, hyz]

section Reference

variable {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

theorem reference_preparation_entry (p : A → DensityState B) (ρ : DensityState (R × A))
    (r s : R) (y z : B) :
    CStarMatrix.ofMatrix.symm (referenceState (preparationChannel p) ρ).1 (r, y) (s, z) =
      ∑ x, ρ.1 (r, x) (s, x) * CStarMatrix.ofMatrix.symm (p x).1 y z := by
  have h := (finite_preparation_quantum_channel p).choose_spec
    (fun i j => ρ.1 (r, i) (s, j))
  change (CStarMatrix.ofMatrix.symm
    ((preparationChannel p).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix fun i j => ρ.1 (r, i) (s, j)))) y z = _
  change CStarMatrix.ofMatrix.symm
    ((preparationChannel p).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix fun i j => ρ.1 (r, i) (s, j))) = _ at h
  rw [h]
  simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- The reference extension of a basis preparation agrees with a native CPTP map. -/
theorem preparation_reference_contract (p : A → DensityState A) (ρ σ : DensityState (R × A)) :
    traceDistance (referenceState (preparationChannel p) ρ)
      (referenceState (preparationChannel p) σ) ≤ traceDistance ρ σ := by
  obtain ⟨C, hC⟩ := finite_local_preparation_quantum_channel (s := R) p
  have he (τ : DensityState (R × A)) :
      C.mapState τ = referenceState (preparationChannel p) τ := by
    apply Subtype.ext
    ext ⟨r, y⟩ ⟨s, z⟩
    exact (hC (CStarMatrix.ofMatrix.symm τ.1) (r, y) (s, z)).trans
      (reference_preparation_entry p τ r s y z).symm
  simpa only [he] using traceDistance_contract C ρ σ

/-- The reference block selected by outcome `a` on the queried register. -/
def referenceBlock (ρ : DensityState (R × A)) (a : A) : Matrix R R ℂ :=
  (CStarMatrix.ofMatrix.symm ρ.1).submatrix (fun r => (r, a)) (fun r => (r, a))

theorem referenceBlock_positive (ρ : DensityState (R × A)) (a : A) :
    (referenceBlock ρ a).PosSemidef :=
  (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1).posSemidef.submatrix _

def queryMass (ρ : DensityState (R × A)) (a : A) : ℝ := (referenceBlock ρ a).trace.re

theorem queryMass_nonneg (ρ : DensityState (R × A)) (a : A) : 0 ≤ queryMass ρ a :=
  (Complex.nonneg_iff.mp (referenceBlock_positive ρ a).trace_nonneg).1

theorem referenceBlock_traceNorm (ρ : DensityState (R × A)) (a : A) :
    traceNorm (referenceBlock ρ a) = queryMass ρ a := by
  have h := congrArg Complex.re (traceNorm_of_posSemidef (referenceBlock_positive ρ a))
  change (Complex.ofReal (traceNorm (referenceBlock ρ a))).re = _ at h
  exact (Complex.ofReal_re _).symm.trans h

theorem sum_queryMass (ρ : DensityState (R × A)) : ∑ a, queryMass ρ a = 1 := by
  unfold queryMass referenceBlock
  rw [← Complex.re_sum]
  change (∑ a : A, ∑ r : R, ρ.1 (r, a) (r, a)).re = 1
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (fun p : R × A => ρ.1 p p)]
  change (Matrix.trace ρ.1).re = 1
  simp only [ρ.2.2, Complex.one_re]

end Reference

/-- The sign is positive exactly when the prepared parity is the observed parity. -/
def paritySign (b : Bit) (y : Word (n + 1)) : ℝ := if parity y = b then 1 else -1

theorem paritySign_eq_pow (b : Bit) (y : Word (n + 1)) :
    paritySign b y = (-1 : ℝ) ^ (b + parity y).val := by
  unfold paritySign
  generalize parity y = c
  by_cases h : c = b
  · rw [ite_eq_left h, h, show b + b = 0 from (by decide : ∀ v : Bit, v + v = 0) b]
    rw [show (0 : Bit).val = 0 by decide, pow_zero]
  · rw [ite_eq_right h, show b + c = 1 from
      (by decide : ∀ v w : Bit, w ≠ v → v + w = 1) b c h]
    rw [show (1 : Bit).val = 1 by decide, pow_one]

def signedDiagonal (b : Bit) : Matrix (Word (n + 1)) (Word (n + 1)) ℂ :=
  diagonal fun y => (paritySign b y * uniformMass (n + 1) : ℝ)

theorem signedDiagonal_entry (b : Bit) (y : Word (n + 1)) :
    signedDiagonal b y y = (((-1 : ℝ) ^ (b + parity y).val / 2 ^ (n + 1)) : ℂ) := by
  simp [signedDiagonal, paritySign_eq_pow, uniformMass, div_eq_mul_inv]

private theorem parityMass_sub_uniform (b : Bit) (y : Word (n + 1)) :
    parityMass b y - uniformMass (n + 1) = paritySign b y * uniformMass (n + 1) := by
  unfold parityMass paritySign
  split <;> ring

private theorem traceNorm_real_diagonal {A : Type} [Fintype A] [DecidableEq A] (f : A → ℝ) :
    traceNorm (diagonal fun x => (f x : ℂ)) = ∑ x, |f x| := by
  let D := diagonal fun x => Complex.ofReal (|f x|)
  have hD : D.PosSemidef :=
    Matrix.PosSemidef.diagonal fun x => Complex.zero_le_real.mpr (abs_nonneg (f x))
  have hgram (g : A → ℝ) :
      (diagonal fun x => (g x : ℂ))ᴴ * (diagonal fun x => (g x : ℂ)) =
        diagonal fun x => ((g x * g x : ℝ) : ℂ) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp
  have hsq : (diagonal fun x => ((|f x| * |f x| : ℝ) : ℂ)) =
      diagonal fun x => ((f x * f x : ℝ) : ℂ) := by
    congr 1
    funext x
    exact_mod_cast (show |f x| * |f x| = f x * f x by simpa only [pow_two] using sq_abs (f x))
  calc
    _ = traceNorm D := by
      unfold traceNorm D
      rw [hgram, hgram, hsq]
    _ = _ := by
      simpa [D, Matrix.trace_diagonal, map_sum] using
        congrArg Complex.re (traceNorm_of_posSemidef hD)

theorem signedDiagonal_traceNorm (b : Bit) : traceNorm (signedDiagonal (n := n) b) = 1 := by
  unfold signedDiagonal
  rw [traceNorm_real_diagonal, ← sum_uniformMass (n + 1)]
  apply Finset.sum_congr rfl
  intro y _
  rw [abs_mul, abs_of_nonneg (uniformMass_nonneg _)]
  have h : |paritySign b y| = 1 := by unfold paritySign; split <;> norm_num
  rw [h, one_mul]

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The exact marked-minus-uniform output, with the reference register first. -/
theorem reference_difference (a : Word (n + 1)) (b : Bit) (ρ : DensityState (R × Word (n + 1))) :
    CStarMatrix.ofMatrix.symm (referenceState (markedChannel a b) ρ).1 -
      CStarMatrix.ofMatrix.symm (referenceState (uniformChannel (n + 1)) ρ).1 =
        referenceBlock ρ a ⊗ₖ signedDiagonal b := by
  ext ⟨r, y⟩ ⟨s, z⟩
  simp only [Matrix.sub_apply, markedChannel, uniformChannel, reference_preparation_entry,
    markedPrepared, uniformPrepared, prepare, diagonalState, Matrix.kronecker_apply]
  change (∑ x, ρ.1 (r, x) (s, x) * diagonal (fun w => (markedMass a b x w : ℂ)) y z) -
    (∑ x, ρ.1 (r, x) (s, x) * diagonal (fun _ => (uniformMass (n + 1) : ℂ)) y z) =
    ρ.1 (r, a) (s, a) * signedDiagonal b y z
  rw [← Finset.sum_sub_distrib]
  by_cases hyz : y = z
  · subst z
    simp only [Matrix.diagonal_apply_eq, signedDiagonal, ← mul_sub, ← Complex.ofReal_sub]
    have h (x : Word (n + 1)) : markedMass a b x y - uniformMass (n + 1) =
        if x = a then paritySign b y * uniformMass (n + 1) else 0 := by
      by_cases hx : x = a <;> simp [markedMass, hx, parityMass_sub_uniform]
    simp [h, apply_ite Complex.ofReal, mul_ite]
  · simp [Matrix.diagonal_apply_ne _ hyz, signedDiagonal]

/-- The unhalved trace norm for a call equals the baseline input's probability of the mark. -/
theorem referenceError_exact (a : Word (n + 1)) (b : Bit) (ρ : DensityState (R × Word (n + 1))) :
    referenceError (markedChannel a b) (uniformChannel (n + 1)) ρ = queryMass ρ a := by
  rw [referenceError, reference_difference, traceNorm_kronecker, signedDiagonal_traceNorm, mul_one]
  exact referenceBlock_traceNorm ρ a

theorem reference_traceDistance_exact (a : Word (n + 1)) (b : Bit)
    (ρ : DensityState (R × Word (n + 1))) :
    traceDistance (referenceState (markedChannel a b) ρ)
      (referenceState (uniformChannel (n + 1)) ρ) = queryMass ρ a / 2 :=
  congrArg (fun x : ℝ => x / 2) (referenceError_exact a b ρ)

private theorem opposite_sign (y : Word (n + 1)) : paritySign 1 y = -paritySign 0 y := by
  rcases (show ∀ b : Bit, b = 0 ∨ b = 1 by decide) (parity y) with h | h
  · simp [paritySign, h, show (0 : Bit) ≠ 1 by decide]
  · simp [paritySign, h, show (1 : Bit) ≠ 0 by decide]

private theorem opposite_signedDiagonal_traceNorm :
    traceNorm (signedDiagonal (n := n) 0 - signedDiagonal 1) = 2 := by
  have h : signedDiagonal (n := n) 0 - signedDiagonal 1 =
      diagonal (fun y => ((2 * (paritySign 0 y * uniformMass (n + 1)) : ℝ) : ℂ)) := by
    ext y z
    by_cases hyz : y = z
    · subst z
      simp [signedDiagonal, opposite_sign]
      ring
    · simp [signedDiagonal, hyz]
  rw [h, traceNorm_real_diagonal]
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← Finset.mul_sum]
  have hOne := signedDiagonal_traceNorm (n := n) 0
  rw [signedDiagonal, traceNorm_real_diagonal] at hOne
  simp only [abs_mul] at hOne
  rw [hOne, mul_one]

/-- The two marked branches have unhalved error twice the selected input probability. -/
theorem markedPair_referenceError (a : Word (n + 1)) (ρ : DensityState (R × Word (n + 1))) :
    referenceError (markedChannel a 0) (markedChannel a 1) ρ = 2 * queryMass ρ a := by
  let A := CStarMatrix.ofMatrix.symm (referenceState (markedChannel a 0) ρ).1
  let B := CStarMatrix.ofMatrix.symm (referenceState (markedChannel a 1) ρ).1
  let U := CStarMatrix.ofMatrix.symm (referenceState (uniformChannel (n + 1)) ρ).1
  change traceNorm (A - B) = _
  rw [show A - B = (A - U) - (B - U) by abel, reference_difference, reference_difference]
  have h : referenceBlock ρ a ⊗ₖ signedDiagonal (n := n) 0 -
      referenceBlock ρ a ⊗ₖ signedDiagonal 1 =
        referenceBlock ρ a ⊗ₖ (signedDiagonal 0 - signedDiagonal 1) := by
    ext ⟨r, y⟩ ⟨s, z⟩
    simp only [Matrix.sub_apply, Matrix.kronecker_apply, mul_sub]
  rw [h, traceNorm_kronecker, opposite_signedDiagonal_traceNorm, referenceBlock_traceNorm, mul_comm]

private def markedProbe (a : Word (n + 1)) : DensityState (Fin 1 × Word (n + 1)) :=
  diagonalState (fun p => if p = (0, a) then 1 else 0)
    (fun p => by split <;> norm_num) (by simp)

private theorem markedProbe_queryMass (a : Word (n + 1)) :
    queryMass (markedProbe a) a = 1 := by
  simp [queryMass, referenceBlock, markedProbe, diagonalState, Matrix.trace]

private theorem referenceError_le_two (C D : QuantumChannel (Word (n + 1)) (Word (n + 1)))
    (ρ : DensityState (R × Word (n + 1))) : referenceError C D ρ ≤ 2 := by
  have h : referenceError C D ρ / 2 ≤ 1 :=
    traceDistance_le_one (referenceState C ρ) (referenceState D ρ)
  linarith

private theorem diamond_values_bounded (C D : QuantumChannel (Word (n + 1)) (Word (n + 1))) :
    BddAbove ({0} ∪ {x : ℝ | ∃ k : ℕ, ∃ ρ : DensityState (Fin k × Word (n + 1)),
      x = referenceError C D ρ}) := by
  refine ⟨2, ?_⟩
  rintro x (hx | ⟨k, ρ, rfl⟩)
  · simp at hx
    simp [hx]
  · exact referenceError_le_two C D ρ

private theorem probe_error_le_diamond
    (C D : QuantumChannel (Word (n + 1)) (Word (n + 1))) (a : Word (n + 1)) :
    referenceError C D (markedProbe a) ≤ diamondDistance C D :=
  le_csSup (diamond_values_bounded C D) (Or.inr ⟨1, markedProbe a, rfl⟩)

theorem markedPair_diamond (a : Word (n + 1)) :
    diamondDistance (markedChannel a 0) (markedChannel a 1) = 2 := by
  apply le_antisymm
  · unfold diamondDistance
    refine csSup_le ⟨(0 : ℝ), Or.inl rfl⟩ ?_
    rintro x (hx | ⟨k, ρ, rfl⟩)
    · simp at hx
      simp [hx]
    · exact referenceError_le_two _ _ ρ
  · have h := probe_error_le_diamond (markedChannel a 0) (markedChannel a 1) a
    simpa only [markedPair_referenceError, markedProbe_queryMass, mul_one] using h

/-- An estimate of unhalved diamond error strictly below one belongs to at most one branch. -/
theorem markedPair_diamond_balls_disjoint (a : Word (n + 1))
    (C : QuantumChannel (Word (n + 1)) (Word (n + 1)))
    (h0 : diamondDistance (markedChannel a 0) C < 1)
    (h1 : diamondDistance (markedChannel a 1) C < 1) : False := by
  let ρ := markedProbe a
  let A := referenceState (markedChannel a 0) ρ
  let B := referenceState (markedChannel a 1) ρ
  let D := referenceState C ρ
  have hs : referenceError (markedChannel a 0) (markedChannel a 1) ρ = 2 := by
    rw [markedPair_referenceError, show queryMass ρ a = 1 from markedProbe_queryMass a, mul_one]
  have ht := traceDistance_triangle A D B
  rw [traceDistance_symm D B] at ht
  change referenceError (markedChannel a 0) (markedChannel a 1) ρ / 2 ≤
    referenceError (markedChannel a 0) C ρ / 2 + referenceError (markedChannel a 1) C ρ / 2 at ht
  linarith [probe_error_le_diamond (markedChannel a 0) C a,
    probe_error_le_diamond (markedChannel a 1) C a]

end D5.S3.Quantum.EnvironmentRecords.HiddenInput

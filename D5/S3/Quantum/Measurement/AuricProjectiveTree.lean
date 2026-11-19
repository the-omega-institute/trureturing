import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! # Finite same-register projective trees with recorded terminal flags -/

namespace D5.S3.Quantum.Measurement.AuricProjectiveTree

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complete Lüders measurement, including the zero-outcome components. -/
structure CompletePVM (n : Type*) [Fintype n] [DecidableEq n] (k : ℕ) where
  proj : Fin k → Matrix n n ℂ
  hermitian : ∀ i, (proj i).IsHermitian
  idempotent : ∀ i, proj i * proj i = proj i
  orthogonal : ∀ i j, i ≠ j → proj i * proj j = 0
  complete : ∑ i, proj i = 1

/-- Each internal node applies its unitary and its PVM on the same register.
A leaf applies a final unitary and deterministically records its flag. -/
inductive Protocol (n : Type*) [Fintype n] [DecidableEq n] : Type _
  | leaf (flag : Fin 2) (unitary : Matrix.unitaryGroup n ℂ)
  | branch (unitary : Matrix.unitaryGroup n ℂ) (k : ℕ) (pvm : CompletePVM n k)
      (descend : Fin k → Protocol n)

def Terminal : Protocol n → Type
  | .leaf _ _ => Unit
  | .branch _ _ _ descend => Sigma fun i => Terminal (descend i)

@[instance_reducible]
def terminalFintype (p : Protocol n) : Fintype (Terminal p) :=
  match p with
  | .leaf _ _ => inferInstanceAs (Fintype Unit)
  | .branch _ k _ descend =>
    letI : ∀ i : Fin k, Fintype (Terminal (descend i)) := fun i => terminalFintype (descend i)
    inferInstanceAs (Fintype (Sigma fun i => Terminal (descend i)))

instance (p : Protocol n) : Fintype (Terminal p) := terminalFintype p

def flag : (p : Protocol n) → Terminal p → Fin 2
  | .leaf j _, _ => j
  | .branch _ _ _ descend, ⟨i, h⟩ => flag (descend i) h

def kraus : (p : Protocol n) → Terminal p → Matrix n n ℂ
  | .leaf _ u, _ => u.val
  | .branch u _ pvm descend, ⟨i, h⟩ => kraus (descend i) h * (pvm.proj i * u.val)

private theorem sum_effects_postcompose {h : Type*} [Fintype h]
    (K : h → Matrix n n ℂ) (B : Matrix n n ℂ) :
    ∑ i, (K i * B)ᴴ * (K i * B) = Bᴴ * (∑ i, (K i)ᴴ * K i) * B := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply sum_congr rfl
  intro i _
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The effect of a projective outcome includes every descendant history. -/
theorem sum_child_effects_of_normalized {h : Type*} [Fintype h] {k : ℕ}
    (u : Matrix.unitaryGroup n ℂ) (pvm : CompletePVM n k) (i : Fin k)
    (K : h → Matrix n n ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) :
    ∑ j, (K j * (pvm.proj i * u.val))ᴴ * (K j * (pvm.proj i * u.val)) =
      u.valᴴ * pvm.proj i * u.val := by
  rw [sum_effects_postcompose, hK, Matrix.mul_one, Matrix.conjTranspose_mul,
    (pvm.hermitian i).eq, Matrix.mul_assoc u.valᴴ,
    ← Matrix.mul_assoc (pvm.proj i), pvm.idempotent, ← Matrix.mul_assoc]

/-- The full fine Kraus family is normalized on the entire register. -/
theorem sum_terminal_effects (p : Protocol n) :
    ∑ h : Terminal p, (kraus p h)ᴴ * kraus p h = 1 := by
  classical
  induction p with
  | leaf j u =>
    change (∑ _ : Unit, u.valᴴ * u.val) = 1
    simpa only [Fintype.sum_unique, ← Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem u.prop
  | branch u k pvm descend ih =>
    change ∑ h : Sigma (fun i => Terminal (descend i)),
      (kraus (descend h.1) h.2 * (pvm.proj h.1 * u.val))ᴴ *
        (kraus (descend h.1) h.2 * (pvm.proj h.1 * u.val)) = 1
    rw [Fintype.sum_sigma]
    simp_rw [fun i : Fin k =>
      sum_child_effects_of_normalized u pvm i (kraus (descend i)) (ih i)]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, pvm.complete, Matrix.mul_one,
      ← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem u.prop

/-- Pull the coarsened first PVM back through the unitary before it. -/
def firstGroupEffect {k : ℕ} (u : Matrix.unitaryGroup n ℂ) (pvm : CompletePVM n k)
    (s : Finset (Fin k)) : Matrix n n ℂ :=
  u.valᴴ * (∑ i ∈ s, pvm.proj i) * u.val

/-- The descendants of every group of first outcomes retain exactly the
pulled-back effect of that group. -/
theorem sum_group_terminal_effects {k : ℕ} (u : Matrix.unitaryGroup n ℂ)
    (pvm : CompletePVM n k) (descend : Fin k → Protocol n) (s : Finset (Fin k)) :
    (∑ i ∈ s, ∑ h : Terminal (descend i),
      (kraus (.branch u k pvm descend) ⟨i, h⟩)ᴴ *
        kraus (.branch u k pvm descend) ⟨i, h⟩) = firstGroupEffect u pvm s := by
  change (∑ i ∈ s, ∑ h : Terminal (descend i),
    (kraus (descend i) h * (pvm.proj i * u.val))ᴴ *
      (kraus (descend i) h * (pvm.proj i * u.val))) = _
  simp_rw [fun i : Fin k => sum_child_effects_of_normalized u pvm i (kraus (descend i))
    (sum_terminal_effects (descend i))]
  unfold firstGroupEffect
  rw [Matrix.mul_sum, Matrix.sum_mul]

/-- A complete terminal history factors through the pulled back first
projective effect of any group containing its first recorded outcome. -/
theorem terminal_has_group_right_support {k : ℕ} (u : Matrix.unitaryGroup n ℂ)
    (pvm : CompletePVM n k) (descend : Fin k → Protocol n)
    (s : Finset (Fin k)) (i : Fin k) (hi : i ∈ s) (h : Terminal (descend i)) :
    kraus (.branch u k pvm descend) ⟨i, h⟩ * firstGroupEffect u pvm s =
      kraus (.branch u k pvm descend) ⟨i, h⟩ := by
  classical
  have hunit : u.val * u.valᴴ = 1 := by
    simpa only [← Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem u.prop
  have hgroup : pvm.proj i * (∑ j ∈ s, pvm.proj j) = pvm.proj i := by
    rw [Matrix.mul_sum, Finset.sum_eq_single i]
    · exact pvm.idempotent i
    · intro j _ hij
      exact pvm.orthogonal i j hij.symm
    · exact fun hnin => False.elim (hnin hi)
  change (kraus (descend i) h * (pvm.proj i * u.val)) *
      (u.valᴴ * (∑ j ∈ s, pvm.proj j) * u.val) =
    kraus (descend i) h * (pvm.proj i * u.val)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (pvm.proj i * u.val) (u.valᴴ * ∑ j ∈ s, pvm.proj j), Matrix.mul_assoc (pvm.proj i),
    ← Matrix.mul_assoc u.val u.valᴴ, hunit, Matrix.one_mul, hgroup]

def flagKraus (j : Fin 2) (K : Matrix n n ℂ) : Matrix (Fin 2 × n) n ℂ :=
  fun out i => if out.1 = j then K out.2 i else 0

theorem flagKraus_effect (j : Fin 2) (K : Matrix n n ℂ) :
    (flagKraus j K)ᴴ * flagKraus j K = Kᴴ * K := by
  ext i l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, flagKraus,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel

/-- The normalization of the recorded terminal channel, on the full input. -/
theorem flagged_normalized (p : Protocol n) :
    (∑ h : Terminal p, (flagKraus (flag p h) (kraus p h))ᴴ *
      flagKraus (flag p h) (kraus p h)) = 1 := by
  simp_rw [flagKraus_effect]
  exact sum_terminal_effects p

/-- The full two-flag action as a genuine finite CPTP map on the same
input register, with the output determined by the terminal flag. -/
noncomputable def flaggedChannel (p : Protocol n) : QuantumChannel n (Fin 2 × n) :=
  (finite_kraus_quantum_channel (fun h : Terminal p => flagKraus (flag p h) (kraus p h))
    (flagged_normalized p)).choose

theorem flaggedChannel_apply (p : Protocol n) (X : Matrix n n ℂ) :
    CStarMatrix.ofMatrix.symm ((flaggedChannel p).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) =
      ∑ h : Terminal p, flagKraus (flag p h) (kraus p h) * X *
        (flagKraus (flag p h) (kraus p h))ᴴ :=
  (finite_kraus_quantum_channel (fun h : Terminal p => flagKraus (flag p h) (kraus p h))
    (flagged_normalized p)).choose_spec X

end D5.S3.Quantum.Measurement.AuricProjectiveTree

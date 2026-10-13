/- GID: D5/S3/Quantum/Measurement/CyclicRefractoryGenerator
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/CyclicRefractoryGenerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite refractory quantum instrument reproduces every classical output word. -/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Foundation.FiniteKrausChannel

/-!
# Cyclic refractory quantum generator

For each residue, a free state and a generally nonorthogonal tail state share
a two-dimensional block. A zero output returns to the free state; a one output
moves a free state to the next residue's tail state. A tail state cannot emit
one. The source-order product of the two Kraus operators realizes the full
classical word law, including impossible words and zero transition weights.

This is a finite-dimensional quantum simulation of the refractory process,
not a claim of dimension optimality, stationary entropy advantage, or a native
physical implementation. Quantum stochastic simulation is established in the
literature; the statement here supplies an explicit refractory family.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Measurement.CyclicRefractoryGenerator

def localZero (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), (b : ℂ); 0, 0]

def localOne (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c : ℂ) * b, -(c : ℂ) * a; (d : ℂ) * b, -(d : ℂ) * a]

private theorem local_kraus_complete (a b c d : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) (hcd : c ^ 2 + d ^ 2 = 1) :
    (localZero a b)ᴴ * localZero a b +
      (localOne a b c d)ᴴ * localOne a b c d = 1 := by
  have habC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  have hcdC : (c : ℂ) ^ 2 + (d : ℂ) ^ 2 = 1 := by exact_mod_cast hcd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localZero, localOne, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
  · linear_combination habC + (b : ℂ) ^ 2 * hcdC
  · linear_combination -(a : ℂ) * (b : ℂ) * hcdC
  · linear_combination -(a : ℂ) * (b : ℂ) * hcdC
  · linear_combination habC + (a : ℂ) ^ 2 * hcdC

private theorem local_kraus_updates (a b c d : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    localZero a b *ᵥ ![1,0] = ![(a : ℂ),0] ∧
    localOne a b c d *ᵥ ![1,0] = (b : ℂ) • ![(c : ℂ),(d : ℂ)] ∧
    localZero a b *ᵥ ![(a : ℂ),(b : ℂ)] = ![1,0] ∧
    localOne a b c d *ᵥ ![(a : ℂ),(b : ℂ)] = 0 := by
  have habC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals ext i
  all_goals fin_cases i <;>
    simp [localZero, localOne, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring_nf at habC ⊢
  all_goals exact habC

private theorem permutation_isometry {I : Type*} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) :
    (e.toPEquiv.toMatrix : Matrix I I ℂ)ᴴ * e.toPEquiv.toMatrix = 1 := by
  rw [PEquiv.toMatrix_toPEquiv_eq]
  simp only [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : Matrix I I ℂ).submatrix id e *
    (1 : Matrix I I ℂ).submatrix e id = 1
  rw [Matrix.submatrix_mul_equiv]
  simp

private theorem cyclic_kraus_complete {Z : Type*} [Fintype Z] [DecidableEq Z]
    (a b : Z → ℝ) (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (e : Equiv.Perm Z) :
    let U : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ :=
      (Equiv.prodCongr (Equiv.refl (Fin 2)) e.symm).toPEquiv.toMatrix
    let K0 := Matrix.blockDiagonal fun z => localZero (a z) (b z)
    let K1 := U * Matrix.blockDiagonal fun z =>
      localOne (a z) (b z) (a (e z)) (b (e z))
    K0ᴴ * K0 + K1ᴴ * K1 = 1 := by
  dsimp only
  let U : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ :=
    (Equiv.prodCongr (Equiv.refl (Fin 2)) e.symm).toPEquiv.toMatrix
  let L0 := Matrix.blockDiagonal fun z => localZero (a z) (b z)
  let L1 := Matrix.blockDiagonal fun z => localOne (a z) (b z) (a (e z)) (b (e z))
  change L0ᴴ * L0 + (U * L1)ᴴ * (U * L1) = 1
  have hU : Uᴴ * U = 1 := permutation_isometry _
  have hprod : (U * L1)ᴴ * (U * L1) = L1ᴴ * L1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      L1ᴴ * Uᴴ * (U * L1) = L1ᴴ * (Uᴴ * U) * L1 := by simp [Matrix.mul_assoc]
      _ = L1ᴴ * L1 := by rw [hU]; simp
  rw [hprod]
  dsimp only [L0, L1]
  rw [Matrix.blockDiagonal_conjTranspose, Matrix.blockDiagonal_conjTranspose,
    ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_add]
  have heq : (fun z => (localZero (a z) (b z))ᴴ * localZero (a z) (b z)) +
      (fun z => (localOne (a z) (b z) (a (e z)) (b (e z)))ᴴ *
        localOne (a z) (b z) (a (e z)) (b (e z))) =
      (1 : Z → Matrix (Fin 2) (Fin 2) ℂ) := by
    funext z
    exact local_kraus_complete _ _ _ _ (hab z) (hab (e z))
  rw [heq, Matrix.blockDiagonal_one]


variable {Z : Type*} [Fintype Z] [DecidableEq Z]

def liftVec (z : Z) (v : Fin 2 → ℂ) : Fin 2 × Z → ℂ :=
  fun i => if i.2 = z then v i.1 else 0

private theorem block_mul_lift (D : Z → Matrix (Fin 2) (Fin 2) ℂ)
    (z : Z) (v : Fin 2 → ℂ) :
    Matrix.blockDiagonal D *ᵥ liftVec z v = liftVec z (D z *ᵥ v) := by
  ext ⟨i,w⟩
  by_cases hw : w = z
  · subst w
    simp [liftVec, Matrix.blockDiagonal_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, mul_ite, ite_mul]
  · simp [liftVec, Matrix.blockDiagonal_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, mul_ite, ite_mul, hw]

private theorem shift_mul_lift (e : Equiv.Perm Z) (z : Z) (v : Fin 2 → ℂ) :
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) e.symm).toPEquiv.toMatrix :
      Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ) *ᵥ liftVec z v = liftVec (e z) v := by
  rw [PEquiv.toMatrix_toPEquiv_mulVec]
  ext ⟨i,w⟩
  simp [liftVec, Equiv.symm_apply_eq]

omit [Fintype Z] in
private theorem lift_smul (z : Z) (c : ℂ) (v : Fin 2 → ℂ) :
    liftVec z (c • v) = c • liftVec z v := by
  ext i
  by_cases hi : i.2 = z <;> simp [liftVec, hi]

def Kzero (a b : Z → ℝ) : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ :=
  Matrix.blockDiagonal fun z => localZero (a z) (b z)

def Kone (a b : Z → ℝ) (e : Equiv.Perm Z) : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) e.symm).toPEquiv.toMatrix *
    Matrix.blockDiagonal fun z => localOne (a z) (b z) (a (e z)) (b (e z))

def Fstate (z : Z) : Fin 2 × Z → ℂ := liftVec z ![1,0]

def Tstate (a b : Z → ℝ) (z : Z) : Fin 2 × Z → ℂ :=
  liftVec z ![(a z : ℂ),(b z : ℂ)]

private theorem global_kraus_updates (a b : Z → ℝ)
    (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (e : Equiv.Perm Z) (z : Z) :
    Kzero a b *ᵥ Fstate z = (a z : ℂ) • Fstate z ∧
    Kone a b e *ᵥ Fstate z = (b z : ℂ) • Tstate a b (e z) ∧
    Kzero a b *ᵥ Tstate a b z = Fstate z ∧
    Kone a b e *ᵥ Tstate a b z = 0 := by
  have h := local_kraus_updates (a z) (b z) (a (e z)) (b (e z)) (hab z)
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Kzero, Fstate]
    rw [block_mul_lift, h.1]
    have hv : ![(a z : ℂ),0] = (a z : ℂ) • (![1,0] : Fin 2 → ℂ) := by
      ext i
      fin_cases i <;> simp
    rw [hv, lift_smul]
  · dsimp only [Kone, Fstate, Tstate]
    rw [← Matrix.mulVec_mulVec, block_mul_lift, h.2.1, lift_smul,
      Matrix.mulVec_smul, shift_mul_lift]
  · dsimp only [Kzero, Fstate, Tstate]
    rw [block_mul_lift, h.2.2.1]
  · dsimp only [Kone, Tstate]
    rw [← Matrix.mulVec_mulVec, block_mul_lift, h.2.2.2]
    have hz : liftVec z (0 : Fin 2 → ℂ) = 0 := by
      ext i
      change (if i.2 = z then (0 : ℂ) else 0) = 0
      split <;> rfl
    rw [hz]
    exact Matrix.mulVec_zero _


def stateVec (a b : Z → ℝ) (s : Fin 2 × Z) : Fin 2 × Z → ℂ :=
  if s.1 = 0 then Fstate s.2 else Tstate a b s.2

def nextState (e : Equiv.Perm Z) (s : Fin 2 × Z) (x : Bool) : Fin 2 × Z :=
  if x then (1,e s.2) else (0,s.2)

def stepAmplitude (a b : Z → ℝ) (s : Fin 2 × Z) (x : Bool) : ℝ :=
  if s.1 = 0 then (if x then b s.2 else a s.2) else (if x then 0 else 1)

def branchK (a b : Z → ℝ) (e : Equiv.Perm Z) (x : Bool) :=
  if x then Kone a b e else Kzero a b

private theorem one_step_amplitude (a b : Z → ℝ)
    (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (e : Equiv.Perm Z)
    (s : Fin 2 × Z) (x : Bool) :
    branchK a b e x *ᵥ stateVec a b s =
      (stepAmplitude a b s x : ℂ) • stateVec a b (nextState e s x) := by
  rcases s with ⟨k,z⟩
  have h := global_kraus_updates a b hab e z
  cases x <;> fin_cases k <;>
    simp [branchK, stateVec, nextState, stepAmplitude, h.1, h.2.1, h.2.2.1, h.2.2.2]

def wordK (a b : Z → ℝ) (e : Equiv.Perm Z) : List Bool →
    Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ
  | [] => 1
  | x :: w => wordK a b e w * branchK a b e x

def wordState (e : Equiv.Perm Z) (s : Fin 2 × Z) : List Bool → Fin 2 × Z
  | [] => s
  | x :: w => wordState e (nextState e s x) w

def wordAmplitude (a b : Z → ℝ) (e : Equiv.Perm Z) (s : Fin 2 × Z) : List Bool → ℝ
  | [] => 1
  | x :: w => stepAmplitude a b s x * wordAmplitude a b e (nextState e s x) w

private theorem all_word_amplitude (a b : Z → ℝ)
    (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (e : Equiv.Perm Z)
    (s : Fin 2 × Z) (w : List Bool) :
    wordK a b e w *ᵥ stateVec a b s =
      (wordAmplitude a b e s w : ℂ) • stateVec a b (wordState e s w) := by
  induction w generalizing s with
  | nil => simp [wordK, wordAmplitude, wordState]
  | cons x w ih =>
    simp only [wordK, wordAmplitude, wordState]
    rw [← Matrix.mulVec_mulVec, one_step_amplitude a b hab, Matrix.mulVec_smul, ih]
    simp only [smul_smul, Complex.ofReal_mul]

def classicalStepWeight (p : Z → ℝ) (s : Fin 2 × Z) (x : Bool) : ℝ :=
  if s.1 = 0 then (if x then p s.2 else 1-p s.2) else (if x then 0 else 1)

def classicalWordProbability (p : Z → ℝ) (e : Equiv.Perm Z) (s : Fin 2 × Z) :
    List Bool → ℝ
  | [] => 1
  | x :: w => classicalStepWeight p s x *
      classicalWordProbability p e (nextState e s x) w

omit [Fintype Z] [DecidableEq Z] in
private theorem step_amplitude_sq (a b : Z → ℝ)
    (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (s : Fin 2 × Z) (x : Bool) :
    (stepAmplitude a b s x) ^ 2 = classicalStepWeight (fun z => b z ^ 2) s x := by
  rcases s with ⟨k,z⟩
  have h := hab z
  cases x <;> fin_cases k <;> simp [stepAmplitude, classicalStepWeight] <;> linarith

omit [Fintype Z] [DecidableEq Z] in
private theorem all_word_probability_amplitude (a b : Z → ℝ)
    (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (e : Equiv.Perm Z)
    (s : Fin 2 × Z) (w : List Bool) :
    (wordAmplitude a b e s w) ^ 2 =
      classicalWordProbability (fun z => b z ^ 2) e s w := by
  induction w generalizing s with
  | nil => simp [wordAmplitude, classicalWordProbability]
  | cons x w ih =>
    simp only [wordAmplitude, classicalWordProbability, mul_pow,
      step_amplitude_sq a b hab, ih]

private theorem lift_inner (z : Z) (v : Fin 2 → ℂ) :
    star (liftVec z v) ⬝ᵥ liftVec z v = star v ⬝ᵥ v := by
  simp [liftVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, mul_ite]

private theorem state_normalized (a b : Z → ℝ)
    (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (s : Fin 2 × Z) :
    star (stateVec a b s) ⬝ᵥ stateVec a b s = 1 := by
  rcases s with ⟨k,z⟩
  have habC : (a z : ℂ) ^ 2 + (b z : ℂ) ^ 2 = 1 := by exact_mod_cast hab z
  fin_cases k
  · change star (liftVec z (![1,0] : Fin 2 → ℂ)) ⬝ᵥ liftVec z ![1,0] = 1
    rw [lift_inner]
    norm_num [dotProduct, Fin.sum_univ_two]
  · change star (liftVec z ![(a z : ℂ),(b z : ℂ)]) ⬝ᵥ
      liftVec z ![(a z : ℂ),(b z : ℂ)] = 1
    rw [lift_inner]
    simp [dotProduct, Fin.sum_univ_two]
    ring_nf at habC ⊢
    exact habC

private theorem all_word_born_probability (a b : Z → ℝ)
    (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (e : Equiv.Perm Z)
    (s : Fin 2 × Z) (w : List Bool) :
    star (wordK a b e w *ᵥ stateVec a b s) ⬝ᵥ
      (wordK a b e w *ᵥ stateVec a b s) =
        (classicalWordProbability (fun z => b z ^ 2) e s w : ℂ) := by
  rw [all_word_amplitude a b hab]
  simp only [star_smul, smul_dotProduct, dotProduct_smul, state_normalized a b hab,
    smul_eq_mul, mul_one, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← pow_two, all_word_probability_amplitude a b hab]



/-- The trace of a pure-state Kraus branch is its squared vector norm. -/
private theorem pure_word_trace {I : Type*} [Fintype I]
    (K : Matrix I I ℂ) (v : I → ℂ) :
    Matrix.trace (K * Matrix.vecMulVec v (star v) * Kᴴ) =
      star (K *ᵥ v) ⬝ᵥ (K *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
    Matrix.trace_vecMulVec, dotProduct_comm]

/-- The explicit branches form a canonical completely positive trace-preserving
channel and reproduce the classical probability of every finite output word
from every free or tail initial state. -/
theorem cyclic_refractory_generator (a b : Z → ℝ)
    (hab : ∀ z, a z ^ 2 + b z ^ 2 = 1) (e : Equiv.Perm Z) :
    ∃ channel :
        D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel
          (Fin 2 × Z) (Fin 2 × Z),
      (∀ ρ : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ,
        CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix ρ)) =
          ∑ x : Bool, branchK a b e x * ρ * (branchK a b e x)ᴴ) ∧
      ∀ (s : Fin 2 × Z) (w : List Bool),
        Matrix.trace (wordK a b e w *
            Matrix.vecMulVec (stateVec a b s) (star (stateVec a b s)) *
            (wordK a b e w)ᴴ) =
          (classicalWordProbability (fun z => b z ^ 2) e s w : ℂ) := by
  have hcomplete : (∑ x : Bool, (branchK a b e x)ᴴ * branchK a b e x) = 1 := by
    simpa [branchK, Kzero, Kone, Fintype.sum_bool, add_comm] using
      cyclic_kraus_complete a b hab e
  obtain ⟨channel, hchannel⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
      (branchK a b e) hcomplete
  refine ⟨channel, hchannel, ?_⟩
  intro s w
  rw [pure_word_trace]
  exact all_word_born_probability a b hab e s w

#print axioms cyclic_refractory_generator

end D5.S3.Quantum.Measurement.CyclicRefractoryGenerator

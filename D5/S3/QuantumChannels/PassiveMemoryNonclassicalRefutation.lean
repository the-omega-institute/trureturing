/- GID: D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.claim; result=D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.result; claim=D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.claim
   digest: A passive qutrit-memory implementation refutes classical Gram simulation. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import D5.S3.Quantum.FiniteDimensional
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
open D5.S3.Quantum.FiniteDimensional

namespace D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation

abbrev Mat (ι : Type*) := Matrix ι ι ℂ

def KrausChannel (ι : Type*) [Fintype ι] [DecidableEq ι] : Type _ :=
  Σ n : ℕ, {K : Fin n → Mat ι // (∑ a, (K a).conjTranspose * K a) = 1}

def act {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : KrausChannel ι) : MatrixMap ι ι ℂ :=
  MatrixMap.of_kraus E.2.1 E.2.1

def stateMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityState ι) : Mat ι :=
  CStarMatrix.ofMatrix.symm ρ.1

def appendMemory {d r : ℕ} (τ : DensityState (Fin r)) :
    MatrixMap (Fin d) (Fin d × Fin r) ℂ :=
  { toFun := fun A => Matrix.kronecker A (stateMatrix τ)
    map_add' := fun A B => Matrix.add_kronecker A B (stateMatrix τ)
    map_smul' := by
      intro c A
      ext ⟨i, a⟩ ⟨j, b⟩
      simp [Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul]
      ring }

def discardMemory {d r : ℕ} : MatrixMap (Fin d × Fin r) (Fin d) ℂ :=
  { toFun := partialTraceRight
    map_add' := partialTraceRight_add
    map_smul' := by
      intro c A
      ext i j
      simp [partialTraceRight, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum] }

def implemented {d r : ℕ} (τ : DensityState (Fin r))
    (Nen Nde : KrausChannel (Fin d × Fin r))
    (E : KrausChannel (Fin d)) : MatrixMap (Fin d) (Fin d) ℂ :=
  (discardMemory (d := d) (r := r)).comp
    ((act Nde).comp
      ((MatrixMap.kron (act E) (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ)).comp
        ((act Nen).comp (appendMemory (d := d) τ))))

def choi (d : ℕ) (F : MatrixMap (Fin d) (Fin d) ℂ) :
    Mat (Fin d × Fin d) :=
  fun p q => (d : ℂ)⁻¹ * F (Matrix.single p.2 q.2 1) p.1 q.1

def Gram {ι : Type*} (C : Mat ι) : Prop :=
  C.PosSemidef ∧ ∀ i, C i i = 1

def DephasingGram {d : ℕ} (C : Mat (Fin d × Fin d)) : Prop :=
  Gram C ∧ ∀ i k j l : Fin d, C (i,j) (i,l) = C (k,j) (k,l)

def Passive {d r : ℕ} (τ : DensityState (Fin r))
    (Nen : KrausChannel (Fin d × Fin r)) : Prop :=
  ∀ ρ σ : DensityState (Fin d),
    partialTraceLeft (act Nen (Matrix.kronecker (stateMatrix ρ) (stateMatrix τ))) =
    partialTraceLeft (act Nen (Matrix.kronecker (stateMatrix σ) (stateMatrix τ)))

def ClassicalGram {d : ℕ} (C : Mat (Fin d × Fin d)) : Prop :=
  ∃ (n : ℕ) (q : Fin n → ℝ) (P Q : Fin n → Mat (Fin d)),
    (∀ a, 0 ≤ q a) ∧ (∑ a, q a) = 1 ∧
    (∀ a, Gram (P a) ∧ Gram (Q a)) ∧
    C = ∑ a, q a • Matrix.kronecker (P a) (Q a)

def Implements {d r : ℕ} (τ : DensityState (Fin r))
    (Nen Nde : KrausChannel (Fin d × Fin r))
    (C : Mat (Fin d × Fin d)) : Prop :=
  DephasingGram C ∧ ∀ E : KrausChannel (Fin d),
    choi d (implemented τ Nen Nde E) = Matrix.hadamard C (choi d (act E))

def claim : Prop :=
  ∀ (d r : ℕ), 0 < d → 0 < r →
    ∀ (τ : DensityState (Fin r))
      (Nen Nde : KrausChannel (Fin d × Fin r))
      (C : Mat (Fin d × Fin d)),
      Implements τ Nen Nde C → Passive τ Nen → ClassicalGram C

private noncomputable def tau0 : DensityState (Fin 2) := by
  refine ⟨CStarMatrix.ofMatrix ((1 / 2 : ℝ) • (1 : Mat (Fin 2))), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.nonneg_iff_posSemidef.mpr
    exact (Matrix.PosSemidef.one (n := Fin 2) (R := ℂ)).smul (a := (1 / 2 : ℝ))
      (by norm_num)
  · change Matrix.trace ((1 / 2 : ℝ) • (1 : Mat (Fin 2))) = 1
    rw [Matrix.trace_smul]
    norm_num

private def controls : Fin 3 → Mat (Fin 2) := fun i =>
  if i = 0 then 1 else if i = 1 then qubitX else qubitZ

private def controlled : Mat (Fin 3 × Fin 2) := fun p q =>
  if p.1 = q.1 then controls p.1 p.2 q.2 else 0

private theorem controlled_unitary :
    controlled.conjTranspose * controlled = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [controlled, controls, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, qubitX, qubitZ]

private def witnessChannel : KrausChannel (Fin 3 × Fin 2) :=
  ⟨1, ⟨fun _ => controlled, by simpa [Fin.sum_univ_one] using controlled_unitary⟩⟩

private def gramFactor : Matrix (Fin 4) (Fin 3 × Fin 3) ℂ := fun a p =>
  if a = 0 then (if p.1 = p.2 then 1 else 0)
  else if a = 1 then
    (if (p = (0, 1) ∨ p = (1, 0)) then 1 else 0)
  else if a = 2 then
    (if (p = (0, 2) ∨ p = (2, 0)) then 1 else 0)
  else if p = (1, 2) then 1 else if p = (2, 1) then -1 else 0

private def witnessC : Mat (Fin 3 × Fin 3) := gramFactor.conjTranspose * gramFactor

private theorem witnessC_gram : Gram witnessC := by
  constructor
  · exact Matrix.posSemidef_conjTranspose_mul_self gramFactor
  · intro p
    rcases p with ⟨p1, p2⟩
    fin_cases p1 <;> fin_cases p2 <;>
      simp [witnessC, gramFactor, Matrix.mul_apply, Fin.sum_univ_four]

private theorem witnessC_formula (p q : Fin 3 × Fin 3) :
    witnessC p q = (1 / 2 : ℂ) * Matrix.trace
      (controls p.1 * controls p.2 * (controls q.2).conjTranspose *
        (controls q.1).conjTranspose) := by
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    norm_num +decide [witnessC, gramFactor, controls, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.trace, Fin.sum_univ_four,
      Fin.sum_univ_two, dotProduct, Matrix.mulVec, Matrix.vecMul,
      Matrix.mulVec_eq_sum, Matrix.vecMul_eq_sum, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk, Fin.reduceEq,
      qubitX, qubitZ]

end D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation

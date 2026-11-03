/- GID: D5/S3/Quantum/Entanglement/DickeExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/DickeExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unnormalized Dicke diagonal operators and Bose symmetric extension cones. -/

import D5.S3.QuantumStates.ZeroWeightSupportFace
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.GroupTheory.Perm.Sign

open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumStates.ZeroWeightSupportFace

namespace D5.S3.Quantum.Entanglement.DickeExtension

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

/-- The computational tensor basis split into the ordered sites `a,b` and their complement. -/
def edgeSplit (a b : I) (hab : a ≠ b) :
    (I → L) ≃ (L × L) × ({k : I // k ≠ a ∧ k ≠ b} → L) where
  toFun x := ((x a, x b), fun k => x k)
  invFun u k := if ha : k = a then u.1.1 else
    if hb : k = b then u.1.2 else u.2 ⟨k, ha, hb⟩
  left_inv x := by
    funext k
    dsimp
    split_ifs <;> simp_all
  right_inv u := by
    rcases u with ⟨⟨x,y⟩,z⟩
    apply Prod.ext
    · simp [hab, Ne.symm hab]
    · funext k
      simp [k.property.1, k.property.2]

/-- The actual unnormalized partial trace over every site other than the ordered pair. -/
noncomputable def edgeMarginal (a b : I) (hab : a ≠ b)
    (E : Matrix (I → L) (I → L) ℂ) : Matrix (L × L) (L × L) ℂ :=
  partialTraceRight (E.submatrix (edgeSplit a b hab).symm (edgeSplit a b hab).symm)

/-- The standard two-particle Dicke vector; off-diagonal vectors have coefficient `1/√2`. -/
noncomputable def dickeVector {n : ℕ} (i j : Fin n) (x : Fin n × Fin n) : ℂ :=
  if i = j then (if x = (i,i) then 1 else 0) else
    (Real.sqrt 2 : ℂ)⁻¹ *
      ((if x = (i,j) then 1 else 0) + (if x = (j,i) then 1 else 0))

/-- The unnormalized cone coordinates, with only upper-triangular coefficients used. -/
noncomputable def dickeOperator {n : ℕ} (Y : Fin n → Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ∑ i, ∑ j, if i ≤ j then
    (Y i j : ℂ) • Matrix.vecMulVec (dickeVector i j) (star (dickeVector i j)) else 0

/-- All nonempty proper standard-basis partial-transpose inequalities. -/
def FullyPPT (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  ∀ S : Finset I, S.Nonempty → S ≠ Finset.univ → (partialTransposeOn S E).PosSemidef

/-- The product projector onto the root factor times the symmetric leaf factors. -/
noncomputable def leafProjector (root : I) : Matrix (I → L) (I → L) ℂ :=
  Local.localP ({root} : Finset I)

/-- A star extension on the original tensor factors, with a genuine support sandwich. -/
def StarExtension (root : I) (ρ : Matrix (L × L) (L × L) ℂ)
    (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  E.PosSemidef ∧ leafProjector root * E * leafProjector root = E ∧
    (∀ i (hi : root ≠ i), edgeMarginal root i hi E = ρ) ∧ FullyPPT E

/-- A complete graph extension on the same factors, supported on the full Bose subspace. -/
def CompleteExtension (ρ : Matrix (L × L) (L × L) ℂ)
    (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  E.PosSemidef ∧ P I L * E * P I L = E ∧
    (∀ a b (hab : a ≠ b), edgeMarginal a b hab E = ρ) ∧ FullyPPT E

private lemma dicke_swap {n : ℕ} (i j : Fin n) (x : Fin n × Fin n) :
    dickeVector i j x.swap = dickeVector i j x := by
  rcases x with ⟨a,b⟩
  simp only [dickeVector, Prod.swap_prod_mk, Prod.mk.injEq]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    congr 1
    exact propext (and_comm)
  · simp only [hij, ite_false]
    congr 1
    rw [show (b = i ∧ a = j) ↔ (a = j ∧ b = i) from and_comm,
      show (b = j ∧ a = i) ↔ (a = i ∧ b = j) from and_comm]
    exact add_comm _ _

private lemma dicke_operator_swap {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (x y : Fin n × Fin n) :
    dickeOperator Y x.swap y = dickeOperator Y x y := by
  simp only [dickeOperator, Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, dicke_swap]

end D5.S3.Quantum.Entanglement.DickeExtension

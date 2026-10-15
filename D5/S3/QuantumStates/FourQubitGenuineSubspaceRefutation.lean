/- GID: D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumStates/FourQubitGenuineSubspaceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.claim; result=D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.result; claim=D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.claim
   digest: A nonzero product across A₁A₂B₁ | B₂ refutes Antipin's universal GES claim. -/

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
The seven vectors (35) and substitutions (39)–(40) of arXiv:2104.09664v1,
§III.B.2, define a four-qubit subspace for each parameter tuple in (0,1)⁷.
At (1/2,16/25,1/2,1/2,1/17,1/2,1/2), its span contains a nonzero vector
that factors across A₁A₂B₁ | B₂.
-/

namespace D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation

noncomputable section
open scoped BigOperators

abbrev Bit := Fin 2
abbrev Party := Fin 4

abbrev Qubit := Bit → ℂ
abbrev Ququart := Fin 4 → ℂ
abbrev TwoQubit := TensorProduct ℂ Qubit Qubit

abbrev Config := Bit × Bit × Bit × Bit
abbrev State := Config → ℂ
abbrev Original := (Fin 4 × Fin 4) → ℂ

-- Party 0 = A₁; 1 = A₂; 2 = B₁; 3 = B₂.
def coordinate (q : Config) : Party → Bit :=
  ![q.1, q.2.1, q.2.2.1, q.2.2.2]

def IsProductAcross (s : Finset Party) (z : State) : Prop :=
  ∃
    (f : ({p : Party // p ∈ s} → Bit) → ℂ)
    (g : ({p : Party // p ∉ s} → Bit) → ℂ),
    ∀ q : Config,
      z q =
        f (fun p => coordinate q p.val) *
        g (fun p => coordinate q p.val)

def IsGES (W : Submodule ℂ State) : Prop :=
  ∀ z : State,
    z ∈ W →
    z ≠ 0 →
    ∀ s : Finset Party,
      s.Nonempty →
      s ≠ Finset.univ →
      ¬ IsProductAcross s z

def ket44 (a b : Fin 4) : Original :=
  Pi.single (a, b) 1

def ket22 (a b : Bit) : TwoQubit :=
  TensorProduct.tmul ℂ
    (Pi.single a 1 : Qubit)
    (Pi.single b 1 : Qubit)

def v35 («λ» : Fin 7 → ℝ) : Fin 7 → Original :=
  ![
    (Real.sqrt («λ» 0) : ℂ) • ket44 0 0 +
      (Real.sqrt (1 - «λ» 0) : ℂ) • ket44 2 1,

    (Real.sqrt («λ» 1) : ℂ) • ket44 1 2 +
      (Real.sqrt (1 - «λ» 1) : ℂ) • ket44 3 3,

    (Real.sqrt («λ» 2) : ℂ) • ket44 0 1 +
      (Real.sqrt (1 - «λ» 2) : ℂ) • ket44 3 2,

    (Real.sqrt («λ» 3) : ℂ) • ket44 3 0 +
      (Real.sqrt (1 - «λ» 3) : ℂ) • ket44 2 2,

    (Real.sqrt («λ» 4) : ℂ) • ket44 1 1 +
      (Real.sqrt (1 - «λ» 4) : ℂ) • ket44 0 3,

    (Real.sqrt («λ» 5) : ℂ) • ket44 1 0 +
      (Real.sqrt (1 - «λ» 5) : ℂ) • ket44 2 3,

    (Real.sqrt («λ» 6) : ℂ) • ket44 2 0 +
      (Real.sqrt (1 - «λ» 6) : ℂ) • ket44 3 1
  ]

def columns39 : Fin 4 → TwoQubit :=
  ![
    (1 / 6 : ℂ) •
      ((5 : ℂ) • ket22 0 0 - ket22 0 1 +
        (3 : ℂ) • ket22 1 0 - ket22 1 1),

    (1 / 6 : ℂ) •
      (-ket22 0 0 + (5 : ℂ) • ket22 0 1 +
        (3 : ℂ) • ket22 1 0 - ket22 1 1),

    (1 / 2 : ℂ) •
      (ket22 0 0 + ket22 0 1 -
        ket22 1 0 + ket22 1 1),

    (1 / 6 : ℂ) •
      (-ket22 0 0 - ket22 0 1 +
        (3 : ℂ) • ket22 1 0 + (5 : ℂ) • ket22 1 1)
  ]

def columns40 : Fin 4 → TwoQubit :=
  ![
    (1 / 3 : ℂ) •
      (-ket22 0 0 + (2 : ℂ) • ket22 0 1 +
        (2 : ℂ) • ket22 1 1),

    (1 / 3 : ℂ) •
      ((2 : ℂ) • ket22 0 0 - ket22 0 1 +
        (2 : ℂ) • ket22 1 1),

    ket22 1 0,

    (1 / 3 : ℂ) •
      ((2 : ℂ) • ket22 0 0 + (2 : ℂ) • ket22 0 1 -
        ket22 1 1)
  ]

def substitution39 : Ququart →ₗ[ℂ] TwoQubit :=
  (Pi.basisFun ℂ (Fin 4)).constr ℂ columns39

def substitution40 : Ququart →ₗ[ℂ] TwoQubit :=
  (Pi.basisFun ℂ (Fin 4)).constr ℂ columns40

def twoBasis :
    Module.Basis (Bit × Bit) ℂ TwoQubit :=
  (Pi.basisFun ℂ Bit).tensorProduct
    (Pi.basisFun ℂ Bit)

def inputCoordinates :
    TensorProduct ℂ Ququart Ququart ≃ₗ[ℂ] Original :=
  ((Pi.basisFun ℂ (Fin 4)).tensorProduct
    (Pi.basisFun ℂ (Fin 4))).equivFun

def outputCoordinates :
    TensorProduct ℂ TwoQubit TwoQubit ≃ₗ[ℂ] State :=
  ((twoBasis.tensorProduct twoBasis).reindex
    (Equiv.prodAssoc Bit Bit (Bit × Bit))).equivFun

def factorwise : Original →ₗ[ℂ] State :=
  outputCoordinates.toLinearMap.comp
    ((TensorProduct.map substitution39 substitution40).comp
      inputCoordinates.symm.toLinearMap)

def transformed («λ» : Fin 7 → ℝ) (i : Fin 7) : State :=
  factorwise (v35 «λ» i)

def S («λ» : Fin 7 → ℝ) : Submodule ℂ State :=
  Submodule.span ℂ (Set.range (transformed «λ»))

def claim : Prop :=
  ∀ «λ» : Fin 7 → ℝ,
    (∀ i, 0 < «λ» i ∧ «λ» i < 1) →
    IsGES (S «λ»)

private def lambdaStar : Fin 7 → ℝ :=
  ![1 / 2, 16 / 25, 1 / 2, 1 / 2, 1 / 17, 1 / 2, 1 / 2]

private def weight : Fin 7 → ℂ :=
  ![
    ((3 * Real.sqrt 2 : ℝ) : ℂ),
    5,
    ((3 * Real.sqrt 2 : ℝ) : ℂ),
    ((3 * Real.sqrt 2 : ℝ) : ℂ),
    ((3 * Real.sqrt 17 : ℝ) : ℂ),
    ((3 * Real.sqrt 2 : ℝ) : ℂ),
    ((3 * Real.sqrt 2 : ℝ) : ℂ)
  ]

private def x : Original :=
  ∑ i : Fin 7, weight i • v35 lambdaStar i

private def M : Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![3, 3, 0, 12],
    ![3, 3, 4, 0],
    ![3, 3, 3, 3],
    ![3, 3, 3, 3]
  ]

private def threeFactor (a b c : Bit) : ℂ :=
  (
    (![![![25, 1], ![1, 13]],
       ![![15, 6], ![7, 10]]] :
      Bit → Bit → Bit → ℂ) a b c
  ) / 3

private def y (q : Config) : ℂ :=
  threeFactor q.1 q.2.1 q.2.2.1

private def witnessCut : Finset Party :=
  {0, 1, 2}

private def leftFactor
    (u : {p : Party // p ∈ witnessCut} → Bit) : ℂ :=
  threeFactor
    (u ⟨0, by decide⟩)
    (u ⟨1, by decide⟩)
    (u ⟨2, by decide⟩)

private def integer35 : Fin 7 → Original :=
  ![
    (3 : ℂ) • ket44 0 0 + (3 : ℂ) • ket44 2 1,
    (4 : ℂ) • ket44 1 2 + (3 : ℂ) • ket44 3 3,
    (3 : ℂ) • ket44 0 1 + (3 : ℂ) • ket44 3 2,
    (3 : ℂ) • ket44 3 0 + (3 : ℂ) • ket44 2 2,
    (3 : ℂ) • ket44 1 1 + (12 : ℂ) • ket44 0 3,
    (3 : ℂ) • ket44 1 0 + (3 : ℂ) • ket44 2 3,
    (3 : ℂ) • ket44 2 0 + (3 : ℂ) • ket44 3 1
  ]

private def u6 : Bit → Bit → Fin 4 → ℂ :=
  ![
    ![![5, -1, 3, -1], ![-1, 5, 3, -1]],
    ![![3, 3, -3, 3], ![-1, -1, 3, 5]]
  ]

private def t3 : Bit → Bit → Fin 4 → ℂ :=
  ![
    ![![-1, 2, 0, 2], ![2, -1, 0, 2]],
    ![![0, 0, 3, 0], ![2, 2, 0, -1]]
  ]

private lemma twoBasis_tmul
    (u v : Qubit) (a b : Bit) :
    twoBasis.equivFun (TensorProduct.tmul ℂ u v) (a, b) =
      u a * v b := by
  simp only [twoBasis.eq_1, Module.Basis.equivFun_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, Pi.basisFun_repr, smul_eq_mul, mul_comm]

private lemma outputCoordinates_tmul
    (u v : TwoQubit) (a b c d : Bit) :
    outputCoordinates (TensorProduct.tmul ℂ u v) (a, b, c, d) =
      twoBasis.equivFun u (a, b) *
      twoBasis.equivFun v (c, d) := by
  rw [outputCoordinates.eq_1, Module.Basis.equivFun_apply,
    Module.Basis.repr_reindex_apply]
  change (twoBasis.tensorProduct twoBasis).repr _ ((a, b), (c, d)) = _
  simp only [Module.Basis.tensorProduct_repr_tmul_apply,
    Module.Basis.equivFun_apply, smul_eq_mul, mul_comm]

private lemma substitution39_basis (a : Fin 4) :
    substitution39 (Pi.single a 1) = columns39 a := by
  rw [substitution39.eq_1, ← Pi.basisFun_apply ℂ (Fin 4) a, Module.Basis.constr_basis]

private lemma substitution40_basis (a : Fin 4) :
    substitution40 (Pi.single a 1) = columns40 a := by
  rw [substitution40.eq_1, ← Pi.basisFun_apply ℂ (Fin 4) a, Module.Basis.constr_basis]

private lemma columns39_coordinates
    (a : Fin 4) (i j : Bit) :
    twoBasis.equivFun (columns39 a) (i, j) =
      u6 i j a / 6 := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [columns39.eq_1, u6.eq_1, ket22.eq_1] <;>
    simp_rw [← Module.Basis.equivFun_apply, twoBasis_tmul] <;> norm_num

private lemma columns40_coordinates
    (a : Fin 4) (i j : Bit) :
    twoBasis.equivFun (columns40 a) (i, j) =
      t3 i j a / 3 := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [columns40.eq_1, t3.eq_1, ket22.eq_1] <;>
    simp_rw [← Module.Basis.equivFun_apply, twoBasis_tmul] <;> norm_num

private lemma factorwise_apply (z : Original) (q : Config) :
    factorwise z q =
      ∑ a : Fin 4, ∑ b : Fin 4,
        (u6 q.1 q.2.1 a / 6) *
        z (a, b) *
        (t3 q.2.2.1 q.2.2.2 b / 3) := by
  rcases q with ⟨i, j, k, l⟩
  change outputCoordinates ((TensorProduct.map substitution39 substitution40)
    (inputCoordinates.symm z)) (i, j, k, l) = _
  rw [inputCoordinates.eq_1, Module.Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, Module.Basis.tensorProduct_apply', Pi.basisFun_apply,
    TensorProduct.map_tmul, substitution39_basis, substitution40_basis,
    Finset.sum_apply, Pi.smul_apply, outputCoordinates_tmul,
    columns39_coordinates, columns40_coordinates, Fintype.sum_prod_type, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ac_rfl

end
end D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation

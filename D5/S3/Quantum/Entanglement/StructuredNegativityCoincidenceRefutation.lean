/- GID: D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.claim; result=D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.result; claim=D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.claim
   digest: A pure 3 x 3 state has three negative PT eigenvalues but N = 8/9 and N_S = 4/3. -/

/-
proof_shape: result: bind-only (explicit rational similarity certificates, the pinned
  Hermitian characteristic-polynomial theorem, and finite rational normalization)
escape_witness: none
admission_basis: open-problem-resolution (#11475; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation

open Matrix
open scoped ComplexOrder

/-- Partial transposition on the second tensor factor. -/
def partialTransposeB {d : ℕ}
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun (i, j) (k, l) => ρ (i, l) (k, j)

/-- A density matrix is positive semidefinite and has trace one. -/
def IsDensity {d : ℕ} (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Hermitian eigenvalues with multiplicity: one entry for each vector of the
Mathlib orthonormal eigenbasis. The non-Hermitian extension is the empty multiset. -/
noncomputable def eigenvalues {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Multiset ℝ :=
  if h : A.IsHermitian then Finset.univ.val.map h.eigenvalues else 0

/-- The number of strictly negative eigenvalues, counted with multiplicity. -/
noncomputable def negCount {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℕ :=
  ((eigenvalues A).filter (fun x => x < 0)).card

/-- Equation (6), using its sum over the negative partial-transpose eigenvalues. -/
noncomputable def negativity (d : ℕ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (2 / ((d : ℝ) - 1)) * (((eigenvalues (partialTransposeB ρ)).filter
    (fun x => x < 0)).map abs).sum

/-- Equation (7): the structural physical approximation of partial transposition. -/
noncomputable def spaPT {d : ℕ}
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((d : ℂ) / ((d : ℂ) ^ 3 + 1)) • 1 +
    (1 / ((d : ℂ) ^ 3 + 1)) • partialTransposeB ρ

/-- The least Hermitian eigenvalue, expressed as the infimum of the finite spectrum.
The empty-spectrum extension is irrelevant for density matrices with d at least two. -/
noncomputable def leastEigenvalue {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  sInf {x | x ∈ eigenvalues A}

/-- Equation (9), with K = d(d^3 + 1). -/
noncomputable def structuredNegativity (d : ℕ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  ((d : ℝ) * ((d : ℝ) ^ 3 + 1)) *
    max ((d : ℝ) / ((d : ℝ) ^ 3 + 1) - leastEigenvalue (spaPT ρ)) 0

/-- The Kumari–Adhikari conjecture, arXiv:2209.03909v1, abstract and conclusion. -/
def claim : Prop :=
  ∀ (d : ℕ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
    2 ≤ d → IsDensity ρ → negCount (partialTransposeB ρ) = d * (d - 1) / 2 →
      negativity d ρ = structuredNegativity d ρ

private noncomputable def coefficients : Fin 3 → ℝ :=
  fun i => if i.val = 0 then 1 / 3 else 2 / 3
private noncomputable def psi : Fin 3 × Fin 3 → ℂ :=
  fun (i, j) => if i.val = j.val then (coefficients i : ℂ) else 0
private noncomputable def rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  vecMulVec psi (star psi)

private def changeBasis : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun (i, j) (k, l) =>
    if (i.val, j.val) = (k.val, l.val) then (if k.val ≤ l.val then 1 else -1)
    else if (i.val, j.val) = (l.val, k.val) then 1 else 0
private noncomputable def inverseBasis : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun (i, j) (k, l) => if i.val = j.val then changeBasis (i, j) (k, l)
    else changeBasis (i, j) (k, l) / 2
private noncomputable def ptValues : Fin 3 × Fin 3 → ℝ :=
  fun (i, j) => if i.val = j.val then coefficients i ^ 2
    else if i.val < j.val then coefficients i * coefficients j else -(coefficients i * coefficients j)
private noncomputable def spaValues : Fin 3 × Fin 3 → ℝ :=
  fun ij => 3 / 28 + ptValues ij / 28

set_option maxHeartbeats 2000000 in
-- The entrywise certificates expand five matrices with 81 entries each.
/-- The pure state (|00> + 2|11> + 2|22>)/3 has q = 3, N = 8/9 and N_S = 4/3. -/
theorem result : ¬ claim := by
  classical
  intro hclaim
  have hdensity : IsDensity rho := by
    refine ⟨posSemidef_vecMulVec_self_star psi, ?_⟩
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, rho, psi, coefficients, Matrix.trace, Matrix.diag, Matrix.vecMulVec, map_ofNat, Fin.reduceEq, Fin.reduceFinMk,
      Fintype.sum_prod_type, Fin.sum_univ_three]
  have hptHerm : (partialTransposeB rho).IsHermitian := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, partialTransposeB, rho, psi, coefficients, Matrix.vecMulVec, map_ofNat, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk,
        Matrix.conjTranspose_apply]
  have hspaHerm : (spaPT rho).IsHermitian := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, spaPT, partialTransposeB, rho, psi, coefficients, Matrix.vecMulVec, map_ofNat, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk,
        Matrix.conjTranspose_apply, Matrix.one_apply]
  have hQP : inverseBasis * changeBasis = 1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, inverseBasis, changeBasis, Matrix.mul_apply, Matrix.one_apply, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk,
        Fintype.sum_prod_type, Fin.sum_univ_three]
  have hdiagPT : changeBasis * diagonal (fun ij => (ptValues ij : ℂ)) * inverseBasis =
      partialTransposeB rho := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, inverseBasis, changeBasis, partialTransposeB, rho, psi, coefficients,
        ptValues, Matrix.vecMulVec, map_ofNat, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal,
        Fintype.sum_prod_type, Fin.sum_univ_three]
  have hdiagSPA : changeBasis * diagonal (fun ij => (spaValues ij : ℂ)) * inverseBasis =
      spaPT rho := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, spaPT, inverseBasis, changeBasis, partialTransposeB, rho, psi, coefficients,
        ptValues, spaValues, Matrix.vecMulVec, map_ofNat, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal,
        Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  have spectralBridge : ∀ (A : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
      (hA : A.IsHermitian) (v : Fin 3 × Fin 3 → ℝ),
      changeBasis * diagonal (fun ij => (v ij : ℂ)) * inverseBasis = A →
      eigenvalues A = Finset.univ.val.map v := by
    intro A hA v hdiag
    have hc : A.charpoly = (diagonal (fun ij => (v ij : ℂ))).charpoly := by
      rw [← hdiag, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
    have hroots : (diagonal (fun ij => (v ij : ℂ))).charpoly.roots =
        Finset.univ.val.map (fun ij => (v ij : ℂ)) := by
      rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
      · simp
      · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
    have hr := congrArg (Multiset.map Complex.re)
      (hA.roots_charpoly_eq_eigenvalues.symm.trans
        ((congrArg Polynomial.roots hc).trans hroots))
    simpa [eigenvalues, hA, Multiset.map_map, Function.comp_def] using hr
  have hpt := spectralBridge _ hptHerm ptValues hdiagPT
  have hspa := spectralBridge _ hspaHerm spaValues hdiagSPA
  have hu : (Finset.univ : Finset (Fin 3 × Fin 3)).val =
      ({(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)} :
        Multiset (Fin 3 × Fin 3)) := by decide
  have hptList : eigenvalues (partialTransposeB rho) =
      ({1/9, 2/9, 2/9, -2/9, 4/9, 4/9, -2/9, -4/9, 4/9} : Multiset ℝ) := by
    rw [hpt]
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, hu, ptValues, spaValues, coefficients, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk]
  have hspaList : eigenvalues (spaPT rho) =
      ({7/63, 29/252, 29/252, 25/252, 31/252, 31/252, 25/252, 23/252, 31/252} : Multiset ℝ) := by
    rw [hspa]
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, hu, ptValues, spaValues, coefficients, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk]
  have hq : negCount (partialTransposeB rho) = 3 * (3 - 1) / 2 := by
    norm_num [negCount, hptList, Multiset.filter_singleton]
  have hN : negativity 3 rho = 8 / 9 := by
    norm_num [negativity, hptList, Multiset.filter_singleton]
  have hmin : leastEigenvalue (spaPT rho) = 23 / 252 := by
    apply IsLeast.csInf_eq
    norm_num [hspaList, IsLeast, lowerBounds]
  have hNS : structuredNegativity 3 rho = 4 / 3 := by
    norm_num [structuredNegativity, hmin]
  have heq := hclaim 3 rho (by norm_num) hdensity hq
  rw [hN, hNS] at heq
  norm_num at heq

end D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation

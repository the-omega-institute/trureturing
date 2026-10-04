/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Period-three operator data and hard-core occupation support. -/

/-
HCBlock_fullNumber:
  proof_shape: content
  escape_witness: HCBlock_fullNumber (form 2): Every nonzero occupation-tensor entry is diagonal and therefore preserves the hard-core block.
  Direct frozen dependencies: tensorOp, Assignment, visibleProjector.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
tensorOp = D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp; sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel, D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicProducts, D5.S3.Quantum.SpinChains.SupersymmetricFermion.HoppingProducts; freeze in topological import order.
Information-escape registration is paused under CLAUDE.md §3.9.
-/


import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicProducts
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HoppingProducts
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix Classical
set_option quotPrecheck false in
local notation "tensorOp" => (fun {N : ℕ} (w : Fin N → Matrix Bool Bool ℂ) =>
  Matrix.submatrix
    (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp (n := N)
      (fun i => Matrix.submatrix (w i) finTwoEquiv finTwoEquiv))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i)))
open PredictiveThermodynamic.Physical (Assignment visibleProjector)
open D5.S3.Quantum.FiniteDimensional (qubitZ)
local notation "spinZ" => (qubitZ.submatrix finTwoEquiv.symm finTwoEquiv.symm)
local notation "spinP" => ((1 : Matrix Bool Bool ℂ) - visibleProjector)

namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicCompression
noncomputable section
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HoppingProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel

def fullR (N : ℕ) (a b cc : ℝ) : D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.FullOperator N :=
  if hN : 0 < N then
    (a * cc^2 : ℝ) • (D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD (⟨0,hN⟩ : Fin N))ᴴ -
    (a^2 * cc : ℝ) • (D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD (⟨N-1,by omega⟩ : Fin N))ᴴ +
    (∑ k : Fin (N-2),
      (periodThree a b cc (k.val+3) * periodThree a b cc (k.val+2)^2 : ℝ) •
        (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp (⟨k.val,by omega⟩ : Fin N) (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) *
          (D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD (⟨k.val+2,by omega⟩ : Fin N))ᴴ)) -
    (∑ k : Fin (N-2),
      (periodThree a b cc (k.val+1) * periodThree a b cc (k.val+2)^2 : ℝ) •
        (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp (⟨k.val+2,by omega⟩ : Fin N) (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) *
          (D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD (⟨k.val,by omega⟩ : Fin N))ᴴ)) +
    (a*b*cc : ℝ) • (∑ k : Fin (N-2), D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullSplit (⟨k.val,by omega⟩ : Fin N))
  else 0

def HCBlock {N : ℕ} (A : D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.FullOperator N) : Prop :=
  ∀ (s t : Assignment N), A s t ≠ 0 → (Adm N s ↔ Adm N t)

theorem HCBlock_fullNumber {N : ℕ} (i : Fin N) : HCBlock (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)))) := by
  have localOp_as_tensor {N : ℕ} (i : Fin N) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = tensorOp (numberWord i) := by
    classical
    ext s t
    simp only [D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply, Matrix.of_apply]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = i
    · subst k
      simp [Function.update_self, numberWord, sub_sub_cancel]
    · simp [Function.update_of_ne h, numberWord, h, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
  classical
  intro s t h
  have hentry : ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) s t = ∏ k : Fin N, numberWord i k (s k) (t k) := by
    rw [localOp_as_tensor]
    simp [D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp, Matrix.submatrix_apply]
  rw [hentry] at h
  have hst : s = t := by
    by_contra hn
    have he : ∃ k, s k ≠ t k := by
      by_contra hh
      push Not at hh
      exact hn (funext hh)
    obtain ⟨k,hk⟩ := he
    apply h
    change (∏ k : Fin N, numberWord i k (s k) (t k)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    change (if k = i then (1 - spinP) else (1 : Local)) (s k) (t k) = 0
    split_ifs <;> simp [spinP_def, visibleProjector,Matrix.diagonal_apply,Matrix.sub_apply,
      Matrix.one_apply,hk]
  subst t
  rfl

def chainG (a b cc : ℝ) (j : ℕ) : ℝ := periodThree a b cc (j+1)

def blockR {N : ℕ} (a b cc : ℝ) (k : Fin N) (hr : k.val+2<N) : FullOperator N :=
  let j : Fin N := ⟨k.val+2,hr⟩
  ((chainG a b cc (k.val+2) * chainG a b cc (k.val+1)^2 : ℝ) : ℂ) •
    (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ) -
  ((chainG a b cc k.val * chainG a b cc (k.val+1)^2 : ℝ) : ℂ) •
    (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD k)ᴴ) +
  ((a*b*cc : ℝ) : ℂ) • fullSplit k

def blockDiagonal {N : ℕ} (a b cc : ℝ) (k : Fin N) (hr : k.val+2<N) : FullOperator N :=
  let j : Fin N := ⟨k.val+2,hr⟩
  ((2 * chainG a b cc (k.val+2)^2 * chainG a b cc (k.val+1)^2 : ℝ) : ℂ) •
    (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorOp (neighbourPWord j)) -
  ((2 * chainG a b cc k.val^2 * chainG a b cc (k.val+1)^2 : ℝ) : ℂ) •
    (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorOp (neighbourPWord k))

def hopCurrent (N : ℕ) (a b cc : ℝ) (j : ℕ) : FullOperator N :=
  (chainG a b cc (j+2) : ℂ) • symOp (fullHop N j)

def fourCurrent (N : ℕ) (a b cc : ℝ) (j : ℕ) : FullOperator N :=
  (chainG a b cc (j+3) : ℂ) • symOp (fullFourHop N j)

def bulkCurrent (N : ℕ) (a b cc : ℝ) (j : ℕ) : FullOperator N :=
  let C := hopCurrent N a b cc
  let x := fullOccupationAt N
  C (j+1) * (1 - (if j=0 then 0 else x (j-1))) -
  C j * (1 - x (j+3)) + C (j+2) * x j -
  (if j=0 then 0 else C (j-1)) * x (j+2)

def fullBoundary (N : ℕ) (a b cc : ℝ) : FullOperator N :=
  if hN : 0<N then
    ((a*cc^2 : ℝ) : ℂ) • (fullD (⟨0,hN⟩ : Fin N))ᴴ -
    ((a^2*cc : ℝ) : ℂ) • (fullD (⟨N-1,by omega⟩ : Fin N))ᴴ
  else 0

def w (a b cc : ℝ) (j : ℕ) : ℝ :=
  periodThree a b cc (j + 1) ^ 2 * periodThree a b cc (j + 2) ^ 2

def occReal {N : ℕ} (s : HardCore N) (j : ℕ) : ℝ :=
  if occupied s.val j then 1 else 0

def diagonalCoefficient (N : ℕ) (a b cc : ℝ) (s : HardCore N) : ℝ :=
  a ^ 2 * cc ^ 2 * (occReal s (N - 1) - occReal s 2) +
  ∑ i ∈ Finset.range (N - 2),
    (w a b cc (i + 1) * occReal s (i + 1) * (1 - occReal s (i + 4)) -
     w a b cc (i + 3) * occReal s (i + 3) * (1 - occReal s i))

end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicCompression

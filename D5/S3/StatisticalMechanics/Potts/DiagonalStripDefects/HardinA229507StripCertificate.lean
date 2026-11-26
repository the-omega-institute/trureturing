/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.finite_certificate
   digest: Exact defect sectors of the five-column diagonal strip. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229507Strip.result)
representative_counts: proof_shape=bind-only; consumers=HardinA229507Strip.result
one_counts: proof_shape=bind-only; consumers=HardinA229507Strip.result
transition_counts: proof_shape=bind-only; consumers=HardinA229507Strip.result
W: proof_shape=bind-only; consumers=HardinA229507Strip.result
tail_step: proof_shape=bind-only; consumers=HardinA229507Strip.result
powers: proof_shape=bind-only; consumers=HardinA229507Strip.result
tail_polynomial: proof_shape=bind-only; consumers=HardinA229507Strip.result
finite_certificate: proof_shape=bind-only; consumers=HardinA229507Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripCertificate
open HardinA203980StripData (Row boundary between representatives)
open HardinA229507StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem representative_counts : ∀ i j : Fin 8,
    (∑ r : Row, if bondDefects between (representatives i) r = 1 ∧ boundary r = j
      then (1 : ℤ) else 0) = costOne i j := by
  intro i
  fin_cases i <;> decide +kernel

theorem one_counts (p : Row) (j : Fin 8) :
    (∑ r : Row, if bondDefects between p r = 1 ∧ boundary r = j
      then (1 : ℤ) else 0) = costOne (boundary p) j :=
  DiagonalSymmetry.lift_counts 1 costOne representative_counts p j

/-- Exact residual-budget counts, with the exhausted sector supplied by the zero-cost transfer. -/
theorem transition_counts (p : Row) (d : Fin 2) (s : Fin 16) :
    (∑ r : Row, if bondDefects between p r ≤ d.val ∧
      cl r (d.val - bondDefects between p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s := by
  have tt (i j : Fin 8) : T (i.castAdd 8) (j.castAdd 8) = HardinA203980StripData.T i j := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have bb (i j : Fin 8) : T (i.natAdd 8) (j.natAdd 8) = HardinA203980StripData.T i j := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd]
    rfl
  have bt (i j : Fin 8) : T (i.natAdd 8) (j.castAdd 8) = 0 := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
    rfl
  have tb (i j : Fin 8) : T (i.castAdd 8) (j.natAdd 8) = costOne i j := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
    rfl
  induction s using Fin.addCases (m := 8) (n := 8) with
  | left j =>
    have cut (r : Row) :
        (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = j.castAdd 8) ↔
          d.val = 1 ∧ bondDefects between p r = 0 ∧ boundary r = j := by
      have hi := (boundary r).isLt
      have hj := j.isLt
      have hd := d.isLt
      unfold cl
      split_ifs <;> simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] <;> omega
    simp_rw [cut]
    fin_cases d
    · simp only [Fin.val_zero, cl, Nat.lt_irrefl, ite_false, bt]
      simp
    · simp only [Fin.val_one, cl, Nat.zero_lt_one, ite_true, tt, true_and]
      exact HardinA203980StripCertificate.counts p j
  | right j =>
    have cut (r : Row) :
        (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = j.natAdd 8) ↔
          bondDefects between p r = d.val ∧ boundary r = j := by
      have hi := (boundary r).isLt
      have hj := j.isLt
      unfold cl
      split_ifs <;> simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] <;> omega
    simp_rw [cut]
    fin_cases d
    · simp only [Fin.val_zero, cl, Nat.lt_irrefl, ite_false, bb]
      exact HardinA203980StripCertificate.counts p j
    · simp only [Fin.val_one, cl, Nat.zero_lt_one, ite_true, tb]
      exact one_counts p j

def W (i : Fin 14) : Fin 16 → ℤ :=
  Fin.append ((![![0, 0, 0, 0, 0, 0, 0, 0],
    ![32, 48, 40, 28, 48, 40, 40, 28],
    ![1584, 1080, 720, 456, 1152, 720, 792, 444],
    ![33792, 21336, 14400, 8568, 21936, 13008, 12576, 6780],
    ![639168, 371400, 252672, 142800, 387120, 217056, 201984, 105612],
    ![11095200, 6186600, 4268736, 2333808, 6473808, 3520224, 3131280, 1613340],
    ![184214304, 99539496, 69396480, 36993888, 104756112, 55600128, 48008592, 24436620],
    ![2962663776, 1566123336, 1101019392, 576100512, 1654464528, 862809408, 726577776, 366456636],
    ![46593519840, 24217961256, 17136157824, 8836708608, 25665555024, 13200086592, 10898192304, 5454483948],
    ![720388958688, 369548651592, 262840215168, 133982315136, 392611278096, 199705036032, 162187861680, 80653431132],
    ![10991100364128, 5578893935208, 3984632818560, 2012094727488, 5939154613584, 2993764774464, 2398126226544, 1185987853836],
    ![165911255587296, 83485332648072, 59835099758976, 29979095208768, 89026214563728, 44538673084416, 35261701574832, 17355584636028],
    ![2482577963786592, 1240175568593448, 891443422719360, 443701400370624, 1324362737395152, 658350112271040, 515993070177648, 252911039874732],
    ![36876273023227104, 18308473102197576, 13192895441662848, 6529628650933440, 19574972690426640, 9677843212977792, 7518913427576880, 3671821223923356]]) i)
    (HardinA203980StripCertificate.W i)

private theorem tail_step (i : Fin 13) (j : Fin 8) :
    W i.succ (j.natAdd 8) = T.mulVec (W i.castSucc) (j.natAdd 8) := by
  have block_tail (a b e : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 16 → ℤ) :
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks a b (0 : Matrix (Fin 8) (Fin 8) ℤ) e)).mulVec v
          (j.natAdd 8) = e.mulVec (fun k : Fin 8 => v (k.natAdd 8)) j := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm]
    rw [Matrix.fromBlocks_mulVec]
    simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr,
      Matrix.zero_mulVec, zero_add]
    rfl
  rw [show T.mulVec (W i.castSucc) (j.natAdd 8) =
    HardinA203980StripData.T.mulVec (fun k : Fin 8 => W i.castSucc (k.natAdd 8)) j from block_tail _ _ _ _]
  simp only [W, Fin.append_right]
  simp_rw [← HardinA203980StripCertificate.powers]
  simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Matrix.mulVec_mulVec]

theorem powers (i : Fin 14) : (T ^ i.val).mulVec terminal = W i := by
  have hz : W 0 = terminal := by
    funext j
    induction j using Fin.addCases (m := 8) (n := 8) with
    | left j => fin_cases j <;> rfl
    | right j =>
      simp only [W, terminal, Fin.append_right]
      have h := congrFun (HardinA203980StripCertificate.powers (0 : Fin 14)) j
      change (HardinA203980StripData.T ^ 0).mulVec HardinA203980StripData.terminal j = _ at h
      simpa only [pow_zero, Matrix.one_mulVec] using h.symm
  have step (i : Fin 13) : W i.succ = T.mulVec (W i.castSucc) := by
    funext j
    induction j using Fin.addCases (m := 8) (n := 8) with
    | left j =>
      have fresh : ∀ (i : Fin 13) (j : Fin 8),
        W i.succ (j.castAdd 8) = T.mulVec (W i.castSucc) (j.castAdd 8) := by decide +kernel
      exact fresh i j
    | right j => exact tail_step i j
  induction i using Fin.induction with
  | zero => simpa only [Fin.val_zero, pow_zero, Matrix.one_mulVec] using hz.symm
  | succ i ih =>
    simp only [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec]
    rw [show (T ^ i.val).mulVec terminal = W i.castSucc from ih]
    exact (step i).symm

private theorem tail_polynomial (j : Fin 8) :
    W 9 (j.natAdd 8) = (∑ k : Fin 8,
      (![-104976, 174960, -72900, -9720, 8748, -540, -225, 30] k : ℤ) •
        W ⟨1 + k.val, by omega⟩) (j.natAdd 8) := by
  have rel (n : ℕ) := D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix.scalarRelationShift
    HardinA203980StripData.T (Pi.single j 1) 4 1 ![324, -270, 0, 15]
    HardinA203980StripCertificate.finite_certificate n
  have h0 := rel 0
  have h1 := rel 1
  have h2 := rel 2
  have h3 := rel 3
  have h4 := rel 4
  simp only [W, Fin.append_right, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [← HardinA203980StripCertificate.powers]
  simp only [single_dotProduct, one_mul, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_one, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Nat.reduceAdd] at h0 h1 h2 h3 h4 ⊢
  norm_num only [Fin.reduceFinMk, Fin.val_ofNat, Fin.val_natCast, Nat.reduceMod,
    HardinA203980StripData.terminal] at h0 h1 h2 h3 h4 ⊢
  change (HardinA203980StripData.T ^ 9).mulVec 1 j = _
  linarith only [h0, h1, h2, h3, h4]

theorem finite_certificate :
    (T ^ 9).mulVec terminal = ∑ k : Fin 8,
      (![-104976, 174960, -72900, -9720, 8748, -540, -225, 30] k : ℤ) •
        (T ^ (1 + k.val)).mulVec terminal := by
  rw [show 9 = (9 : Fin 14).val from rfl, powers]
  simp_rw [show ∀ k : Fin 8, (T ^ (1 + k.val)).mulVec terminal =
    W ⟨1 + k.val, by omega⟩ from fun k => powers ⟨1 + k.val, by omega⟩]
  funext j
  induction j using Fin.addCases (m := 8) (n := 8) with
  | left j =>
    have fresh : ∀ j : Fin 8, W 9 (j.castAdd 8) = (∑ k : Fin 8,
      (![-104976, 174960, -72900, -9720, 8748, -540, -225, 30] k : ℤ) •
        W ⟨1 + k.val, by omega⟩) (j.castAdd 8) := by decide +kernel
    exact fresh j
  | right j => exact tail_polynomial j

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripCertificate

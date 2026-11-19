/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.finite_certificate
   digest: Exact defect sectors of the five-column diagonal strip. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229682Strip.result)
representative_counts: proof_shape=bind-only; consumers=HardinA229682Strip.result
two_counts: proof_shape=bind-only; consumers=HardinA229682Strip.result
transition_counts: proof_shape=bind-only; consumers=HardinA229682Strip.result
W: proof_shape=bind-only; consumers=HardinA229682Strip.result
tail_step: proof_shape=bind-only; consumers=HardinA229682Strip.result
powers: proof_shape=bind-only; consumers=HardinA229682Strip.result
tail_polynomial: proof_shape=bind-only; consumers=HardinA229682Strip.result
finite_certificate: proof_shape=bind-only; consumers=HardinA229682Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
open HardinA203980StripData (Row boundary between representatives)
open HardinA229682StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem representative_counts : ∀ i j : Fin 8,
    (∑ r : Row, if bondDefects between (representatives i) r = 2 ∧ boundary r = j
      then (1 : ℤ) else 0) = costTwo i j := by
  intro i
  fin_cases i <;> decide +kernel

theorem two_counts (p : Row) (j : Fin 8) :
    (∑ r : Row, if bondDefects between p r = 2 ∧ boundary r = j
      then (1 : ℤ) else 0) = costTwo (boundary p) j :=
  DiagonalSymmetry.lift_counts 2 costTwo representative_counts p j

/-- The sixteen old residual states retain their transfer, and the added sector counts cost two. -/
theorem transition_counts (p : Row) (d : Fin 3) (s : Fin 24) :
    (∑ r : Row, if bondDefects between p r ≤ d.val ∧
      cl r (d.val - bondDefects between p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s := by
  have tt (i j : Fin 8) : T (i.castAdd 16) (j.castAdd 16) = HardinA203980StripData.T i j := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have bb (i j : Fin 16) : T (i.natAdd 8) (j.natAdd 8) = HardinA229507StripData.T i j := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd]
    rfl
  have bt (i : Fin 16) (j : Fin 8) : T (i.natAdd 8) (j.castAdd 16) = 0 := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
    rfl
  have tb (i : Fin 8) (j : Fin 16) : T (i.castAdd 16) (j.natAdd 8) =
      Fin.append (HardinA229507StripData.costOne i) (costTwo i) j := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
    rfl
  induction s using Fin.addCases (m := 8) (n := 16) with
  | left j =>
    have cut (r : Row) :
        (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = j.castAdd 16) ↔
          d.val = 2 ∧ bondDefects between p r = 0 ∧ boundary r = j := by
      have hi := (boundary r).isLt
      have hj := j.isLt
      have hd := d.isLt
      have ho := (HardinA229507StripData.cl r (d.val - bondDefects between p r)).isLt
      unfold cl
      split_ifs <;> simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] <;> omega
    simp_rw [cut]
    fin_cases d
    · simp only [Fin.val_zero, cl, Nat.reduceEqDiff, ite_false, bt]
      simp
    · simp only [Fin.val_one, cl, Nat.reduceEqDiff, ite_false, bt]
      simp
    · simp only [Fin.val_ofNat, Fin.val_natCast, Nat.reduceMod, cl, ite_true, tt, true_and]
      exact HardinA203980StripCertificate.counts p j
  | right j =>
    by_cases hd : d.val < 2
    · have hn : d.val ≠ 2 := by omega
      have cut (r : Row) :
          (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = j.natAdd 8) ↔
            bondDefects between p r ≤ d.val ∧ HardinA229507StripData.cl r
              (d.val - bondDefects between p r) = j := by
        by_cases hc : bondDefects between p r ≤ d.val
        · have hr : d.val - bondDefects between p r ≠ 2 := by omega
          simp only [cl, hr, ite_false, Fin.ext_iff, Fin.val_natAdd,
            Nat.add_left_cancel_iff]
        · simp only [hc, false_and]
      simp_rw [cut]
      simp only [cl, hn, ite_false, bb]
      exact HardinA229507StripCertificate.transition_counts p ⟨d.val, hd⟩ j
    · have hv : d.val = 2 := by have := d.isLt; omega
      simp only [hv]
      rw [show cl p 2 = (boundary p).castAdd 16 from if_pos rfl, tb]
      induction j using Fin.addCases (m := 8) (n := 8) with
      | left j =>
        have cut (r : Row) :
            (bondDefects between p r ≤ 2 ∧ cl r (2 - bondDefects between p r) = (j.castAdd 8).natAdd 8) ↔
              bondDefects between p r = 1 ∧ boundary r = j := by
          have hi := (boundary r).isLt
          have hj := j.isLt
          unfold cl HardinA229507StripData.cl
          split_ifs <;> simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] <;> omega
        simp_rw [cut]
        simpa only [Fin.append_left] using HardinA229507StripCertificate.one_counts p j
      | right j =>
        have cut (r : Row) :
            (bondDefects between p r ≤ 2 ∧ cl r (2 - bondDefects between p r) = (j.natAdd 8).natAdd 8) ↔
              bondDefects between p r = 2 ∧ boundary r = j := by
          have hi := (boundary r).isLt
          have hj := j.isLt
          unfold cl HardinA229507StripData.cl
          split_ifs <;> simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] <;> omega
        simp_rw [cut]
        simpa only [Fin.append_right] using two_counts p j

def W (i : Fin 14) : Fin 24 → ℤ :=
  Fin.append ((![![0, 0, 0, 0, 0, 0, 0, 0],
    ![56, 52, 70, 73, 52, 70, 70, 73],
    ![3660, 3414, 2732, 2022, 3270, 2667, 2770, 2001],
    ![125864, 91526, 66520, 44842, 91876, 63907, 65388, 42357],
    ![3077608, 2052034, 1460368, 921892, 2083940, 1340105, 1318900, 802033],
    ![65860368, 41179578, 29031648, 17531340, 42293496, 25781925, 24684936, 14392149],
    ![1292285808, 774548010, 544788864, 318324960, 800799336, 470490381, 438826392, 248361561],
    ![23962825728, 13908516210, 9783942912, 5571799056, 14457808368, 8259228369, 7535693952, 4169936349],
    ![426404150208, 241441045002, 170083660032, 94884205464, 252026682768, 140851079901, 126041647968, 68526731025],
    ![7355393990496, 4082754618162, 2881709737344, 1580590648152, 4276482700320, 2347947394065, 2065733237232, 1107169397109],
    ![123817288691808, 67614478166106, 47826604732032, 25862974730568, 71026520738400, 38427968252421, 33305467702896, 17640631699497],
    ![2043630766052640, 1100849659646850, 780370057201536, 416942197320744, 1159229603495808, 619479492919353, 529789791870288, 277817204952045],
    ![33187200327082656, 17670795954350346, 12552922207502208, 6637716803284200, 18647033937099264, 9860052736825245, 8332507527765264, 4332180987113409],
    ![531644945185310112, 280265523773228658, 199494185419430784, 104542036048730376, 296289981637346880, 155244999968816625, 129794447860088976, 66981001570341093]]) i)
    (HardinA229507StripCertificate.W i)

private theorem tail_step (i : Fin 13) (j : Fin 16) :
    W i.succ (j.natAdd 8) = T.mulVec (W i.castSucc) (j.natAdd 8) := by
  have block_tail (a : Matrix (Fin 8) (Fin 8) ℤ) (b : Matrix (Fin 8) (Fin 16) ℤ)
      (e : Matrix (Fin 16) (Fin 16) ℤ) (v : Fin 24 → ℤ) :
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks a b (0 : Matrix (Fin 16) (Fin 8) ℤ) e)).mulVec v
          (j.natAdd 8) = e.mulVec (fun k : Fin 16 => v (k.natAdd 8)) j := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm]
    rw [Matrix.fromBlocks_mulVec]
    simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr,
      Matrix.zero_mulVec, zero_add]
    rfl
  rw [show T.mulVec (W i.castSucc) (j.natAdd 8) =
    HardinA229507StripData.T.mulVec (fun k : Fin 16 => W i.castSucc (k.natAdd 8)) j from block_tail _ _ _ _]
  simp only [W, Fin.append_right]
  simp_rw [← HardinA229507StripCertificate.powers]
  simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Matrix.mulVec_mulVec]

theorem powers (i : Fin 14) : (T ^ i.val).mulVec terminal = W i := by
  have hz : W 0 = terminal := by
    funext j
    induction j using Fin.addCases (m := 8) (n := 16) with
    | left j => fin_cases j <;> rfl
    | right j =>
      simp only [W, terminal, Fin.append_right]
      have h := congrFun (HardinA229507StripCertificate.powers (0 : Fin 14)) j
      change (HardinA229507StripData.T ^ 0).mulVec HardinA229507StripData.terminal j = _ at h
      simpa only [pow_zero, Matrix.one_mulVec] using h.symm
  have step (i : Fin 13) : W i.succ = T.mulVec (W i.castSucc) := by
    funext j
    induction j using Fin.addCases (m := 8) (n := 16) with
    | left j =>
      have fresh : ∀ (i : Fin 13) (j : Fin 8),
        W i.succ (j.castAdd 16) = T.mulVec (W i.castSucc) (j.castAdd 16) := by decide +kernel
      exact fresh i j
    | right j => exact tail_step i j
  induction i using Fin.induction with
  | zero => simpa only [Fin.val_zero, pow_zero, Matrix.one_mulVec] using hz.symm
  | succ i ih =>
    simp only [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec]
    rw [show (T ^ i.val).mulVec terminal = W i.castSucc from ih]
    exact (step i).symm

private theorem tail_polynomial (j : Fin 16) :
    W 13 (j.natAdd 8) = (∑ k : Fin 12,
      (![34012224, -85030560, 70858800, -14959080, -8188128, 3805380,
        0, -211410, 25272, 2565, -675, 45] k : ℤ) •
        W ⟨1 + k.val, by omega⟩) (j.natAdd 8) := by
  have rel (n : ℕ) := congrArg (fun w => ((HardinA229507StripData.T ^ n).mulVec w) j)
    HardinA229507StripCertificate.finite_certificate
  have h0 := rel 0
  have h1 := rel 1
  have h2 := rel 2
  have h3 := rel 3
  have h4 := rel 4
  simp only [W, Fin.append_right, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [← HardinA229507StripCertificate.powers]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_add, Matrix.mulVec_zero, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_add,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, Finset.sum_apply,
    Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul,
    Nat.reduceAdd] at h0 h1 h2 h3 h4 ⊢
  norm_num only [Fin.reduceFinMk, Fin.val_ofNat, Fin.val_natCast, Nat.reduceMod] at h0 h1 h2 h3 h4 ⊢
  change (HardinA229507StripData.T ^ 13).mulVec HardinA229507StripData.terminal j = _
  linarith only [h0, h1, h2, h3, h4]

theorem finite_certificate :
    (T ^ 13).mulVec terminal = ∑ k : Fin 12,
      (![34012224, -85030560, 70858800, -14959080, -8188128, 3805380,
        0, -211410, 25272, 2565, -675, 45] k : ℤ) •
        (T ^ (1 + k.val)).mulVec terminal := by
  rw [show 13 = (13 : Fin 14).val from rfl, powers]
  simp_rw [show ∀ k : Fin 12, (T ^ (1 + k.val)).mulVec terminal =
    W ⟨1 + k.val, by omega⟩ from fun k => powers ⟨1 + k.val, by omega⟩]
  funext j
  induction j using Fin.addCases (m := 8) (n := 16) with
  | left j =>
    have fresh : ∀ j : Fin 8, W 13 (j.castAdd 16) = (∑ k : Fin 12,
      (![34012224, -85030560, 70858800, -14959080, -8188128, 3805380,
        0, -211410, 25272, 2565, -675, 45] k : ℤ) •
        W ⟨1 + k.val, by omega⟩) (j.castAdd 16) := by decide +kernel
    exact fresh j
  | right j => exact tail_polynomial j

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate

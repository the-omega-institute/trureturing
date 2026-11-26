/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripCertificate.finite_certificate
   digest: Exact two-defect extension of the four-row HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31548; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229640Strip.result)
two_representatives: proof_shape=bind-only; consumers=HardinA229640Strip.result
two_counts: proof_shape=bind-only; consumers=HardinA229640Strip.result
transition_counts: proof_shape=bind-only; consumers=HardinA229640Strip.result
W: proof_shape=bind-only; consumers=HardinA229640Strip.result
tail_step: proof_shape=bind-only; consumers=HardinA229640Strip.result
powers: proof_shape=bind-only; consumers=HardinA229640Strip.result
tail_polynomial: proof_shape=bind-only; consumers=HardinA229640Strip.result
finite_certificate: proof_shape=bind-only; consumers=HardinA229640Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229640StripData
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
import Mathlib.Data.Matrix.Block

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229640StripCertificate
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.StatisticalMechanics.Potts.StripDefectsTwo
open HardinA229537StripData (between horizontal)
open HardinA229640StripData
open DefectTransfer (bondDefects)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem two_representatives : ∀ i j : Fin 14,
    (∑ r : HardinA233177PairTransfer.Col,
      if bondDefects between (HardinA233177PairTransfer.column (HardinA233177PairTransfer.representatives i))
        (HardinA233177PairTransfer.column r) = 2 ∧ HardinA233177PairTransfer.cls r = j
      then (1 : ℤ) else 0) = T (i.castAdd 28) ((j.natAdd 14).natAdd 14) := by
  decide +kernel

private theorem two_counts (p : Fin 4 → Fin 3) (j : Fin 14) :
    (∑ r : Fin 4 → Fin 3, if bondDefects between p r = 2 ∧
      HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3) = j then (1 : ℤ) else 0) =
      T ((HardinA233177PairTransfer.cls (p 0,p 1,p 2,p 3)).castAdd 28)
        ((j.natAdd 14).natAdd 14) := by
  have transport (b : HardinA233177PairTransfer.Col) :
      (∑ r : HardinA233177PairTransfer.Col,
        if bondDefects between (HardinA233177PairTransfer.column b)
          (HardinA233177PairTransfer.column r) = 2 ∧ HardinA233177PairTransfer.cls r = j
        then (1 : ℤ) else 0) = T ((HardinA233177PairTransfer.cls b).castAdd 28)
          ((j.natAdd 14).natAdd 14) := by
    obtain ⟨e, he⟩ := HardinA233177PairTransfer.class_rep b
    calc
      _ = ∑ r : HardinA233177PairTransfer.Col,
        if bondDefects between
          (HardinA233177PairTransfer.column (HardinA233177PairTransfer.relabel e b))
          (HardinA233177PairTransfer.column (HardinA233177PairTransfer.relabel e r)) = 2 ∧
          HardinA233177PairTransfer.cls (HardinA233177PairTransfer.relabel e r) = j
        then (1 : ℤ) else 0 := by
          simp only [HardinA229537StripCertificate.cost_relabel,
            HardinA233177PairTransfer.class_relabel]
      _ = _ := by
        rw [he]
        exact ((HardinA233177PairTransfer.relabel e).sum_comp (fun r =>
          if bondDefects between
            (HardinA233177PairTransfer.column (HardinA233177PairTransfer.representatives (HardinA233177PairTransfer.cls b)))
            (HardinA233177PairTransfer.column r) = 2 ∧ HardinA233177PairTransfer.cls r = j
          then (1 : ℤ) else 0)).trans (two_representatives _ _)
  rw [HardinA233125SquareStrip.label_sum]
  have ht := transport (p 0,p 1,p 2,p 3)
  have hc : HardinA233177PairTransfer.column (p 0,p 1,p 2,p 3) = p := by
    funext k
    exact HardinA233177PairTransfer.column_grid 1 (fun x => p x.1) 0 k
  rw [hc] at ht
  simpa only [Fintype.sum_prod_type, HardinA233177PairTransfer.column,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using ht

private theorem transition_counts (p : Fin 4 → Fin 3) (d : Fin 3) (s : Fin 42) :
    (∑ r : Fin 4 → Fin 3, if bondDefects between p r ≤ d.val ∧
      cl r (d.val - bondDefects between p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s := by
  have q00 (i j : Fin 14) : T (i.castAdd 28) (j.castAdd 28) = HardinA233177PairTransfer.Q i j := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have old (i j : Fin 28) : T (i.natAdd 14) (j.natAdd 14) = HardinA229537StripData.T i j := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd]
    rfl
  have lower (i : Fin 28) (j : Fin 14) : T (i.natAdd 14) (j.castAdd 28) = 0 := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have upper (i j : Fin 14) : T (i.castAdd 28) ((j.castAdd 14).natAdd 14) =
      HardinA229537StripData.T (i.castAdd 14) (j.natAdd 14) := by
    simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
    change Fin.append _ _ (j.castAdd 14) = _
    rw [Fin.append_left]
    rfl
  have q11 (i j : Fin 14) : HardinA229537StripData.T (i.castAdd 14) (j.castAdd 14) = HardinA233177PairTransfer.Q i j := by
    simp only [HardinA229537StripData.T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd]
    rfl
  have q22 (i j : Fin 14) : HardinA229537StripData.T (i.natAdd 14) (j.natAdd 14) = HardinA233177PairTransfer.Q i j := by
    simp only [HardinA229537StripData.T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_natAdd]
    rfl
  have z21 (i j : Fin 14) : HardinA229537StripData.T (i.natAdd 14) (j.castAdd 14) = 0 := by
    simp only [HardinA229537StripData.T, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  induction s using Fin.addCases (m := 14) (n := 28) with
  | left j =>
    have cut (r : Fin 4 → Fin 3) :
        (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = j.castAdd 28) ↔
        d.val = 2 ∧ bondDefects between p r = 0 ∧ HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3) = j := by
      have hi := (HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3)).isLt
      have hj := j.isLt
      have hd := d.isLt
      unfold cl HardinA229537StripData.cl
      split_ifs <;> simp only [HardinA229697StripData.cl, HardinA229589StripData.cl,
        Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false,
        Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] <;> omega
    simp_rw [cut]
    fin_cases d
    · simp only [Fin.val_zero, cl, HardinA229697StripData.cl, HardinA229589StripData.cl,
      Nat.reduceLT, Nat.reduceSub, show (0 : ℕ) ≠ 2 by decide, ite_false]
      rw [lower]
      simp
    · simp only [Fin.val_one, cl, HardinA229697StripData.cl, HardinA229589StripData.cl,
      Nat.reduceLT, Nat.reduceSub, show (1 : ℕ) ≠ 2 by decide, ite_false]
      rw [lower]
      simp
    · simp only [show (2 : Fin 3).val = 2 from rfl, cl, HardinA229697StripData.cl,
      HardinA229589StripData.cl, Nat.reduceLT, Nat.reduceSub, Fin.castAdd_castAdd, Nat.reduceAdd,
      Fin.cast_refl, id_eq, Nat.reduceEqDiff, ite_false, ite_true]
      rw [q00]
      simpa only [true_and] using HardinA229537StripCertificate.zero_counts p j
  | right s =>
    induction s using Fin.addCases (m := 14) (n := 14) with
    | left j =>
      have cut (r : Fin 4 → Fin 3) :
          (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = (j.castAdd 14).natAdd 14) ↔
          ((d.val = 1 ∧ bondDefects between p r = 0) ∨ (d.val = 2 ∧ bondDefects between p r = 1)) ∧
            HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3) = j := by
        have hi := (HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3)).isLt
        have hj := j.isLt
        have hd := d.isLt
        unfold cl HardinA229537StripData.cl
        split_ifs <;> simp only [HardinA229697StripData.cl, HardinA229589StripData.cl,
          Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false,
          Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] <;> omega
      simp_rw [cut]
      fin_cases d
      · simp only [Fin.val_zero, cl, HardinA229697StripData.cl, HardinA229589StripData.cl,
        Nat.reduceLT, Nat.reduceSub, show (0 : ℕ) ≠ 2 by decide, ite_false]
        rw [old]
        simp only [HardinA229537StripData.cl, HardinA229589StripData.cl, Nat.reduceEqDiff, ite_true,
          ite_false, ite_true]
        rw [z21]
        simp
      · simp only [Fin.val_one, cl, HardinA229697StripData.cl, HardinA229589StripData.cl,
        Nat.reduceLT, Nat.reduceSub, show (1 : ℕ) ≠ 2 by decide, ite_false]
        rw [old]
        simp only [HardinA229537StripData.cl, HardinA229589StripData.cl, Nat.reduceEqDiff, ite_true,
          ite_false, show (1 : ℕ) ≠ 0 by decide, ite_false]
        rw [q11]
        simpa using HardinA229537StripCertificate.zero_counts p j
      · simp only [show (2 : Fin 3).val = 2 from rfl, cl, HardinA229697StripData.cl,
        HardinA229589StripData.cl, Nat.reduceLT, Nat.reduceSub, Fin.castAdd_castAdd, Nat.reduceAdd,
        Fin.cast_refl, id_eq, Nat.reduceEqDiff, ite_false, ite_true]
        rw [upper]
        simpa using HardinA229537StripCertificate.one_counts p j
    | right j =>
      have cut (r : Fin 4 → Fin 3) :
          (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = (j.natAdd 14).natAdd 14) ↔
          bondDefects between p r = d.val ∧ HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3) = j := by
        have hi := (HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3)).isLt
        have hj := j.isLt
        have hd := d.isLt
        unfold cl HardinA229537StripData.cl
        split_ifs <;> simp only [HardinA229697StripData.cl, HardinA229589StripData.cl,
          Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false,
          Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] <;> omega
      simp_rw [cut]
      fin_cases d
      · simp only [Fin.val_zero, cl, HardinA229697StripData.cl, HardinA229589StripData.cl,
        Nat.reduceLT, Nat.reduceSub, show (0 : ℕ) ≠ 2 by decide, ite_false]
        rw [old]
        simp only [HardinA229537StripData.cl, HardinA229589StripData.cl, Nat.reduceEqDiff, ite_true,
          ite_false, ite_true]
        rw [q22]
        exact HardinA229537StripCertificate.zero_counts p j
      · simp only [Fin.val_one, cl, HardinA229697StripData.cl, HardinA229589StripData.cl,
        Nat.reduceLT, Nat.reduceSub, show (1 : ℕ) ≠ 2 by decide, ite_false]
        rw [old]
        simp only [HardinA229537StripData.cl, HardinA229589StripData.cl, Nat.reduceEqDiff, ite_true,
          ite_false, show (1 : ℕ) ≠ 0 by decide, ite_false]
        exact HardinA229537StripCertificate.one_counts p j
      · simpa only [show (2 : Fin 3).val = 2 from rfl, cl, HardinA229697StripData.cl, HardinA229589StripData.cl, Nat.reduceLT, Nat.reduceSub, Fin.castAdd_castAdd, Nat.reduceAdd, Fin.cast_refl, id_eq, Nat.reduceEqDiff, ite_false, ite_true] using two_counts p j

private def W (i : Fin 22) : Fin 42 → ℤ :=
  Fin.append ((![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![16, 14, 15, 16, 18, 15, 15, 15, 15, 14, 15, 9, 15, 18],
    ![260, 189, 118, 129, 86, 118, 98, 63, 99, 189, 114, 14, 63, 86],
    ![2520, 1237, 900, 1113, 429, 900, 680, 341, 696, 1237, 567, 97, 341, 429],
    ![19222, 10182, 7161, 7935, 2593, 7161, 5634, 2090, 5702, 10182, 4191, 495, 2090, 2593],
    ![150018, 70335, 49977, 58186, 15365, 49977, 38448, 12492, 38882, 70335, 25931, 2877, 12492, 15365],
    ![1072948, 497538, 354339, 407955, 92319, 354339, 274872, 75814, 277192, 497538, 170932, 15925, 75814, 92319],
    ![7589002, 3369219, 2398389, 2796203, 548799, 2398389, 1850898, 453373, 1864204, 3369219, 1086879, 89945, 453373, 548799],
    ![51920778, 22585364, 16107853, 18837133, 3263060, 16107853, 12435604, 2714316, 12509676, 22585364, 6917299, 503879, 2714316, 3263060],
    ![349825802, 148697761, 106031251, 124749576, 19313939, 106031251, 81702682, 16150579, 82120184, 148697761, 43580675, 2832435, 16150579, 19313939],
    ![2316195368, 968048448, 690732433, 816169003, 114093573, 690732433, 531778796, 95899124, 534119676, 968048448, 273026442, 15899143, 95899124, 114093573],
    ![15146660246, 6232821103, 4447432211, 5278296261, 672146087, 4447432211, 3419799122, 567470964, 3432953304, 6232821103, 1700356031, 89299485, 567470964, 672146087],
    ![97922320234, 39773450273, 28385837577, 33818697141, 3951590335, 28385837577, 21805558568, 3349964376, 21879406780, 39773450273, 10535039903, 501434053, 3349964376, 3951590335],
    ![627116110166, 251778463542, 179695048104, 214860405660, 23183659575, 179695048104, 137902605184, 19726949103, 138317357910, 251778463542, 64969964669, 2815953153, 19726949103, 23183659575],
    ![3982654998300, 1582785498019, 1129675984390, 1355190241011, 135770581046, 1129675984390, 866167505288, 115921571952, 868496481604, 1582785498019, 398969185996, 15813107663, 115921571952, 135770581046],
    ![25109242865426, 9888454124475, 7057509726762, 8492147764487, 793761974923, 7057509726762, 5406680261256, 679836397641, 5419759186402, 9888454124475, 2440564292609, 88800912179, 679836397641, 793761974923],
    ![157281822657898, 61437293801998, 43847203073469, 52908473834043, 4633403297497, 43847203073469, 33564363848620, 3979832042062, 33637809453520, 61437293801998, 14876426468069, 498670943903, 3979832042062, 4633403297497],
    ![979529877125338, 379815445792307, 271056960281441, 327923337286520, 27007373100065, 271056960281441, 207336203920036, 23259590912860, 207748648103126, 379815445792307, 90384146835895, 2800349340805, 23259590912860, 27007373100065],
    ![6068821023081920, 2337536013506528, 1668094377178547, 2022925009675283, 157211192270831, 1668094377178547, 1275069336495112, 135729523273114, 1277385462437744, 2337536013506528, 547492731205442, 15725690339269, 135729523273114, 157211192270831],
    ![37424669085019018, 14327381356919033, 10223505477094939, 12426073904401541, 913993668546143, 10223505477094939, 7809619986598030, 790914700571617, 7822626478375552, 14327381356919033, 3307157811925111, 88309514862441, 790914700571617, 913993668546143],
    ![229808279777601326, 87488887920961154, 62424427572400663, 76032271671190237, 5307598676440184, 62424427572400663, 47656110867544068, 4602698237322612, 47729150359042532, 87488887920961154, 19925441979151741, 495912622650647, 4602698237322612, 5307598676440184],
    ![1405691884244348450, 532416357272082417, 379857062815933457, 463568131669789598, 30787949982677939, 379857062815933457, 289823627100936694, 26752361059466943, 290233789168377676, 532416357272082417, 119760943011261539, 2784856846749587, 26752361059466943, 30787949982677939]]) i) (HardinA229537StripCertificate.W i)

private theorem tail_step (i : Fin 21) (j : Fin 28) :
    W i.succ (j.natAdd 14) = T.mulVec (W i.castSucc) (j.natAdd 14) := by
  have block_tail (A : Matrix (Fin 14) (Fin 14) ℤ) (B : Matrix (Fin 14) (Fin 28) ℤ)
      (D : Matrix (Fin 28) (Fin 28) ℤ) (v : Fin 42 → ℤ) :
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A B (0 : Matrix (Fin 28) (Fin 14) ℤ) D)).mulVec v
          (j.natAdd 14) = D.mulVec (fun k : Fin 28 => v (k.natAdd 14)) j := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm]
    rw [Matrix.fromBlocks_mulVec]
    simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr,
      Matrix.zero_mulVec, zero_add]
    rfl
  rw [show T.mulVec (W i.castSucc) (j.natAdd 14) =
    HardinA229537StripData.T.mulVec (fun k : Fin 28 => W i.castSucc (k.natAdd 14)) j
      from block_tail _ _ _ _]
  simp only [W, Fin.append_right]
  simp_rw [← HardinA229537StripCertificate.powers]
  simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Matrix.mulVec_mulVec]

private theorem powers (i : Fin 22) : (T ^ i.val).mulVec terminal = W i := by
  have hz : W 0 = terminal := by
    funext j
    induction j using Fin.addCases (m := 14) (n := 28) with
    | left j => fin_cases j <;> rfl
    | right j =>
      simp only [W, Fin.append_right, terminal]
      rw [← HardinA229537StripCertificate.powers]
      norm_num
      fin_cases j <;> rfl
  have step (k : Fin 21) : W k.succ = T.mulVec (W k.castSucc) := by
    funext j
    induction j using Fin.addCases (m := 14) (n := 28) with
    | left j =>
      have new_coordinates : ∀ (k : Fin 21) (j : Fin 14),
          W k.succ (j.castAdd 28) = T.mulVec (W k.castSucc) (j.castAdd 28) := by
        decide +kernel
      exact new_coordinates k j
    | right j => exact tail_step k j
  induction i using Fin.induction with
  | zero => simpa only [Fin.val_zero, pow_zero, Matrix.one_mulVec] using hz.symm
  | succ i ih =>
    simp only [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec]
    rw [show (T ^ i.val).mulVec terminal = W i.castSucc from ih]
    exact (step i).symm

private theorem tail_polynomial (j : Fin 28) :
    W 21 (j.natAdd 14) = (∑ k : Fin 18,
      (![64, 96, -1152, -1336, 7824, 6426, -23929, -13335, 31293, 15750, -18957, -10083, 4906, 2967, -357, -270, 21, 9] k : ℤ) •
        W ⟨3 + k.val, by omega⟩) (j.natAdd 14) := by
  have rel (n : ℕ) :
      ((HardinA229537StripData.T ^ (n + 14)).mulVec HardinA229537StripData.terminal) j =
        (∑ k : Fin 12, (![-16,-16,196,124,-741,-238,787,250,-288,-102,23,6] k : ℤ) •
          (HardinA229537StripData.T ^ (n + 2 + k.val)).mulVec HardinA229537StripData.terminal) j := by
    have h := congrArg (fun w => (HardinA229537StripData.T ^ n).mulVec w)
      HardinA229537StripCertificate.finite_certificate.2
    have he : (HardinA229537StripData.T ^ (n + 14)).mulVec HardinA229537StripData.terminal =
        ∑ k : Fin 12, (![-16,-16,196,124,-741,-238,787,250,-288,-102,23,6] k : ℤ) •
          (HardinA229537StripData.T ^ (n + 2 + k.val)).mulVec HardinA229537StripData.terminal := by
      simpa only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        ← pow_add, Nat.add_assoc] using h
    exact congrFun he j
  have h0 := rel 1
  have h1 := rel 2
  have h2 := rel 3
  have h3 := rel 4
  have h4 := rel 5
  have h5 := rel 6
  have h6 := rel 7
  simp only [W, Fin.append_right, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.reduceAdd]
  simp_rw [← HardinA229537StripCertificate.powers]
  simp only [show (21 : Fin 22).val = 21 from rfl]
  norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6
  linear_combination h6 - 4*h0 - 2*h1 + 25*h2 + 3*h3 - 16*h4 - 3*h5

/-- Exact-budget transition counts and the eventual order-eighteen vector relation. -/
theorem finite_certificate :
    (∀ p (d : Fin 3) (s : Fin 42),
      (∑ r : Fin 4 → Fin 3, if bondDefects between p r ≤ d.val ∧
        cl r (d.val - bondDefects between p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (T ^ 21).mulVec terminal = ∑ k : Fin 18,
      (![64, 96, -1152, -1336, 7824, 6426, -23929, -13335, 31293, 15750, -18957, -10083, 4906, 2967, -357, -270, 21, 9] k : ℤ) •
        (T ^ (3 + k.val)).mulVec terminal := by
  refine ⟨transition_counts, ?_⟩
  rw [show 21 = (21 : Fin 22).val from rfl, powers]
  simp_rw [show ∀ k : Fin 18, (T ^ (3 + k.val)).mulVec terminal =
    W ⟨3 + k.val, by omega⟩ from fun k => powers ⟨3 + k.val, by omega⟩]
  funext j
  induction j using Fin.addCases (m := 14) (n := 28) with
  | left j =>
    have new_coordinates : ∀ j : Fin 14,
        W 21 (j.castAdd 28) = (∑ k : Fin 18,
          (![64, 96, -1152, -1336, 7824, 6426, -23929, -13335, 31293, 15750, -18957, -10083, 4906, 2967, -357, -270, 21, 9] k : ℤ) •
            W ⟨3 + k.val, by omega⟩) (j.castAdd 28) := by decide +kernel
    exact new_coordinates j
  | right j => exact tail_polynomial j

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229640StripCertificate

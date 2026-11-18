/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.finite_certificate
   digest: Exact defect sectors of the four-row HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31548; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229537Strip.result)
zero_cut: proof_shape=bind-only; consumers=HardinA229537Strip.result
tuple_column: proof_shape=bind-only; consumers=HardinA229537Strip.result
zero_counts: proof_shape=bind-only; consumers=HardinA229537Strip.result
one_representatives: proof_shape=bind-only; consumers=HardinA229537Strip.result
cost_relabel: proof_shape=bind-only; consumers=HardinA229537Strip.result
one_counts: proof_shape=bind-only; consumers=HardinA229537Strip.result
transition_counts: proof_shape=bind-only; consumers=HardinA229537Strip.result
Z: proof_shape=bind-only; consumers=HardinA229537Strip.result
zero_powers: proof_shape=bind-only; consumers=HardinA229537Strip.result
W: proof_shape=bind-only; consumers=HardinA229537Strip.result
tail_step: proof_shape=bind-only; consumers=HardinA229537Strip.result
tail_polynomial: proof_shape=bind-only; consumers=HardinA229537Strip.result
powers: proof_shape=bind-only; consumers=HardinA229537Strip.result
finite_certificate: proof_shape=bind-only; consumers=HardinA229537Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.Data.Matrix.Block

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229537StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem tuple_column (p : Fin 4 → Fin 3) :
    HardinA233177PairTransfer.column (p 0, p 1, p 2, p 3) = p := by
  funext i
  fin_cases i <;> rfl

private theorem zero_cut (p r : Fin 4 → Fin 3) :
    bondDefects between p r = 0 ↔
      HardinA233177PairTransfer.compatible (p 0, p 1, p 2, p 3) (r 0, r 1, r 2, r 3) := by
  simp only [bondDefects, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    between, Finset.mem_filter, Finset.mem_univ, true_and,
    HardinA233177PairTransfer.compatible, tuple_column]
  constructor
  · intro h i j hij
    exact h (i, j) hij
  · intro h e he
    exact h e.1 e.2 he

private theorem zero_counts (p : Fin 4 → Fin 3) (j : Fin 14) :
    (∑ r : Fin 4 → Fin 3, if bondDefects between p r = 0 ∧
      HardinA233177PairTransfer.cls (r 0, r 1, r 2, r 3) = j then (1 : ℤ) else 0) =
      HardinA233177PairTransfer.Q (HardinA233177PairTransfer.cls (p 0, p 1, p 2, p 3)) j := by
  simp_rw [zero_cut]
  rw [HardinA233125SquareStrip.label_sum]
  simpa only [Fintype.sum_prod_type] using
    HardinA233177PairTransfer.quotient_rows (p 0, p 1, p 2, p 3) j

private theorem cost_relabel (e : Equiv.Perm (Fin 3)) (p r : HardinA233177PairTransfer.Col) :
    bondDefects between (HardinA233177PairTransfer.column (HardinA233177PairTransfer.relabel e p))
      (HardinA233177PairTransfer.column (HardinA233177PairTransfer.relabel e r)) =
      bondDefects between (HardinA233177PairTransfer.column p) (HardinA233177PairTransfer.column r) := by
  simp only [bondDefects, HardinA233177PairTransfer.column_relabel, e.injective.eq_iff]

private theorem one_representatives : ∀ i j : Fin 14,
    (∑ r : HardinA233177PairTransfer.Col,
      if bondDefects between (HardinA233177PairTransfer.column (HardinA233177PairTransfer.representatives i))
        (HardinA233177PairTransfer.column r) = 1 ∧ HardinA233177PairTransfer.cls r = j
      then (1 : ℤ) else 0) = T (i.castAdd 14) (j.natAdd 14) := by
  decide +kernel

private theorem one_counts (p : Fin 4 → Fin 3) (j : Fin 14) :
    (∑ r : Fin 4 → Fin 3, if bondDefects between p r = 1 ∧
      HardinA233177PairTransfer.cls (r 0, r 1, r 2, r 3) = j then (1 : ℤ) else 0) =
      T ((HardinA233177PairTransfer.cls (p 0, p 1, p 2, p 3)).castAdd 14) (j.natAdd 14) := by
  rw [HardinA233125SquareStrip.label_sum]
  let b : HardinA233177PairTransfer.Col := (p 0, p 1, p 2, p 3)
  change (∑ a : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, ∑ e : Fin 3, _) = _
  have hc := tuple_column p
  change HardinA233177PairTransfer.column b = p at hc
  rw [← hc]
  change (∑ a : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, ∑ e : Fin 3,
    if bondDefects between (HardinA233177PairTransfer.column b)
      (HardinA233177PairTransfer.column (a,c,d,e)) = 1 ∧
      HardinA233177PairTransfer.cls (a,c,d,e) = j then (1 : ℤ) else 0) = _
  rw [← Fintype.sum_prod_type, ← Fintype.sum_prod_type, ← Fintype.sum_prod_type]
  obtain ⟨e, he⟩ := HardinA233177PairTransfer.class_rep b
  calc
    _ = ∑ r : HardinA233177PairTransfer.Col,
      if bondDefects between
        (HardinA233177PairTransfer.column (HardinA233177PairTransfer.relabel e b))
        (HardinA233177PairTransfer.column (HardinA233177PairTransfer.relabel e r)) = 1 ∧
        HardinA233177PairTransfer.cls (HardinA233177PairTransfer.relabel e r) = j
      then (1 : ℤ) else 0 := by simp only [cost_relabel, HardinA233177PairTransfer.class_relabel]
    _ = _ := by
      rw [he]
      rw [(HardinA233177PairTransfer.relabel e).sum_comp]
      exact one_representatives _ _

private theorem transition_counts (p : Fin 4 → Fin 3) (d : Fin 2) (s : Fin 28) :
    (∑ r : Fin 4 → Fin 3, if bondDefects between p r ≤ d.val ∧
      cl r (d.val - bondDefects between p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s := by
  induction s using Fin.addCases (m := 14) (n := 14) with
  | left j =>
    have cut (r : Fin 4 → Fin 3) :
      (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = j.castAdd 14) ↔
      d.val = 1 ∧ bondDefects between p r = 0 ∧
        HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3) = j := by
      unfold cl
      split_ifs with h
      · have hn : (HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3)).natAdd 14 ≠ j.castAdd 14 := by
          intro he
          have := congrArg Fin.val he
          have := j.isLt
          simp only [Fin.val_natAdd, Fin.val_castAdd] at *
          omega
        simp only [hn, and_false]
        omega
      · simp only [Fin.castAdd_inj]
        have := d.isLt
        constructor <;> rintro ⟨h1,h2⟩
        · exact ⟨by omega, by omega, h2⟩
        · exact ⟨by omega, h2.2⟩
    simp_rw [cut]
    fin_cases d
    · simp [cl, T, Finset.sum_const_zero, Matrix.reindex_apply]
    · simpa only [true_and, cl, show (1 : ℕ) ≠ 0 by decide, if_false,
        T, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁] using zero_counts p j
  | right j =>
    have cut (r : Fin 4 → Fin 3) :
      (bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = j.natAdd 14) ↔
      bondDefects between p r = d.val ∧
        HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3) = j := by
      unfold cl
      split_ifs with h
      · simp only [Fin.natAdd_inj]
        constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨by omega, h2⟩
      · have hn : (HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3)).castAdd 14 ≠ j.natAdd 14 := by
          intro he
          have := congrArg Fin.val he
          have := (HardinA233177PairTransfer.cls (r 0,r 1,r 2,r 3)).isLt
          simp only [Fin.val_natAdd, Fin.val_castAdd] at *
          omega
        simp only [hn, and_false]
        omega
    simp_rw [cut]
    fin_cases d
    · simpa only [cl, if_true, T, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂] using zero_counts p j
    · simpa only [cl, show (1 : ℕ) ≠ 0 by decide, if_false] using one_counts p j

private def Z : Fin 22 → Fin 14 → ℤ :=
  Fin.append HardinA233177PairTransfer.W
    (![![2340880, 783812, 557050, 719483, 0, 557050, 417502, 0, 417502, 783812, 127826, 0, 0, 0],
    ![13154182, 4401225, 3124692, 4036330, 0, 3124692, 2340880, 0, 2340880, 4401225, 719483, 0, 0, 0],
    ![73848212, 24716429, 17555407, 22676115, 0, 17555407, 13154182, 0, 13154182, 24716429, 4036330, 0, 0, 0],
    ![414752726, 138796163, 98564641, 127317400, 0, 98564641, 73848212, 0, 73848212, 138796163, 22676115, 0, 0, 0],
    ![2328976316, 779430930, 553548889, 715021167, 0, 553548889, 414752726, 0, 414752726, 779430930, 127317400, 0, 0, 0],
    ![13078925146, 4376977302, 3108407246, 4015155576, 0, 3108407246, 2328976316, 0, 2328976316, 4376977302, 715021167, 0, 0, 0],
    ![73445604900, 24579465270, 17455902448, 22547900917, 0, 17455902448, 13078925146, 0, 13078925146, 24579465270, 4015155576, 0, 0, 0],
    ![412444183090, 138028873535, 98025070170, 126619691016, 0, 98025070170, 73445604900, 0, 73445604900, 138028873535, 22547900917, 0, 0, 0],
    ![2316125942632, 775117817811, 550473056625, 711049831077, 0, 550473056625, 412444183090, 0, 412444183090, 775117817811, 126619691016, 0, 0, 0],
    ![13006491777522, 4352766648145, 3091243760443, 3992981269270, 0, 3091243760443, 2316125942632, 0, 2316125942632, 4352766648145, 711049831077, 0, 0, 0],
    ![73039491498464, 24443483455380, 17359258425667, 22423074904889, 0, 17359258425667, 13006491777522, 0, 13006491777522, 24443483455380, 3992981269270, 0, 0, 0],
    ![410162067440982, 137265308284400, 97482974953844, 125919439678494, 0, 97482974953844, 73039491498464, 0, 73039491498464, 137265308284400, 22423074904889, 0, 0, 0],
    ![2303314113185784, 770829790357720, 547427375725382, 707115758914671, 0, 547427375725382, 410162067440982, 0, 410162067440982, 770829790357720, 125919439678494, 0, 0, 0],
    ![12934536678297246, 4328687038183557, 3074143903543504, 3970893133579718, 0, 3074143903543504, 2303314113185784, 0, 2303314113185784, 4328687038183557, 707115758914671, 0, 0, 0]])

private theorem zero_powers (i : Fin 22) :
    (HardinA233177PairTransfer.Q ^ i.val).mulVec (1 : Fin 14 → ℤ) = Z i := by
  have recurrence (n : ℕ) :
      (HardinA233177PairTransfer.Q ^ (n + 7)).mulVec (1 : Fin 14 → ℤ) =
        ∑ j : Fin 6, HardinA233177PairTransfer.coefficients j •
          (HardinA233177PairTransfer.Q ^ (n + 1 + j.val)).mulVec (1 : Fin 14 → ℤ) := by
    have h := congrArg (fun w => (HardinA233177PairTransfer.Q ^ n).mulVec w)
      HardinA233177PairTransfer.power_polynomial
    simpa only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      ← pow_add, Nat.add_assoc] using h
  have go (n : ℕ) (hn : n < 22) :
      (HardinA233177PairTransfer.Q ^ n).mulVec (1 : Fin 14 → ℤ) = Z ⟨n, hn⟩ := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hsmall : n < 8
      · exact HardinA233177PairTransfer.powers_table ⟨n, hsmall⟩
      · have hrec := recurrence (n - 7)
        rw [show n - 7 + 7 = n by omega] at hrec
        rw [hrec]
        have earlier (j : Fin 6) :
            (HardinA233177PairTransfer.Q ^ (n - 7 + 1 + j.val)).mulVec
              (1 : Fin 14 → ℤ) = Z ⟨n - 7 + 1 + j.val, by omega⟩ :=
          ih _ (by omega) (by omega)
        simp_rw [earlier]
        interval_cases n <;> funext k <;> fin_cases k <;>
          norm_num [Z, HardinA233177PairTransfer.W,
            HardinA233177PairTransfer.coefficients, Fin.sum_univ_succ]
  exact go i.val i.isLt

private def W (i : Fin 15) : Fin 28 → ℤ :=
  Fin.append ((![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 12, 8, 8, 6, 8, 6, 3, 6, 12, 6, 0, 3, 6],
    ![120, 49, 31, 42, 9, 31, 20, 8, 20, 49, 20, 0, 8, 9],
    ![724, 428, 322, 328, 55, 322, 264, 51, 264, 428, 134, 0, 51, 55],
    ![6160, 2704, 1903, 2150, 288, 1903, 1468, 263, 1468, 2704, 794, 0, 263, 288],
    ![40920, 18296, 13321, 14982, 1652, 13321, 10470, 1528, 10470, 18296, 4878, 0, 1528, 1652],
    ![280152, 117021, 83683, 96664, 9184, 83683, 64826, 8447, 64826, 117021, 30046, 0, 8447, 9184],
    ![1815752, 744816, 535878, 625464, 51775, 535878, 415062, 47749, 415062, 744816, 181846, 0, 47749, 51775],
    ![11665456, 4657599, 3336391, 3940754, 290259, 3336391, 2571816, 267374, 2571816, 4657599, 1102432, 0, 267374, 290259],
    ![73475644, 28863570, 20687092, 24636152, 1631121, 20687092, 15914804, 1503295, 15914804, 28863570, 6622478, 0, 1503295, 1631121],
    ![458085456, 177198520, 126828621, 152147306, 9157038, 126828621, 97329928, 8437555, 97329928, 177198520, 39687986, 0, 8437555, 9157038],
    ![2825893800, 1080173062, 772848457, 932633526, 51428874, 772848457, 592061986, 47392544, 592061986, 1080173062, 236690978, 0, 47392544, 51428874],
    ![17297388672, 6543135579, 4678478409, 5674694984, 288789678, 4678478409, 3578207734, 266113563, 3578207734, 6543135579, 1407355134, 0, 266113563, 288789678],
    ![105143454200, 39425416516, 28178327908, 34328155076, 1621769497, 28178327908, 21522210170, 1494452097, 21522210170, 39425416516, 8340654622, 0, 1494452097, 1621769497],
    ![635447036928, 236454026529, 168927769187, 206582067498, 9107154045, 168927769187, 128868177900, 8392132878, 128868177900, 236454026529, 49298924172, 0, 8392132878, 9107154045]]) i)
    (Z ⟨i.val, by omega⟩)

private theorem tail_step (i : Fin 14) (j : Fin 14) :
    W i.succ (j.natAdd 14) = T.mulVec (W i.castSucc) (j.natAdd 14) := by
  simp only [W, Fin.append_right]
  rw [← zero_powers, ← zero_powers]
  simp only [T, Matrix.reindex_apply]
  rw [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inr, Matrix.zero_mulVec, zero_add, Equiv.symm_symm]
  simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Matrix.mulVec_mulVec]
  rfl

private theorem powers (i : Fin 15) :
    (T ^ i.val).mulVec terminal = W i := by
  have hzero : W 0 = terminal := by
    have hz := HardinA233177PairTransfer.powers_table 0
    change (1 : Fin 14 → ℤ) = HardinA233177PairTransfer.W 0 at hz
    change Fin.append (0 : Fin 14 → ℤ) (HardinA233177PairTransfer.W 0) = terminal
    rw [← hz]
    rfl
  have step (k : Fin 14) : W k.succ = T.mulVec (W k.castSucc) := by
    funext j
    induction j using Fin.addCases (m := 14) (n := 14) with
    | left j =>
      have new_coordinates : ∀ (k : Fin 14) (j : Fin 14),
          W k.succ (j.castAdd 14) = T.mulVec (W k.castSucc) (j.castAdd 14) := by
        decide +kernel
      exact new_coordinates k j
    | right j => exact tail_step k j
  induction i using Fin.induction with
  | zero => simpa only [Fin.val_zero, pow_zero, Matrix.one_mulVec] using hzero.symm
  | succ i ih =>
    simp only [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec]
    rw [show (T ^ i.val).mulVec terminal = W i.castSucc from ih]
    exact (step i).symm

private theorem tail_polynomial (j : Fin 14) :
    W 14 (j.natAdd 14) = (∑ k : Fin 12,
      (![-16, -16, 196, 124, -741, -238, 787, 250, -288, -102, 23, 6] k : ℤ) •
        W ⟨2 + k.val, by omega⟩) (j.natAdd 14) := by
  have rel (n : ℕ) :
      ((HardinA233177PairTransfer.Q ^ (n + 7)).mulVec (1 : Fin 14 → ℤ)) j =
        (∑ k : Fin 6, HardinA233177PairTransfer.coefficients k •
          (HardinA233177PairTransfer.Q ^ (n + 1 + k.val)).mulVec (1 : Fin 14 → ℤ)) j := by
    have h := congrArg (fun w => (HardinA233177PairTransfer.Q ^ n).mulVec w)
      HardinA233177PairTransfer.power_polynomial
    have he : (HardinA233177PairTransfer.Q ^ (n + 7)).mulVec (1 : Fin 14 → ℤ) =
        ∑ k : Fin 6, HardinA233177PairTransfer.coefficients k •
          (HardinA233177PairTransfer.Q ^ (n + 1 + k.val)).mulVec (1 : Fin 14 → ℤ) := by
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
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, Nat.reduceAdd,
    Fin.mk_zero']
  simp_rw [← zero_powers]
  norm_num [HardinA233177PairTransfer.coefficients, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6
  linear_combination 4 * h0 + 2 * h1 - 25 * h2 - 3 * h3 + 16 * h4 + 3 * h5 + h6

/-- Exact-budget transition counts and the eventual order-twelve vector relation. -/
theorem finite_certificate :
    (∀ p (d : Fin 2) (s : Fin 28),
      (∑ r : Fin 4 → Fin 3, if bondDefects between p r ≤ d.val ∧
        cl r (d.val - bondDefects between p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (T ^ 14).mulVec terminal = ∑ k : Fin 12,
      (![-16, -16, 196, 124, -741, -238, 787, 250, -288, -102, 23, 6] k : ℤ) •
        (T ^ (2 + k.val)).mulVec terminal := by
  refine ⟨transition_counts, ?_⟩
  rw [show 14 = (14 : Fin 15).val from rfl, powers]
  simp_rw [show ∀ k : Fin 12, (T ^ (2 + k.val)).mulVec terminal =
    W ⟨2 + k.val, by omega⟩ from fun k => powers ⟨2 + k.val, by omega⟩]
  funext j
  induction j using Fin.addCases (m := 14) (n := 14) with
  | left j =>
    have new_coordinates : ∀ j : Fin 14,
        W 14 (j.castAdd 14) = (∑ k : Fin 12,
          (![-16, -16, 196, 124, -741, -238, 787, 250, -288, -102, 23, 6] k : ℤ) •
            W ⟨2 + k.val, by omega⟩) (j.castAdd 14) := by decide +kernel
    exact new_coordinates j
  | right j => exact tail_polynomial j

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate

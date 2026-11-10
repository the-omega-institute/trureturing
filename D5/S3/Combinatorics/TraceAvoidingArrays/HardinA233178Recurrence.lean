/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal all-width five-row recurrence through exact source cardinalities. -/

/-
admission_basis: staged open-problem-resolution candidate for preregistered issue #28580.
No freeze, final OpenProblemResolutionClaim or project settlement is supplied here.
proof_shape: count_transfer=bind-only (array/column equivalence and generic continuation count),
consumed by chromatic_recurrence and result;
chromatic_recurrence=bind-only, consumed by scaled_recurrence and result;
result=content after inlining the new literal source-cardinality bridge.
columnEquiv, column_apply and arrayEquiv feed proper_columns and count_transfer;
proper_columns and tail_iff_good feed count_transfer;
count_transfer feeds chromatic_recurrence; scaled_recurrence feeds result.
The final exact source bridge is HardinA233178Literal.chromatic_source_count.
Generic propagation reuses the original TransferMatrix.cont_matrix and scalarRelationShift.
utility none: this module proves an unbounded literal recurrence by source bijections and
algebra; the numerical certificate belongs to the consumed HardinA233178Chromatic module.
No exact full-E supplier was found in the acquired bounded searches; third-party search
remains incomplete and this unit makes no global-priority claim.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic

/-! The array-to-column correspondence precedes the all-width recurrence. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence

attribute [local instance] Classical.propDecidable

open HardinA233178Literal (Array Edges Proper chromaticCount a FullE)
open HardinA233178Chromatic (Column colour Bond T v)

private def columnEquiv : Column ≃ (Fin 5 → Fin 3) :=
  (finFunctionFinEquiv (m := 3) (n := 5)).symm

private theorem column_apply (p : Column) (r : Fin 5) : columnEquiv p r = colour p r := rfl

private def arrayEquiv (n : ℕ) : (Fin n → Column) ≃ Array n 3 where
  toFun f p := colour (f p.2) p.1
  invFun q j := columnEquiv.symm (fun r => q (r,j))
  left_inv f := by
    funext j
    have he : (fun r => colour (f j) r) = columnEquiv (f j) := by
      funext r
      exact (column_apply _ _).symm
    change columnEquiv.symm (fun r => colour (f j) r) = f j
    rw [he]
    exact columnEquiv.symm_apply_apply (f j)
  right_inv q := by
    funext p
    simpa only [column_apply] using
      congrFun (columnEquiv.apply_symm_apply (fun r => q (r,p.2))) p.1

private theorem proper_columns (n : ℕ) (f : Fin (n + 1) → Column) :
    Proper (arrayEquiv (n+1) f) ↔
      TransferMatrix.good Bond (fun _ _ _ => True) (List.ofFn f) := by
  rw [TransferMatrix.good_iff_local]
  simp only [List.length_ofFn, implies_true, and_true]
  have get (i : ℕ) (hi : i < n+1) :
      (List.ofFn f).getD i default = f ⟨i,hi⟩ := by
    rw [List.getD_eq_getElem (List.ofFn f) default (by simpa using hi), List.getElem_ofFn]
  constructor
  · intro hp i hi
    rw [get i (by omega), get (i+1) hi]
    intro r s hrs
    exact hp (r,⟨i,by omega⟩) (s,⟨i+1,hi⟩) ⟨rfl,hrs⟩
  · intro hf p q he
    have hi : p.2.val + 1 < n+1 := by have := q.2.isLt; have := he.1; omega
    have hg := hf p.2.val hi
    rw [get _ p.2.isLt, get _ hi] at hg
    have hq : (⟨p.2.val+1,hi⟩ : Fin (n+1)) = q.2 := Fin.ext he.1.symm
    change colour (f p.2) p.1 ≠ colour (f q.2) q.1
    simpa only [hq] using hg p.1 q.1 he.2

private theorem tail_iff_good (a b : Column) (cs : List Column) :
    TransferMatrix.tailGood (fun _ _ => True) (fun _ b c => Bond b c) a b cs ↔
      TransferMatrix.good Bond (fun _ _ _ => True) (b :: cs) := by
  induction cs generalizing a b with
  | nil => simp [TransferMatrix.tailGood, TransferMatrix.good]
  | cons c cs ih =>
    simp only [TransferMatrix.tailGood, true_and, ih]
    cases cs with
    | nil => simp [TransferMatrix.good, TransferMatrix.tailGood]
    | cons d ds => simp [TransferMatrix.good, TransferMatrix.tailGood]

set_option maxHeartbeats 1000000 in
/-- The complete finite-domain cardinality bridge, uniform in the width. -/
theorem count_transfer (n : ℕ) :
    chromaticCount (n+1) = dotProduct (1 : Column → ℤ) (v n) := by
  classical
  unfold chromaticCount
  rw [← (arrayEquiv (n+1)).sum_comp]
  simp_rw [proper_columns]
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Column)).sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons]
  have hc (p : Column) :
      (∑ f : Fin n → Column, if TransferMatrix.good Bond (fun _ _ _ => True)
        (p :: List.ofFn f) then (1:ℤ) else 0) =
      TransferMatrix.cont (fun _ _ : Column => True) (fun _ b c => Bond b c) n p p := by
    simp only [← tail_iff_good p p, TransferMatrix.cont,
      Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast
    rfl
  simp_rw [hc]
  have hT (a b : Column) (_ : True) (s : Column) :
      (∑ c : Column, if True ∧ Bond b c ∧ c = s then (1:ℤ) else 0) = T b s := by
    calc
      _ = ∑ c : Column, if c = s then (if Bond b c then (1:ℤ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : c = s <;> by_cases hb : Bond b c <;> simp [hc,hb]
      _ = T b s := by rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, ite_true]; rfl
  have hm (p : Column) := TransferMatrix.cont_matrix (fun _ _ : Column => True)
    (fun _ b c => Bond b c) (fun _ b => b) T
    (by intro a b hab s; simpa only [true_and] using hT a b hab s) n p p trivial
  simp_rw [hm]
  simp only [dotProduct, Pi.one_apply, one_mul, v]

/-- The unscaled chromatic count has the certified recurrence at every required width. -/
theorem chromatic_recurrence (n : ℕ) :
    chromaticCount (n+12) = 6 * chromaticCount (n+11) + 31 * chromaticCount (n+10) -
      97 * chromaticCount (n+9) - 163 * chromaticCount (n+8) +
      417 * chromaticCount (n+7) + 93 * chromaticCount (n+6) -
      514 * chromaticCount (n+5) + 192 * chromaticCount (n+4) +
      72 * chromaticCount (n+3) - 36 * chromaticCount (n+2) := by
  have h := HardinA233178Chromatic.result (1 : Column → ℤ) n
  simpa only [← count_transfer, Nat.add_assoc] using h

private theorem scaled_recurrence (n : ℕ) :
    (a (n+12) : ℤ) = 192 * (a (n+11) : ℤ) + 31744 * (a (n+10) : ℤ) -
      3178496 * (a (n+9) : ℤ) - 170917888 * (a (n+8) : ℤ) +
      13992198144 * (a (n+7) : ℤ) + 99857989632 * (a (n+6) : ℤ) -
      17660905521152 * (a (n+5) : ℤ) + 211106232532992 * (a (n+4) : ℤ) +
      2533274790395904 * (a (n+3) : ℤ) - 40532396646334464 * (a (n+2) : ℤ) := by
  have s12 := HardinA233178Literal.chromatic_source_count (n+12) (by omega)
  have s11 := HardinA233178Literal.chromatic_source_count (n+11) (by omega)
  have s10 := HardinA233178Literal.chromatic_source_count (n+10) (by omega)
  have s9 := HardinA233178Literal.chromatic_source_count (n+9) (by omega)
  have s8 := HardinA233178Literal.chromatic_source_count (n+8) (by omega)
  have s7 := HardinA233178Literal.chromatic_source_count (n+7) (by omega)
  have s6 := HardinA233178Literal.chromatic_source_count (n+6) (by omega)
  have s5 := HardinA233178Literal.chromatic_source_count (n+5) (by omega)
  have s4 := HardinA233178Literal.chromatic_source_count (n+4) (by omega)
  have s3 := HardinA233178Literal.chromatic_source_count (n+3) (by omega)
  have s2 := HardinA233178Literal.chromatic_source_count (n+2) (by omega)
  norm_num [pow_add] at s12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2
  have hr := chromatic_recurrence n
  have h48 : 48 * ((a (n+12) : ℤ) - (192 * (a (n+11) : ℤ) +
      31744 * (a (n+10) : ℤ) - 3178496 * (a (n+9) : ℤ) -
      170917888 * (a (n+8) : ℤ) + 13992198144 * (a (n+7) : ℤ) +
      99857989632 * (a (n+6) : ℤ) - 17660905521152 * (a (n+5) : ℤ) +
      211106232532992 * (a (n+4) : ℤ) + 2533274790395904 * (a (n+3) : ℤ) -
      40532396646334464 * (a (n+2) : ℤ))) = 0 := by
    linear_combination s12 - 192*s11 - 31744*s10 + 3178496*s9 + 170917888*s8 -
      13992198144*s7 - 99857989632*s6 + 17660905521152*s5 - 211106232532992*s4 -
      2533274790395904*s3 + 40532396646334464*s2 +
      (32:ℤ)^n * 1152921504606846976 * hr
  linarith

/-- The exact registered event on the literal source count, with no upper cutoff. -/
theorem result : FullE := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n = k+12 := ⟨n-12,by omega⟩
  have h := scaled_recurrence k
  simpa only [show k+12-1 = k+11 by omega, show k+12-2 = k+10 by omega,
    show k+12-3 = k+9 by omega, show k+12-4 = k+8 by omega,
    show k+12-5 = k+7 by omega, show k+12-6 = k+6 by omega,
    show k+12-7 = k+5 by omega, show k+12-8 = k+4 by omega,
    show k+12-9 = k+3 by omega, show k+12-10 = k+2 by omega] using h

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence

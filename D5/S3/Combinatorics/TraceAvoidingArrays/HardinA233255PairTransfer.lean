/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer
   mirror-E: none
   anchors: []
   utility: kind=consumer; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.literal_pair_bridge
   digest: Literal positive-height seven-column arrays and their exact scanner-weighted pair transfer. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer

open HardinA233175PairStrip (Seen good finish)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open HardinA233251TriangleStrip
  (widthNormal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233255LiteralBridge (rowWeight rowFinish scanner_fibres)

abbrev Row := Fin 7 → Fin 6
abbrev PairRow := Fin 7 → Fin 3
abbrev Boundary := Fin 6 → Fin 3

def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 6, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 6, c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5

def Legal {h : ℕ} (A : Fin h × Fin 7 → Fin 6) : Prop :=
  (∃ i : Fin h, i.val = 0 ∧ A (i, 0) = 0) ∧
    (∀ i, rowLegal (fun j => A (i, j))) ∧
    (∀ (i : Fin h) (hi : i.val + 1 < h),
      bonds (fun j => A (i, j)) (fun j => A (⟨i.val + 1, hi⟩, j))) ∧
    widthNormal (false, false) (fun i j => A (i, j))

private instance decidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance decidableNormal {h : ℕ} (s : Seen) (f : Fin h → Row) :
    Decidable (widthNormal s f) :=
  inferInstanceAs (Decidable (∀ _ _, (_ → _) ∧ (_ → _)))
private instance decidableLegal {h : ℕ} (A : Fin h × Fin 7 → Fin 6) : Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
private instance decidableGood (s : Seen) (c : Row) : Decidable (good s c) := by
  unfold good
  infer_instance

/-- The original individual-array count, on the positive source domain only. -/
def a (h : ℕ+) : ℕ := (Finset.univ.filter (fun A : Fin h.val × Fin 7 → Fin 6 => Legal A)).card

def pairs (c : Row) : Boundary := fun j => beta (c j.succ)
def compatible (p : Boundary) (c : Row) : Prop := ∀ j : Fin 6, p j ≠ beta (c j.castSucc)
private instance decidableCompatible (p : Boundary) (c : Row) : Decidable (compatible p c) :=
  inferInstanceAs (Decidable (∀ _, _))

def rowProper (q : PairRow) : Prop := ∀ j : Fin 6, q j.castSucc ≠ q j.succ
def labelCompatible (p : Boundary) (q : PairRow) : Prop := ∀ j : Fin 6, p j ≠ q j.castSucc
def labelBoundary (q : PairRow) : Boundary := fun j => q j.succ
private instance decidableRowProper (q : PairRow) : Decidable (rowProper q) :=
  inferInstanceAs (Decidable (∀ _, _))
private instance decidableLabelCompatible (p : Boundary) (q : PairRow) :
    Decidable (labelCompatible p q) := inferInstanceAs (Decidable (∀ _, _))

def pairV : ℕ → Seen → Boundary → ℤ
  | 0, _, _ => 1
  | n + 1, s, p => ∑ q : PairRow, if rowProper q ∧ labelCompatible p q then
      rowWeight s q * pairV n (rowFinish s q) (labelBoundary q) else 0

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private theorem step_pair (w : Seen → Boundary → ℤ) (s : Seen) (p : Boundary) :
    widthStep rowLegal pairs compatible w s p =
      ∑ q : PairRow, if rowProper q ∧ labelCompatible p q then
        rowWeight s q * w (rowFinish s q) (labelBoundary q) else 0 := by
  unfold widthStep
  have h := scanner_fibres 7 s (fun t q =>
    if rowProper q ∧ labelCompatible p q then w t (labelBoundary q) else 0)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro c _
    simp only [rowLegal, colour_bond_iff, rowProper, labelCompatible, compatible,
      labelBoundary, pairs]
    split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp_all

/-- All continuation heights retain the exact original scanner and individual-colour fibres. -/
theorem continuation_pair_bridge (n : ℕ) (s : Seen) (p : Boundary) :
    widthV rowLegal pairs compatible n s p = pairV n s p := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [widthV, step_pair]
    simp_rw [ih]
    rfl

/-- The anchored first row is counted in individual colours, with the full row scanner. -/
theorem literal_pair_bridge (n : ℕ) :
    (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
      ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
        pairV n (finish (false, false) c) (pairs c) else 0 := by
  have h := width_counting_bridge rowLegal pairs compatible bonds bonds_iff n
  change (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) = widthTotal rowLegal pairs
    (widthV rowLegal pairs compatible n) at h
  rw [h]
  unfold widthTotal
  simp_rw [continuation_pair_bridge]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer

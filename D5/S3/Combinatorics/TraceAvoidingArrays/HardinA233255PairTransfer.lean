/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal positive-height arrays and their exact scanner-weighted pair transfer. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge

/-! The labelled transfer retains every individual-colour scanner fibre. -/

/-
decidableRowProper: proof_shape=bind-only; consumers=pairV, step_pair, literal_pair_bridge
first_fibres: proof_shape=bind-only; consumers=literal_pair_bridge
-/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer

open HardinA233175PairStrip (Seen good finish)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233255LiteralBridge (rowWeight rowFinish scanner_fibres)

abbrev Row := Fin 7 → Fin 6
abbrev PairRow := Fin 7 → Fin 3
abbrev Boundary := Fin 6 → Fin 3

def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 6, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 6, c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5

abbrev Legal {h : ℕ} (A : Fin h × Fin 7 → Fin 6) : Prop :=
  widthLegal rowLegal bonds A

instance decidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

/-- The original individual-array count, on the positive source domain only. -/
def a (h : ℕ+) : ℕ := (Finset.univ.filter (fun A : Fin h.val × Fin 7 → Fin 6 => Legal A)).card

def pairs (c : Row) : Boundary := fun j => beta (c j.succ)
def compatible (p : Boundary) (c : Row) : Prop := ∀ j : Fin 6, p j ≠ beta (c j.castSucc)
private instance decidableCompatible (p : Boundary) (c : Row) : Decidable (compatible p c) :=
  inferInstanceAs (Decidable (∀ _, _))

def rowProper (q : PairRow) : Prop := ∀ j : Fin 6, q j.castSucc ≠ q j.succ
def labelCompatible (p : Boundary) (q : PairRow) : Prop := ∀ j : Fin 6, p j ≠ q j.castSucc
def labelBoundary (q : PairRow) : Boundary := fun j => q j.succ
instance decidableRowProper (q : PairRow) : Decidable (rowProper q) :=
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
    have hr : rowProper (fun j => beta (c j)) ↔ rowLegal c := by
      simp only [rowProper, rowLegal, colour_bond_iff]
    have hc : labelCompatible p (fun j => beta (c j)) ↔ compatible p c := Iff.rfl
    have hb : labelBoundary (fun j => beta (c j)) = pairs c := rfl
    simp only [hr, hc, hb]
    by_cases hg : good s c <;> by_cases hl : rowLegal c ∧ compatible p c <;>
      simp only [hg, hl, ite_true, ite_false, and_true, and_false]
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

private theorem literal_colour_bridge (n : ℕ) :
    (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
      ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
        pairV n (finish (false, false) c) (pairs c) else 0 := by
  have h := width_counting_bridge rowLegal pairs compatible bonds bonds_iff n
  change (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) = widthTotal rowLegal pairs
    (widthV rowLegal pairs compatible n) at h
  rw [h]
  unfold widthTotal
  simp_rw [continuation_pair_bridge]

theorem first_fibres (H : Seen → PairRow → ℤ) :
    (∑ c : Row, if c 0 = 0 ∧ good (false, false) c then
      H (finish (false, false) c) (fun j => beta (c j)) else 0) =
    ∑ q : Fin 6 → Fin 3, rowWeight (false, false) q *
      H (rowFinish (false, false) q) (Fin.cons 0 q) := by
  rw [← (Fin.consEquiv (fun _ : Fin 7 => Fin 6)).sum_comp, Fintype.sum_prod_type]
  change (∑ x : Fin 6, ∑ c : Fin 6 → Fin 6,
    if x = 0 ∧ good (false, false) (Fin.cons x c) then
      H (finish (false, false) (Fin.cons x c))
        (fun j => beta ((Fin.cons x c : Row) j)) else 0) = _
  rw [Finset.sum_eq_single (0 : Fin 6)]
  · have hh := scanner_fibres 6 (false, false)
      (fun t q => H t (Fin.cons 0 q))
    convert hh using 1
    apply Finset.sum_congr rfl
    intro c _
    have hb : (fun j => beta ((Fin.cons 0 c : Row) j)) =
        Fin.cons 0 (fun j => beta (c j)) := Fin.comp_cons beta 0 c
    have ha : HardinA233175PairStrip.allowed (false, false) (0 : Fin 6) := by decide +kernel
    have hadv : HardinA233175PairStrip.advance (false, false) (0 : Fin 6) =
        (false, false) := by decide +kernel
    have hg : good (false, false) (Fin.cons 0 c) ↔ good (false, false) c := by
      change (HardinA233175PairStrip.allowed (false, false) 0 ∧
        good (HardinA233175PairStrip.advance (false, false) 0) c) ↔ good (false, false) c
      rw [hadv]
      simp only [ha, true_and]
    have hf : finish (false, false) (Fin.cons 0 c) = finish (false, false) c := by
      change finish (HardinA233175PairStrip.advance (false, false) 0) c = _
      rw [hadv]
    simp only [hg, hf, hb, eq_self, true_and]
  · intro x _ hx
    simp [hx]
  · simp

/-- The original literal count is an exact scanner-weighted sum on labelled pair rows. -/
theorem literal_pair_bridge (n : ℕ) :
    (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
      ∑ q : Fin 6 → Fin 3, if rowProper (Fin.cons 0 q) then
        rowWeight (false, false) q * pairV n (rowFinish (false, false) q) q else 0 := by
  rw [literal_colour_bridge]
  have h := first_fibres (fun t q =>
    if rowProper q then pairV n t (labelBoundary q) else 0)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro c _
    have hr : rowProper (fun j => beta (c j)) ↔ rowLegal c := by
      simp only [rowProper, rowLegal, colour_bond_iff]
    have hb : labelBoundary (fun j => beta (c j)) = pairs c := rfl
    simp only [hr, hb]
    by_cases h0 : c 0 = 0 <;> by_cases hg : good (false, false) c <;>
      by_cases hl : rowLegal c <;> simp [h0, hg, hl]
  · apply Finset.sum_congr rfl
    intro q _
    have hb : labelBoundary (Fin.cons 0 q) = q := rfl
    simp only [hb]
    split_ifs <;> simp_all

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer

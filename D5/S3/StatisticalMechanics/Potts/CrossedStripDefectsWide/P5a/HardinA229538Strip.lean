/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.vector_polynomial
   digest: The order-twenty recurrence for five-row one-defect canonical HDA colourings. -/

/-
admission_basis: open-problem-resolution (#32224; Proved)
escape_witness: labelled_scale uses the computed lower bound on the width-two cut; result uses labelled_scale and the one-defect vector_polynomial.
canonicalCount: proof_shape=bind-only; consumers=HardinA229538Strip.a
a: proof_shape=bind-only; consumers=HardinA229538Strip.result
residual: proof_shape=bind-only; consumers=HardinA229538Strip.transfer_count
transition_entry: proof_shape=bind-only; consumers=HardinA229538Strip.transfer_count
transfer_count: proof_shape=bind-only; consumers=HardinA229538Strip.result
labelled_scale: proof_shape=content; consumers=HardinA229538Strip.result, HardinA229641Strip.result
result: proof_shape=content; consumers=none (external open-problem-resolution #32224)
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538StripData
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538StripCertificate
import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Chromatic
import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Recurrence
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip

open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA233177Canonical (Canonical canonical_pattern_card)
open HardinA233178Chromatic (Column)
open HardinA233178Recurrence (columnEquiv)
open HardinA229538StripData
  (edges cost bondDefects_empty zero_cost_entry oneDefect transfer terminal transfer_readout)
open HardinA229538StripCertificate (coefficients538 vector_polynomial)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects defects literalCount lumped_count)

set_option maxHeartbeats 0
set_option maxRecDepth 100000


/-- Exact-defect five-row HDA arrays with canonical row-major colour names. -/
def canonicalCount (D n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 5 × Fin n → Fin 3 =>
    @Canonical (Fin 5 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 5 × Fin n → Fin 3 =>
    defects ∅ edges (List.ofFn fun j i => A (i, j)) = D ∧
    (@Canonical (Fin 5 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

def a (n : ℕ) : ℕ := canonicalCount 1 n

def residual (p : Column) (d : ℕ) : Column ⊕ Column :=
    if d = 0 then Sum.inr p else Sum.inl p

theorem transition_entry (p q : Column) (d : ℕ) (hd : d ≤ 1) (s : Column ⊕ Column) :
    (if cost p q ≤ d ∧ residual q (d - cost p q) = s then (1 : ℤ) else 0) =
      (if Sum.elim id id s = q then transfer (residual p d) s else 0) := by
  have zero := zero_cost_entry p q
  have cutoff : cost p q ≤ 1 ↔ cost p q = 0 ∨ cost p q = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one
  have hd' : d = 0 ∨ d = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hd
  rcases hd' with rfl | rfl <;> cases s with
  | inl s =>
    all_goals
      by_cases h₀ : cost p q = 0 <;> by_cases h₁ : cost p q = 1
      all_goals
        have hz := zero
        simp only [h₀, ite_true, ite_false] at hz
        by_cases hq : s = q
        · subst s
          simp [residual, transfer, oneDefect, cutoff, h₀, h₁, ← hz]
        · simp [residual, transfer, oneDefect, cutoff, h₀, h₁, ← hz, hq, Ne.symm hq]
  | inr s =>
    all_goals
      by_cases h₀ : cost p q = 0 <;> by_cases h₁ : cost p q = 1
      all_goals
        by_cases hq : s = q
        · subst s
          simp [residual, transfer, oneDefect, ← zero, cutoff, h₀, h₁]
        · simp [residual, transfer, oneDefect, ← zero, cutoff, h₀, h₁, hq, Ne.symm hq]

private theorem transfer_count (n : ℕ) :
    (literalCount (q := 3) ∅ edges 1 (n + 1) : ℤ) =
      dotProduct (Sum.elim (1 : Column → ℤ) 0) ((transfer ^ n).mulVec terminal) := by
  let C (p : Column) (r : Fin 5 → Fin 3) : ℕ := bondDefects edges (columnEquiv p) r
  have ctr (p q : Column) : C p (columnEquiv q) = cost p q := rfl
  apply lumped_count ∅ edges columnEquiv.symm C (fun _ d => d ≤ 1) residual transfer
    (Sum.elim (1 : Column → ℤ) 0) terminal 1
  · intro r t
    simp [C]
  · intro p d _
    by_cases hd : d = 0 <;> simp [residual, terminal, hd]
  · intro p d hd r _
    exact (Nat.sub_le _ _).trans hd
  · intro p d hd s
    rw [← columnEquiv.sum_comp]
    simp_rw [bondDefects_empty, Nat.add_zero, ctr, columnEquiv.symm_apply_apply,
      transition_entry p _ d hd]
    simp [Finset.sum_ite_eq']
  · intro r _
    exact Nat.sub_le _ _
  · intro s
    rw [← columnEquiv.sum_comp]
    simp_rw [bondDefects_empty, Nat.zero_le, Nat.sub_zero, true_and, columnEquiv.symm_apply_apply]
    cases s with
    | inl s =>
      simp [residual, Finset.sum_ite_eq', Finset.sum_ite_eq]
    | inr s => simp [residual]

theorem labelled_scale (D m : ℕ) (hm : 1 ≤ m) (hD : D < 3) :
    literalCount (q := 3) ∅ edges D (m + 1) = 6 * canonicalCount D (m + 1) := by
  classical
  let S : (Fin 5 × Fin (m + 1) → Fin 3) → Prop := fun A =>
    defects ∅ edges (List.ofFn fun j i => A (i, j)) = D
  have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
    intro e A
    change defects ∅ edges _ = D ↔ _
    rw [show (List.ofFn fun j i => (e ∘ A) (i, j)) =
      (List.ofFn fun j i => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
      DefectTransfer.relabel_defects]
  have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
    intro A h
    by_contra! he
    have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
    change defects ∅ edges _ = D at h
    rw [const] at h
    simp only [List.ofFn_const] at h
    rw [DefectTransfer.constant_defects] at h
    have positive : 3 ≤ edges.card := by decide +kernel
    simp only [Finset.card_empty, mul_zero, zero_add] at h
    have hx : m * edges.card = D := by simpa using h
    have hy : 3 ≤ m * edges.card := by simpa only [Nat.one_mul] using Nat.mul_le_mul hm positive
    exact (Nat.not_lt_of_ge (hx ▸ hy)) hD
  have orbit := @canonical_pattern_card (Fin 5 × Fin (m + 1)) inferInstance
    (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
  let e := Equiv.arrowCongr (Equiv.prodComm (Fin (m + 1)) (Fin 5)) (Equiv.refl (Fin 3))
  have card := Fintype.card_congr (e.subtypeEquiv (p := fun A =>
    defects ∅ edges (List.ofFn fun i j => A (i, j)) = D) (q := S) (fun _ => Iff.rfl))
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit card
  unfold literalCount
  convert card.trans orbit using 1
  apply congrArg (fun x : ℕ => 6 * x)
  unfold canonicalCount
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]

attribute [local irreducible] a

/-- Hardin's order-twenty recurrence, starting at width twenty-three. -/
theorem result (n : ℕ) :
    (a (n + 23) : ℤ) = 12 * (a (n + 22) : ℤ) + 26 * (a (n + 21) : ℤ) - 566 * (a (n + 20) : ℤ) -
      123 * (a (n + 19) : ℤ) + 8804 * (a (n + 18) : ℤ) - 4121 * (a (n + 17) : ℤ) -
      59620 * (a (n + 16) : ℤ) + 55115 * (a (n + 15) : ℤ) + 183692 * (a (n + 14) : ℤ) -
      256127 * (a (n + 13) : ℤ) - 211910 * (a (n + 12) : ℤ) + 498819 * (a (n + 11) : ℤ) -
      48036 * (a (n + 10) : ℤ) - 371692 * (a (n + 9) : ℤ) + 214008 * (a (n + 8) : ℤ) +
      43848 * (a (n + 7) : ℤ) - 64656 * (a (n + 6) : ℤ) + 8640 * (a (n + 5) : ℤ) +
      5184 * (a (n + 4) : ℤ) - 1296 * (a (n + 3) : ℤ) := by
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct (Sum.elim (1 : Column → ℤ) 0) ((transfer ^ m).mulVec terminal) =
        6 * (a (m + 1) : ℤ) := by
    rw [← transfer_count]
    have hscale : literalCount (q := 3) ∅ edges 1 (m + 1) = 6 * a (m + 1) := by
      simpa only [a] using labelled_scale 1 m hm (Nat.lt_succ_of_le (Nat.le_succ 1))
    rw [hscale]
    push_cast
    rfl
  have h := transfer_readout transfer terminal (Sum.elim (1 : Column → ℤ) 0)
    20 2 _ vector_polynomial n
  have mge (k : Fin 20) : 1 ≤ n + 2 + k.val :=
    Nat.le_add_right_of_le (Nat.le_add_left 1 (n + 1))
  have hn : 1 ≤ n + 2 + 20 := Nat.le_add_right_of_le (Nat.le_add_left 1 (n + 1))
  rw [bridge _ hn] at h
  simp_rw [fun k : Fin 20 => bridge (n + 2 + k.val) (mge k)] at h
  norm_num [coefficients538, Fin.sum_univ_succ, Nat.add_assoc] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip

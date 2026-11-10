/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256RowOne
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233256RowOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256RowOne.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256RowOne.finite_certificate
   digest: The literal one-row path count has recurrence six minus eight from width four. -/
/-
admission_basis: open-problem-resolution (#28883; Proved)
escape_witness: none
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic

/-! Transposition identifies the one-row array with a scanned path. -/
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233256RowOne
open HardinA233251TriangleStrip
open HardinA233175PairStrip (Seen good finish)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

def Legal {k : ℕ} (A : Fin 1 × Fin k → Fin 6) : Prop :=
  (∃ j : Fin k, j.val = 0 ∧ A (0, j) = 0) ∧
  (∀ (j : Fin k) (h : j.val + 1 < k), A (0, j) ≠ A (0, ⟨j.val + 1, h⟩) ∧
    (A (0, j)).val + (A (0, ⟨j.val + 1, h⟩)).val ≠ 5) ∧
  (∀ j : Fin k,
    ((A (0, j) = 2 ∨ A (0, j) = 3 ∨ A (0, j) = 4) →
      ∃ i, i < j ∧ A (0, i) = 1) ∧
    (A (0, j) = 3 → ∃ i, i < j ∧ A (0, i) = 2))
private instance instDecidableLegal {k : ℕ} (A : Fin 1 × Fin k → Fin 6) : Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def a (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 1 × Fin k → Fin 6 => Legal A)).card

attribute [local irreducible] a

private abbrev R : (Fin 1 → Fin 6) → Prop := fun _ => True
private def E (c d : Fin 1 → Fin 6) : Prop := c 0 ≠ d 0 ∧ (c 0).val + (d 0).val ≠ 5
private instance instDecidableE (c d : Fin 1 → Fin 6) : Decidable (E c d) :=
  inferInstanceAs (Decidable (_ ∧ _))
private abbrev P (c : Fin 1 → Fin 6) : Fin 3 := beta (c 0)
private def C (p : Fin 3) (c : Fin 1 → Fin 6) : Prop := p ≠ beta (c 0)
private instance instDecidableC (p : Fin 3) (c : Fin 1 → Fin 6) : Decidable (C p c) :=
  inferInstanceAs (Decidable (_ ≠ _))
private abbrev v := widthV R P C
private abbrev total := widthTotal R P
private def b (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 1 → Fin 6 => widthLegal R E A)).card

private theorem transpose_count (k : ℕ) : a k = b k := by
  classical
  let e : (Fin 1 × Fin k → Fin 6) ≃ (Fin k × Fin 1 → Fin 6) :=
    Equiv.arrowCongr (Equiv.prodComm _ _) (Equiv.refl _)
  have hf (A : Fin 1 × Fin k → Fin 6) : Legal A ↔ widthLegal R E (e A) := by
    have hn : widthNormal (false, false) (fun (i : Fin k) (j : Fin 1) => A (j, i)) ↔
        ∀ j : Fin k,
          ((A (0, j) = 2 ∨ A (0, j) = 3 ∨ A (0, j) = 4) →
            ∃ i, i < j ∧ A (0, i) = 1) ∧
          (A (0, j) = 3 → ∃ i, i < j ∧ A (0, i) = 2) := by
      change (∀ (i : Fin k) (j : Fin 1),
        ((A (j, i) = 2 ∨ A (j, i) = 3 ∨ A (j, i) = 4) →
          false = true ∨ ∃ r l, (r < i ∨ r = i ∧ l < j) ∧ A (l, r) = 1) ∧
        (A (j, i) = 3 →
          false = true ∨ ∃ r l, (r < i ∨ r = i ∧ l < j) ∧ A (l, r) = 2)) ↔ _
      simp only [Fin.forall_fin_one, Fin.exists_fin_one, lt_self_iff_false,
        and_false, or_false, Bool.false_eq_true, false_or]
    change Legal A ↔ widthLegal R E (fun p => A (p.2, p.1))
    simp only [Legal, widthLegal, R, E, implies_true, true_and, hn]
  have hc := Fintype.card_congr (Equiv.subtypeEquiv e hf)
  simpa only [a, b, Fintype.card_subtype] using hc

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  rw [transpose_count]
  exact width_counting_bridge R P C E (fun c d => colour_bond_iff (c 0) (d 0)) n

private def Valid (s : Seen) (p : Fin 3) : Prop :=
  (s.2 = true → s.1 = true) ∧ (s.1 = false → p = 0) ∧ (s.2 = false → p ≠ 2)
private instance instDecidableValid (s : Seen) (p : Fin 3) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable ((_ → _) ∧ (_ → _) ∧ (_ → _)))
private theorem valid_next : ∀ s p c, Valid s p → R c ∧ C p c ∧ good s c →
    Valid (finish s c) (P c) := by decide +kernel
private theorem initial_valid : ∀ c : Fin 1 → Fin 6,
    c 0 = 0 ∧ R c ∧ good (false, false) c → Valid (finish (false, false) c) (P c) := by
  decide +kernel
set_option maxRecDepth 100000 in
private theorem vector_certificate : ∀ s p, Valid s p →
    v 3 s p = 6 * v 2 s p - 8 * v 1 s p := by decide +kernel

private theorem vector_recurrence (n : ℕ) : ∀ s p, Valid s p →
    v (n + 3) s p = 6 * v (n + 2) s p - 8 * v (n + 1) s p := by
  induction n with
  | zero => exact vector_certificate
  | succ n ih =>
    intro s p hv
    change widthStep R P C (v (n + 3)) s p =
      6 * widthStep R P C (v (n + 2)) s p - 8 * widthStep R P C (v (n + 1)) s p
    unfold widthStep
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : R c ∧ C p c ∧ good s c
    · simp only [h, ite_true]
      exact ih _ _ (valid_next s p c hv h)
    · simp only [if_neg h, mul_zero, sub_self, zero_add]

private theorem recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = 6 * a (n + 3) - 8 * a (n + 2) := by
  rw [show n + 4 = (n + 3) + 1 by omega, counting_bridge,
    show n + 3 = (n + 2) + 1 by omega, counting_bridge,
    show n + 2 = (n + 1) + 1 by omega, counting_bridge]
  unfold total widthTotal
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c 0 = 0 ∧ R c ∧ good (false, false) c
  · simp only [h, ite_true]
    exact vector_recurrence n _ _ (initial_valid c h)
  · simp only [if_neg h, mul_zero, sub_self, zero_add]

theorem finite_certificate : a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 3 ∧ a 4 = 10 := by
  have h (n : ℕ) := counting_bridge n
  have h0 : total (v 0) = 1 := by decide +kernel
  have h1 : total (v 1) = 1 := by decide +kernel
  have h2 : total (v 2) = 3 := by decide +kernel
  have h3 : total (v 3) = 10 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast ((counting_bridge 0).trans h0)
  · exact_mod_cast ((counting_bridge 1).trans h1)
  · exact_mod_cast ((counting_bridge 2).trans h2)
  · exact_mod_cast ((counting_bridge 3).trans h3)

theorem result :
    (∀ k : ℕ, 4 ≤ k → (a k : ℤ) = 6 * a (k - 1) - 8 * a (k - 2)) ∧
    (a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 3 ∧ a 4 = 10) := by
  refine ⟨?_, finite_certificate⟩
  intro k hk
  have h := recurrence (k - 4)
  simpa only [show k - 4 + 4 = k by omega,
    show k - 4 + 3 = k - 1 by omega,
    show k - 4 + 2 = k - 2 by omega] using h

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233256RowOne

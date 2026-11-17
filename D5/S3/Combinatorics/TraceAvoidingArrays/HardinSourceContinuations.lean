/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.four_class_result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.four_class_certificate
   digest: Exact source boundary classes and universal literal continuations. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip

/-! The literal scanner supplies the source four-class continuation recursion. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations
open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip (widthV widthStep widthTotal widthLegal width_counting_bridge)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

private abbrev Row := Fin 4 → Fin 6
private abbrev Boundary := Fin 4 → Fin 3
private def rowOK (c : Row) : Prop := HardinThinGraphTransport.proper (fun j => beta (c j))
private def pairs (c : Row) : Boundary := fun j => beta (c j)
private def nextOK (p : Boundary) (c : Row) : Prop :=
  HardinThinGraphTransport.compatible true p (pairs c)
private instance (c : Row) : Decidable (rowOK c) := inferInstanceAs (Decidable (HardinThinGraphTransport.proper _))
private instance (p : Boundary) (c : Row) : Decidable (nextOK p c) :=
  inferInstanceAs (Decidable (HardinThinGraphTransport.compatible true _ _))

/-- A completed literal boundary has seen 1; an unseen 2 excludes its pair. -/
def admissible (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ HardinThinGraphTransport.proper p ∧ (s.2 = false → ∀ j, p j ≠ 2)
instance (s : Seen) (p : Boundary) : Decidable (admissible s p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ → ∀ _, _)))

/-- U,A,B,C, in that order, using the actual seen flag and equality pattern. -/
def sourceClass (s : Seen) (p : Boundary) : Fin 4 :=
  if s.2 = false then 0 else
  if p 0 = p 2 ∧ p 1 = p 3 then 1 else if p 0 = p 3 then 2 else 3

/-- Literal next-row counts, without division by a symmetry group. -/
def M : Fin 4 → Fin 4 → ℤ := ![![16,16,8,32], ![0,48,16,64], ![0,16,16,32], ![0,32,16,48]]
def r : Fin 4 → ℤ := ![4,0,2,4]
def sourceV : ℕ → Fin 4 → ℤ
  | 0, _ => 1
  | m+1, i => ∑ j, M i j * sourceV m j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem four_class_certificate :
    (∀ s p, admissible s p → ∀ c : Row,
      rowOK c ∧ nextOK p c ∧ good s c → admissible (finish s c) (pairs c)) ∧
    (∀ c : Row, c 0 = 0 ∧ rowOK c ∧ good (false,false) c →
      admissible (finish (false,false) c) (pairs c)) ∧
    (∀ s p, admissible s p → ∀ j : Fin 4,
      (∑ c : Row, if rowOK c ∧ nextOK p c ∧ good s c ∧
        sourceClass (finish s c) (pairs c) = j then (1:ℤ) else 0) = M (sourceClass s p) j) ∧
    (∀ j : Fin 4,
      (∑ c : Row, if c 0 = 0 ∧ rowOK c ∧ good (false,false) c ∧
        sourceClass (finish (false,false) c) (pairs c) = j then (1:ℤ) else 0) = r j) := by
  decide +kernel

private theorem class_sum {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    (cl : α → Fin 4) (w : Fin 4 → ℤ) :
    (∑ a, if P a then w (cl a) else 0) =
      ∑ j : Fin 4, (∑ a, if P a ∧ cl a = j then (1:ℤ) else 0) * w j := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a
  · simp [h]
  · simp [h]

private theorem continuation_classes (m : ℕ) (s : Seen) (p : Boundary)
    (h : admissible s p) :
    widthV rowOK pairs nextOK m s p = sourceV m (sourceClass s p) := by
  induction m generalizing s p with
  | zero => rfl
  | succ m ih =>
    rw [widthV, widthStep]
    calc
      _ = ∑ c : Row, if rowOK c ∧ nextOK p c ∧ good s c then
          sourceV m (sourceClass (finish s c) (pairs c)) else 0 := by
        apply Finset.sum_congr rfl
        intro c _
        split_ifs with hc
        · exact ih _ _ (four_class_certificate.1 s p h c hc)
        · rfl
      _ = _ := by
        rw [class_sum, sourceV]
        apply Finset.sum_congr rfl
        intro j _
        simp only [and_assoc]
        rw [four_class_certificate.2.2.1 s p h j]

/-- The exact source classes govern every continuation length and every literal height. -/
theorem four_class_result (m : ℕ) :
    (∀ s p, admissible s p →
      widthV rowOK pairs nextOK m s p = sourceV m (sourceClass s p)) ∧
    (Nat.card (HardinThinGraphTransport.literalStrip true m 3) : ℤ) =
      ∑ j : Fin 4, r j * sourceV m j := by
  refine ⟨continuation_classes m, ?_⟩
  have bridge : (Nat.card (HardinThinGraphTransport.literalStrip true m 3) : ℤ) =
      widthTotal rowOK pairs (widthV rowOK pairs nextOK m) := by
    classical
    unfold HardinThinGraphTransport.literalStrip
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact width_counting_bridge rowOK pairs nextOK
      (fun c d => nextOK (pairs c) d) (fun _ _ => Iff.rfl) m
  rw [bridge, widthTotal]
  calc
    _ = ∑ c : Row, if c 0 = 0 ∧ rowOK c ∧ good (false,false) c then
        sourceV m (sourceClass (finish (false,false) c) (pairs c)) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      split_ifs with hc
      · exact continuation_classes m _ _ (four_class_certificate.2.1 c hc)
      · rfl
    _ = _ := by
      rw [class_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [and_assoc]
      rw [four_class_certificate.2.2.2 j]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations

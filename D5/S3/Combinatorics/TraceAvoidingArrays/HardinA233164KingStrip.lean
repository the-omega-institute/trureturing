/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.finite_certificate,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.saturated_certificate
   digest: Literal normalized four-column eight-colour king-strip counts and their series. -/

/-
admission_basis: open-problem-resolution (#28747).
The independent literal count is the target; the labelled chromatic polynomial
is already supplied by Chang and Shrock, DOI 10.1103/PhysRevE.62.4650.
No chromatic-polynomial novelty is asserted.
proof_shape: bind-only for the finite certificates, boundary and scanner bridges,
seed congruence and linearity, zero count and algebraic consequences.
The finite certificates are premises of the all-height continuation induction.
The only public result collects the full literal-count settlement event.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
The cell domain has four columns. Horizontal, vertical and both diagonal
bonds exclude equal colours and colours summing to seven. Normalization is
strict row-major precedence, with no surjectivity or orbit divisor.
-/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
  (Seen beta colour_bond_iff good finish widthNormal widthLegal widthStep widthV
    widthTotal width_counting_bridge)

private abbrev Row := Fin 4 → Fin 8
private abbrev Boundary := Fin 4 → Fin 4

private def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 3, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 7

private def bonds (c d : Row) : Prop :=
  (∀ j, c j ≠ d j ∧ (c j).val + (d j).val ≠ 7) ∧
    (∀ j : Fin 3,
      (c j.castSucc ≠ d j.succ ∧ (c j.castSucc).val + (d j.succ).val ≠ 7) ∧
      (c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 7))

private def pairs (c : Row) : Boundary := fun j => beta (c j)
private def compatible (p : Boundary) (c : Row) : Prop :=
  (∀ j, p j ≠ beta (c j)) ∧
    (∀ j : Fin 3, p j.castSucc ≠ beta (c j.succ) ∧ p j.succ ≠ beta (c j.castSucc))

private instance (c : Row) : Decidable (rowLegal c) := inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable ((∀ _, _ ∧ _) ∧ (∀ _, (_ ∧ _) ∧ (_ ∧ _))))
private instance (p : Boundary) (c : Row) : Decidable (compatible p c) :=
  inferInstanceAs (Decidable ((∀ _, _) ∧ (∀ _, _ ∧ _)))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private def Normal {n : ℕ} (A : Fin n × Fin 4 → Fin 8) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4 ∨ A p = 5 ∨ A p = 6) →
      ∃ q, 4*q.1.val + q.2.val < 4*p.1.val + p.2.val ∧ A q = 1) ∧
    ((A p = 3 ∨ A p = 4 ∨ A p = 5) →
      ∃ q, 4*q.1.val + q.2.val < 4*p.1.val + p.2.val ∧ A q = 2) ∧
    (A p = 4 → ∃ q, 4*q.1.val + q.2.val < 4*p.1.val + p.2.val ∧ A q = 3)

private def Legal {n : ℕ} (A : Fin n × Fin 4 → Fin 8) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
  (∀ i, rowLegal (fun j => A (i,j))) ∧
  (∀ (i : Fin n) (h : i.val+1<n), bonds (fun j => A (i,j))
    (fun j => A (⟨i.val+1,h⟩,j))) ∧ Normal A

private instance {n : ℕ} (A : Fin n × Fin 4 → Fin 8) : Decidable (Normal A) :=
  inferInstanceAs (Decidable (∀ _, (_ → _) ∧ (_ → _) ∧ (_ → _)))
private instance {n : ℕ} (A : Fin n × Fin 4 → Fin 8) : Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Literal array cardinality, with zero constant coefficient. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 4 → Fin 8 => Legal A)).card

private theorem normal_iff {n : ℕ} (A : Fin n × Fin 4 → Fin 8) :
    widthNormal (false,false,false) (fun i j => A (i,j)) ↔ Normal A := by
  have he (i : Fin n) (j : Fin 4) (d : Fin 8) :
      (∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r,k) = d) ↔
      ∃ q, 4*q.1.val+q.2.val < 4*i.val+j.val ∧ A q = d := by
    constructor
    · rintro ⟨r,k,h,hc⟩
      refine ⟨(r,k), ?_, hc⟩
      change 4*r.val+k.val < 4*i.val+j.val
      rcases h with h | ⟨h,hk⟩ <;> simp_all only [Fin.lt_def] <;> omega
    · rintro ⟨⟨r,k⟩,h,hc⟩
      dsimp only [Prod.fst, Prod.snd] at h
      refine ⟨r,k,?_,hc⟩
      by_cases hr : r < i
      · exact Or.inl hr
      · right
        have eq : r = i := Fin.ext (by simp only [Fin.lt_def] at hr; omega)
        exact ⟨eq, by simp only [Fin.lt_def]; omega⟩
  change (∀ i j, (((A (i,j)=2 ∨ A (i,j)=3 ∨ A (i,j)=4 ∨ A (i,j)=5 ∨ A (i,j)=6) →
    (false : Bool)=true ∨ ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r,k)=1) ∧
    ((A (i,j)=3 ∨ A (i,j)=4 ∨ A (i,j)=5) →
      (false : Bool)=true ∨ ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r,k)=2) ∧
    (A (i,j)=4 → (false : Bool)=true ∨ ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r,k)=3))) ↔ _
  simp only [Bool.false_eq_true, false_or, he, Normal, Prod.forall]

private abbrev v := widthV rowLegal pairs compatible
private abbrev total := widthTotal rowLegal pairs
private abbrev step := widthStep rowLegal pairs compatible

private theorem counting_bridge (n : ℕ) : (a (n+1) : ℤ) = total (v n) := by
  have hc : Finset.univ.filter (fun A : Fin (n+1) × Fin 4 → Fin 8 => Legal A) =
      Finset.univ.filter (fun A : Fin (n+1) × Fin 4 → Fin 8 => widthLegal rowLegal bonds A) := by
    ext A
    simp [widthLegal, Legal, normal_iff]
  rw [a, hc]
  exact width_counting_bridge rowLegal pairs compatible bonds bonds_iff n

private def saturated : Seen := (true,true,true)
private def proper (p : Boundary) : Prop :=
  (∀ j : Fin 3, p j.castSucc ≠ p j.succ) ∧ p 0 ≠ p 3
private instance (p : Boundary) : Decidable (proper p) :=
  inferInstanceAs (Decidable (_ ∧ _))
private def kind (p : Boundary) : Bool := decide (p 0 = p 2 ∧ p 1 = p 3)
private def rate (b : Bool) : ℤ := if b then 32 else 16
private def initial (c : Row) : Prop := c 0 = 0 ∧ rowLegal c ∧ good (false,false,false) c
private instance (c : Row) : Decidable (initial c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem saturated_certificate : ∀ p : Boundary, proper p →
    (∀ c : Row, rowLegal c ∧ compatible p c ∧ good saturated c →
      finish saturated c = saturated ∧ proper (pairs c) ∧ kind (pairs c) = kind p) ∧
    step (fun _ _ => 1) saturated p = rate (kind p) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem finite_certificate :
    (∀ c : Row, initial c → ∀ d : Row,
      rowLegal d ∧ compatible (pairs c) d ∧ good (finish (false,false,false) c) d →
      finish (finish (false,false,false) c) d = saturated ∧ proper (pairs d)) ∧
    total (fun _ _ => 1) = 11 ∧
    (∀ b : Bool, total (step (fun _ p => if kind p = b then 1 else 0)) =
      if b then 16 else 48) := by
  decide +kernel



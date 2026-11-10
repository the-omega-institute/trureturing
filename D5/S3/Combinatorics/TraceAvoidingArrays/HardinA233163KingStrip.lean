/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.finite_certificate,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.saturated_certificate
   digest: The whole generating series of literal normalized eight-colour king strips. -/

/-
admission_basis: open-problem-resolution (#28719)
escape_witness: the live all-length proper-boundary invariant in continuation.
The literal source count and its whole generating function are the external target.
proof_shape: content for continuation, count_formula, recurrence,
product_identity and result: inlining retains induction at variable length,
using the finite preservation and eigenweight certificate. The imported
width-generic counting bridge does not supply this invariant.
proof_shape: bind-only for bonds_iff, normal_iff, counting_bridge,
saturated_certificate, finite_certificate, seed_congr, seed_linear,
initial_counts and zero_count. Fixed initial counts reduce the continuation
induction at lengths zero and one; they need no all-length inference.
These shape judgements assert no independent literature novelty.
Consumed helpers: bonds_iff and normal_iff feed counting_bridge;
saturated_certificate feeds continuation; finite_certificate feeds seed_congr,
count_formula and initial_counts; continuation, seed_congr and seed_linear
feed count_formula; counting_bridge and count_formula feed initial_counts
and recurrence; initial_counts, recurrence and zero_count feed product_identity;
product_identity feeds the external open-problem-resolution result.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
The cell domain has three columns. Horizontal, vertical and both diagonal
bonds exclude equal colours and colours summing to seven. Normalization is
strict row-major precedence, with no surjectivity or orbit divisor.
-/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
  (Seen beta colour_bond_iff good finish widthNormal widthLegal widthStep widthV
    widthTotal width_counting_bridge)

private abbrev Row := Fin 3 → Fin 8
private abbrev Boundary := Fin 3 → Fin 4

private def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 2, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 7

private def bonds (c d : Row) : Prop :=
  (∀ j, c j ≠ d j ∧ (c j).val + (d j).val ≠ 7) ∧
    (∀ j : Fin 2,
      (c j.castSucc ≠ d j.succ ∧ (c j.castSucc).val + (d j.succ).val ≠ 7) ∧
      (c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 7))

private def pairs (c : Row) : Boundary := fun j => beta (c j)
private def compatible (p : Boundary) (c : Row) : Prop :=
  (∀ j, p j ≠ beta (c j)) ∧
    (∀ j : Fin 2, p j.castSucc ≠ beta (c j.succ) ∧ p j.succ ≠ beta (c j.castSucc))

private instance (c : Row) : Decidable (rowLegal c) := inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable ((∀ _, _ ∧ _) ∧ (∀ _, (_ ∧ _) ∧ (_ ∧ _))))
private instance (p : Boundary) (c : Row) : Decidable (compatible p c) :=
  inferInstanceAs (Decidable ((∀ _, _) ∧ (∀ _, _ ∧ _)))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private def Normal {n : ℕ} (A : Fin n × Fin 3 → Fin 8) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4 ∨ A p = 5 ∨ A p = 6) →
      ∃ q, 3*q.1.val + q.2.val < 3*p.1.val + p.2.val ∧ A q = 1) ∧
    ((A p = 3 ∨ A p = 4 ∨ A p = 5) →
      ∃ q, 3*q.1.val + q.2.val < 3*p.1.val + p.2.val ∧ A q = 2) ∧
    (A p = 4 → ∃ q, 3*q.1.val + q.2.val < 3*p.1.val + p.2.val ∧ A q = 3)

private def Legal {n : ℕ} (A : Fin n × Fin 3 → Fin 8) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
  (∀ i, rowLegal (fun j => A (i,j))) ∧
  (∀ (i : Fin n) (h : i.val+1<n), bonds (fun j => A (i,j))
    (fun j => A (⟨i.val+1,h⟩,j))) ∧ Normal A

private instance {n : ℕ} (A : Fin n × Fin 3 → Fin 8) : Decidable (Normal A) :=
  inferInstanceAs (Decidable (∀ _, (_ → _) ∧ (_ → _) ∧ (_ → _)))
private instance {n : ℕ} (A : Fin n × Fin 3 → Fin 8) : Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Literal array cardinality, with zero constant coefficient. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 3 → Fin 8 => Legal A)).card

private theorem normal_iff {n : ℕ} (A : Fin n × Fin 3 → Fin 8) :
    widthNormal (false,false,false) (fun i j => A (i,j)) ↔ Normal A := by
  have he (i : Fin n) (j : Fin 3) (d : Fin 8) :
      (∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r,k) = d) ↔
      ∃ q, 3*q.1.val+q.2.val < 3*i.val+j.val ∧ A q = d := by
    constructor
    · rintro ⟨r,k,h,hc⟩
      refine ⟨(r,k), ?_, hc⟩
      change 3*r.val+k.val < 3*i.val+j.val
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
  have hc : Finset.univ.filter (fun A : Fin (n+1) × Fin 3 → Fin 8 => Legal A) =
      Finset.univ.filter (fun A : Fin (n+1) × Fin 3 → Fin 8 => widthLegal rowLegal bonds A) := by
    ext A
    simp [widthLegal, Legal, normal_iff]
  rw [a, hc]
  exact width_counting_bridge rowLegal pairs compatible bonds bonds_iff n

private def saturated : Seen := (true,true,true)
private def proper (p : Boundary) : Prop := p 0 ≠ p 1 ∧ p 1 ≠ p 2
private instance (p : Boundary) : Decidable (proper p) := inferInstanceAs (Decidable (_ ∧ _))
private def kind (p : Boundary) : Bool := decide (p 0 = p 2)
private def rate (b : Bool) : ℤ := if b then 16 else 8
private def initial (c : Row) : Prop := c 0 = 0 ∧ rowLegal c ∧ good (false,false,false) c
private instance (c : Row) : Decidable (initial c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the 64 pair boundaries and their 512 colour rows.
private theorem saturated_certificate : ∀ p : Boundary, proper p →
    (∀ c : Row, rowLegal c ∧ compatible p c ∧ good saturated c →
      finish saturated c = saturated ∧ proper (pairs c) ∧ kind (pairs c) = kind p) ∧
    step (fun _ _ => 1) saturated p = rate (kind p) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates first rows and their one-row continuations.
private theorem finite_certificate :
    (∀ c : Row, initial c → ∀ d : Row,
      rowLegal d ∧ compatible (pairs c) d ∧ good (finish (false,false,false) c) d →
      finish (finish (false,false,false) c) d = saturated ∧ proper (pairs d)) ∧
    total (fun _ _ => 1) = 3 ∧
    (∀ b : Bool, total (step (fun _ p => if kind p = b then 1 else 0)) = 4) := by
  decide +kernel

private theorem continuation (n : ℕ) (p : Boundary) (hp : proper p) :
    v n saturated p = rate (kind p)^n := by
  induction n generalizing p with
  | zero => simp [v, widthV]
  | succ n ih =>
    change step (v n) saturated p = _
    have he : ∀ c : Row,
        (if rowLegal c ∧ compatible p c ∧ good saturated c then
          v n (finish saturated c) (pairs c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good saturated c then (1 : ℤ) else 0) *
          rate (kind p)^n := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good saturated c
      · have hh := (saturated_certificate p hp).1 c hc
        rw [ite_eq_left hc, ite_eq_left hc, hh.1, ih (pairs c) hh.2.1, hh.2.2, one_mul]
      · simp [hc]
    change (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good saturated c then
      v n (finish saturated c) (pairs c) else 0) = _
    simp_rw [he]
    rw [← Finset.sum_mul]
    change step (fun _ _ => 1) saturated p * rate (kind p)^n = _
    rw [(saturated_certificate p hp).2, pow_succ']

private theorem seed_congr (f g : Seen → Boundary → ℤ)
    (he : ∀ p, proper p → f saturated p = g saturated p) :
    total (step f) = total (step g) := by
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : initial c
  · change (if initial c then step f (finish (false,false,false) c) (pairs c) else 0) =
      (if initial c then step g (finish (false,false,false) c) (pairs c) else 0)
    rw [ite_eq_left hc, ite_eq_left hc]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : rowLegal d ∧ compatible (pairs c) d ∧ good (finish (false,false,false) c) d
    · have hh := finite_certificate.1 c hc d hd
      simp only [ite_eq_left hd, hh.1]
      exact he (pairs d) hh.2
    · simp only [ite_eq_right hd]
  · change (if initial c then _ else 0) = (if initial c then _ else 0)
    simp only [ite_eq_right hc]

private theorem seed_linear (f g : Seen → Boundary → ℤ) (x y : ℤ) :
    total (step (fun s p => x*f s p + y*g s p)) = x*total (step f) + y*total (step g) := by
  have hi (P : Prop) [Decidable P] (a b : ℤ) :
      (if P then x*a+y*b else 0) = x*(if P then a else 0)+y*(if P then b else 0) := by
    split_ifs <;> ring
  have hs : step (fun s p => x*f s p+y*g s p) =
      fun s p => x*step f s p+y*step g s p := by
    funext s p
    unfold step widthStep
    simp only [hi, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hs]
  unfold total widthTotal
  simp only [hi, Finset.sum_add_distrib, Finset.mul_sum]

private theorem count_formula (n : ℕ) : (a (n+2) : ℤ) = 4*16^n+4*8^n := by
  rw [show n+2=(n+1)+1 by omega, counting_bridge]
  change total (step (v n)) = _
  rw [seed_congr (v n)
    (fun _ p => 16^n*(if kind p = true then 1 else 0)+8^n*(if kind p = false then 1 else 0))
    (by
      intro p hp
      rw [continuation n p hp]
      cases hk : kind p <;> simp [rate])]
  rw [seed_linear]
  rw [finite_certificate.2.2 true, finite_certificate.2.2 false]
  ring

private theorem initial_counts : a 1 = 3 ∧ a 2 = 8 ∧ a 3 = 96 := by
  have h1 := counting_bridge 0
  change (a 1 : ℤ) = total (fun _ _ => 1) at h1
  rw [finite_certificate.2.1] at h1
  have h2 : (a 2 : ℤ) = 8 := (count_formula 0).trans (by norm_num)
  have h3 : (a 3 : ℤ) = 96 := (count_formula 1).trans (by norm_num)
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

private theorem recurrence (n : ℕ) :
    (a (n+4) : ℤ) = 24*a (n+3)-128*a (n+2) := by
  rw [show n+4=(n+2)+2 by omega, count_formula,
    show n+3=(n+1)+2 by omega, count_formula, count_formula]
  simp only [pow_succ]
  ring

private theorem zero_count : a 0 = 0 := by simp [a, Legal]

open PowerSeries in
private theorem product_identity :
    (1-8*X)*(1-16*X)*(PowerSeries.mk fun n => (a n : ℚ)) =
      X*(3-64*X+288*X^2) := by
  let F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
  have hp : (1-8*X)*(1-16*X)*F = F-24*(F*X^1)+128*(F*X^2) := by ring
  have hr : (X*(3-64*X+288*X^2) : PowerSeries ℚ) = 3*X-64*X^2+288*X^3 := by ring
  change (1-8*X)*(1-16*X)*F = _
  rw [hp,hr]
  ext n
  simp only [map_add,map_sub,coeff_ofNat_mul,coeff_mul_X_pow',coeff_X,coeff_X_pow,F,coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega)]
    have hh : (a (n-4+4) : ℚ) = 24*a (n-4+3)-128*a (n-4+2) := by
      exact_mod_cast recurrence (n-4)
    rw [show n-4+4=n by omega, show n-4+3=n-1 by omega,
      show n-4+2=n-2 by omega] at hh
    linarith
  · interval_cases n <;> norm_num [zero_count,initial_counts.1,
      initial_counts.2.1,initial_counts.2.2]

open PowerSeries in
theorem result :
    (PowerSeries.mk fun n => (a n : ℚ)) =
      X*(3-64*X+288*X^2)*((1-8*X)*(1-16*X))⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp :
    constantCoeff ((1-8*X)*(1-16*X) : PowerSeries ℚ) ≠ 0)).2
  rw [mul_comm]
  exact product_identity

#print axioms result
end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip

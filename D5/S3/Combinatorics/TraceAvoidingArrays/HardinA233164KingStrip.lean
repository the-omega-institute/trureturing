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
proof_shape: content for continuation, count_formula, recurrence, closed_formula,
product_identity and result: live variable-height induction remains after inlining.
The other nine theorems are consumed bind-only helpers, including both finite
certificates; their computations are not claimed as novel data.
Problems/hardin233164.md gives the per-declaration judgements and live consumers.
The numeric-reduction premises remain finite_certificate and saturated_certificate.
The only public result collects the full literal-count settlement event.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FinCases

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
  intro p
  fin_cases p <;> decide +kernel

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

private theorem count_formula (n : ℕ) : (a (n+2) : ℤ) = 16*32^n+48*16^n := by
  rw [show n+2=(n+1)+1 by omega, counting_bridge]
  change total (step (v n)) = _
  rw [seed_congr (v n)
    (fun _ p => 32^n*(if kind p = true then 1 else 0)+16^n*(if kind p = false then 1 else 0))
    (by
      intro p hp
      rw [continuation n p hp]
      cases hk : kind p <;> simp [rate])]
  rw [seed_linear]
  rw [finite_certificate.2.2 true, finite_certificate.2.2 false]
  norm_num
  ring

private theorem initial_counts : a 1 = 11 ∧ a 2 = 64 ∧ a 3 = 1280 := by
  have h1 := counting_bridge 0
  change (a 1 : ℤ) = total (fun _ _ => 1) at h1
  rw [finite_certificate.2.1] at h1
  have h2 : (a 2 : ℤ) = 64 := (count_formula 0).trans (by norm_num)
  have h3 : (a 3 : ℤ) = 1280 := (count_formula 1).trans (by norm_num)
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

private theorem recurrence (n : ℕ) :
    (a (n+4) : ℤ) = 48*a (n+3)-512*a (n+2) := by
  rw [show n+4=(n+2)+2 by omega, count_formula,
    show n+3=(n+1)+2 by omega, count_formula, count_formula]
  simp only [pow_succ]
  ring

private theorem closed_formula (n : ℕ) :
    a (n+2) = 4^(2*(n+2)-3)*(2^(n+2)+12) := by
  have h : a (n+2) = 16*32^n+48*16^n := by exact_mod_cast count_formula n
  rw [h, show 2*(n+2)-3 = 2*n+1 by omega, pow_succ, pow_mul, pow_add]
  norm_num
  have hp : (32:ℕ)^n = 16^n*2^n := by rw [← mul_pow]; norm_num
  rw [hp]
  ring

private theorem zero_count : a 0 = 0 := by simp [a, Legal]

open PowerSeries in
private theorem product_identity :
    (1-16*X)*(1-32*X)*(PowerSeries.mk fun n => (a n : ℚ)) =
      X*(11-464*X+3840*X^2) := by
  let F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
  have hp : (1-16*X)*(1-32*X)*F = F-48*(F*X^1)+512*(F*X^2) := by ring
  have hr : (X*(11-464*X+3840*X^2) : PowerSeries ℚ) = 11*X-464*X^2+3840*X^3 := by ring
  change (1-16*X)*(1-32*X)*F = _
  rw [hp,hr]
  ext n
  simp only [map_add,map_sub,coeff_ofNat_mul,coeff_mul_X_pow',coeff_X,coeff_X_pow,F,coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega)]
    have hh : (a (n-4+4) : ℚ) = 48*a (n-4+3)-512*a (n-4+2) := by
      exact_mod_cast recurrence (n-4)
    rw [show n-4+4=n by omega, show n-4+3=n-1 by omega,
      show n-4+2=n-2 by omega] at hh
    linarith
  · interval_cases n <;> norm_num [zero_count,initial_counts.1,
      initial_counts.2.1,initial_counts.2.2]

open PowerSeries in
/-- The complete literal-count event, including every positive-height formula. -/
theorem result :
    a 1 = 11 ∧ a 2 = 64 ∧ a 3 = 1280 ∧
    (∀ n : ℕ, 1 < n → a n = 4^(2*n-3)*(2^n+12)) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 48*a (n-1)-512*a (n-2)) ∧
    (PowerSeries.mk fun n => (a n : ℚ)) =
      X*(11-464*X+3840*X^2)*((1-16*X)*(1-32*X))⁻¹ := by
  refine ⟨initial_counts.1, initial_counts.2.1, initial_counts.2.2, ?_, ?_, ?_⟩
  · intro n hn
    simpa only [show n-2+2=n by omega] using closed_formula (n-2)
  · intro n hn
    simpa only [show n-4+4=n by omega, show n-4+3=n-1 by omega,
      show n-4+2=n-2 by omega] using recurrence (n-4)
  · apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp :
      constantCoeff ((1-16*X)*(1-32*X) : PowerSeries ℚ) ≠ 0)).2
    rw [mul_comm]
    exact product_identity

#print axioms result
end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip

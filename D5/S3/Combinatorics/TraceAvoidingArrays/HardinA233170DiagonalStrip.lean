/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.finite_certificate
   digest: The full generating series for literal normalized four-column six-colour arrays. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
Horizontal and both diagonal bonds exclude equal and complementary colours.
The count includes every literal array satisfying row-major normalization;
there is no orbit quotient, vertical constraint or wraparound constraint.
The finite continuation certificate feeds induction for all continuation lengths.
-/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233170DiagonalStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip (Seen good finish)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip (widthNormal widthLegal widthStep widthV widthTotal
  width_counting_bridge colour_bond_iff)
open _root_.D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

private abbrev Row := Fin 4 → Fin 6
private abbrev Boundary := Fin 4 → Fin 3

private def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 3, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5

private def bonds (c d : Row) : Prop :=
  ∀ j : Fin 3,
    (c j.castSucc ≠ d j.succ ∧ (c j.castSucc).val + (d j.succ).val ≠ 5) ∧
    (c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5)

private def pairs (c : Row) : Boundary := fun j => beta (c j)
private def compatible (p : Boundary) (c : Row) : Prop :=
  ∀ j : Fin 3, p j.castSucc ≠ beta (c j.succ) ∧ p j.succ ≠ beta (c j.castSucc)
private instance (c : Row) : Decidable (rowLegal c) := inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance (c d : Row) : Decidable (bonds c d) := inferInstanceAs (Decidable (∀ _, (_ ∧ _) ∧ (_ ∧ _)))
private instance (p : Boundary) (c : Row) : Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _ ∧ _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private def Normal {n : ℕ} (A : Fin n × Fin 4 → Fin 6) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4) →
      ∃ q, 4*q.1.val + q.2.val < 4*p.1.val + p.2.val ∧ A q = 1) ∧
    (A p = 3 → ∃ q, 4*q.1.val + q.2.val < 4*p.1.val + p.2.val ∧ A q = 2)

private def Legal {n : ℕ} (A : Fin n × Fin 4 → Fin 6) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
  (∀ i, rowLegal (fun j => A (i,j))) ∧
  (∀ (i : Fin n) (h : i.val+1<n), bonds (fun j => A (i,j))
    (fun j => A (⟨i.val+1,h⟩,j))) ∧ Normal A
private instance {n : ℕ} (A : Fin n × Fin 4 → Fin 6) : Decidable (Normal A) :=
  inferInstanceAs (Decidable (∀ _, (_ → _) ∧ (_ → _)))
private instance {n : ℕ} (A : Fin n × Fin 4 → Fin 6) : Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun A : Fin n × Fin 4 → Fin 6 => Legal A)).card

private theorem normal_iff {n : ℕ} (A : Fin n × Fin 4 → Fin 6) :
    widthNormal (false,false) (fun i j => A (i,j)) ↔ Normal A := by
  have he (i : Fin n) (j : Fin 4) (d : Fin 6) :
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
  change (∀ i j, (((A (i,j)=2 ∨ A (i,j)=3 ∨ A (i,j)=4) →
    (false : Bool)=true ∨ ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r,k)=1) ∧
    (A (i,j)=3 → (false : Bool)=true ∨ ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r,k)=2))) ↔ _
  simp only [Bool.false_eq_true, false_or, he, Normal, Prod.forall]

private abbrev v := widthV rowLegal pairs compatible
private abbrev total := widthTotal rowLegal pairs

private theorem counting_bridge (n : ℕ) : (a (n+1) : ℤ) = total (v n) := by
  have hc : Finset.univ.filter (fun A : Fin (n+1) × Fin 4 → Fin 6 => Legal A) =
      Finset.univ.filter (fun A : Fin (n+1) × Fin 4 → Fin 6 => widthLegal rowLegal bonds A) := by
    ext A
    simp [widthLegal, Legal, normal_iff]
  rw [a, hc]
  exact width_counting_bridge rowLegal pairs compatible bonds bonds_iff n

private def Valid (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ (∀ j : Fin 3, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)
private instance (s : Seen) (p : Boundary) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _, _) ∧ (_ → ∀ _, _)))

private def weight1 (s : Seen) (p : Boundary) : ℤ :=
  if s.2 then
    if p 0 = p 2 ∧ p 1 = p 3 then 128 else if p 0 = p 3 then 64 else 96
  else 72

private def weight2 (s : Seen) (p : Boundary) : ℤ :=
  if s.2 then
    if p 0 = p 2 ∧ p 1 = p 3 then 13312 else if p 0 = p 3 then 6144 else 9728
  else 6784

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finite_certificate :
    (∀ s p, Valid s p → ∀ c : Row,
      rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (pairs c)) ∧
    (∀ c : Row, c 0 = 0 ∧ rowLegal c ∧ good (false,false) c →
      Valid (finish (false,false) c) (pairs c)) ∧
    (∀ s p, Valid s p →
      widthStep rowLegal pairs compatible (fun _ _ => 1) s p = weight1 s p ∧
      widthStep rowLegal pairs compatible weight1 s p = weight2 s p ∧
      widthStep rowLegal pairs compatible weight2 s p =
        128*weight2 s p-2816*weight1 s p+16384) ∧
    total (fun _ _ => 1) = 10 ∧ total weight1 = 800 ∧ total weight2 = 78336 := by
  decide +kernel


private theorem step_congr (f g : Seen → Boundary → ℤ) (s : Seen) (p : Boundary)
    (h : Valid s p) (he : ∀ s p, Valid s p → f s p = g s p) :
    widthStep rowLegal pairs compatible f s p = widthStep rowLegal pairs compatible g s p := by
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
  · simp only [ite_eq_left hc]
    exact he _ _ (finite_certificate.1 s p h c hc)
  · simp only [ite_eq_right hc]

private theorem total_congr (f g : Seen → Boundary → ℤ)
    (he : ∀ s p, Valid s p → f s p = g s p) : total f = total g := by
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false,false) c
  · simp only [ite_eq_left hc]
    exact he _ _ (finite_certificate.2.1 c hc)
  · simp only [ite_eq_right hc]

private theorem v_one (s : Seen) (p : Boundary) (h : Valid s p) : v 1 s p = weight1 s p :=
  (finite_certificate.2.2.1 s p h).1

private theorem v_two (s : Seen) (p : Boundary) (h : Valid s p) : v 2 s p = weight2 s p := by
  change widthStep rowLegal pairs compatible (v 1) s p = _
  rw [step_congr (v 1) weight1 s p h v_one]
  exact (finite_certificate.2.2.1 s p h).2.1

private theorem v_three (s : Seen) (p : Boundary) (h : Valid s p) :
    v 3 s p = 128*weight2 s p-2816*weight1 s p+16384 := by
  change widthStep rowLegal pairs compatible (v 2) s p = _
  rw [step_congr (v 2) weight2 s p h v_two]
  exact (finite_certificate.2.2.1 s p h).2.2

private theorem ite_linear (P : Prop) [Decidable P] (x y z : ℤ) :
    (if P then 128*x-2816*y+16384*z else 0) =
      128*(if P then x else 0)-2816*(if P then y else 0)+16384*(if P then z else 0) := by
  split_ifs <;> ring

private theorem continuation_recurrence (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v (n+3) s p = 128*v (n+2) s p-2816*v (n+1) s p+16384*v n s p := by
  induction n generalizing s p with
  | zero =>
    change v 3 s p = 128*v 2 s p-2816*v 1 s p+16384*v 0 s p
    rw [v_three s p h, v_two s p h, v_one s p h]
    rfl
  | succ n ih =>
    change widthStep rowLegal pairs compatible (v (n+3)) s p = _
    rw [step_congr (v (n+3))
      (fun s p => 128*v (n+2) s p-2816*v (n+1) s p+16384*v n s p) s p h ih]
    change (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c then
      128*v (n+2) (finish s c) (pairs c)-2816*v (n+1) (finish s c) (pairs c)+
        16384*v n (finish s c) (pairs c) else 0) = _
    change _ = 128 * widthStep rowLegal pairs compatible (v (n+2)) s p -
      2816 * widthStep rowLegal pairs compatible (v (n+1)) s p +
      16384 * widthStep rowLegal pairs compatible (v n) s p
    unfold widthStep
    simp only [ite_linear, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem initial_counts : a 1 = 10 ∧ a 2 = 800 ∧ a 3 = 78336 := by
  have h1 := counting_bridge 0
  have h2 := counting_bridge 1
  have h3 := counting_bridge 2
  rw [total_congr (v 1) weight1 v_one] at h2
  rw [total_congr (v 2) weight2 v_two] at h3
  have hh := finite_certificate.2.2.2
  change (a 1 : ℤ) = total (fun _ _ => 1) at h1
  rw [hh.1] at h1
  rw [hh.2.1] at h2
  rw [hh.2.2] at h3
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

private theorem recurrence (n : ℕ) :
    (a (n+4) : ℤ) = 128*a (n+3)-2816*a (n+2)+16384*a (n+1) := by
  rw [show n+4=(n+3)+1 by omega, counting_bridge,
    show n+3=(n+2)+1 by omega, counting_bridge,
    show n+2=(n+1)+1 by omega, counting_bridge, counting_bridge]
  rw [total_congr (v (n+3))
    (fun s p => 128*v (n+2) s p-2816*v (n+1) s p+16384*v n s p)
    (continuation_recurrence n)]
  unfold total widthTotal
  simp only [ite_linear, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem zero_count : a 0 = 0 := by simp [a, Legal]

open PowerSeries in
private theorem product_identity :
    (1-16*X)*(1-112*X+1024*X^2)*(PowerSeries.mk fun n => (a n : ℚ)) =
      2*X*(5-240*X+2048*X^2) := by
  let F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
  have hp : (1-16*X)*(1-112*X+1024*X^2)*F =
      F-128*(F*X^1)+2816*(F*X^2)-16384*(F*X^3) := by ring
  have hr : (2*X*(5-240*X+2048*X^2) : PowerSeries ℚ) =
      10*X-480*X^2+4096*X^3 := by ring
  change (1-16*X)*(1-112*X+1024*X^2)*F = _
  rw [hp,hr]
  ext n
  simp only [map_add,map_sub,coeff_ofNat_mul,coeff_mul_X_pow',coeff_X,coeff_X_pow,F,coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_right (show n ≠ 1 by omega),
      ite_eq_right (show n ≠ 2 by omega), ite_eq_right (show n ≠ 3 by omega)]
    have hh : (a (n-4+4) : ℚ) =
        128*a (n-4+3)-2816*a (n-4+2)+16384*a (n-4+1) := by
      exact_mod_cast recurrence (n-4)
    rw [show n-4+4=n by omega, show n-4+3=n-1 by omega,
      show n-4+2=n-2 by omega, show n-4+1=n-3 by omega] at hh
    linarith
  · interval_cases n <;> norm_num [zero_count,initial_counts.1,
      initial_counts.2.1,initial_counts.2.2]

open PowerSeries in
theorem result :
    (PowerSeries.mk fun n => (a n : ℚ)) =
      2*X*(5-240*X+2048*X^2)*((1-16*X)*(1-112*X+1024*X^2))⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp :
    constantCoeff ((1-16*X)*(1-112*X+1024*X^2) : PowerSeries ℚ) ≠ 0)).2
  rw [mul_comm]
  exact product_identity


#print axioms result
end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233170DiagonalStrip

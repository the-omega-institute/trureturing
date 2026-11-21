/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source full-column relations transported from the four-row and six-row quotients. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer

/-! Quotient powers pull back to the unrestricted source columns. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnPolynomials

open HardinActualTransfers
open HardinColumnContinuations (Column cross)

open private cross_iff from
  D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers

private theorem column_pullback {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    {h : ℕ} (e : A ≃ Column h) (Q : Matrix B B ℤ) (cls : A → B)
    (P : A → A → Prop) [DecidableRel P]
    (agree : ∀ a b, cross (e a) (e b) ↔ P a b)
    (rows : ∀ a j, (∑ b, if P a b ∧ cls b = j then (1 : ℤ) else 0) = Q (cls a) j)
    (m : ℕ) (a : A) :
    ((C h)^m).mulVec (1 : Column h → ℤ) (e a) =
      (Q ^ m).mulVec (1 : B → ℤ) (cls a) := by
  have hrows (p : Column h) (j : B) :
      (∑ q : Column h, if cls (e.symm q) = j then C h p q else 0) =
        Q (cls (e.symm p)) j := by
    obtain ⟨a, rfl⟩ := e.surjective p
    rw [← e.sum_comp (fun q => if cls (e.symm q) = j then C h (e a) q else 0)]
    simp only [Equiv.symm_apply_apply]
    rw [← rows a j]
    apply Finset.sum_congr rfl
    intro x _
    unfold C
    simp only [agree]
    split_ifs <;> simp_all
  simpa using powerOnes_of_rows (C h) Q (cls ∘ e.symm) hrows m (e a)

private theorem of_ascending {A : Type} [Fintype A] [DecidableEq A]
    (T : Matrix A A ℤ) (b : ℕ) {d : ℕ} (c : Fin d → ℤ)
    (hc : (T ^ (b + d)).mulVec (1 : A → ℤ) =
       ∑ j : Fin d, c j.rev • (T ^ (b + j.val)).mulVec (1 : A → ℤ)) :
    IsLagRelation T b c := by
  unfold IsLagRelation
  rw [hc, ← Equiv.sum_comp Fin.revPerm (fun j : Fin d =>
    c j • (T ^ (b + d-(j.val + 1))).mulVec (1 : A → ℤ))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply]
  have he : b + d - (j.rev.val + 1) = b + j.val := by
    rw [Fin.val_rev]
    have hj := j.isLt
    omega
  rw [he]

private theorem transportLag {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (T : Matrix A A ℤ) (Q : Matrix B B ℤ) (cls : A → B)
    (powers : ∀ m a, (T ^ m).mulVec (1 : A → ℤ) a = (Q ^ m).mulVec (1 : B → ℤ) (cls a))
    (b : ℕ) {d : ℕ} (c : Fin d → ℤ) (hQ : IsLagRelation Q b c) :
    IsLagRelation T b c := by
  unfold IsLagRelation at *
  funext a
  have h := congrFun hQ (cls a)
  simpa only [Finset.sum_apply, Pi.smul_apply, powers] using h

private def col4 : HardinA233177PairTransfer.Col ≃ Column 3 where
  toFun := HardinA233177PairTransfer.column
  invFun p := (p 0, p 1, p 2, p 3)
  left_inv p := rfl
  right_inv p := funext (fun i => by fin_cases i <;> rfl)

private def col6 : HardinA233179PairTransfer.Col ≃ Column 5 where
  toFun := HardinA233179PairTransfer.column
  invFun p := (p 0, p 1, p 2, p 3, p 4, p 5)
  left_inv p := rfl
  right_inv p := funext (fun i => by fin_cases i <;> rfl)

/-- The degree-eight source relation on all 81 four-row columns. -/
theorem rowFour :
    IsLagRelation (C 3) 1 ![4, 13, -19, -22, 27, 2, -4] ∧
    (∑ j : Fin 7, (![4, 13, -19, -22, 27, 2, -4] : Fin 7 → ℤ) j) = 1 := by
  let Q := HardinA233177PairTransfer.Q
  let cls := HardinA233177PairTransfer.cls
  have pullback := column_pullback col4 Q cls HardinA233177PairTransfer.compatible
    (fun a b => cross_iff (col4 a) (col4 b)) HardinA233177PairTransfer.quotient_rows
  refine ⟨transportLag (C 3) Q (cls ∘ col4.symm) (fun m a => ?_) 1 _ ?_, by decide⟩
  · simpa using pullback m (col4.symm a)
  · apply of_ascending
    funext i
    have base : (Q ^ 7).mulVec 1 =
        ∑ j : Fin 6, HardinA233177PairTransfer.coefficients j • (Q ^ (1 + j.val)).mulVec 1 :=
      HardinA233177PairTransfer.power_polynomial
    have advance (m : ℕ) : Q.mulVec ((Q ^ m).mulVec 1) = (Q ^ (m + 1)).mulVec 1 := by
      rw [Matrix.mulVec_mulVec, pow_succ']
    have advanced := congrArg (fun v => Q.mulVec v) base
    change Q.mulVec ((Q ^ 7).mulVec 1) = Q.mulVec _ at advanced
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, advance] at advanced
    have h := congrFun base i
    have hh := congrFun advanced i
    norm_num [Q, HardinA233177PairTransfer.coefficients, Fin.sum_univ_succ,
      Fin.rev, smul_eq_mul] at h hh ⊢
    linear_combination hh - h

section Six
open private compatible cls Q coefficients quotient_rows power_polynomial from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer

/-- The source degree-25 relation on all 729 six-row columns. -/
theorem rowSix :
    IsLagRelation (C 5) 1 ![7, 103, -365, -2896, 7168, 32291, -75471, -161805, 426135,
      333692, -1225001, -155206, 1850161, -363389, -1524689, 557502, 690388, -312941,
      -166928, 81406, 19997, -9672, -906, 420] ∧
    (∑ j : Fin 24, (![7, 103, -365, -2896, 7168, 32291, -75471, -161805, 426135,
      333692, -1225001, -155206, 1850161, -363389, -1524689, 557502, 690388, -312941,
      -166928, 81406, 19997, -9672, -906, 420] : Fin 24 → ℤ) j) = 1 := by
  have pullback := column_pullback col6 Q cls compatible
    (fun a b => cross_iff (col6 a) (col6 b)) quotient_rows
  refine ⟨transportLag (C 5) Q (cls ∘ col6.symm) (fun m a => ?_) 1 _ ?_, by decide⟩
  · simpa using pullback m (col6.symm a)
  · apply of_ascending
    have hcoef : ∀ j : Fin 24, coefficients j =
        (![7, 103, -365, -2896, 7168, 32291, -75471, -161805, 426135,
      333692, -1225001, -155206, 1850161, -363389, -1524689, 557502, 690388, -312941,
      -166928, 81406, 19997, -9672, -906, 420] : Fin 24 → ℤ) j.rev := by decide +kernel
    simpa only [← hcoef] using power_polynomial

end Six
section Walk

open private tailGood tail_local from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations

private def sixGrid (m : ℕ) :
    (Fin 6 × Fin (m + 1) → Fin 3) ≃ (Fin (m + 1) → Column 5) where
  toFun P := fun j i => P (i, j)
  invFun f := fun x => f x.2 x.1
  left_inv _ := rfl
  right_inv _ := rfl

private theorem proper_sixGrid (m : ℕ) (P : Fin 6 × Fin (m + 1) → Fin 3) :
    HardinA233179PairTransfer.Proper P ↔
      tailGood ((sixGrid m P) 0) (Fin.tail (sixGrid m P)) := by
  rw [tail_local]
  constructor
  · intro h j
    apply (cross_iff _ _).mpr
    intro r s hrs
    exact h j.castSucc (by have hj := j.isLt; simpa using hj) r s hrs
  · intro h j bound r s hrs
    let i : Fin m := ⟨j.val, by omega⟩
    exact (cross_iff _ _).mp (h i) r s hrs

/-- The source L is the sum of the actual six-row continuation vector, including width one. -/
theorem sixRow_walk (m : ℕ) :
    (HardinA233179PairTransfer.L (m + 1) : ℤ) =
      ∑ p : Column 5, ((C 5) ^ m).mulVec (1 : Column 5 → ℤ) p := by
  have raw : HardinA233179PairTransfer.L (m + 1) =
      Nat.card {P : Fin 6 × Fin (m + 1) → Fin 3 // HardinA233179PairTransfer.Proper P} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have e := (sixGrid m).subtypeEquiv
    (p := fun P => HardinA233179PairTransfer.Proper P)
    (q := fun f => tailGood (f 0) (Fin.tail f)) (proper_sixGrid m)
  rw [raw, Nat.card_congr e,
    ← Nat.card_congr (HardinColumnContinuations.coloringEquiv 5 m)]
  exact column_count 5 m

end Walk

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnPolynomials

/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/
/-
finiteSixJ_action:
  proof_shape: content
  escape_witness: four_spin_raw_recurrence, fully inlined: its actual shifted offsetTerm sum identity supplies the positive-channel matrix rows; zero and half-spin boundary cases then complete the finite matrix action.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint

def channelLabel (n j l t : ℕ) : ℕ := channelBase n j l + 2*t

def upperBand (m : ℕ) (e : Fin (m+1) → ℝ) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => if i.val+1=j.val then e i else 0

def jacobiMatrix (m : ℕ) (a e : Fin (m+1) → ℝ) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := Matrix.diagonal a + upperBand m e + (upperBand m e)ᵀ

noncomputable def physicalU (n j l : ℕ) : Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ := fun k i => Real.sqrt (((channelLabel n j l k.val+1 : ℕ) : ℝ)* ((2*(l-j+i.val)+1 : ℕ) : ℝ))*
      sixJ n n (2*(l-j+i.val)) (2*j) (2*l) (channelLabel n j l k.val)
noncomputable def normalizedSixJ (a b u c d y : ℕ) : ℝ := Real.sqrt (((y+1 : ℕ) : ℝ)*((u+1 : ℕ) : ℝ))*sixJ a b u c d y

noncomputable def normalizedUpper (a b c d y : ℕ) : ℝ := recurrenceUpperCoefficient a b c d y*Real.sqrt ((y+1 : ℕ) : ℝ)/Real.sqrt ((y+3 : ℕ) : ℝ)

private noncomputable def normalizedLower (a b c d y : ℕ) : ℝ := recurrenceLowerCoefficient a b c d y*Real.sqrt ((y+1 : ℕ) : ℝ)/Real.sqrt ((y-1 : ℕ) : ℝ)

def recurrenceDiagonalQ (a b c d y : ℕ) : ℚ := if y=0 then ((a : ℚ)/2)*((a : ℚ)/2+1)+((b : ℚ)/2)*((b : ℚ)/2+1)
  else rawDiagonal ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2)
noncomputable def finiteSixJMatrix (a b c d base m : ℕ) {ι : Type*} (us : ι → ℕ) : Matrix (Fin (m+1)) ι ℝ := fun k i => normalizedSixJ a b (us i) c d (base+2*k.val)

noncomputable def finiteSixJJacobi (a b c d base m : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := jacobiMatrix m (fun k => (recurrenceDiagonalQ a b c d (base+2*k.val) : ℝ))
    (fun k => normalizedUpper a b c d (base+2*k.val))
lemma finiteSixJ_action {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d base m : ℕ) (us : ι → ℕ)
    (had : ∀ k : Fin (m+1), ∀ i, admissible a b (us i) c d (base+2*k.val))
    (hlower : ∀ i, 2≤base → normalizedSixJ a b (us i) c d (base-2)=0)
    (hupper : ∀ i, normalizedSixJ a b (us i) c d (base+2*m+2)=0) : finiteSixJJacobi a b c d base m*finiteSixJMatrix a b c d base m us = finiteSixJMatrix a b c d base m us* diagonal (fun i => (((us i : ℚ)/2*((us i : ℚ)/2+1) : ℚ) : ℝ)) := by
  have offset_zero_sum (a b q : ℕ) (hq : q ≤ a+b) : (∑ z ∈ range (a+b+1), offsetTerm (zeroOffsets a b q) z) = offsetTerm (zeroOffsets a b q) q := by
    have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
      simp only [invFactorial, if_neg (not_le.mpr hz)]
    have offsetTerm_left_zero (q : RacahOffsets) (z : ℕ)
        (hz : (z : ℤ) < q.ta ∨ (z : ℤ) < q.tb ∨ (z : ℤ) < q.tc ∨ (z : ℤ) < q.td) : offsetTerm q z = 0 := by
      rcases hz with h | h | h | h <;>
        simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
    have offsetTerm_right_zero (q : RacahOffsets) (z : ℕ)
        (hz : q.e < z ∨ q.f < z ∨ q.g < z) : offsetTerm q z = 0 := by
      rcases hz with h | h | h <;>
        simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
    have offsetTerm_zero_support (a b q z : ℕ) (hz : z ≠ q) : offsetTerm (zeroOffsets a b q) z = 0 := by
      rcases lt_or_gt_of_ne hz with hz | hz
      · apply offsetTerm_left_zero
        simp only [zeroOffsets]
        omega
      · apply offsetTerm_right_zero
        simp only [zeroOffsets]
        omega
    apply sum_eq_single q
    · intro z _ hz
      exact offsetTerm_zero_support a b q z hz
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))
  have offset_one_sum (a b q : ℕ) (hq : q ≤ a+b) : (∑ z ∈ range (a+b+1), offsetTerm (zeroOffsets a b q).raise z) = offsetTerm (zeroOffsets a b q).raise q + offsetTerm (zeroOffsets a b q).raise (q+1) := by
    have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
      simp only [invFactorial, if_neg (not_le.mpr hz)]
    have offsetTerm_left_zero (q : RacahOffsets) (z : ℕ)
        (hz : (z : ℤ) < q.ta ∨ (z : ℤ) < q.tb ∨ (z : ℤ) < q.tc ∨ (z : ℤ) < q.td) : offsetTerm q z = 0 := by
      rcases hz with h | h | h | h <;>
        simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
    have offsetTerm_right_zero (q : RacahOffsets) (z : ℕ)
        (hz : q.e < z ∨ q.f < z ∨ q.g < z) : offsetTerm q z = 0 := by
      rcases hz with h | h | h <;>
        simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
    have offsetTerm_one_support (a b q z : ℕ) (hz : z ≠ q) (hz1 : z ≠ q+1) : offsetTerm (zeroOffsets a b q).raise z = 0 := by
      by_cases hlt : z < q
      · apply offsetTerm_left_zero
        simp only [zeroOffsets, RacahOffsets.raise]
        omega
      · apply offsetTerm_right_zero
        simp only [zeroOffsets, RacahOffsets.raise]
        omega
    have hp : ({q, q+1} : Finset ℕ) ⊆ range (a+b+2) := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      apply mem_range.mpr
      rcases hz with rfl | rfl <;> omega
    have hs : (∑ z ∈ ({q, q+1} : Finset ℕ), offsetTerm (zeroOffsets a b q).raise z) = ∑ z ∈ range (a+b+2), offsetTerm (zeroOffsets a b q).raise z := by
      apply sum_subset hp
      intro z _ hz
      simp only [mem_insert, mem_singleton, not_or] at hz
      exact offsetTerm_one_support a b q z hz.1 hz.2
    have hend : offsetTerm (zeroOffsets a b q).raise (a+b+1) = 0 := by
      apply offsetTerm_right_zero
      simp only [zeroOffsets, RacahOffsets.raise]
      omega
    rw [sum_pair (by omega : q ≠ q+1)] at hs
    rw [show a+b+2 = (a+b+1)+1 by omega, sum_range_succ, hend, add_zero] at hs
    exact hs.symm
  have offsetSum_racahSum (a b u c d y : ℕ) : (∑ z ∈ range ((a+b+c+d)/2+1), offsetTerm (racahOffsets a b u c d y) z) = racahSum a b u c d y := by
    have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
      simp only [invFactorial, if_neg (not_le.mpr hz)]
    have invFactorial_nat (n : ℕ) : invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
      simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    have invFactorial_nat_sub (n m : ℕ) (h : m ≤ n) : invFactorial ((n : ℤ)-(m : ℤ)) = (Nat.factorial (n-m) : ℚ)⁻¹ := by
      rw [← Int.natCast_sub h, invFactorial_nat]
    have offsetTerm_left_zero (q : RacahOffsets) (z : ℕ)
        (hz : (z : ℤ) < q.ta ∨ (z : ℤ) < q.tb ∨ (z : ℤ) < q.tc ∨ (z : ℤ) < q.td) : offsetTerm q z = 0 := by
      rcases hz with h | h | h | h <;>
        simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
    have offsetTerm_right_zero (q : RacahOffsets) (z : ℕ)
        (hz : q.e < z ∨ q.f < z ∨ q.g < z) : offsetTerm q z = 0 := by
      rcases hz with h | h | h <;>
        simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
    have offsetTerm_racahTerm (a b u c d y z : ℕ)
        (hl : lower a b u c d y ≤ z) (hu : z ≤ upper a b u c d y) : offsetTerm (racahOffsets a b u c d y) z = racahTerm a b u c d y z := by
      have hl' := hl
      unfold lower at hl'
      have hu' := hu
      unfold upper at hu'
      have hta : (a+d+y)/2 ≤ z := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hl')
      have htc : (a+b+u)/2 ≤ z := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hl')
      have htb : (c+b+y)/2 ≤ z := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hl')
      have htd : (c+d+u)/2 ≤ z := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hl')
      have he : z ≤ (a+b+c+d)/2 := le_trans hu' (min_le_left _ _)
      have hf : z ≤ (u+a+y+c)/2 := le_trans hu' (le_trans (min_le_right _ _) (min_le_right _ _))
      have hg : z ≤ (b+u+d+y)/2 := le_trans hu' (le_trans (min_le_right _ _) (min_le_left _ _))
      unfold offsetTerm racahOffsets racahTerm
      dsimp only
      rw [invFactorial_nat_sub z ((a+d+y)/2) hta, invFactorial_nat_sub z ((c+b+y)/2) htb, invFactorial_nat_sub z ((a+b+u)/2) htc, invFactorial_nat_sub z ((c+d+u)/2) htd, invFactorial_nat_sub ((a+b+c+d)/2) z he,
        invFactorial_nat_sub ((u+a+y+c)/2) z hf, invFactorial_nat_sub ((b+u+d+y)/2) z hg]
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ac_rfl
    have hu : upper a b u c d y ≤ (a+b+c+d)/2 := by
      unfold upper
      exact min_le_left _ _
    have hsub : range (upper a b u c d y+1) ⊆ range ((a+b+c+d)/2+1) := range_mono (Nat.add_le_add_right hu 1)
    have htrim : (∑ z ∈ range (upper a b u c d y+1), offsetTerm (racahOffsets a b u c d y) z) = ∑ z ∈ range ((a+b+c+d)/2+1), offsetTerm (racahOffsets a b u c d y) z := by
      apply sum_subset hsub
      intro z _ hz
      apply offsetTerm_right_zero
      simp only [racahOffsets]
      have ht : upper a b u c d y < z := by
        have ht : ¬ z < upper a b u c d y+1 := by simpa only [mem_range] using hz
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_not_lt ht)
      unfold upper at ht
      rcases min_lt_iff.mp ht with he | hfg
      · left
        exact_mod_cast he
      · rcases min_lt_iff.mp hfg with hg | hf
        · right; right
          exact_mod_cast hg
        · right; left
          exact_mod_cast hf
    rw [← htrim]
    unfold racahSum
    apply sum_congr rfl
    intro z hz
    by_cases hl : lower a b u c d y ≤ z
    · rw [if_pos hl]
      exact offsetTerm_racahTerm a b u c d y z hl (Nat.le_of_lt_succ (mem_range.mp hz))
    · rw [if_neg hl]
      apply offsetTerm_left_zero
      simp only [racahOffsets]
      have ht : z < lower a b u c d y := Nat.lt_of_not_ge hl
      unfold lower at ht
      rcases lt_max_iff.mp ht with hab | hcd
      · rcases lt_max_iff.mp hab with htc | hta
        · right; right; left
          exact_mod_cast htc
        · left
          exact_mod_cast hta
      · rcases lt_max_iff.mp hcd with htb | htd
        · right; left
          exact_mod_cast htb
        · right; right; right
          exact_mod_cast htd
  have upperBand_mul (m : ℕ) (e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) ι ℝ) (i : Fin (m+1)) (h : ι) : (upperBand m e*U) i h = if hi : i.val < m then e i*U ⟨i.val+1,by omega⟩ h else 0 := by
    classical
    simp only [Matrix.mul_apply,upperBand]
    by_cases hi : i.val < m
    · rw [dif_pos hi]
      rw [Finset.sum_eq_single (⟨i.val+1,by omega⟩ : Fin (m+1))]
      · simp
      · intro j _ hj
        have hn : i.val+1 ≠ j.val := by
          intro he
          apply hj
          apply Fin.ext
          exact he.symm
        simp only [if_neg hn,zero_mul]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      have hn : i.val+1 ≠ j.val := by omega
      simp only [if_neg hn,zero_mul]
  have lowerBand_mul (m : ℕ) (e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) ι ℝ) (i : Fin (m+1)) (h : ι) : ((upperBand m e)ᵀ*U) i h = if hi : 0 < i.val then
          e ⟨i.val-1,by omega⟩*U ⟨i.val-1,by omega⟩ h else 0 := by
    classical
    simp only [Matrix.mul_apply,Matrix.transpose_apply,upperBand]
    by_cases hi : 0 < i.val
    · rw [dif_pos hi]
      rw [Finset.sum_eq_single (⟨i.val-1,by omega⟩ : Fin (m+1))]
      · have he : i.val-1+1=i.val := by omega
        simp only [Fin.val_mk,if_pos he]
      · intro j _ hj
        have hn : j.val+1 ≠ i.val := by
          intro he
          apply hj
          apply Fin.ext
          change j.val=i.val-1
          omega
        simp only [if_neg hn,zero_mul]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      have hn : j.val+1 ≠ i.val := by omega
      simp only [if_neg hn,zero_mul]
  have jacobiMatrix_mul (m : ℕ) (a e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) ι ℝ) (i : Fin (m+1)) (h : ι) : (jacobiMatrix m a e*U) i h = a i*U i h + (if hi : i.val < m then e i*U ⟨i.val+1,by omega⟩ h else 0) +
        (if hi : 0 < i.val then e ⟨i.val-1,by omega⟩*U ⟨i.val-1,by omega⟩ h else 0) := by
    simp only [jacobiMatrix,Matrix.add_mul,Matrix.add_apply,Matrix.diagonal_mul, upperBand_mul,lowerBand_mul]
  have normalized_edge_symmetry (a b c d y : ℕ) : normalizedUpper a b c d y=normalizedLower a b c d (y+2) := by
    have recurrence_edge_symmetry (a b c d y : ℕ) : recurrenceUpperCoefficient a b c d y*Real.sqrt ((y : ℝ)+1)/Real.sqrt ((y : ℝ)+3) = recurrenceLowerCoefficient a b c d (y+2)*Real.sqrt ((y : ℝ)+3)/Real.sqrt ((y : ℝ)+1) := by
      unfold recurrenceUpperCoefficient recurrenceLowerCoefficient
      rw [Nat.add_sub_cancel_right]
      push_cast
      have h1 : 2*((y : ℝ)/2+1)*(2*((y : ℝ)/2)+1)=((y : ℝ)+2)*((y : ℝ)+1) := by ring
      have h2 : 2*(((y : ℝ)+2)/2)*(2*(((y : ℝ)+2)/2)+1)=((y : ℝ)+2)*((y : ℝ)+3) := by ring
      rw [h1,h2]
      have hx : Real.sqrt ((y : ℝ)+1)^2=(y : ℝ)+1 := Real.sq_sqrt (by positivity)
      have hz : Real.sqrt ((y : ℝ)+3)^2=(y : ℝ)+3 := Real.sq_sqrt (by positivity)
      have hxne : Real.sqrt ((y : ℝ)+1) ≠ 0 := by positivity
      have hzne : Real.sqrt ((y : ℝ)+3) ≠ 0 := by positivity
      have hd1 : (y : ℝ)+1 ≠ 0 := by positivity
      have hd2 : (y : ℝ)+2 ≠ 0 := by positivity
      have hd3 : (y : ℝ)+3 ≠ 0 := by positivity
      field_simp
      linear_combination
        Real.sqrt ((raisingNumerator a b c d y : ℝ)*(raisingDenominator a b c d y : ℝ))* ((y : ℝ)+3)*hx - Real.sqrt ((raisingNumerator a b c d y : ℝ)*(raisingDenominator a b c d y : ℝ))* ((y : ℝ)+1)*hz
    unfold normalizedUpper normalizedLower
    rw [show y+2+1=y+3 by omega,show y+2-1=y+1 by omega]
    push_cast
    exact recurrence_edge_symmetry a b c d y
  have normalizedSixJ_action_all (a b u c d y : ℕ)
      (had : admissible a b u c d y) : (((u : ℚ)/2*((u : ℚ)/2+1) : ℚ) : ℝ)*normalizedSixJ a b u c d y = (recurrenceDiagonalQ a b c d y : ℝ)*normalizedSixJ a b u c d y +
        (if 2≤y then normalizedLower a b c d y*normalizedSixJ a b u c d (y-2) else 0) + normalizedUpper a b c d y*normalizedSixJ a b u c d (y+2) := by
    have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
      simp only [invFactorial, if_neg (not_le.mpr hz)]
    have half_cast (n : ℕ) (hn : n % 2 = 0) : (((n/2 : ℕ) : ℤ) : ℚ) = (n : ℚ)/2 := by
      have he : 2*(n/2) = n := by omega
      have hq := congrArg (fun k : ℕ => (k : ℚ)) he
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hq
      simp only [Int.cast_natCast]
      apply (eq_div_iff (by positivity : (2 : ℚ) ≠ 0)).mpr
      simpa only [mul_comm] using hq
    have racahOffsets_raise (a b u c d y : ℕ) : racahOffsets a b u c d (y+2) = (racahOffsets a b u c d y).raise := by
      unfold racahOffsets RacahOffsets.raise
      congr 1 <;> push_cast <;> omega
    have deltaSq_pos (a b c : ℕ) : 0 < deltaSq a b c := by
      unfold deltaSq
      positivity
    have positive_sqrt_coefficient (x y num den : ℝ)
        (hx : 0 < x) (hy : 0 < y) (hn : 0 < num) (hd : 0 < den)
        (hrel : y*den=x*num) : num*Real.sqrt x = Real.sqrt (num*den)*Real.sqrt y := by
      have hs : (num*Real.sqrt x)^2 = (Real.sqrt (num*den)*Real.sqrt y)^2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hx.le, Real.sq_sqrt (mul_pos hn hd).le, Real.sq_sqrt hy.le]
        nlinarith [congrArg (fun t : ℝ => num*t) hrel]
      exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hs
    have triangle_difference_halves (a b c : ℕ) (ht : triangle a b c) : ((((a+b-c)/2 : ℕ) : ℚ) = ((a : ℚ)+b-c)/2) ∧ ((((a+c-b)/2 : ℕ) : ℚ) = ((a : ℚ)+c-b)/2) ∧ ((((b+c-a)/2 : ℕ) : ℚ) = ((b : ℚ)+c-a)/2) ∧
        ((((a+b+c)/2 : ℕ) : ℚ) = ((a : ℚ)+b+c)/2) := by
      rcases ht with ⟨ha,hb,hc,hp⟩
      have hp1 : (a+b-c)%2=0 := by omega
      have hp2 : (a+c-b)%2=0 := by omega
      have hp3 : (b+c-a)%2=0 := by omega
      have h1 := half_cast (a+b-c) hp1
      have h2 := half_cast (a+c-b) hp2
      have h3 := half_cast (b+c-a) hp3
      have h4 := half_cast (a+b+c) hp
      simp only [Int.cast_natCast,Nat.cast_sub hc,Nat.cast_sub hb,Nat.cast_sub ha,Nat.cast_add] at *
      exact ⟨h1,h2,h3,h4⟩
    have racahSum_empty (a b u c d y : ℕ)
        (he : upper a b u c d y < lower a b u c d y) : racahSum a b u c d y = 0 := by
      unfold racahSum
      apply sum_eq_zero
      intro z hz
      rw [if_neg]
      have hz' := mem_range.mp hz
      omega
    have triangleSqProduct_positive (a b u c d y : ℕ) : 0 < triangleSqProduct a b u c d y := by
      have h1 := deltaSq_pos a b u
      have h2 := deltaSq_pos a d y
      have h3 := deltaSq_pos c b y
      have h4 := deltaSq_pos c d u
      unfold triangleSqProduct
      positivity
    have prefactor_raise_scaled (a b u c d y : ℕ)
        (had : admissible a b u c d y) (hp : admissible a b u c d (y+2)) : triangleSqProduct a b u c d (y+2)*raisingDenominator a b c d y = triangleSqProduct a b u c d y*raisingNumerator a b c d y := by
      have deltaSq_raise_scaled (a b c : ℕ) (ht : triangle a b c)
          (hi : c+2 ≤ a+b) : deltaSq a b (c+2)* ((((a : ℚ)+b)/2+1)^2-((c : ℚ)/2+1)^2) = deltaSq a b c*(((c : ℚ)/2+1)^2-(((a : ℚ)-b)/2)^2) := by
        have deltaSq_raise_ratio (a b c : ℕ) (ht : triangle a b c)
            (hi : c+2 ≤ a+b) : deltaSq a b (c+2) / deltaSq a b c = (((a+c-b)/2+1 : ℕ) : ℚ)*((b+c-a)/2+1 : ℕ) / ((((a+b-c)/2 : ℕ) : ℚ)*((a+b+c)/2+2 : ℕ)) := by
          have hab : 1 ≤ (a+b-c)/2 := by omega
          have h1 : (a+b-(c+2))/2+1=(a+b-c)/2 := by omega
          have h2 : (a+(c+2)-b)/2=(a+c-b)/2+1 := by rcases ht with ⟨_,_,_,_⟩; omega
          have h3 : (b+(c+2)-a)/2=(b+c-a)/2+1 := by rcases ht with ⟨_,_,_,_⟩; omega
          have h4 : (a+b+(c+2))/2+1=((a+b+c)/2+1)+1 := by omega
          have hf : (((a+b-c)/2).factorial : ℚ) = ((a+b-c)/2 : ℕ)*((a+b-(c+2))/2).factorial := by
            rw [← h1, Nat.factorial_succ]
            push_cast
            rfl
          unfold deltaSq
          rw [h2,h3,h4,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,hf]
          push_cast
          have hz1 : (((a+b-(c+2))/2).factorial : ℚ) ≠ 0 := by positivity
          have hz2 : (((a+c-b)/2).factorial : ℚ) ≠ 0 := by positivity
          have hz3 : (((b+c-a)/2).factorial : ℚ) ≠ 0 := by positivity
          have hz4 : (((a+b+c)/2+1).factorial : ℚ) ≠ 0 := by positivity
          have hza : (((a+b-c)/2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : (a+b-c)/2 ≠ 0)
          have hzb : ((((a+b+c)/2 : ℕ) : ℚ)+2) ≠ 0 := by positivity
          field_simp
          ring
        have h := deltaSq_raise_ratio a b c ht hi
        rcases triangle_difference_halves a b c ht with ⟨h1,h2,h3,h4⟩
        push_cast at h
        rw [h1,h2,h3,h4] at h
        have hcq : (((a : ℚ)+b-c)/2) ≠ 0 := by
          have hp : 0 < (((a+b-c)/2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < (a+b-c)/2)
          rw [h1] at hp
          exact ne_of_gt hp
        have hs : ((a : ℚ)+b+c)/2+2 ≠ 0 := by positivity
        have hd : deltaSq a b c ≠ 0 := ne_of_gt (deltaSq_pos a b c)
        have he := (div_eq_div_iff hd (mul_ne_zero hcq hs)).mp h
        linear_combination he
      have ha := deltaSq_raise_scaled a d y had.2.1 hp.2.1.2.2.1
      have hb := deltaSq_raise_scaled c b y had.2.2.1 hp.2.2.1.2.2.1
      have h := congrArg₂ (fun x y : ℚ => x*y) ha hb
      unfold triangleSqProduct raisingDenominator raisingNumerator
      linear_combination (deltaSq a b u*deltaSq c d u)*h
    have raising_factors_positive (a b u c d y : ℕ)
        (had : admissible a b u c d y) (hp : admissible a b u c d (y+2)) : 0 < raisingNumerator a b c d y ∧ 0 < raisingDenominator a b c d y := by
      have deltaSq_raise_factors_positive (a b c : ℕ) (ht : triangle a b c)
          (hi : c+2 ≤ a+b) : (0 : ℚ) < ((c : ℚ)/2+1)^2-(((a : ℚ)-b)/2)^2 ∧ (0 : ℚ) < (((a : ℚ)+b)/2+1)^2-((c : ℚ)/2+1)^2 := by
        rcases triangle_difference_halves a b c ht with ⟨h1,h2,h3,h4⟩
        have h1p : (0 : ℚ) < (((a+b-c)/2 : ℕ) : ℚ) := by
          exact_mod_cast (by omega : 0 < (a+b-c)/2)
        have h2p : (0 : ℚ) < (((a+c-b)/2 : ℕ) : ℚ)+1 := by positivity
        have h3p : (0 : ℚ) < (((b+c-a)/2 : ℕ) : ℚ)+1 := by positivity
        have h4p : (0 : ℚ) < (((a+b+c)/2 : ℕ) : ℚ)+2 := by positivity
        rw [h1] at h1p
        rw [h2] at h2p
        rw [h3] at h3p
        rw [h4] at h4p
        constructor
        · have h := mul_pos h2p h3p
          convert h using 1 <;> first | rfl | ring
        · have h := mul_pos h1p h4p
          convert h using 1 <;> first | rfl | ring
      have ha := deltaSq_raise_factors_positive a d y had.2.1 hp.2.1.2.2.1
      have hb := deltaSq_raise_factors_positive c b y had.2.2.1 hp.2.2.1.2.2.1
      constructor
      · unfold raisingNumerator
        have h := mul_pos ha.1 hb.1
        convert h using 1 <;> first | rfl | ring
      · unfold raisingDenominator
        have h := mul_pos ha.2 hb.2
        convert h using 1 <;> first | rfl | ring
    have sixJ_upper_term_scaled (a b u c d y : ℕ)
        (had : admissible a b u c d y) : Real.sqrt (triangleSqProduct a b u c d y : ℝ)* (rawAlpha ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2) : ℝ)* (racahSum a b u c d (y+2) : ℝ) =
          recurrenceUpperCoefficient a b c d y*sixJ a b u c d (y+2) := by
      have racahSum_upper_missing (a b u c d y : ℕ)
          (had : admissible a b u c d y) (hp : a+d<y+2 ∨ b+c<y+2) : racahSum a b u c d (y+2) = 0 := by
        apply racahSum_empty
        rcases hp with hp | hp
        · have h := had.2.1
          have hgap : (a+b+c+d)/2 < (c+b+(y+2))/2 := by unfold triangle at h; omega
          have hlo : (c+b+(y+2))/2 ≤ lower a b u c d (y+2) := by
            unfold lower
            exact le_trans (le_max_left _ _) (le_max_right _ _)
          have hup : upper a b u c d (y+2) ≤ (a+b+c+d)/2 := by
            unfold upper
            exact min_le_left _ _
          exact lt_of_le_of_lt hup (lt_of_lt_of_le hgap hlo)
        · have h := had.2.2.1
          have hgap : (a+b+c+d)/2 < (a+d+(y+2))/2 := by unfold triangle at h; omega
          have hlo : (a+d+(y+2))/2 ≤ lower a b u c d (y+2) := by
            unfold lower
            exact le_trans (le_max_right _ _) (le_max_left _ _)
          have hup : upper a b u c d (y+2) ≤ (a+b+c+d)/2 := by
            unfold upper
            exact min_le_left _ _
          exact lt_of_le_of_lt hup (lt_of_lt_of_le hgap hlo)
      have rawAlpha_triangle_form (a b c d y : ℕ) : rawAlpha ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2) = raisingNumerator a b c d y/(2*((y : ℚ)/2+1)*(2*((y : ℚ)/2)+1)) := by
        unfold rawAlpha raisingNumerator
        ring
      have admissible_raise_bounds (a b u c d y : ℕ)
          (had : admissible a b u c d y) (hp : ¬admissible a b u c d (y+2)) : a+d<y+2 ∨ b+c<y+2 := by
        by_contra hn
        push_neg at hn
        apply hp
        refine ⟨had.1, ?_, ?_, had.2.2.2⟩
        · have h := had.2.1
          unfold triangle at h ⊢
          omega
        · have h := had.2.2.1
          unfold triangle at h ⊢
          omega
      by_cases hp : admissible a b u c d (y+2)
      · have hrel := prefactor_raise_scaled a b u c d y had hp
        have hpos := raising_factors_positive a b u c d y had hp
        have hr := positive_sqrt_coefficient
          (triangleSqProduct a b u c d y : ℝ) (triangleSqProduct a b u c d (y+2) : ℝ)
          (raisingNumerator a b c d y : ℝ) (raisingDenominator a b c d y : ℝ)
          (by exact_mod_cast triangleSqProduct_positive a b u c d y)
          (by exact_mod_cast triangleSqProduct_positive a b u c d (y+2))
          (by exact_mod_cast hpos.1) (by exact_mod_cast hpos.2) (by exact_mod_cast hrel)
        rw [rawAlpha_triangle_form,sixJ,if_pos hp]
        change _ = recurrenceUpperCoefficient a b c d y* (Real.sqrt (triangleSqProduct a b u c d (y+2) : ℝ)*(racahSum a b u c d (y+2) : ℝ))
        simp only [Rat.cast_div,recurrenceUpperCoefficient,Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]
        calc
          _ = ((raisingNumerator a b c d y : ℝ)*Real.sqrt (triangleSqProduct a b u c d y : ℝ))* (racahSum a b u c d (y+2) : ℝ)/ ((2*((y : ℚ)/2+1)*(2*((y : ℚ)/2)+1) : ℚ) : ℝ) := by push_cast; ring
          _ = _ := by rw [hr]; push_cast; ring
      · rw [sixJ,if_neg hp,racahSum_upper_missing a b u c d y had
          (admissible_raise_bounds a b u c d y had hp)]
        simp only [Rat.cast_zero,mul_zero]
    have normalizedSixJ_weight (a b u c d y : ℕ) : normalizedSixJ a b u c d y = Real.sqrt ((y+1 : ℕ) : ℝ)*Real.sqrt ((u+1 : ℕ) : ℝ)*sixJ a b u c d y := by
      unfold normalizedSixJ
      rw [Real.sqrt_mul (by positivity)]
    have normalized_term (a b u c d y z : ℕ) (e : ℝ) : (Real.sqrt ((y+1 : ℕ) : ℝ)*Real.sqrt ((u+1 : ℕ) : ℝ))*(e*sixJ a b u c d z) = (e*Real.sqrt ((y+1 : ℕ) : ℝ)/Real.sqrt ((z+1 : ℕ) : ℝ))*normalizedSixJ a b u c d z := by
      rw [normalizedSixJ_weight]
      have hz : Real.sqrt ((z+1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    have normalizedSixJ_recurrence (a b u c d y : ℕ) (hy : 2≤y)
        (had : admissible a b u c d y) : (((u : ℚ)/2*((u : ℚ)/2+1) : ℚ) : ℝ)*normalizedSixJ a b u c d y = (rawDiagonal ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2) : ℝ)* normalizedSixJ a b u c d y +
          normalizedLower a b c d y*normalizedSixJ a b u c d (y-2) + normalizedUpper a b c d y*normalizedSixJ a b u c d (y+2) := by
      have sixJ_recurrence (a b u c d y : ℕ) (hy : 2 ≤ y)
          (had : admissible a b u c d y) : (((u : ℚ)/2*((u : ℚ)/2+1) : ℚ) : ℝ)*sixJ a b u c d y = (rawDiagonal ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2) : ℝ)* sixJ a b u c d y +
            recurrenceLowerCoefficient a b c d y*sixJ a b u c d (y-2) + recurrenceUpperCoefficient a b c d y*sixJ a b u c d (y+2) := by
        have sixJ_lower_term_scaled (a b u c d y : ℕ) (hy : 2 ≤ y)
            (had : admissible a b u c d y) : Real.sqrt (triangleSqProduct a b u c d y : ℝ)* (rawGamma ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2) : ℝ)* (racahSum a b u c d (y-2) : ℝ) =
              recurrenceLowerCoefficient a b c d y*sixJ a b u c d (y-2) := by
          have racahSum_lower_missing (a b u c d y : ℕ) (hy : 2 ≤ y)
              (had : admissible a b u c d y)
              (hm : y-2+a<d ∨ y-2+d<a ∨ y-2+b<c ∨ y-2+c<b) : racahSum a b u c d (y-2) = 0 := by
            apply racahSum_empty
            have hupf : upper a b u c d (y-2) ≤ (u+a+(y-2)+c)/2 := by
              unfold upper
              exact le_trans (min_le_right _ _) (min_le_right _ _)
            have hupg : upper a b u c d (y-2) ≤ (b+u+d+(y-2))/2 := by
              unfold upper
              exact le_trans (min_le_right _ _) (min_le_left _ _)
            have hlotc : (a+b+u)/2 ≤ lower a b u c d (y-2) := by
              unfold lower
              exact le_trans (le_max_left _ _) (le_max_left _ _)
            have hlotd : (c+d+u)/2 ≤ lower a b u c d (y-2) := by
              unfold lower
              exact le_trans (le_max_right _ _) (le_max_right _ _)
            rcases hm with hm | hm | hm | hm
            · have h := had.2.1
              have hgap : (u+a+(y-2)+c)/2 < (c+d+u)/2 := by unfold triangle at h; omega
              exact lt_of_le_of_lt hupf (lt_of_lt_of_le hgap hlotd)
            · have h := had.2.1
              have hgap : (b+u+d+(y-2))/2 < (a+b+u)/2 := by unfold triangle at h; omega
              exact lt_of_le_of_lt hupg (lt_of_lt_of_le hgap hlotc)
            · have h := had.2.2.1
              have hgap : (b+u+d+(y-2))/2 < (c+d+u)/2 := by unfold triangle at h; omega
              exact lt_of_le_of_lt hupg (lt_of_lt_of_le hgap hlotd)
            · have h := had.2.2.1
              have hgap : (u+a+(y-2)+c)/2 < (a+b+u)/2 := by unfold triangle at h; omega
              exact lt_of_le_of_lt hupf (lt_of_lt_of_le hgap hlotc)
          have prefactor_lower_scaled (a b u c d y : ℕ) (hy : 2 ≤ y)
              (had : admissible a b u c d y) (hm : admissible a b u c d (y-2)) : triangleSqProduct a b u c d y*raisingDenominator a b c d (y-2) = triangleSqProduct a b u c d (y-2)*raisingNumerator a b c d (y-2) := by
            have h := prefactor_raise_scaled a b u c d (y-2) hm
              (by simpa only [Nat.sub_add_cancel hy] using had)
            simpa only [Nat.sub_add_cancel hy] using h
          have rawGamma_triangle_form (a b c d y : ℕ) (hy : 2 ≤ y) : rawGamma ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2) = raisingDenominator a b c d (y-2)/(2*((y : ℚ)/2)*(2*((y : ℚ)/2)+1)) := by
            unfold rawGamma raisingDenominator
            rw [Nat.cast_sub hy]
            push_cast
            ring
          have admissible_lower_bounds (a b u c d y : ℕ) (hy : 2 ≤ y)
              (had : admissible a b u c d y) (hm : ¬admissible a b u c d (y-2)) : y-2+a<d ∨ y-2+d<a ∨ y-2+b<c ∨ y-2+c<b := by
            by_contra hn
            push_neg at hn
            apply hm
            refine ⟨had.1, ?_, ?_, had.2.2.2⟩
            · have h := had.2.1
              unfold triangle at h ⊢
              omega
            · have h := had.2.2.1
              unfold triangle at h ⊢
              omega
          by_cases hm : admissible a b u c d (y-2)
          · have hrel := prefactor_lower_scaled a b u c d y hy had hm
            have hpos := raising_factors_positive a b u c d (y-2) hm
              (by simpa only [Nat.sub_add_cancel hy] using had)
            have hr := positive_sqrt_coefficient
              (triangleSqProduct a b u c d y : ℝ) (triangleSqProduct a b u c d (y-2) : ℝ)
              (raisingDenominator a b c d (y-2) : ℝ) (raisingNumerator a b c d (y-2) : ℝ)
              (by exact_mod_cast triangleSqProduct_positive a b u c d y)
              (by exact_mod_cast triangleSqProduct_positive a b u c d (y-2))
              (by exact_mod_cast hpos.2) (by exact_mod_cast hpos.1) (by exact_mod_cast hrel.symm)
            rw [rawGamma_triangle_form _ _ _ _ _ hy,sixJ,if_pos hm]
            change _ = recurrenceLowerCoefficient a b c d y* (Real.sqrt (triangleSqProduct a b u c d (y-2) : ℝ)*(racahSum a b u c d (y-2) : ℝ))
            simp only [Rat.cast_div,recurrenceLowerCoefficient,Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]
            calc
              _ = ((raisingDenominator a b c d (y-2) : ℝ)*Real.sqrt (triangleSqProduct a b u c d y : ℝ))* (racahSum a b u c d (y-2) : ℝ)/ ((2*((y : ℚ)/2)*(2*((y : ℚ)/2)+1) : ℚ) : ℝ) := by push_cast; ring
              _ = _ := by rw [hr]; push_cast; ring
          · rw [sixJ,if_neg hm,racahSum_lower_missing a b u c d y hy had
              (admissible_lower_bounds a b u c d y hy had hm)]
            simp only [Rat.cast_zero,mul_zero]
        have hraw := racahSum_recurrence a b u c d y hy had
        have hr := congrArg (fun x : ℚ => (x : ℝ)) hraw
        push_cast at hr
        have hs := congrArg (fun x : ℝ => Real.sqrt (triangleSqProduct a b u c d y : ℝ)*x) hr
        simp only [mul_zero,mul_add,← mul_assoc] at hs
        rw [sixJ_upper_term_scaled a b u c d y had, sixJ_lower_term_scaled a b u c d y hy had] at hs
        have hv : sixJ a b u c d y = Real.sqrt (triangleSqProduct a b u c d y : ℝ)*(racahSum a b u c d y : ℝ) := by
          rw [sixJ,if_pos had]
          rfl
        rw [hv]
        push_cast
        linear_combination -hs
      have h := sixJ_recurrence a b u c d y hy had
      have hw := congrArg (fun x : ℝ =>
        (Real.sqrt ((y+1 : ℕ) : ℝ)*Real.sqrt ((u+1 : ℕ) : ℝ))*x) h
      conv_rhs at hw => rw [mul_add,mul_add]
      rw [normalized_term a b u c d y (y-2),normalized_term a b u c d y (y+2)] at hw
      rw [show y-2+1=y-1 by omega,show y+2+1=y+3 by omega] at hw
      change _ = _+normalizedLower a b c d y*normalizedSixJ a b u c d (y-2)+ normalizedUpper a b c d y*normalizedSixJ a b u c d (y+2) at hw
      rw [normalizedSixJ_weight a b u c d y]
      linear_combination hw
    have normalizedSixJ_half_boundary (a b u c d : ℕ)
        (had : admissible a b u c d 1) : (((u : ℚ)/2*((u : ℚ)/2+1) : ℚ) : ℝ)*normalizedSixJ a b u c d 1 = (rawDiagonal ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) (1/2) : ℝ)* normalizedSixJ a b u c d 1 +
          normalizedUpper a b c d 1*normalizedSixJ a b u c d 3 := by
      have sixJ_half_boundary (a b u c d : ℕ)
          (had : admissible a b u c d 1) : (((u : ℚ)/2*((u : ℚ)/2+1) : ℚ) : ℝ)*sixJ a b u c d 1 = (rawDiagonal ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) (1/2) : ℝ)* sixJ a b u c d 1 +
            recurrenceUpperCoefficient a b c d 1*sixJ a b u c d 3 := by
        have racahSum_half_boundary (a b u c d : ℕ)
            (had : admissible a b u c d 1) : rawAlpha ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) (1/2)* racahSum a b u c d 3 + (rawDiagonal ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) (1/2)-
                ((u : ℚ)/2)*((u : ℚ)/2+1))*racahSum a b u c d 1 = 0 := by
          have racahOffsets_compatible (a b u c d y : ℕ)
              (had : admissible a b u c d y) : (racahOffsets a b u c d y).compatible
                ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((u : ℚ)/2) ((y : ℚ)/2) := by
            rcases had with ⟨⟨_, _, _, htc⟩, ⟨_, _, _, hta⟩, ⟨_, _, _, htb⟩, ⟨_, _, _, htd⟩⟩
            have htb' : (b+c+y)%2 = 0 := by omega
            have he : (a+b+c+d)%2 = 0 := by omega
            have hf : (u+a+y+c)%2 = 0 := by omega
            have hg : (b+u+d+y)%2 = 0 := by omega
            unfold racahOffsets RacahOffsets.compatible
            dsimp only
            rw [half_cast _ hta, half_cast _ htb, half_cast _ htc, half_cast _ htd, half_cast _ he, half_cast _ hf, half_cast _ hg]
            push_cast
            exact ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩
          have half_spin_lower_offsets_zero (a b u c d z : ℕ)
              (had : admissible a b u c d 1) : offsetTerm (racahOffsets a b u c d 1).lower z = 0 := by
            have offsetTerm_left_zero (q : RacahOffsets) (z : ℕ)
                (hz : (z : ℤ) < q.ta ∨ (z : ℤ) < q.tb ∨ (z : ℤ) < q.tc ∨ (z : ℤ) < q.td) : offsetTerm q z = 0 := by
              rcases hz with h | h | h | h <;>
                simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
            have offsetTerm_right_zero (q : RacahOffsets) (z : ℕ)
                (hz : q.e < z ∨ q.f < z ∨ q.g < z) : offsetTerm q z = 0 := by
              rcases hz with h | h | h <;>
                simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
            have hac : a=d+1 ∨ d=a+1 := by
              rcases had.2.1 with ⟨h1,h2,h3,h4⟩
              omega
            rcases hac with h | h
            · by_cases hz : (z : ℤ) < ((racahOffsets a b u c d 1).lower).tc
              · exact offsetTerm_left_zero _ _ (Or.inr (Or.inr (Or.inl hz)))
              · apply offsetTerm_right_zero
                right; right
                simp only [racahOffsets,RacahOffsets.lower] at hz ⊢
                omega
            · by_cases hz : (z : ℤ) < ((racahOffsets a b u c d 1).lower).td
              · exact offsetTerm_left_zero _ _ (Or.inr (Or.inr (Or.inr hz)))
              · apply offsetTerm_right_zero
                right; left
                simp only [racahOffsets,RacahOffsets.lower] at hz ⊢
                omega
          have hq := racahOffsets_compatible a b u c d 1 had
          have ht : 0 ≤ (racahOffsets a b u c d 1).tc := by simp only [racahOffsets]; positivity
          have he : (racahOffsets a b u c d 1).e = (((a+b+c+d)/2 : ℕ) : ℤ) := rfl
          have hr := four_spin_raw_recurrence (racahOffsets a b u c d 1)
            ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((u : ℚ)/2) ((1 : ℚ)/2)
            hq ht ((a+b+c+d)/2) he (by norm_num) (by norm_num) (by norm_num)
          have hzero : (∑ z ∈ range ((a+b+c+d)/2+1), offsetTerm (racahOffsets a b u c d 1).lower z) = 0 := by
            apply sum_eq_zero
            intro z _
            exact half_spin_lower_offsets_zero a b u c d z had
          rw [← racahOffsets_raise,offsetSum_racahSum,offsetSum_racahSum,hzero] at hr
          simpa only [mul_zero,add_zero] using hr
        have hraw := racahSum_half_boundary a b u c d had
        have hr := congrArg (fun x : ℚ => (x : ℝ)) hraw
        push_cast at hr
        have hs := congrArg (fun x : ℝ => Real.sqrt (triangleSqProduct a b u c d 1 : ℝ)*x) hr
        simp only [mul_zero,mul_add,← mul_assoc] at hs
        have hup := sixJ_upper_term_scaled a b u c d 1 had
        simp only [Nat.cast_one] at hup
        rw [hup] at hs
        have hv : sixJ a b u c d 1 = Real.sqrt (triangleSqProduct a b u c d 1 : ℝ)*(racahSum a b u c d 1 : ℝ) := by
          rw [sixJ,if_pos had]
          rfl
        rw [hv]
        push_cast
        linear_combination -hs
      have h := sixJ_half_boundary a b u c d had
      have hw := congrArg (fun x : ℝ =>
        (Real.sqrt ((1+1 : ℕ) : ℝ)*Real.sqrt ((u+1 : ℕ) : ℝ))*x) h
      conv_rhs at hw => rw [mul_add]
      rw [normalized_term a b u c d 1 3] at hw
      rw [normalizedSixJ_weight a b u c d 1]
      unfold normalizedUpper
      linear_combination hw
    have normalizedSixJ_zero_boundary (a b u : ℕ) (ht : triangle a b u) : (((u : ℚ)/2*((u : ℚ)/2+1) : ℚ) : ℝ)*normalizedSixJ a b u b a 0 = (((a : ℚ)/2*((a : ℚ)/2+1)+((b : ℚ)/2)*((b : ℚ)/2+1) : ℚ) : ℝ)* normalizedSixJ a b u b a 0 +
          normalizedUpper a b b a 0*normalizedSixJ a b u b a 2 := by
      have sixJ_zero_boundary (a b u : ℕ) (ht : triangle a b u) : (((u : ℚ)/2*((u : ℚ)/2+1) : ℚ) : ℝ)*sixJ a b u b a 0 = (((a : ℚ)/2*((a : ℚ)/2+1)+((b : ℚ)/2)*((b : ℚ)/2+1) : ℚ) : ℝ)* sixJ a b u b a 0 +
            recurrenceUpperCoefficient a b b a 0*sixJ a b u b a 2 := by
        have racahSum_zero_boundary (a b u : ℕ) (ht : triangle a b u) : racahSum a b u b a 2 / 2 + (((a : ℚ)/2)*((a : ℚ)/2+1)+((b : ℚ)/2)*((b : ℚ)/2+1)- ((u : ℚ)/2)*((u : ℚ)/2+1))*racahSum a b u b a 0 = 0 := by
          have invFactorial_nat (n : ℕ) : invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
            simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
          have invFactorial_step (z : ℤ) : invFactorial (z-1) = (z : ℚ)*invFactorial z := by
            by_cases hz : 0 < z
            · have hz0 : 0 ≤ z := by omega
              have hz1 : 0 ≤ z-1 := by omega
              have he : z.toNat = (z-1).toNat+1 := by omega
              have hc : ((z-1).toNat+1 : ℚ) = (z : ℚ) := by
                have h : (((z-1).toNat+1 : ℕ) : ℤ) = z := by omega
                exact_mod_cast h
              have hn0 : (z : ℚ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
              have hf0 : (Nat.factorial (z-1).toNat : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
              simp only [invFactorial, if_pos hz0, if_pos hz1]
              rw [he, Nat.factorial_succ, Nat.cast_mul]
              simp only [Nat.cast_add, Nat.cast_one]
              rw [hc]
              field_simp
            · have hz1 : z-1 < 0 := by omega
              rw [invFactorial_neg _ hz1]
              by_cases he : z = 0
              · subst z; simp only [Int.cast_zero, zero_mul]
              · rw [invFactorial_neg _ (by omega)]; simp only [mul_zero]
          have invFactorial_zero : invFactorial (0 : ℤ) = 1 := by
            simp [invFactorial]
          have invFactorial_one : invFactorial (1 : ℤ) = 1 := by
            simp [invFactorial]
          have offset_one_first (a b q : ℕ) : offsetTerm (zeroOffsets a b q).raise q = ((q : ℚ)-a)*((q : ℚ)-b)*offsetTerm (zeroOffsets a b q) q := by
            unfold offsetTerm zeroOffsets RacahOffsets.raise
            dsimp only
            rw [show (q : ℤ)-(a+1) = (q : ℤ)-a-1 by ring, show (q : ℤ)-(b+1) = (q : ℤ)-b-1 by ring, invFactorial_step ((q : ℤ)-a), invFactorial_step ((q : ℤ)-b)]
            simp only [show (q : ℤ)+1-q = 1 by ring, sub_self, add_sub_cancel_right, invFactorial_zero, invFactorial_one, invFactorial_nat, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, mul_one]
            push_cast
            ring
          have offset_one_second (a b q : ℕ) : offsetTerm (zeroOffsets a b q).raise (q+1) = -((q : ℚ)+2)*((a : ℚ)+b-q)*offsetTerm (zeroOffsets a b q) q := by
            unfold offsetTerm zeroOffsets RacahOffsets.raise
            dsimp only
            rw [pow_succ, Nat.factorial_succ]
            simp only [Int.natCast_add, Int.natCast_one, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
            rw [show (q : ℤ)+1-(a+1) = (q : ℤ)-a by ring, show (q : ℤ)+1-(b+1) = (q : ℤ)-b by ring, show (q : ℤ)+1-q = 1 by ring, show (a : ℤ)+b-(q+1) = (a : ℤ)+b-q-1 by ring, invFactorial_step ((a : ℤ)+b-q),
              show (q : ℤ)+1-(q+1) = 0 by ring]
            simp only [sub_self, invFactorial_zero, invFactorial_one, invFactorial_nat, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, mul_one]
            push_cast
            ring
          let q := (a+b+u)/2
          have hq : q ≤ a+b := by rcases ht with ⟨_, _, _, _⟩; dsimp [q]; omega
          have he : (a+b+b+a)/2 = a+b := by omega
          have ho : racahOffsets a b u b a 0 = zeroOffsets a b q := by
            unfold racahOffsets zeroOffsets
            dsimp [q]
            congr 1 <;> push_cast <;> omega
          have hqc : (q : ℚ) = (a : ℚ)/2+(b : ℚ)/2+(u : ℚ)/2 := by
            have hc := half_cast (a+b+u) ht.2.2.2
            dsimp [q]
            simp only [Int.cast_natCast] at hc
            rw [hc]
            push_cast
            ring
          rw [← offsetSum_racahSum, ← offsetSum_racahSum, show racahOffsets a b u b a 2 = (racahOffsets a b u b a 0).raise by
              simpa only [Nat.zero_add] using racahOffsets_raise a b u b a 0, ho, he, offset_one_sum a b q hq, offset_zero_sum a b q hq, offset_one_first, offset_one_second]
          generalize offsetTerm (zeroOffsets a b q) q = v
          rw [hqc]
          ring
        have had : admissible a b u b a 0 := by
          refine ⟨ht,?_,?_,?_⟩
          · unfold triangle; omega
          · unfold triangle; omega
          · unfold triangle at ht ⊢; omega
        have hraw := racahSum_zero_boundary a b u ht
        have hr := congrArg (fun x : ℚ => (x : ℝ)) hraw
        push_cast at hr
        have hs := congrArg (fun x : ℝ => Real.sqrt (triangleSqProduct a b u b a 0 : ℝ)*x) hr
        simp only [mul_zero,mul_add] at hs
        have hup := sixJ_upper_term_scaled a b u b a 0 had
        have halpha : rawAlpha ((a : ℚ)/2) ((b : ℚ)/2) ((b : ℚ)/2) ((a : ℚ)/2) 0 = 1/2 := by
          unfold rawAlpha
          ring
        simp only [Nat.cast_zero,zero_div,halpha,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hup
        have hrepl : Real.sqrt (triangleSqProduct a b u b a 0 : ℝ)*(racahSum a b u b a 2 : ℝ)/2 = recurrenceUpperCoefficient a b b a 0*sixJ a b u b a 2 := by
          convert hup using 1 <;> ring
        have hv : sixJ a b u b a 0 = Real.sqrt (triangleSqProduct a b u b a 0 : ℝ)*(racahSum a b u b a 0 : ℝ) := by
          rw [sixJ,if_pos had]
          rfl
        rw [hv]
        push_cast
        linear_combination -hs+hrepl
      have h := sixJ_zero_boundary a b u ht
      have hw := congrArg (fun x : ℝ =>
        (Real.sqrt ((0+1 : ℕ) : ℝ)*Real.sqrt ((u+1 : ℕ) : ℝ))*x) h
      conv_rhs at hw => rw [mul_add]
      rw [normalized_term a b u b a 0 2] at hw
      rw [normalizedSixJ_weight a b u b a 0]
      unfold normalizedUpper
      linear_combination hw
    by_cases h0 : y=0
    · subst y
      have ha : a=d := by have h := had.2.1; unfold triangle at h; omega
      have hb : b=c := by have h := had.2.2.1; unfold triangle at h; omega
      subst d; subst c
      simp only [recurrenceDiagonalQ,if_pos rfl,show ¬2≤(0 : ℕ) by omega,if_false,add_zero]
      exact normalizedSixJ_zero_boundary a b u had.1
    · by_cases h1 : y=1
      · subst y
        simp only [recurrenceDiagonalQ,show (1 : ℕ)≠0 by omega,if_false, show ¬2≤(1 : ℕ) by omega,if_false,add_zero,Nat.cast_one]
        exact normalizedSixJ_half_boundary a b u c d had
      · have hy : 2≤y := by omega
        simp only [recurrenceDiagonalQ,if_neg h0,if_pos hy]
        exact normalizedSixJ_recurrence a b u c d y hy had
  classical
  ext k i
  rw [finiteSixJJacobi,jacobiMatrix_mul,Matrix.mul_diagonal]
  have hr := normalizedSixJ_action_all a b (us i) c d (base+2*k.val) (had k i)
  have hp : normalizedUpper a b c d (base+2*k.val)* normalizedSixJ a b (us i) c d (base+2*k.val+2) = if hk : k.val < m then normalizedUpper a b c d (base+2*k.val)* finiteSixJMatrix a b c d base m us ⟨k.val+1,by omega⟩ i else 0 := by
    by_cases hk : k.val < m
    · rw [dif_pos hk]
      unfold finiteSixJMatrix
      congr 2 <;> omega
    · rw [dif_neg hk]
      have ht : k.val=m := by omega
      rw [ht,hupper,mul_zero]
  have hm : (if 2≤base+2*k.val then normalizedLower a b c d (base+2*k.val)* normalizedSixJ a b (us i) c d (base+2*k.val-2) else 0) = if hk : 0 < k.val then normalizedUpper a b c d (base+2*(k.val-1))*
          finiteSixJMatrix a b c d base m us ⟨k.val-1,by omega⟩ i else 0 := by
    by_cases hk : 0 < k.val
    · have hy : 2≤base+2*k.val := by omega
      rw [if_pos hy,dif_pos hk]
      unfold finiteSixJMatrix
      have he : base+2*(k.val-1)+2=base+2*k.val := by omega
      have hl : base+2*k.val-2=base+2*(k.val-1) := by omega
      have hc : normalizedUpper a b c d (base+2*(k.val-1)) = normalizedLower a b c d (base+2*k.val) := by
        rw [←he]
        exact normalized_edge_symmetry a b c d (base+2*(k.val-1))
      simp only [Fin.val_mk,hc,hl]
    · have ht : k.val=0 := by omega
      rw [dif_neg hk,ht]
      simp only [Nat.mul_zero,Nat.add_zero]
      by_cases hb : 2≤base
      · rw [if_pos hb,hlower i hb,mul_zero]
      · rw [if_neg hb]
  rw [hp,hm] at hr
  simp only [finiteSixJMatrix,Fin.val_mk] at hr ⊢
  linear_combination -hr
end D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence

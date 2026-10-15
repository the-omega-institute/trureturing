/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original twelve-state law has the explicit source affinity constant and erasure allowance. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarErasureTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance 100000] Classical.propDecidable
open MeasureTheory Function
open scoped BigOperators Matrix Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming PositiveSupportPresentation
open UnifilarPairSurvival OriginalUnifilarQuotient OriginalErasureComparison
open TwelveStatePresentation

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateTail

private def positiveEquiv : Positive parameter ≃ Hidden where
  toFun := Subtype.val
  invFun i := ⟨i,mass_pos i⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem retained_unifilar : RowUnifilar (trim parameter).matrix := by
  intro x i j k hj hk
  exact Subtype.ext (unifilar x i.val j.val k.val hj hk)

private theorem retained_word (n : ℕ) (i : Positive parameter) (w : Fin n → Bool) :
    futureMass (trim parameter).matrix i n w = futureMass marked i.val n w := by
  let e := positiveEquiv
  have hw : ∀ n (w : Fin n → Bool), wordMatrix (trim parameter).matrix n w =
      (wordMatrix marked n w).submatrix e e := by
    intro n
    induction n with
    | zero =>
      intro w
      ext i j
      simp only [wordMatrix,Matrix.submatrix_apply,Matrix.one_apply,e.injective.eq_iff]
      by_cases h : i = j <;> simp only [h,if_pos,if_false]
    | succ n ih =>
      intro w
      rw [wordMatrix,ih]
      change (marked (w 0)).submatrix e e * (wordMatrix marked n (Fin.tail w)).submatrix e e = _
      rw [Matrix.submatrix_mul_equiv]
      rfl
  unfold futureMass
  rw [hw]
  exact e.sum_comp (fun j => wordMatrix marked n w i.val j)

private theorem retained_classes (i j : Positive parameter) :
    (futureSetoid (trim parameter).matrix).r i j ↔ label i.val = label j.val := by
  have he : (futureSetoid (trim parameter).matrix).r i j ↔ (futureSetoid marked).r i.val j.val := by
    constructor <;> intro h <;> funext n w
    · exact (retained_word n i w).symm.trans ((congrFun (congrFun h n) w).trans (retained_word n j w))
    · exact (retained_word n i w).trans ((congrFun (congrFun h n) w).trans (retained_word n j w).symm)
  exact he.trans (future_classes i.val j.val)

/-- The retained original-law quotient is identified with the six phase/residue labels. -/
def labelEquiv : FutureClass (trim parameter).matrix ≃ Label := by
  let f : FutureClass (trim parameter).matrix → Label := Quotient.lift (fun i => label i.val)
    (fun i j h => (retained_classes i j).mp h)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b
    induction a using Quotient.inductionOn with | _ i =>
      induction b using Quotient.inductionOn with | _ j =>
        intro h
        exact Quotient.sound ((retained_classes i j).mpr h)
  · intro a
    let i : Hidden := (a.1,⟨a.2.val,by omega⟩)
    refine ⟨classOf (trim parameter).matrix (positiveEquiv.symm i),?_⟩
    change label i = a
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact Nat.mod_eq_of_lt a.2.isLt

/-- The fixed explicit two-step affinity constant from the actual marked matrices. -/
def rho : ℝ := Real.sqrt 15 / 4

theorem specified_survival {S : Type*} [Fintype S]
    (p : S → Bool → ℝ) (δ : S → Bool → S)
    (hp : ∀ a x, 0 ≤ p a x) (hs : ∀ a, ∑ x, p a x = 1)
    (rho : ℝ) (hr0 : 0 ≤ rho)
    (haff : ∀ a b : S, a ≠ b → D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
      (wordMass p δ 2 a) (wordMass p δ 2 b) ≤ rho) :
    ∀ r (s : Pair S), survivingAffinity p δ r s ≤ rho^(r/2) := by
  classical
  have hn (s t : Pair S) : 0 ≤ pairMatrix p δ s t := by
    unfold pairMatrix
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> positivity
  have hrow (s : Pair S) : ∑ t, pairMatrix p δ s t ≤ 1 := by
    have hh := pairMatrix_action p δ s (fun _ => 1)
    simp only [mul_one] at hh
    rw [hh]
    apply le_trans _ (D5.S3.TotalVariation.Bhattacharyya.bhattacharyya_le_one
      (p s.val.1) (p s.val.2) ⟨hp _,hs _⟩ ⟨hp _,hs _⟩)
    exact Finset.sum_le_sum fun x _ => by split_ifs <;> simp [Real.sqrt_nonneg]
  have hb (s : Pair S) : ∑ t, (pairMatrix p δ ^ 2) s t ≤ rho := by
    rw [pair_survival_word_affinity p δ hp]
    apply le_trans _ (haff _ _ s.property)
    unfold survivingAffinity D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
    exact Finset.sum_le_sum fun w _ => by dsimp only; split_ifs <;> simp [Real.sqrt_nonneg]
  intro r s
  rw [← pair_survival_word_affinity p δ hp]
  exact UnifilarAffinityContraction.matrix_block _ hn hrow 2 (by norm_num) rho hr0 hb r s

/-- Both actual half-line defects have the stated explicit geometric bound, the actual
erasure tail has its explicit summable allowance, and the fixed-Q0 MAP losses are summable. -/
theorem actual_explicit_tail :
    0 ≤ rho ∧ rho < 1 ∧
    (∀ r : ℕ, classError parameter r ≤ ENNReal.ofReal ((5/2 : ℝ)*rho^(r/2)) ∧
      leftRisk parameter r ≤ (5/2 : ℝ)*rho^(r/2) ∧
      rightRisk parameter r ≤ (5/2 : ℝ)*rho^(r/2)) ∧
    (∀ R : ℕ, erasureTail parameter R ≤ ENNReal.ofReal (10/(1-rho)*rho^(R/2))) ∧
    (∑' r : ℕ, classError parameter r) ≠ ⊤ := by
  classical
  letI := Fintype.ofFinite (FutureClass (trim parameter).matrix)
  let p := quotientMass (trim parameter).matrix
  let δ := quotientSuccessor (trim parameter).matrix
  let pi := classWeight (trim parameter)
  have hr0 : 0 ≤ rho := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hr1 : rho < 1 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
    have hn := Real.sqrt_nonneg (15 : ℝ)
    dsimp [rho]
    nlinarith
  have hp : ∀ a x, 0 ≤ p a x := q_nonneg (trim parameter)
  have hs : ∀ a, ∑ x, p a x = 1 := q_total (trim parameter)
  have haff (a b : FutureClass (trim parameter).matrix) (hab : a ≠ b) :
      D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
        (wordMass p δ 2 a) (wordMass p δ 2 b) ≤ rho := by
    have ha (c : FutureClass (trim parameter).matrix) : wordMass p δ 2 c = futureMass marked c.out.val 2 := by
      funext w
      have hh := word_class (trim parameter) retained_unifilar 2 c.out w
      rw [show classOf (trim parameter).matrix c.out = c from Quotient.out_eq c] at hh
      exact hh.trans (retained_word 2 c.out w)
    rw [ha a,ha b]
    apply actual_two_word_affinity
    intro he
    exact hab ((Quotient.out_eq a).symm.trans
      ((Quotient.sound ((retained_classes a.out b.out).mpr he)).trans (Quotient.out_eq b)))
  have hsurv := specified_survival p δ hp hs rho hr0 haff
  have hD := actual_geometric_classification parameter retained_unifilar
  have hcard : Fintype.card (FutureClass (trim parameter).matrix) = 6 := by
    simpa using Fintype.card_congr labelEquiv
  have hD0 : 0 ≤ pairWeight pi := by simpa [pairWeight,pi] using hD.1
  have hD5 : pairWeight pi ≤ (5/2 : ℝ) := by
    have hh := hD.2.1
    rw [hcard] at hh
    norm_num at hh
    simpa [pairWeight,pi] using hh
  have hclass (r : ℕ) : classError parameter r ≤ ENNReal.ofReal ((5/2 : ℝ)*rho^(r/2)) := by
    have hf : classError parameter r ≠ ⊤ := by
      obtain ⟨m,hm,_⟩ := current_map_error parameter r
      rw [← hm]
      exact measure_ne_top _ _
    apply (ENNReal.le_ofReal_iff_toReal_le hf (mul_nonneg (by norm_num) (pow_nonneg hr0 _))).mpr
    apply le_trans (actual_map_pairs parameter retained_unifilar r)
    calc
      _ ≤ pairWeight pi * rho^(r/2) := by
        unfold pairWeight
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · simp [hij]
        · rw [dif_pos hij,if_pos hij]
          exact mul_le_mul_of_nonneg_left (hsurv r ⟨(i,j),hij⟩) (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hD5 (pow_nonneg hr0 _)
  have hcomp := full_half_line_erasure_comparison parameter
  have hsum (R : ℕ) := OriginalUnifilarErasureTail.tail_series (5/2 : ℝ) rho
    (by norm_num) hr0 hr1 2 (by norm_num) R
  refine ⟨hr0,hr1,?_,?_,?_⟩
  · intro r
    have hb := (ENNReal.le_ofReal_iff_toReal_le
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hclass r))
      (mul_nonneg (by norm_num) (pow_nonneg hr0 _))).mp (hclass r)
    exact ⟨hclass r,((hcomp.1 r).2.2.2.2.1).trans hb,((hcomp.1 r).2.2.2.2.2).trans hb⟩
  · intro R
    calc
      erasureTail parameter R ≤ 2*∑' n : ℕ, classError parameter (R+n) := hcomp.2.1 R
      _ ≤ 2*∑' n : ℕ, ENNReal.ofReal ((5/2 : ℝ)*rho^((R+n)/2)) := by
        exact mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun n => hclass (R+n)) (by positivity)
      _ = ENNReal.ofReal (2*∑' n : ℕ, (5/2 : ℝ)*rho^((R+n)/2)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (by norm_num) (pow_nonneg hr0 _)) (hsum R).1,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have hh := mul_le_mul_of_nonneg_left (hsum R).2 (by norm_num : (0 : ℝ) ≤ 2)
        exact hh.trans_eq (by ring))
  · apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc
      ∑' r, classError parameter r ≤ ∑' r, ENNReal.ofReal ((5/2 : ℝ)*rho^(r/2)) :=
        ENNReal.tsum_le_tsum hclass
      _ = ENNReal.ofReal (∑' r, (5/2 : ℝ)*rho^(r/2)) := by
        exact (ENNReal.ofReal_tsum_of_nonneg (fun r => mul_nonneg (by norm_num) (pow_nonneg hr0 _))
          (by simpa using (hsum 0).1)).symm

#print axioms actual_explicit_tail
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateTail

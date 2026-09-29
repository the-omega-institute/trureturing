/- GID: D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed standard factors have their defining Lyndon word as leading monomial. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketLeading

open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization
open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra

open private hasLeadingWord_commutator from
  D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra

variable {A : Type*} [LinearOrder A]

/-- The word-theoretic closure needed by the recursive standard factorization.
It mentions only Lyndon suffix cuts and lexicographic rotations, not brackets or
coefficients. -/
noncomputable def StandardFactorClosed : (w : List A) → Prop
  | [] => False
  | [_] => True
  | a :: b :: tail =>
      let w := a :: b :: tail
      let hw : 2 ≤ w.length := by simp [w]
      StandardFactorClosed (standardLeft w hw) ∧
        StandardFactorClosed (standardRight w hw) ∧
        w < standardRight w hw ++ standardLeft w hw
termination_by w => w.length
decreasing_by
  all_goals
    simp only [standardLeft, standardRight, standardCut,
      List.length_take, List.length_drop]
    have hc := @Nat.find_spec _ (Classical.decPred _)
      (exists_lyndon_suffix_cut (a :: b :: tail) (by simp))
    omega

/-- Actual Lyndon words remain Lyndon throughout recursive standard factorization. -/
theorem isLyndon_standardFactorClosed (w : List A) (hw : IsLyndon w) :
    StandardFactorClosed w := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      subst n
      cases w with
      | nil => exact (hw.1 rfl).elim
      | cons a tail =>
          cases tail with
          | nil => simp [StandardFactorClosed]
          | cons b tail =>
              let w := a :: b :: tail
              let htwo : 2 ≤ w.length := by simp [w]
              have hleft : (standardLeft w htwo).length < w.length := by
                simp only [standardLeft, List.length_take]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w htwo)
                change 0 < standardCut w htwo ∧
                  standardCut w htwo < w.length ∧ _ at hc
                omega
              have hright : (standardRight w htwo).length < w.length := by
                simp only [standardRight, List.length_drop]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w htwo)
                change 0 < standardCut w htwo ∧
                  standardCut w htwo < w.length ∧ _ at hc
                omega
              change StandardFactorClosed w
              rw [StandardFactorClosed]
              exact ⟨
                ih _ hleft _ (isLyndon_standardLeft w htwo hw) rfl,
                ih _ hright _ (by
                  simpa [standardRight, standardCut] using
                    (@Nat.find_spec _ (Classical.decPred _)
                      (exists_lyndon_suffix_cut w htwo)).2.2) rfl,
                by
                  have hfactor : standardLeft w htwo ++ standardRight w htwo = w := by
                    simpa [standardLeft, standardRight] using
                      List.take_append_drop (standardCut w htwo) w
                  apply hw.2 (standardLeft w htwo) (standardRight w htwo)
                  · rw [← List.length_pos_iff_ne_nil]
                    simp only [standardLeft, List.length_take]
                    have hc := @Nat.find_spec _ (Classical.decPred _)
                      (exists_lyndon_suffix_cut w htwo)
                    change 0 < standardCut w htwo ∧
                      standardCut w htwo < w.length ∧ _ at hc
                    omega
                  · rw [← List.length_pos_iff_ne_nil]
                    simp only [standardRight, List.length_drop]
                    have hc := @Nat.find_spec _ (Classical.decPred _)
                      (exists_lyndon_suffix_cut w htwo)
                    change 0 < standardCut w htwo ∧
                      standardCut w htwo < w.length ∧ _ at hc
                    omega
                  · exact hfactor.symm⟩

theorem standardBracket_hasLeadingWord (w : List A) (hw : StandardFactorClosed w) :
    HasLeadingWord (standardBracket w) w := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      subst n
      cases w with
      | nil => simp [StandardFactorClosed] at hw
      | cons a tail =>
          cases tail with
          | nil =>
              rw [standardBracket]
              refine ⟨?_, by simp [wordMonomial], ?_⟩
              · intro m hm
                simp only [wordMonomial, MonoidAlgebra.coeff_single,
                  Finsupp.support_single_ne_zero _ one_ne_zero,
                  Finset.mem_singleton] at hm
                subst m
                rfl
              intro x hx
              simp only [wordMonomial, MonoidAlgebra.coeff_single,
                Finsupp.support_single_ne_zero _ one_ne_zero,
                Finset.mem_singleton] at hx
              subst x
              exact le_rfl
          | cons b tail =>
              let w := a :: b :: tail
              let htwo : 2 ≤ w.length := by simp [w]
              have hleft : (standardLeft w htwo).length < w.length := by
                simp only [standardLeft, List.length_take]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w htwo)
                change 0 < standardCut w htwo ∧
                  standardCut w htwo < w.length ∧ _ at hc
                omega
              have hright : (standardRight w htwo).length < w.length := by
                simp only [standardRight, List.length_drop]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w htwo)
                change 0 < standardCut w htwo ∧
                  standardCut w htwo < w.length ∧ _ at hc
                omega
              have hw' : StandardFactorClosed (a :: b :: tail) := hw
              simp only [StandardFactorClosed] at hw'
              rw [standardBracket]
              let u := standardLeft w htwo
              let v := standardRight w htwo
              change HasLeadingWord
                (commutator (standardBracket u) (standardBracket v)) w
              have hfactor : u ++ v = w := by
                simpa [u, v, standardLeft, standardRight] using
                  List.take_append_drop (standardCut w htwo) w
              have hrot : u ++ v < v ++ u := by
                rw [hfactor]
                exact hw'.2.2
              have hlead : HasLeadingWord
                  (commutator (standardBracket u) (standardBracket v)) (u ++ v) :=
                hasLeadingWord_commutator
                  (ih _ hleft _ hw'.1 rfl)
                  (ih _ hright _ hw'.2.1 rfl)
                  hrot
              exact hfactor ▸ hlead

/-- Standard brackets with recursively valid standard factorizations are linearly
independent over the integers, in every degree and hence jointly. -/
theorem standardBracket_linearIndependent :
    LinearIndependent ℤ
      (fun w : {w : List A // StandardFactorClosed w} ↦ standardBracket w.1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter (fun j ↦ g j ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  let m := t.min' ht
  have hm : m ∈ t := Finset.min'_mem t ht
  have hms : m ∈ s := (Finset.mem_filter.mp hm).1
  have hmg : g m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hcoeff := congrArg
    (fun p : WordPolynomial A ↦ p.coeff (FreeMonoid.ofList m.1)) hsum
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at hcoeff
  have hother : ∀ j ∈ s, j ≠ m →
      g j • (standardBracket j.1).coeff (FreeMonoid.ofList m.1) = 0 := by
    intro j hjs hjm
    by_cases hgj : g j = 0
    · simp [hgj]
    have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, hgj⟩
    have hmj : m < j := lt_of_le_of_ne (Finset.min'_le t j hjt) (Ne.symm hjm)
    have hcoeff0 : (standardBracket j.1).coeff (FreeMonoid.ofList m.1) = 0 := by
      rw [← Finsupp.notMem_support_iff]
      intro hmem
      have hjmle : j.1 ≤ m.1 :=
        (standardBracket_hasLeadingWord j.1 j.2).2.2 _ hmem
      exact (not_lt_of_ge hjmle) hmj
    simp [hcoeff0]
  rw [Finset.sum_eq_single m hother (fun hmnot ↦ (hmnot hms).elim)] at hcoeff
  rw [(standardBracket_hasLeadingWord m.1 m.2).2.1] at hcoeff
  exact hmg (by simpa using hcoeff)


end D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketLeading

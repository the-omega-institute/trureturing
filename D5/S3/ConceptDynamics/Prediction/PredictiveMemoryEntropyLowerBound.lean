/- GID: D5/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact memories dominate the minimal quotient, even for zero mass or empty states. -/

import D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient
import D5.S3.Entropy.Forgetting.CompletionEntropyMinimality

/- Library-search audit trail (2026-08-25):
   * The required repository scan for deterministic conditional-entropy data processing found
     `completion_conditional_entropy_le_of_factorization`; it is imported and applied below.
   * That theorem assumes normalized mass. No repository theorem states its nonnegative-mass
     strengthening, so two private scaling identities remove normalization without duplicating
     its entropy argument.
   * `minimal_predictive_completion_quotient` is the exact coarseness result used to show that
     the canonical predictive projection is constant on every memory fiber.
   * `CoarseGrainingCannotAddInformation` supplies mutual-information data processing, not the
     conditional-entropy inequality needed here. Pinned Mathlib has no finite real-valued match. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Prediction.PredictiveMemoryEntropyLowerBound

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.CompletionEntropyMinimality
open D5.S3.Observer.Separation.CongruenceKernel

/-- A memory is exact when both the current readout and the updated memory factor through it. -/
def IsExactPredictiveMemory {X O M : Type*}
    (q : X -> O) (F : X -> X) (r : X -> M) : Prop :=
  Refines q r ∧ Refines (r ∘ F) r

/-- The joint law of the current readout and a proposed predictive state. -/
noncomputable def predictiveMemoryJointLaw {X O Z : Type*} [Fintype X]
    (mu : X -> Real) (q : X -> O) (state : X -> Z) : O × Z -> Real :=
  pushforward (fun x => (q x, state x)) mu

private theorem predictive_projection_factors_through_memory
    {X O M : Type*} (q : X -> O) (F : X -> X) (r : X -> M)
    (hmemory : IsExactPredictiveMemory q F r) :
    (predictiveProjection F q).FactorsThrough r := by
  rcases hmemory.1 with ⟨readoutFactor, hreadout⟩
  rcases hmemory.2 with ⟨updateFactor, hupdate⟩
  obtain ⟨_qbar, _Fbar, _hreadout, _hupdate, hcoarsest⟩ :=
    minimal_predictive_completion_quotient F q
  have hcongruence :
      TauCongruence F (setoidRelation (Setoid.ker r)) := by
    intro x y hxy
    change r x = r y at hxy
    change r (F x) = r (F y)
    calc
      r (F x) = updateFactor (r x) := congrFun hupdate x
      _ = updateFactor (r y) := congrArg updateFactor hxy
      _ = r (F y) := (congrFun hupdate y).symm
  have hinside : setoidRelation (Setoid.ker r) ⊆ readoutRelation q := by
    intro pair hpair
    change r pair.1 = r pair.2 at hpair
    change q pair.1 = q pair.2
    calc
      q pair.1 = readoutFactor (r pair.1) := congrFun hreadout pair.1
      _ = readoutFactor (r pair.2) := congrArg readoutFactor hpair
      _ = q pair.2 := (congrFun hreadout pair.2).symm
  rcases hcoarsest (Setoid.ker r) hcongruence hinside with ⟨factor, hfactor⟩
  intro x y hxy
  rw [hfactor]
  exact congrArg factor (Quotient.sound hxy)

private theorem predictive_memory_joint_law_div
    {X O Z : Type*} [Fintype X]
    (mu : X -> Real) (q : X -> O) (state : X -> Z) (scale : Real) :
    predictiveMemoryJointLaw (fun x => mu x / scale) q state =
      fun z => predictiveMemoryJointLaw mu q state z / scale := by
  classical
  funext z
  simp only [predictiveMemoryJointLaw, pushforward]
  calc
    (∑ x, if (q x, state x) = z then mu x / scale else 0) =
        ∑ x, (if (q x, state x) = z then mu x else 0) / scale := by
      have hterms :
          (fun x => if (q x, state x) = z then mu x / scale else 0) =
            fun x => (if (q x, state x) = z then mu x else 0) / scale := by
        funext x
        by_cases h : (q x, state x) = z <;> simp [h]
      exact congrArg (fun f : X -> Real => ∑ x, f x) hterms
    _ = (∑ x, if (q x, state x) = z then mu x else 0) / scale := by
      simpa using
        (Finset.sum_div Finset.univ
          (fun x => if (q x, state x) = z then mu x else 0) scale).symm
  apply congrArg (fun value : Real => value / scale)
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases h : (q x, state x) = z <;> simp [h]

private theorem conditional_entropy_div
    {A B : Type*} [Fintype A] [Fintype B]
    (p : A × B -> Real) (scale : Real) (hscale : scale ≠ 0) :
    conditionalEntropy (fun z => p z / scale) = conditionalEntropy p / scale := by
  classical
  have hmarginal (a : A) :
      marginal (fun z => p z / scale) a = marginal p a / scale := by
    simp only [marginal]
    rw [← Finset.sum_div]
  have hconditional (a : A) :
      conditional (fun z => p z / scale) a = conditional p a := by
    funext b
    rw [conditional, conditional, hmarginal]
    by_cases hm : marginal p a = 0
    · simp [hm]
    · field_simp [hscale, hm]
  rw [conditionalEntropy, conditionalEntropy]
  simp_rw [hmarginal, hconditional]
  calc
    (∑ a, marginal p a / scale *
        D5.S3.Entropy.MaxEntropy.shannonEntropy (conditional p a)) =
        ∑ a, (marginal p a *
          D5.S3.Entropy.MaxEntropy.shannonEntropy (conditional p a)) / scale := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a, marginal p a *
        D5.S3.Entropy.MaxEntropy.shannonEntropy (conditional p a)) / scale := by
      rw [Finset.sum_div]

open Classical in
/-- The minimal predictive quotient needs no more conditional information beyond the current
readout than any finite exact predictive memory. Nonnegative mass need not be normalized. -/
theorem predictive_memory_entropy_lower_bound
    {X O M : Type*} [Fintype X] [Fintype O] [Fintype M]
    (mu : X -> Real) (q : X -> O) (F : X -> X) (r : X -> M)
    (hmu : forall x, 0 <= mu x)
    (hmemory : IsExactPredictiveMemory q F r) :
    conditionalEntropy
        (predictiveMemoryJointLaw mu q (predictiveProjection F q)) <=
      conditionalEntropy (predictiveMemoryJointLaw mu q r) := by
  classical
  let total : Real := ∑ x, mu x
  have htotal_nonnegative : 0 <= total := by
    exact Finset.sum_nonneg fun x _ => hmu x
  by_cases htotal : total = 0
  · have hzero : forall x, mu x = 0 := by
      have hall :=
        (Finset.sum_eq_zero_iff_of_nonneg fun x (_hx : x ∈ Finset.univ) => hmu x).mp htotal
      exact fun x => hall x (Finset.mem_univ x)
    simp [predictiveMemoryJointLaw, pushforward, conditionalEntropy, marginal, hzero]
  · have htotal_positive : 0 < total := lt_of_le_of_ne htotal_nonnegative (Ne.symm htotal)
    have hexists : exists x, mu x ≠ 0 := by
      by_contra hall
      push Not at hall
      apply htotal
      exact Finset.sum_eq_zero fun x _ => hall x
    rcases hexists with ⟨x0, _hx0⟩
    letI : Nonempty X := ⟨x0⟩
    letI : Nonempty O := ⟨q x0⟩
    letI : Nonempty M := ⟨r x0⟩
    letI : Nonempty (PredictiveQuotient F q) := ⟨predictiveProjection F q x0⟩
    have hthrough := predictive_projection_factors_through_memory q F r hmemory
    let factor : M -> PredictiveQuotient F q :=
      Function.extend r (predictiveProjection F q)
        (fun _ => predictiveProjection F q x0)
    have hfactor_apply (x : X) :
        factor (r x) = predictiveProjection F q x := by
      simpa only [factor] using
        hthrough.extend_apply (fun _ => predictiveProjection F q x0) x
    have hfactor_surjective : Function.Surjective factor := by
      intro z
      refine Quotient.inductionOn z ?_
      intro x
      exact ⟨r x, hfactor_apply x⟩
    have hprojection : predictiveProjection F q = factor ∘ r := by
      funext x
      exact (hfactor_apply x).symm
    let normalized : X -> Real := fun x => mu x / total
    have hnormalized : (forall x, 0 <= normalized x) ∧ ∑ x, normalized x = 1 := by
      constructor
      · intro x
        exact div_nonneg (hmu x) htotal_nonnegative
      · simp only [normalized]
        rw [← Finset.sum_div, show (∑ x, mu x) = total by rfl, div_self htotal]
    have hbound :=
      completion_conditional_entropy_le_of_factorization
        normalized hnormalized q r (predictiveProjection F q) factor
        hfactor_surjective hprojection
    change conditionalEntropy
        (predictiveMemoryJointLaw normalized q (predictiveProjection F q)) <=
      conditionalEntropy (predictiveMemoryJointLaw normalized q r) at hbound
    rw [predictive_memory_joint_law_div, predictive_memory_joint_law_div,
      conditional_entropy_div _ total htotal,
      conditional_entropy_div _ total htotal] at hbound
    exact (div_le_div_iff_of_pos_right htotal_positive).mp hbound
#print axioms predictive_memory_entropy_lower_bound

open Classical in
/-- Signed mass `2, -1` makes the exact identity memory have negative conditional entropy. -/
theorem nonnegative_mass_is_necessary :
    (Not (forall b : Bool, 0 <= if b then (-1 : Real) else 2)) ∧
      IsExactPredictiveMemory (fun _ : Bool => ()) id id ∧
      Not (conditionalEntropy
          (predictiveMemoryJointLaw (fun b : Bool => if b then -1 else 2)
            (fun _ => ()) (predictiveProjection id (fun _ : Bool => ()))) <=
        conditionalEntropy
          (predictiveMemoryJointLaw (fun b : Bool => if b then -1 else 2)
            (fun _ => ()) id)) := by
  have hquotient (z : PredictiveQuotient (id : Bool -> Bool) (fun _ => ())) :
      z = predictiveProjection id (fun _ : Bool => ()) false := by
    refine Quotient.inductionOn z ?_
    intro b
    apply Quotient.sound
    exact fun _ => rfl
  have hcard :
      Fintype.card (PredictiveQuotient (id : Bool -> Bool) (fun _ => ())) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    exact ⟨predictiveProjection id (fun _ : Bool => ()) false, hquotient⟩
  have hleft :
      conditionalEntropy
          (predictiveMemoryJointLaw (fun b : Bool => if b then -1 else 2)
            (fun _ => ()) (predictiveProjection id (fun _ : Bool => ()))) = 0 := by
    simp [conditionalEntropy, marginal, conditional, predictiveMemoryJointLaw,
      pushforward, D5.S3.Entropy.MaxEntropy.shannonEntropy, hquotient,
      hcard, Real.negMulLog]
  have hright :
      conditionalEntropy
          (predictiveMemoryJointLaw (fun b : Bool => if b then -1 else 2)
            (fun _ => ()) id) = -2 * Real.log 2 := by
    simp [conditionalEntropy, marginal, conditional, predictiveMemoryJointLaw,
      pushforward, D5.S3.Entropy.MaxEntropy.shannonEntropy, Real.negMulLog]
    norm_num [Real.log_neg_eq_log]
  refine ⟨?_, ?_, ?_⟩
  · intro hall
    have htrue := hall true
    norm_num at htrue
  · constructor
    · exact ⟨fun _ : Bool => (), rfl⟩
    · exact ⟨id, rfl⟩
  · rw [hleft, hright]
    nlinarith [Real.log_pos (by norm_num : (1 : Real) < 2)]
#print axioms nonnegative_mass_is_necessary

open Classical in
example :
    conditionalEntropy
        (predictiveMemoryJointLaw (@Empty.elim Real) (@Empty.elim Unit)
          (predictiveProjection (@Empty.elim Empty) (@Empty.elim Unit))) <=
      conditionalEntropy
        (predictiveMemoryJointLaw (@Empty.elim Real) (@Empty.elim Unit)
          (@Empty.elim Unit)) := by
  apply predictive_memory_entropy_lower_bound
  · exact fun x => x.elim
  · constructor <;> exact ⟨id, rfl⟩

open Classical in
example :
    conditionalEntropy
        (predictiveMemoryJointLaw (fun _ : Unit => (1 : Real)) (fun _ => ())
          (predictiveProjection id (fun _ : Unit => ()))) <=
      conditionalEntropy
        (predictiveMemoryJointLaw (fun _ : Unit => (1 : Real)) (fun _ => ()) id) := by
  apply predictive_memory_entropy_lower_bound
  · intro x
    positivity
  · constructor <;> exact ⟨id, rfl⟩

open Classical in
example :
    conditionalEntropy
        (predictiveMemoryJointLaw (fun _ : Bool => (0 : Real)) id
          (predictiveProjection id id)) <=
      conditionalEntropy
        (predictiveMemoryJointLaw (fun _ : Bool => (0 : Real)) id id) := by
  apply predictive_memory_entropy_lower_bound
  · intro x
    exact le_rfl
  · constructor <;> exact ⟨id, rfl⟩

end D5.S3.ConceptDynamics.Prediction.PredictiveMemoryEntropyLowerBound

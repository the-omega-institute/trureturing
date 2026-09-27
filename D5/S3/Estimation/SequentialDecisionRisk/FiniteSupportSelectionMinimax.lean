/- GID: D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionMinimax
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionMinimax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual complete-observation permutations transport the uniform cutoff rules and give equal-risk Bayes minimax identities. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes

open scoped BigOperators
open Finset
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionMinimax
noncomputable section

def Conclusion (M q s : ℕ) (r : ℝ) (e : Experiment) : Prop :=
  (∀ S : Support M q, IsRowStochastic (transition r S) ∧
    (∀ y : Vertex M, (∑ x : Vertex M, transition r S x y) = 1)) ∧
  IsRowStochastic (probability (M := M) (q := q) (s := s) r e) ∧
  (∀ (S : Support M q) (o : Obs M s e),
    0 < probability r e S o ∧
    probability r e S o = uniformMass M s e *
      ∏ k : Fin s, (1 + b r S (edges e o k).1 * chi (edges e o k).2) ∧
    probability r e S o = uniformMass M s e * background q r e o *
      ∏ i ∈ S.val, weight q r e o i) ∧
  (∀ o : Obs M s e,
    0 < partition (q := q) r e o ∧
    (∀ i : Fin M, 0 < weight q r e o i ∧ weight q r e o i = Real.exp (score q r e o i)) ∧
    (∀ S : Support M q, posterior r e o S =
      (∏ i ∈ S.val, weight q r e o i) / partition (q := q) r e o) ∧
    (∀ i j : Fin M, i ≠ j →
      inclusion q r e o i - inclusion q r e o j =
        (weight q r e o i - weight q r e o j) *
          (∑ U ∈ ((Finset.univ.erase i).erase j).powersetCard (q-1),
            ∏ k ∈ U, weight q r e o k) / partition (q := q) r e o) ∧
    (∀ i j : Fin M, inclusion q r e o i ≤ inclusion q r e o j ↔
      weight q r e o i ≤ weight q r e o j)) ∧
  (∀ σ : Equiv.Perm (Fin M),
    Function.Bijective (permObs (s := s) σ e) ∧
    Function.Bijective (permSupport (q := q) σ) ∧
    (∀ (S : Support M q) (o : Obs M s e),
      probability r e (permSupport σ S) (permObs σ e o) = probability r e S o) ∧
    (∀ (o : Obs M s e) (i : Fin M), weight q r e (permObs σ e o) (σ i) = weight q r e o i) ∧
    (∀ (o : Obs M s e) (T : Support M q),
      decision q r e (permObs σ e o) (permSupport σ T) = decision q r e o T)) ∧
  (∀ S T : Support M q, ∃ σ : Equiv.Perm (Fin M), permSupport σ S = T) ∧
  ∃ Dq : FiniteMarkovKernel (Obs M s e) (Support M q),
    Dq.val = decision q r e ∧
    (∀ T : Support M q, Measurable (fun o : Obs M s e => Dq.val o T)) ∧
    (∀ o : Obs M s e, ∃ t : ℝ,
      let H := Finset.univ.filter (fun i => t < weight q r e o i)
      let E := Finset.univ.filter (fun i => weight q r e o i = t)
      H.card < q ∧ q ≤ H.card + E.card ∧
      (∀ T : Support M q, Dq.val o T =
        if H ⊆ T.val ∧ T.val ⊆ H ∪ E then ((E.card.choose (q-H.card) : ℕ) : ℝ)⁻¹ else 0)) ∧
    Optimal r e hammingLoss Dq ∧
    ∃ Da : FiniteMarkovKernel (Obs M s e) (Finset (Fin M)),
      Da.val = allDecision q r e ∧
      (∀ T : Finset (Fin M), Measurable (fun o : Obs M s e => Da.val o T)) ∧
      Optimal (q := q) r e exactLoss Da

/-- The full finite support-selection bridge for independent pairs and for one-start paths. -/
theorem result (M q s : ℕ) (r : ℝ)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (e : Experiment) : Conclusion M q s r e := by
  have actual_permutations {M q s : ℕ} (r : ℝ) (e : Experiment)
      (σ : Equiv.Perm (Fin M)) :
      Function.Bijective (permObs (s := s) σ e) ∧
      Function.Bijective (permSupport (q := q) σ) ∧
      (∀ (S : Support M q) (o : Obs M s e),
        probability r e (permSupport σ S) (permObs σ e o) = probability r e S o) ∧
      (∀ (o : Obs M s e) (i : Fin M), weight q r e (permObs σ e o) (σ i) = weight q r e o i) ∧
      (∀ (o : Obs M s e) (T : Support M q),
        decision q r e (permObs σ e o) (permSupport σ T) = decision q r e o T) := by
    classical
    have hv (x : Vertex M) : permVertex σ.symm (permVertex σ x) = x := by
      cases x <;> simp [permVertex]
    have hv' (x : Vertex M) : permVertex σ (permVertex σ.symm x) = x := by
      cases x <;> simp [permVertex]
    have ho : Function.LeftInverse (permObs σ.symm e) (permObs (s := s) σ e) := by
      intro o; cases e <;> funext k
      · exact Prod.ext (hv _) (hv _)
      · exact hv _
    have ho' : Function.RightInverse (permObs σ.symm e) (permObs (s := s) σ e) := by
      intro o; cases e <;> funext k
      · exact Prod.ext (hv' _) (hv' _)
      · exact hv' _
    have hs : Function.LeftInverse (permSupport σ.symm) (permSupport (q := q) σ) := by
      intro S; apply Subtype.ext; ext i
      simp [permSupport]
    have hs' : Function.RightInverse (permSupport σ.symm) (permSupport (q := q) σ) := by
      intro S; apply Subtype.ext; ext i
      simp [permSupport]
    have hb (S : Support M q) (x : Vertex M) : b r (permSupport σ S) (permVertex σ x) = b r S x := by
      cases x <;> simp [b, permVertex, permSupport]
    have hchi (x : Vertex M) : chi (permVertex σ x) = chi x := by
      cases x <;> rfl
    have ht (S : Support M q) (x y : Vertex M) :
        transition r (permSupport σ S) (permVertex σ x) (permVertex σ y) = transition r S x y := by
      simp only [transition, hb, hchi]
    have hedge (o : Obs M s e) (k : Fin s) : edges e (permObs σ e o) k =
        (permVertex σ (edges e o k).1, permVertex σ (edges e o k).2) := by
      cases e <;> rfl
    have hc (o : Obs M s e) (i : Fin M) (z : ℝ) :
        count e (permObs σ e o) (σ i) z = count e o i z := by
      unfold count
      congr 1
      ext k
      simp only [mem_filter, mem_univ, true_and, hedge, hchi]
      have hi : (Sum.inl (σ i) : Vertex M) = permVertex σ (Sum.inl i) := rfl
      rw [hi, Equiv.apply_eq_iff_eq]
    have hw (o : Obs M s e) (i : Fin M) :
        weight q r e (permObs σ e o) (σ i) = weight q r e o i := by
      simp only [weight, hc]
    have htop (o : Obs M s e) (T : Support M q) :
        permSupport σ T ∈ topFamily q r e (permObs σ e o) ↔ T ∈ topFamily q r e o := by
      simp only [topFamily, mem_filter, mem_univ, true_and]
      constructor
      · intro h i hi j hj
        have hmem : σ i ∈ (permSupport σ T).val := by simpa [permSupport] using hi
        have hnot : σ j ∉ (permSupport σ T).val := by simpa [permSupport] using hj
        simpa only [hw] using h (σ i) hmem (σ j) hnot
      · intro h i hi j hj
        obtain ⟨i, rfl⟩ := σ.surjective i
        obtain ⟨j, rfl⟩ := σ.surjective j
        have hi' : i ∈ T.val := by simpa [permSupport] using hi
        have hj' : j ∉ T.val := by simpa [permSupport] using hj
        simpa only [hw] using h i hi' j hj'
    refine ⟨⟨ho.injective, ho'.surjective⟩, ⟨hs.injective, hs'.surjective⟩, ?_, hw, ?_⟩
    · intro S o
      cases e <;> simp only [probability, permObs, ht]
    · intro o T
      have hcard : (topFamily q r e (permObs σ e o)).card = (topFamily q r e o).card := by
        apply (card_bij (fun U _ => permSupport σ U) ?_ ?_ ?_).symm
        · intro U hU; exact (htop o U).mpr hU
        · intro U _ V _ h; exact hs.injective h
        · intro V hV
          obtain ⟨U,rfl⟩ := hs'.surjective V
          exact ⟨U, (htop o U).mp hV, rfl⟩
      simp only [decision, hcard, htop]

  have support_transitive {M q : ℕ} (S T : Support M q) :
      ∃ σ : Equiv.Perm (Fin M), permSupport σ S = T := by
    classical
    let e : S.val ≃ T.val := (Fintype.equivOfCardEq (by simp [S.property, T.property]))
    refine ⟨e.extendSubtype, Subtype.ext ?_⟩
    change S.val.map e.extendSubtype.toEmbedding = T.val
    apply eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
      exact e.extendSubtype_mem j hj
    · simp [S.property, T.property]

  have minimax_rules {M q s : ℕ} {r : ℝ}
      (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
      (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
      (e : Experiment) :
      ∃ Dq : FiniteMarkovKernel (Obs M s e) (Support M q),
        Dq.val = decision q r e ∧
        (∀ T, Measurable (fun o : Obs M s e => Dq.val o T)) ∧
        Optimal r e hammingLoss Dq ∧
        ∃ Da : FiniteMarkovKernel (Obs M s e) (Finset (Fin M)),
          Da.val = allDecision q r e ∧
          (∀ T, Measurable (fun o : Obs M s e => Da.val o T)) ∧
          Optimal (q := q) r e exactLoss Da := by
    classical
    obtain ⟨_,_,_,_,hqD,_,haD,hbq,hba⟩ := finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e
    let Dq : FiniteMarkovKernel (Obs M s e) (Support M q) := ⟨decision q r e,hqD⟩
    let Da : FiniteMarkovKernel (Obs M s e) (Finset (Fin M)) := ⟨allDecision q r e,haD⟩
    have htransport {A : Type} [Fintype A] (loss : Support M q → A → ℝ)
        (D : Obs M s e → A → ℝ) (σ : Equiv.Perm (Fin M)) (τ : A ≃ A)
        (hD : ∀ o a, D (permObs σ e o) (τ a) = D o a)
        (hL : ∀ S a, loss (permSupport σ S) (τ a) = loss S a)
        (S : Support M q) : risk r e loss D (permSupport σ S) = risk r e loss D S := by
      have hperm := actual_permutations (q := q) (s := s) r e σ
      unfold risk
      rw [← hperm.1.sum_comp]
      apply sum_congr rfl
      intro o _
      rw [hperm.2.2.1]
      congr 1
      rw [← τ.sum_comp]
      apply sum_congr rfl
      intro a _
      rw [hD,hL]
    have hqeq (S T : Support M q) : risk r e hammingLoss Dq.val S = risk r e hammingLoss Dq.val T := by
      obtain ⟨σ,rfl⟩ := support_transitive S T
      symm
      apply htransport hammingLoss Dq.val σ (Equiv.ofBijective _ (actual_permutations (q := q) (s := s) r e σ).2.1)
      · exact (actual_permutations (q := q) (s := s) r e σ).2.2.2.2
      · intro S A
        change hammingLoss (permSupport σ S) (permSupport σ A) = hammingLoss S A
        simp only [hammingLoss,permSupport]
        simp only [map_eq_image, Equiv.coe_toEmbedding]
        rw [← image_symmDiff A.val S.val σ.injective,
          card_image_of_injective _ σ.injective]
    have haeq (S T : Support M q) : risk r e exactLoss Da.val S = risk r e exactLoss Da.val T := by
      obtain ⟨σ,rfl⟩ := support_transitive S T
      symm
      apply htransport exactLoss Da.val σ σ.finsetCongr
      · intro o A
        change allDecision q r e (permObs σ e o) (σ.finsetCongr A) = allDecision q r e o A
        have hc : (σ.finsetCongr A).card = A.card := card_map _
        by_cases h : A.card = q
        · simp only [allDecision,hc,dif_pos h]
          exact (actual_permutations (q := q) (s := s) r e σ).2.2.2.2 o ⟨A,h⟩
        · simp only [allDecision,hc,dif_neg h]
      · intro S A
        simp only [exactLoss,permSupport,Equiv.finsetCongr_apply, map_inj]
    obtain ⟨S₀,hS₀⟩ := powersetCard_nonempty.mpr (show q ≤ (univ : Finset (Fin M)).card by simpa using hqm.le)
    let S₀' : Support M q := ⟨S₀,(mem_powersetCard.mp hS₀).2⟩
    letI : Nonempty (Support M q) := ⟨S₀'⟩
    have hprior : (∑ S : Support M q, prior M q S) = 1 := by
      simp only [prior, sum_const, card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
    have finish {A : Type} [Fintype A] (loss : Support M q → A → ℝ)
        (D : FiniteMarkovKernel (Obs M s e) A)
        (hbest : ∀ D' : FiniteMarkovKernel (Obs M s e) A,
          finiteBayesCost (prior M q) loss (probability r e) D.val ≤
            finiteBayesCost (prior M q) loss (probability r e) D'.val)
        (heq : ∀ S T, risk r e loss D.val S = risk r e loss D.val T) : Optimal r e loss D := by
      have hcost (d : Obs M s e → A → ℝ) :
          finiteBayesCost (prior M q) loss (probability r e) d =
            ∑ S, prior M q S * risk r e loss d S := by
        unfold finiteBayesCost risk
        apply sum_congr rfl
        intro S _
        congr 1
        simp only [D5.S3.Divergence.ClassicalDPI.channelOutput,sum_mul,mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro o _
        apply sum_congr rfl
        intro a _
        ring
      have hconst (S : Support M q) : finiteBayesCost (prior M q) loss (probability r e) D.val = risk r e loss D.val S := by
        rw [hcost]
        simp_rw [heq _ S]
        rw [← sum_mul,hprior,one_mul]
      have hworst (D' : FiniteMarkovKernel (Obs M s e) A) (S : Support M q) :
          risk r e loss D.val S ≤ sSup (Set.range (risk r e loss D'.val)) := by
        rw [← hconst S]
        apply (hbest D').trans
        rw [hcost]
        calc
          (∑ T, prior M q T * risk r e loss D'.val T) ≤
              ∑ T, prior M q T * sSup (Set.range (risk r e loss D'.val)) := by
            apply sum_le_sum
            intro T _
            exact mul_le_mul_of_nonneg_left
              (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self T)) (by dsimp [prior]; positivity)
          _ = _ := by rw [← sum_mul,hprior,one_mul]
      have hsmax : sSup (Set.range (risk r e loss D.val)) = risk r e loss D.val S₀' := by
        have hrange : Set.range (risk r e loss D.val) = {risk r e loss D.val S₀'} := by
          ext z
          constructor
          · rintro ⟨S,rfl⟩; exact heq S S₀'
          · intro hz; exact ⟨S₀', hz.symm⟩
        rw [hrange,csSup_singleton]
      refine ⟨hbest,heq,hworst,?_⟩
      rw [hsmax]
      symm
      apply IsLeast.csInf_eq
      refine ⟨⟨D, hsmax⟩, ?_⟩
      rintro z ⟨D',rfl⟩
      exact hworst D' S₀'
    refine ⟨Dq,rfl,fun _ => measurable_from_top,finish hammingLoss Dq hbq hqeq,
      Da,rfl,fun _ => measurable_from_top,finish exactLoss Da hba haeq⟩

  obtain ⟨ht,hp,hf,hpost,_,hcut,_,_,_⟩ := finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e
  refine ⟨ht,hp,hf,hpost,actual_permutations r e,support_transitive,?_⟩
  obtain ⟨Dq,hDq,hmq,hoptq,Da,hDa,hma,hopta⟩ := minimax_rules (s := s) hq hqm hr hr1 ha ha1 e
  refine ⟨Dq,hDq,hmq,?_,hoptq,Da,hDa,hma,hopta⟩
  rw [hDq]
  exact hcut

#print axioms result
end
end D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionMinimax

/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original future recovers the initial residue without recovering its phase. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FixedTargetRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Function Set Filter
open scoped BigOperators Classical Topology ENNReal
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming OriginalFutureScreening
open OriginalErasureComparison OriginalUnifilarQuotient UnifilarPairSurvival OriginalFutureCylinders
open TwelveStatePresentation IndependentSeedPosterior TwelveStateTail FixedTargetRecovery

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateFutureRecovery

private def p (a : Label) (x : Bool) : ℝ := prob (representative a) x
private def δ (a : Label) (x : Bool) : Label :=
  (x,⟨(a.2.val + if x then 1 else 0) % 3,Nat.mod_lt _ (by decide)⟩)

private theorem label_step (i : Hidden) (x : Bool) :
    prob i x = p (label i) x ∧ label (next i x) = δ (label i) x := by
  rcases i with ⟨b,s⟩
  cases b <;> fin_cases s <;> cases x <;>
    norm_num [p,δ,prob,representative,label,next,advance,rate]

private theorem label_word (r : ℕ) (i : Hidden) (w : Fin r → Bool) :
    futureMass marked i r w = wordMass p δ r (label i) w := by
  induction r generalizing i with
  | zero => rw [future_empty]; rfl
  | succ r ih =>
    rw [← Fin.cons_self_tail w,TwelveStatePresentation.future_rec,wordMass,ih]
    rw [(label_step i (w 0)).1,(label_step i (w 0)).2]
    simp only [Fin.cons_zero,Fin.tail_cons]

private theorem p_nonneg (a : Label) (x : Bool) : 0 ≤ p a x := by
  rcases a with ⟨b,s⟩
  cases b <;> fin_cases s <;> cases x <;> norm_num [p,prob,representative,rate]

private theorem p_total (a : Label) : ∑ x, p a x = 1 := by
  rcases a with ⟨b,s⟩
  cases b <;> fin_cases s <;> norm_num [p,prob,representative,rate,Fintype.sum_bool]

private theorem residue_endpoint (r : ℕ) (a b : Label) (w : Fin r → Bool) :
    (endpoint δ r a w).2 = (endpoint δ r b w).2 ↔ a.2 = b.2 := by
  induction r generalizing a b with
  | zero => rfl
  | succ r ih =>
    rw [endpoint,endpoint,ih]
    rcases a with ⟨ba,sa⟩
    rcases b with ⟨bb,sb⟩
    fin_cases sa <;> fin_cases sb <;> cases hx : w 0 <;> norm_num [δ,hx]

private theorem affinity_bound (r : ℕ) (i j : Hidden)
    (hij : (label i).2 ≠ (label j).2) :
    D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
      (futureMass marked i r) (futureMass marked j r) ≤ rho^(r/2) := by
  have htwo (a b : Label) (hab : a ≠ b) :
      D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
        (wordMass p δ 2 a) (wordMass p δ 2 b) ≤ rho := by
    have hr (a : Label) : label (representative a) = a := by
      rcases a with ⟨ba,sa⟩
      cases ba <;> fin_cases sa <;> norm_num [representative,label]
    have hh := actual_two_word_affinity (representative a) (representative b)
      (by rwa [hr,hr])
    have hl (i : Hidden) : futureMass marked i 2 = wordMass p δ 2 (label i) :=
      funext (label_word 2 i)
    simpa only [hl,hr,rho] using hh
  have hs := TwelveStateTail.specified_survival p δ p_nonneg p_total rho
    actual_explicit_tail.1 htwo r ⟨(label i,label j),fun he => hij (congrArg Prod.snd he)⟩
  have he : survivingAffinity p δ r ⟨(label i,label j),fun he => hij (congrArg Prod.snd he)⟩ =
      D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
        (futureMass marked i r) (futureMass marked j r) := by
    have hl (i : Hidden) : futureMass marked i r = wordMass p δ r (label i) :=
      funext (label_word r i)
    simp_rw [hl]
    unfold survivingAffinity D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
    apply Finset.sum_congr rfl
    intro w _
    have hn : endpoint δ r (label i) w ≠ endpoint δ r (label j) w :=
      fun hh => hij ((residue_endpoint r _ _ w).mp (congrArg Prod.snd hh))
    simp only [hn,ne_eq,not_false_eq_true,if_true]
  rwa [he] at hs

/-- The future target is Z1, the residue of the original hidden state at time one. -/
def residueTarget (z : Process) : Fin 3 := (label (z.1 1)).2

/-- Coordinates one through r, retaining the original emitted-bit clock. -/
def futureWord (r : ℕ) (z : Process) : Fin r → Bool := readPrefix r (future 1 z)

private theorem future_cell (r : ℕ) (w : Fin r → Bool) (a : Fin 3) :
    (cellMass (joint : Measure Process) residueTarget (futureWord r) w a).toReal =
      ∑ i : Hidden, if (label i).2 = a then mass i*futureMass marked i r w else 0 := by
  let E : Set Process := residueTarget ⁻¹' {a} ∩ futureWord r ⁻¹' {w}
  have hs := sum_measureReal_preimage_singleton
    (μ := (joint : Measure Process).restrict E) Finset.univ (f := state 1)
    (fun i _ => (measurableSet_singleton i).preimage (by unfold state; fun_prop))
  simp only [Finset.coe_univ,Set.preimage_univ,measureReal_restrict_apply_univ] at hs
  change (joint : Measure Process).real E = _
  rw [← hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [measureReal_restrict_apply ((measurableSet_singleton i).preimage (by unfold state; fun_prop))]
  by_cases hi : (label i).2 = a
  · rw [if_pos hi]
    have he : state 1 ⁻¹' {i} ∩ E = state 1 ⁻¹' {i} ∩
        (future 1 ⁻¹' (OriginalFutureScreening.readPrefix r ⁻¹' {w})) := by
      ext z
      simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,E]
      constructor
      · rintro ⟨hz,_,hw⟩
        exact ⟨hz,hw⟩
      · rintro ⟨hz,hw⟩
        have hz' : z.1 1 = i := hz
        exact ⟨hz,by simpa [residueTarget,hz'] using hi,hw⟩
    rw [he]
    exact future_state_mass parameter (joint : Measure Process)
      (same_law_trimming parameter).1 1 i r w
  · rw [if_neg hi]
    have he : state 1 ⁻¹' {i} ∩ E = ∅ := by
      ext z
      simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,E,Set.mem_empty_iff_false,iff_false,not_and]
      intro hz ha _
      have hz' : z.1 1 = i := hz
      exact hi (by simpa [residueTarget,hz'] using ha)
    rw [he,measureReal_empty]

/-- MAP for the fixed initial future residue, selected from actual J cell masses. -/
def residueMAP (r : ℕ) : (Fin r → Bool) → Fin 3 :=
  OriginalErasureComparison.mapClassifier (joint : Measure Process) residueTarget (futureWord r)

/-- The same original J has summable future-residue MAP errors and almost-sure eventual
correctness. The estimate concerns Z1 alone and makes no claim to recover the initial F/T phase. -/
theorem actual_future_residue_recovery :
    (∀ r : ℕ, (joint : Measure Process) {z | residueTarget z ≠ residueMAP r (futureWord r z)} ≤
      ENNReal.ofReal ((11/2 : ℝ)*rho^(r/2))) ∧
    (∀ᵐ z ∂(joint : Measure Process), ∀ᶠ r : ℕ in atTop,
      residueTarget z = residueMAP r (futureWord r z)) := by
  have hq : Measurable residueTarget :=
    (measurable_of_countable (fun i : Hidden => (label i).2)).comp
      ((measurable_pi_apply 1).comp measurable_fst)
  have hw (r : ℕ) : Measurable (futureWord r) := by unfold futureWord readPrefix future; fun_prop
  have hn (r : ℕ) (w : Fin r → Bool) (i : Hidden) :
      0 ≤ mass i*futureMass marked i r w := by
    rw [label_word]
    exact mul_nonneg (mass_pos i).le (UnifilarAffinityContraction.word_nonneg p δ p_nonneg r (label i) w)
  have hbound (r : ℕ) : (joint : Measure Process) {z | residueTarget z ≠ residueMAP r (futureWord r z)} ≤
      ENNReal.ofReal ((11/2 : ℝ)*rho^(r/2)) := by
    have herr := OriginalUnifilarQuotient.error_real_cells (joint : Measure Process)
      residueTarget (futureWord r) hq (hw r) (residueMAP r)
    have hm (w : Fin r → Bool) (a : Fin 3) := OriginalErasureComparison.mapClassifier_max
      (joint : Measure Process) residueTarget (futureWord r) w a
    have hb (w : Fin r → Bool) := grouped_map_pair_bound
      (fun i : Hidden => mass i*futureMass marked i r w) (hn r w)
      (fun i => (label i).2) (residueMAP r w) (fun a => by
        rw [← future_cell,← future_cell]
        exact ENNReal.toReal_mono (measure_ne_top _ _) (hm w a))
    have hreal : (joint : Measure Process).real {z | residueTarget z ≠ residueMAP r (futureWord r z)} ≤
        (11/2 : ℝ)*rho^(r/2) := by
      rw [herr]
      simp_rw [future_cell]
      have he (w : Fin r → Bool) : (∑ a : Fin 3, ∑ i : Hidden,
          if (label i).2 = a then mass i*futureMass marked i r w else 0) =
          ∑ i : Hidden, mass i*futureMass marked i r w := by rw [Finset.sum_comm]; simp
      simp_rw [he]
      apply le_trans (Finset.sum_le_sum fun w _ => hb w)
      rw [← Finset.sum_div,Finset.sum_comm]
      have hpair (i j : Hidden) :
          (∑ w : Fin r → Bool, if (label i).2 ≠ (label j).2 then
            Real.sqrt ((mass i*futureMass marked i r w)*(mass j*futureMass marked j r w)) else 0) ≤
          (if i ≠ j then Real.sqrt (mass i*mass j) else 0)*rho^(r/2) := by
        by_cases hij : (label i).2 = (label j).2
        · simp only [hij,ne_eq,not_true_eq_false,if_false,Finset.sum_const_zero]
          exact mul_nonneg (by split_ifs <;> positivity)
            (pow_nonneg actual_explicit_tail.1 _)
        · have hne : i ≠ j := fun he => hij (congrArg (fun i => (label i).2) he)
          simp only [hij,ne_eq,not_false_eq_true,if_true,hne]
          have he (w : Fin r → Bool) :
              Real.sqrt ((mass i*futureMass marked i r w)*(mass j*futureMass marked j r w)) =
              Real.sqrt (mass i*mass j)*Real.sqrt (futureMass marked i r w*futureMass marked j r w) := by
            rw [show (mass i*futureMass marked i r w)*(mass j*futureMass marked j r w) =
              (mass i*mass j)*(futureMass marked i r w*futureMass marked j r w) by ring,
              Real.sqrt_mul (mul_nonneg (mass_pos i).le (mass_pos j).le)]
          simp_rw [he]
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (affinity_bound r i j hij) (Real.sqrt_nonneg _)
      calc
        _ = (∑ i : Hidden, ∑ j : Hidden, ∑ w : Fin r → Bool,
            if (label i).2 ≠ (label j).2 then Real.sqrt
              ((mass i*futureMass marked i r w)*(mass j*futureMass marked j r w)) else 0)/2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ ≤ (∑ i : Hidden, ∑ j : Hidden,
            (if i ≠ j then Real.sqrt (mass i*mass j) else 0)*rho^(r/2))/2 :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => hpair i j) (by norm_num)
        _ = pairWeight mass*rho^(r/2) := by
          simp_rw [← Finset.sum_mul]
          unfold pairWeight
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by
            have hh := (pair_weight_bound mass (fun i => (mass_pos i).le) parameter.initial_sum).2.1
            norm_num only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hh
            linarith)
          (pow_nonneg actual_explicit_tail.1 _)
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (mul_nonneg (by norm_num) (pow_nonneg actual_explicit_tail.1 _))).mpr hreal
  refine ⟨hbound,?_⟩
  have hsum : (∑' r : ℕ, (joint : Measure Process)
      {z | residueTarget z ≠ residueMAP r (futureWord r z)}) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc
      _ ≤ ∑' r : ℕ, ENNReal.ofReal ((11/2 : ℝ)*rho^(r/2)) := ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal (∑' r : ℕ, (11/2 : ℝ)*rho^(r/2)) := by
        exact (ENNReal.ofReal_tsum_of_nonneg (fun r => mul_nonneg (by norm_num)
          (pow_nonneg actual_explicit_tail.1 _)) (by
            simpa using (OriginalUnifilarErasureTail.tail_series (11/2 : ℝ) rho
              (by norm_num) actual_explicit_tail.1 actual_explicit_tail.2.1 2 (by norm_num) 0).1)).symm
  simpa only [Set.mem_ofPred_eq,not_not] using ae_eventually_notMem hsum

#print axioms actual_future_residue_recovery
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateFutureRecovery

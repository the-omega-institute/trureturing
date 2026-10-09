/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HistoricalDepthBudgetJointExtremum
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HistoricalDepthBudgetJointExtremum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-history probability rows and depth-budget prefix codes have one attained iid joint extremum. -/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory Preorder ProbabilityTheory
open D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
open D5.S0.Computability.Coding.PrefixFreeCode
set_option maxRecDepth 3000

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HistoricalDepthBudgetJointExtremum

/-- Every full-history row is a normalized nonnegative real vector. -/
def NormalizedRows {A : Type*} [Fintype A] (q : List A → A → ℝ) : Prop :=
  (∀ v a, 0 ≤ q v a) ∧ ∀ v, ∑ a, q v a = 1

/-- The actual trajectory starts from the empty-history row and then reads its own full prefix. -/
noncomputable def trajectoryLaw {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (q : List A → A → ℝ) (hq : NormalizedRows q) : Measure (ℕ → A) := by
  classical
  let row (v : List A) : PMF A := PMF.ofFintype
    (fun a => ENNReal.ofReal (q v a)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hq.1 v a), hq.2 v]; simp)
  let ρ (v : List A) : Measure A := (row v).toMeasure
  let κ (n : ℕ) : Kernel (Iic n → A) A := Kernel.ofFunOfCountable
    (fun u => ρ (List.ofFn (fun i : Fin (n+1) => u ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩)))
  have hκ : ∀ n, IsMarkovKernel (κ n) := fun n =>
    ⟨fun u => inferInstanceAs (IsProbabilityMeasure (row _).toMeasure)⟩
  letI := hκ
  exact Kernel.trajMeasure (X := fun _ => A) (ρ []) κ

/-- The empty word specifies no coordinate. -/
def wordCylinder {A : Type*} (w : List A) : Set (ℕ → A) :=
  {x | ∀ i : Fin w.length, x i.1 = w.get i}

/-- The union of actual word cylinders. -/
def deletedSet {A : Type*} (F : Set (List A)) : Set (ℕ → A) :=
  ⋃ w ∈ F, wordCylinder w

/-- One distinguished letter carries all surplus above the common lower bound. -/
def extremalVector {A : Type*} [Fintype A] [DecidableEq A] (δ : ℝ) (a₀ : A) (a : A) : ℝ :=
  δ + (1 - (Fintype.card A : ℝ) * δ) * if a = a₀ then 1 else 0

/-- The joint surviving gap uses the real masses of these actual probability laws. -/
noncomputable def historicalGap {A : Type*} [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (δ : ℝ) (b : ℕ → ℕ) : ℝ :=
  1 - sSup {x : ℝ | ∃ (q : List A → A → ℝ) (hq : NormalizedRows q), (∀ v a, δ ≤ q v a) ∧
    ∃ (F : Set (List A)), Legal b F ∧ x = ((trajectoryLaw q hq) (deletedSet F)).toReal}

set_option maxHeartbeats 1000000 in
/-- Arbitrary full-history rows obey the finite iid maximum, and one fixed iid law and one
fixed infinite greedy code attain the joint supremum and the surviving gap. -/
theorem historical_depth_budget_joint_extremum {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (a₀ : A) (δ : ℝ) (hδ : 0 < δ) (hd : 2 ≤ Fintype.card A)
    (hδmax : δ ≤ 1 / (Fintype.card A : ℝ))
    (b : ℕ → ℕ) (tie : ℕ → LinearOrder (List A)) :
    let p := extremalVector δ a₀
    let G := greedyCode (fun n => priority p (tie n)) b
    Legal b G ∧
    (∀ (q : List A → A → ℝ) (hq : NormalizedRows q), IsProbabilityMeasure (trajectoryLaw q hq) ∧
      ∀ w, (trajectoryLaw q hq) (wordCylinder w) =
        ENNReal.ofReal (∏ i : Fin w.length, q (w.take i.1) (w.get i))) ∧
    (∀ (q : List A → A → ℝ) (hq : NormalizedRows q), (∀ v a, δ ≤ q v a) → ∀ (F : Set (List A)), Legal b F → ∀ N,
      (trajectoryLaw q hq) (deletedSet {w | w ∈ F ∧ w.length ≤ N}) ≤
        ENNReal.ofReal (truncatedMass p G N)) ∧
    ∃ hiid : NormalizedRows (fun _ => p),
      (∀ v a, δ ≤ (fun _ : List A => p) v a) ∧
      (∀ N, (trajectoryLaw (fun _ => p) hiid) (deletedSet {w | w ∈ G ∧ w.length ≤ N}) =
        ENNReal.ofReal (truncatedMass p G N)) ∧
      (trajectoryLaw (fun _ => p) hiid) (deletedSet G) = codeMass p G ∧
      IsGreatest {x : ℝ≥0∞ | ∃ (q : List A → A → ℝ) (hq : NormalizedRows q), (∀ v a, δ ≤ q v a) ∧
        ∃ (F : Set (List A)), Legal b F ∧ x = (trajectoryLaw q hq) (deletedSet F)} (codeMass p G) ∧
      IsGreatest {x : ℝ | ∃ (q : List A → A → ℝ) (hq : NormalizedRows q), (∀ v a, δ ≤ q v a) ∧
        ∃ (F : Set (List A)), Legal b F ∧ x = ((trajectoryLaw q hq) (deletedSet F)).toReal} (codeMass p G).toReal ∧
      historicalGap (A := A) δ b = 1 - (codeMass p G).toReal := by
  classical
  intro p G
  let m : (List A → A → ℝ) → List A → ℝ := fun r => fun w =>
    w.reverseRecOn (1 : ℝ) (fun v a t => t * r v a)
  have core
      (a₀ : A) (δ : ℝ) (hδ : 0 < δ) (hd : 2 ≤ Fintype.card A)
      (hδmax : δ ≤ 1 / (Fintype.card A : ℝ))
      (q : List A → A → ℝ) (hq : ∀ v a, δ ≤ q v a) (hsum : ∀ v, ∑ a, q v a = 1)
      (b : ℕ → ℕ) (tie : ℕ → LinearOrder (List A)) :
      let m : (List A → A → ℝ) → List A → ℝ := fun r => fun w =>
        w.reverseRecOn (1 : ℝ) (fun v a t => t * r v a)
      let p := fun a => δ + (1 - (Fintype.card A : ℝ) * δ) * if a = a₀ then 1 else 0
      let G := greedyCode (fun n => priority p (tie n)) b
      ∀ F, Legal b F → ∀ N, (∑ n ∈ Finset.range (N+1), ∑ w ∈ level F n, m q w) ≤ truncatedMass p G N := by
    classical
    intro m p G
    have bellman
        (a₀ : A) (δ : ℝ) (hδ : 0 ≤ δ) (hex : 0 ≤ 1 - (Fintype.card A : ℝ) * δ)
        (q : List A → A → ℝ) (hq : ∀ v a, δ ≤ q v a)
        (hs : ∀ v, ∑ a, q v a = 1) (H : Set (List A)) (N : ℕ) :
        let val : (List A → A → ℝ) → ℕ → List A → ℝ := by
          classical
          exact fun r => Nat.rec (fun v => if v ∈ H then 1 else 0)
            (fun _ prev v => if v ∈ H then 1 else ∑ a, r v a * prev (v ++ [a]))
        ∃ h : List A → A,
          let qh := fun v a => δ + (1 - (Fintype.card A : ℝ) * δ) * if a = h v then 1 else 0
          (∀ v a, δ ≤ qh v a) ∧ (∀ v, ∑ a, qh v a = 1) ∧
          val q N [] ≤ val qh N [] := by
      classical
      intro val
      let excess := 1 - (Fintype.card A : ℝ) * δ
      have pickmax (f : A → ℝ) : ∃ a, ∀ z, f z ≤ f a := by
        obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ f ⟨a₀, Finset.mem_univ _⟩
        exact ⟨a, fun z => ha z (Finset.mem_univ _)⟩
      let best (f : A → ℝ) := Classical.choose (pickmax f)
      have bestspec (f : A → ℝ) (a : A) : f a ≤ f (best f) := Classical.choose_spec (pickmax f) a
      let B : ℕ → List A → ℝ := Nat.rec (fun v => if v ∈ H then 1 else 0)
        (fun _ prev v => if v ∈ H then 1 else
          δ * ∑ a, prev (v ++ [a]) + excess * prev (v ++ [best (fun a => prev (v ++ [a]))]))
      let h (v : List A) := best (fun a => B (N - v.length - 1) (v ++ [a]))
      let qh (v : List A) (a : A) := δ + excess * if a = h v then 1 else 0
      have row_nonneg (v : List A) (a : A) : 0 ≤ q v a := hδ.trans (hq v a)
      have hhlo (v : List A) (a : A) : δ ≤ qh v a := by
        dsimp [qh]; split_ifs <;> nlinarith
      have hhsum (v : List A) : ∑ a, qh v a = 1 := by
        dsimp [qh]
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        dsimp [excess]; ring
      have row_bound (v : List A) (f : A → ℝ) :
          ∑ a, q v a * f a ≤ δ * ∑ a, f a + excess * f (best f) := by
        have yy (a : A) : 0 ≤ q v a - δ := sub_nonneg.mpr (hq v a)
        have he : ∑ a, (q v a - δ) = excess := by
          rw [Finset.sum_sub_distrib, hs]; simp [excess]
        calc
          ∑ a, q v a * f a = δ * ∑ a, f a + ∑ a, (q v a - δ) * f a := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro a _; ring
          _ ≤ δ * ∑ a, f a + ∑ a, (q v a - δ) * f (best f) := by
            apply add_le_add_right
            apply Finset.sum_le_sum
            intro a _
            exact mul_le_mul_of_nonneg_left (bestspec f a) (yy a)
          _ = δ * ∑ a, f a + excess * f (best f) := by rw [← Finset.sum_mul, he]
      have opt : ∀ k v, v.length + k = N → val q k v ≤ B k v ∧ val qh k v = B k v := by
        intro k
        induction k with
        | zero => intro v hv; exact ⟨le_rfl,rfl⟩
        | succ k ih =>
          intro v hv
          have child (a : A) := ih (v ++ [a]) (by simp only [List.length_append, List.length_singleton]; omega)
          have hk : N - v.length - 1 = k := by omega
          have hval : val q (k+1) v = if v ∈ H then 1 else ∑ a, q v a * val q k (v ++ [a]) := rfl
          have hqh : val qh (k+1) v = if v ∈ H then 1 else ∑ a, qh v a * val qh k (v ++ [a]) := rfl
          have hb : B (k+1) v = if v ∈ H then 1 else
              δ * ∑ a, B k (v ++ [a]) + excess * B k (v ++ [best (fun a => B k (v ++ [a]))]) := rfl
          rw [hval,hqh,hb]
          by_cases hm : v ∈ H
          · simp only [hm, if_true, le_refl, and_self]
          · simp only [hm, if_false]
            constructor
            · calc
                ∑ a, q v a * val q k (v ++ [a]) ≤ ∑ a, q v a * B k (v ++ [a]) := by
                  apply Finset.sum_le_sum; intro a _; exact mul_le_mul_of_nonneg_left (child a).1 (row_nonneg v a)
                _ ≤ _ := row_bound v (fun a => B k (v ++ [a]))
            · simp_rw [(child _).2]
              dsimp [qh]
              simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
              have hh : h v = best (fun a => B k (v ++ [a])) := by simp only [h, hk]
              rw [hh]
              simp [ite_mul, mul_ite]
      refine ⟨h, hhlo, hhsum, ?_⟩
      exact (opt N [] (by simp)).1.trans_eq (opt N [] (by simp)).2.symm
    have transport
        (δ : ℝ) (a₀ : A) (h : List A → A) (b : ℕ → ℕ) (F : Set (List A))
        (hF : Legal b F) :
        ∃ e : List A ≃ List A,
          (∀ v, (e v).length = v.length) ∧
          (∀ u v, e u <+: e v ↔ u <+: v) ∧ Legal b (e '' F) ∧
          (∀ v,
            v.reverseRecOn (1 : ℝ)
              (fun u a t => t * (δ + (1 - (Fintype.card A : ℝ) * δ) * if a = h u then 1 else 0))
            = wordMass (fun a => δ + (1 - (Fintype.card A : ℝ) * δ) * if a = a₀ then 1 else 0) (e v)) := by
      classical
      let π (v : List A) := Equiv.swap (h v) a₀
      let Φ (v : List A) : List A := v.reverseRecOn [] (fun u a t => t ++ [π u a])
      let Ψ (v : List A) : List A := v.reverseRecOn [] (fun _ a t => t ++ [(π t).symm a])
      have phiz : Φ [] = [] := by simp [Φ]
      have psiz : Ψ [] = [] := by simp [Ψ]
      have phis (v : List A) (a : A) : Φ (v ++ [a]) = Φ v ++ [π v a] := by simp [Φ]
      have psis (v : List A) (a : A) : Ψ (v ++ [a]) = Ψ v ++ [(π (Ψ v)).symm a] := by simp [Ψ]
      have left (v : List A) : Ψ (Φ v) = v := by
        induction v using List.reverseRecOn with
        | nil => rw [phiz, psiz]
        | append_singleton v a ih => rw [phis, psis, ih]; simp
      have right (v : List A) : Φ (Ψ v) = v := by
        induction v using List.reverseRecOn with
        | nil => rw [psiz, phiz]
        | append_singleton v a ih => rw [psis, phis, ih]; simp
      let e : List A ≃ List A := ⟨Φ, Ψ, left, right⟩
      have len (v : List A) : (Φ v).length = v.length := by
        induction v using List.reverseRecOn with
        | nil => simp [phiz]
        | append_singleton v a ih => simp only [phis, List.length_append, List.length_singleton, ih]
      have pref (f : List A → List A)
          (step : ∀ v a, ∃ z, f (v ++ [a]) = f v ++ [z])
          (u v : List A) (huv : u <+: v) : f u <+: f v := by
        obtain ⟨t, rfl⟩ := huv
        induction t using List.reverseRecOn with
        | nil => simp
        | append_singleton t a ih =>
          rw [← List.append_assoc]
          obtain ⟨z, hz⟩ := step (u ++ t) a
          rw [hz]
          exact ih.trans (List.prefix_append _ _)
      have epref (u v : List A) : Φ u <+: Φ v ↔ u <+: v := by
        constructor
        · intro hh
          simpa only [left] using pref Ψ (fun v a => ⟨_, psis v a⟩) _ _ hh
        · exact pref Φ (fun v a => ⟨_, phis v a⟩) u v
      have ml (H : Set (List A)) (v : List A) (n : ℕ) :
          v ∈ level H n ↔ v.length = n ∧ v ∈ H := by
        simp only [level, words, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨v, rfl⟩, hm⟩; exact ⟨v.2, hm⟩
        · rintro ⟨hv, hm⟩; exact ⟨⟨⟨v,hv⟩,rfl⟩,hm⟩
      have lev (n : ℕ) : level (e '' F) n = (level F n).image e := by
        ext v
        rw [ml, Finset.mem_image]
        constructor
        · rintro ⟨hl, u, hu, rfl⟩
          exact ⟨u, (ml _ _ _).mpr ⟨(len u).symm.trans hl,hu⟩,rfl⟩
        · rintro ⟨u, hu, rfl⟩
          obtain ⟨hl, hm⟩ := (ml _ _ _).mp hu
          exact ⟨(len u).trans hl,u,hm,rfl⟩
      refine ⟨e, len, epref, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ hp
          exact congrArg e (hF.1 hu hv ((epref u v).mp hp))
        · rintro ⟨u,hu,he⟩
          have hh : u = [] := List.length_eq_zero_iff.mp (by change Φ u = [] at he; rw [← len u, he]; rfl)
          exact hF.2.1 (hh ▸ hu)
        · intro n
          rw [lev, Finset.card_image_of_injective _ e.injective]
          exact hF.2.2 n
      · intro v
        induction v using List.reverseRecOn with
        | nil => simp [wordMass, phiz, e]
        | append_singleton v a ih =>
          change _ = wordMass _ (Φ (v ++ [a]))
          rw [List.reverseRecOn_concat, phis]
          simp only [wordMass, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one] at ih ⊢
          change _ = wordMass _ (Φ v) at ih
          rw [ih]
          congr 1
          have heq : π v a = a₀ ↔ a = h v := by
            constructor
            · intro hh
              apply (π v).injective
              simpa [π] using hh
            · rintro rfl; simp [π]
          simp only [heq]
    have finitecode
        (q : List A → A → ℝ) (m : List A → ℝ) (mz : m [] = 1)
        (ms : ∀ v a, m (v ++ [a]) = m v * q v a)
        (H : Finset (List A)) (hpf : IsPrefixFree (H : Set (List A)))
        (N : ℕ) (hN : ∀ w ∈ H, w.length ≤ N) :
        let val : ℕ → List A → ℝ :=
          fun n => Nat.rec (fun v => if v ∈ H then 1 else 0)
            (fun _ prev v => if v ∈ H then 1 else ∑ a, q v a * prev (v ++ [a])) n
        ∑ w ∈ H, m w = val N [] := by
      classical
      intro val
      let S (v : List A) := ∑ w ∈ H, if v <+: w then m w else 0
      have selected (v : List A) (hv : v ∈ H) : S v = m v := by
        dsimp only [S]
        rw [Finset.sum_eq_single v]
        · simp
        · intro w hw hne
          have hp : ¬ v <+: w := fun hh => hne (hpf hv hw hh).symm
          simp only [hp, if_false]
        · exact fun hn => (hn hv).elim
      have term (v : List A) (hv : v ∉ H) (hl : v.length = N) : S v = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        have hp : ¬ v <+: w := by
          intro hh
          have he := hh.eq_of_length_le (by rw [hl]; exact hN w hw)
          exact hv (he ▸ hw)
        simp only [hp, if_false]
      have branch (v : List A) (hv : v ∉ H) : S v = ∑ a, S (v ++ [a]) := by
        change (∑ w ∈ H, if v <+: w then m w else 0) =
          ∑ a, ∑ w ∈ H, if v ++ [a] <+: w then m w else 0
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hp : v <+: w
        · have hlt : v.length < w.length := by
            have hle := hp.length_le
            by_contra hn
            exact hv ((hp.eq_of_length (by omega)) ▸ hw)
          let c := w.get ⟨v.length,hlt⟩
          have hc : v ++ [c] <+: w := List.concat_get_prefix hp hlt
          have unique (a : A) : v ++ [a] <+: w ↔ a = c := by
            constructor
            · intro ha
              have he : v ++ [a] = v ++ [c] := by
                rcases List.prefix_or_prefix_of_prefix ha hc with hh | hh
                · exact hh.eq_of_length (by simp)
                · exact (hh.eq_of_length (by simp)).symm
              simpa using List.append_cancel_left he
            · rintro rfl; exact hc
          simp only [hp, if_true, unique]
          simp
        · have hpa (a : A) : ¬ v ++ [a] <+: w := fun hh => hp ((List.prefix_append _ _).trans hh)
          simp only [hp, hpa, if_false, Finset.sum_const_zero]
      have equals : ∀ k v, v.length + k = N → S v = m v * val k v := by
        intro k
        induction k with
        | zero =>
          intro v hv
          change S v = m v * (if v ∈ H then 1 else 0)
          by_cases hm : v ∈ H
          · simpa only [hm, if_true, mul_one] using selected v hm
          · simpa only [hm, if_false, mul_zero] using term v hm (by omega)
        | succ k ih =>
          intro v hv
          change S v = m v * (if v ∈ H then 1 else ∑ a, q v a * val k (v ++ [a]))
          by_cases hm : v ∈ H
          · simpa only [hm, if_true, mul_one] using selected v hm
          · simp only [hm, if_false]
            rw [branch v hm, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            rw [ih (v ++ [a]) (by simp only [List.length_append, List.length_singleton]; omega), ms]
            ring
      have hroot := equals N [] (by simp)
      simpa only [S, List.nil_prefix, if_true, mz, one_mul] using hroot
    have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
    have hex : 0 ≤ 1 - (Fintype.card A : ℝ) * δ := by
      have := (le_div_iff₀ hc).mp hδmax
      nlinarith
    have hp (a : A) : 0 < p a := by
      dsimp [p]; split_ifs <;> nlinarith
    have hp_sum : ∑ a, p a = 1 := by
      dsimp [p]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    obtain ⟨hG, hfinite, _⟩ := depth_budget_iid_greedy_optimality p hp hp_sum b tie
    change Legal b G at hG
    change ∀ N, IsGreatest _ (truncatedMass p G N) at hfinite
    have ml (H : Set (List A)) (v : List A) (n : ℕ) : v ∈ level H n ↔ v.length = n ∧ v ∈ H := by
      simp only [level, words, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨v, rfl⟩, hm⟩; exact ⟨v.2, hm⟩
      · rintro ⟨hv, hm⟩; exact ⟨⟨⟨v,hv⟩,rfl⟩,hm⟩
    have finite_sum (H : Finset (List A)) (N : ℕ) (hN : ∀ w ∈ H, w.length ≤ N) (f : List A → ℝ) :
        (∑ w ∈ H, f w) = ∑ n ∈ Finset.range (N+1), ∑ w ∈ level (H : Set (List A)) n, f w := by
      let T := (Finset.range (N+1)).biUnion (fun n => level (H : Set (List A)) n)
      have te : T = H := by
        ext w
        simp only [T, Finset.mem_biUnion, ml, Finset.mem_range, Finset.mem_coe]
        constructor
        · rintro ⟨n,_,_,hw⟩; exact hw
        · intro hw; exact ⟨w.length,by have := hN w hw; omega,rfl,hw⟩
      calc
        (∑ w ∈ H, f w) = ∑ w ∈ T, f w := by rw [te]
        _ = _ := Finset.sum_biUnion (f := f) (fun n hn k hk hne => Finset.disjoint_left.mpr (fun w hwn hwk =>
          hne (((ml _ _ _).mp hwn).1.symm.trans ((ml _ _ _).mp hwk).1)))
    intro F hF N
    let H := (Finset.range (N+1)).biUnion (fun n => level F n)
    have hm (w : List A) : w ∈ H ↔ w ∈ F ∧ w.length ≤ N := by
      simp only [H, Finset.mem_biUnion, ml, Finset.mem_range]
      constructor
      · rintro ⟨n,hn,hl,hw⟩; exact ⟨hw,by omega⟩
      · rintro ⟨hw,hl⟩; exact ⟨w.length,by omega,rfl,hw⟩
    have hN : ∀ w ∈ H, w.length ≤ N := fun w hw => ((hm w).mp hw).2
    have hH : Legal b (H : Set (List A)) := by
      refine ⟨fun _ hu _ hv hp => hF.1 ((hm _).mp hu).1 ((hm _).mp hv).1 hp,
        fun hn => hF.2.1 ((hm _).mp hn).1, fun n => ?_⟩
      apply (Finset.card_le_card ?_).trans (hF.2.2 n)
      intro w hw
      obtain ⟨hl,hwH⟩ := (ml _ _ _).mp hw
      exact (ml _ _ _).mpr ⟨hl, ((hm _).mp hwH).1⟩
    have hsumH (r : List A → A → ℝ) : (∑ w ∈ H, m r w) = ∑ n ∈ Finset.range (N+1), ∑ w ∈ level F n, m r w := by
      change (∑ w ∈ (Finset.range (N+1)).biUnion (fun n => level F n), m r w) = _
      exact Finset.sum_biUnion (fun n hn k hk hne => Finset.disjoint_left.mpr (fun w hwn hwk =>
        hne (((ml _ _ _).mp hwn).1.symm.trans ((ml _ _ _).mp hwk).1)))
    let val : (List A → A → ℝ) → ℕ → List A → ℝ := fun r => Nat.rec
      (fun v => if v ∈ (H : Set (List A)) then 1 else 0) (fun _ prev v => if v ∈ (H : Set (List A)) then 1 else ∑ a, r v a * prev (v ++ [a]))
    obtain ⟨h,hhlo,hhsum,hdom⟩ := bellman a₀ δ hδ.le hex q hq hsum (H : Set (List A)) N
    let qh := fun v a => δ + (1 - (Fintype.card A : ℝ) * δ) * if a = h v then 1 else 0
    have hdom' : val q N [] ≤ val qh N [] := by simpa only [val, Finset.mem_coe] using hdom
    obtain ⟨e,elen,epref,elegal,emass⟩ := transport δ a₀ h b (H : Set (List A)) hH
    have vals (r : List A → A → ℝ) : (∑ w ∈ H, m r w) = val r N [] :=
      by
        simpa only [val, Finset.mem_coe] using finitecode r (m r) (by simp [m]) (fun v a => by simp [m]) H hH.1 N hN
    let J := H.image e
    have jset : (J : Set (List A)) = e '' (H : Set (List A)) := by ext v; simp [J]
    have jlegal : Legal b (J : Set (List A)) := jset.symm ▸ elegal
    have jdepth : ∀ w ∈ J, w.length ≤ N := by
      rintro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      rw [elen]; exact hN v hv
    have je : (∑ w ∈ J, wordMass p w) = ∑ w ∈ H, m qh w := by
      rw [Finset.sum_image (fun _ _ _ _ he => e.injective he)]
      apply Finset.sum_congr rfl
      intro v _
      exact (emass v).symm
    have bound := (hfinite N).2 ⟨(J : Set (List A)),jlegal,jdepth,rfl⟩
    calc
      (∑ n ∈ Finset.range (N+1), ∑ w ∈ level F n, m q w) = ∑ w ∈ H, m q w := (hsumH q).symm
      _ = val q N [] := vals q
      _ ≤ val qh N [] := hdom'
      _ = ∑ w ∈ H, m qh w := (vals qh).symm
      _ = ∑ w ∈ J, wordMass p w := je.symm
      _ = truncatedMass p (J : Set (List A)) N := finite_sum J N jdepth (wordMass p)
      _ ≤ truncatedMass p G N := bound
  have codebridge
      (μ : Measure (ℕ → A)) (F : Set (List A)) (hF : IsPrefixFree F) :
      let C := fun w : List A => {x : ℕ → A | ∀ i : Fin w.length, x i.1 = w.get i}
      let U := fun H : Set (List A) => ⋃ w ∈ H, C w
      μ (U F) = ∑' w : F, μ (C w.1) ∧
      (∀ N, μ (U {w | w ∈ F ∧ w.length ≤ N}) =
        ∑ n ∈ Finset.range (N+1), ∑ w ∈ level F n, μ (C w)) ∧
      μ (U F) = ⨆ N, μ (U {w | w ∈ F ∧ w.length ≤ N}) := by
    classical
    intro C U
    have cm (w : List A) : MeasurableSet (C w) := by
      have each (i : Fin w.length) : MeasurableSet {x : ℕ → A | x i.1 = w.get i} :=
        (measurableSet_singleton (w.get i)).preimage (measurable_pi_apply i.1)
      convert MeasurableSet.iInter each using 1
      ext x; simp [C]
    have hd (H : Set (List A)) (hH : IsPrefixFree H) : H.PairwiseDisjoint C := by
      intro u hu v hv hne
      apply Set.disjoint_left.mpr
      intro x hx hy
      have pref (w z : List A) (hw : x ∈ C w) (hz : x ∈ C z) (hle : w.length ≤ z.length) : w <+: z := by
        apply List.prefix_iff_getElem.mpr
        refine ⟨hle, fun i hi => ?_⟩
        exact (hw ⟨i,hi⟩).symm.trans (hz ⟨i,hi.trans_le hle⟩)
      rcases le_total u.length v.length with hle | hle
      · exact hne (hH hu hv (pref u v hx hy hle))
      · exact hne (hH hv hu (pref v u hy hx hle)).symm
    have total := measure_biUnion (μ := μ) (Set.to_countable F) (hd F hF) (fun w _ => cm w)
    have ml (H : Set (List A)) (v : List A) (n : ℕ) : v ∈ level H n ↔ v.length = n ∧ v ∈ H := by
      simp only [level, words, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨v, rfl⟩, hm⟩; exact ⟨v.2, hm⟩
      · rintro ⟨hv, hm⟩; exact ⟨⟨⟨v,hv⟩,rfl⟩,hm⟩
    have finite (N : ℕ) : μ (U {w | w ∈ F ∧ w.length ≤ N}) =
        ∑ n ∈ Finset.range (N+1), ∑ w ∈ level F n, μ (C w) := by
      let T := (Finset.range (N+1)).biUnion (fun n => level F n)
      have tm (w : List A) : w ∈ T ↔ w ∈ F ∧ w.length ≤ N := by
        simp only [T, Finset.mem_biUnion, ml, Finset.mem_range]
        constructor
        · rintro ⟨n,hn,hl,hm⟩; exact ⟨hm,by omega⟩
        · rintro ⟨hm,hl⟩; exact ⟨w.length,by omega,rfl,hm⟩
      have te : (T : Set (List A)) = {w | w ∈ F ∧ w.length ≤ N} := by ext w; exact tm w
      have tpf : IsPrefixFree (T : Set (List A)) := fun _ hu _ hv hp => hF ((tm _).mp hu).1 ((tm _).mp hv).1 hp
      change μ (⋃ w ∈ {w | w ∈ F ∧ w.length ≤ N}, C w) = _
      rw [← te]
      change μ (⋃ w ∈ T, C w) = _
      rw [measure_biUnion_finset (μ := μ) (hd _ tpf) (fun w _=>cm w)]
      apply Finset.sum_biUnion
      intro n hn m hm hne
      apply Finset.disjoint_left.mpr
      intro w hwn hwm
      exact hne (((ml _ _ _).mp hwn).1.symm.trans ((ml _ _ _).mp hwm).1)
    have mono : Monotone (fun N => U {w | w ∈ F ∧ w.length ≤ N}) := by
      intro n m hnm x hx
      simp only [U, Set.mem_iUnion] at hx ⊢
      obtain ⟨w, ⟨hw,hn⟩,hx⟩ := hx
      exact ⟨w,⟨hw,hn.trans hnm⟩,hx⟩
    have unions : (⋃ N, U {w | w ∈ F ∧ w.length ≤ N}) = U F := by
      ext x
      simp only [U, Set.mem_iUnion]
      constructor
      · rintro ⟨N,w,⟨hw,_⟩,hx⟩; exact ⟨w,hw,hx⟩
      · rintro ⟨w,hw,hx⟩; exact ⟨w.length,w,⟨hw,le_rfl⟩,hx⟩
    exact ⟨total, finite, unions ▸ mono.measure_iUnion⟩
  have lawmass (q : List A → A → ℝ) (hqr : NormalizedRows q) :
      IsProbabilityMeasure (trajectoryLaw q hqr) ∧
      ∀ w, (trajectoryLaw q hqr) (wordCylinder w) = ENNReal.ofReal (m q w) := by
    have hq := hqr.1
    have hsum := hqr.2
    let row (v : List A) : PMF A := PMF.ofFintype
      (fun a => ENNReal.ofReal (q v a)) (by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hq v a), hsum v]; simp)
    let ρ (v : List A) : Measure A := (row v).toMeasure
    let κ (n : ℕ) : Kernel (Iic n → A) A := Kernel.ofFunOfCountable
      (fun u => ρ (List.ofFn (fun i : Fin (n+1) => u ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩)))
    have hκ : ∀ n, IsMarkovKernel (κ n) := fun n => ⟨fun u => inferInstanceAs (IsProbabilityMeasure (row _).toMeasure)⟩
    letI := hκ
    letI : IsProbabilityMeasure (ρ []) := inferInstanceAs (IsProbabilityMeasure (row []).toMeasure)
    let μ := Kernel.trajMeasure (X := fun _ => A) (ρ []) κ
    let C (w : List A) := {x : ℕ → A | ∀ i : Fin w.length, x i.1 = w.get i}
    have hρ (v : List A) (a : A) : ρ v {a} = ENNReal.ofReal (q v a) :=
      PMF.toMeasure_apply_singleton (row v) a (measurableSet_singleton a)
    have hrow (n : ℕ) (u : Iic n → A) (a : A) : κ n u {a} = ENNReal.ofReal
        (q (List.ofFn (fun i : Fin (n+1) => u ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩)) a) := hρ _ a
    have root : μ.map (frestrictLe 0) = (ρ []).map (MeasurableEquiv.piUnique (fun _ : Iic 0 => A)).symm := by
      change (Kernel.trajMeasure (X := fun _=>A) (ρ []) κ).map (frestrictLe 0) = _
      rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe _),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
    have step (n : ℕ) (u : Iic n → A) (a : A) :
        μ {x | frestrictLe n x = u ∧ x (n+1) = a} =
        μ {x | frestrictLe n x = u} * ENNReal.ofReal
          (q (List.ofFn (fun i : Fin (n+1) => u ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩)) a) := by
      have hprod := Measure.compProd_apply_prod (μ := μ.map (frestrictLe n)) (κ := κ n)
        (measurableSet_singleton u) (measurableSet_singleton a)
      rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
        Measure.map_apply (by fun_prop) (MeasurableSet.prod (measurableSet_singleton u) (measurableSet_singleton a)),
        lintegral_singleton, hrow, Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton u), mul_comm] at hprod
      exact hprod
    have cz : C [] = Set.univ := by ext x; simp [C]
    have cs (v : List A) (a : A) : C (v ++ [a]) = {x | x ∈ C v ∧ x v.length = a} := by
      ext x
      constructor
      · intro hx
        refine ⟨fun i => ?_, ?_⟩
        · have hh := hx ⟨i.1, by simp⟩
          simpa [List.get_eq_getElem, List.getElem_append_left] using hh
        · have hh := hx ⟨v.length, by simp⟩
          simpa [List.get_eq_getElem] using hh
      · rintro ⟨hx, ha⟩ i
        by_cases hi : i.1 < v.length
        · simpa [List.get_eq_getElem, List.getElem_append_left, hi] using hx ⟨i.1, hi⟩
        · have hi' : i.1 = v.length := by
            have hbound : i.1 < v.length + 1 := by simpa only [List.length_append, List.length_singleton] using i.2
            omega
          simpa [List.get_eq_getElem, hi'] using ha
    have recurrence (v : List A) (a : A) : μ (C (v ++ [a])) = μ (C v) * ENNReal.ofReal (q v a) := by
      by_cases hz : v = []
      · subst v
        have he : C [a] = (frestrictLe (π := fun _ => A) 0) ⁻¹' {((MeasurableEquiv.piUnique (fun _ : Iic 0 => A)).symm a : Iic 0 → A)} := by
          ext x
          simp only [C, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
          constructor
          · intro hh i
            have hh0 := hh ⟨0, by simp⟩
            have hi : i.1 = 0 := by have := i.2; simp only [mem_Iic] at this; omega
            simpa [frestrictLe, hi, MeasurableEquiv.piUnique, Equiv.piUnique] using hh0
          · intro hh i
            have hh0 := hh ⟨0, by simp⟩
            have hi : i.1 = 0 := by
              have hbound : i.1 < 1 := by simpa only [List.length_singleton] using i.2
              omega
            simpa [frestrictLe, hi, MeasurableEquiv.piUnique, Equiv.piUnique] using hh0
        change μ (C [a]) = μ (C []) * ENNReal.ofReal (q [] a)
        rw [he, ← Measure.map_apply (measurable_frestrictLe 0) (measurableSet_singleton _), root,
          Measure.map_apply (MeasurableEquiv.measurable _) (measurableSet_singleton _)]
        have hp : (MeasurableEquiv.piUnique (fun _ : Iic 0 => A)).symm ⁻¹'
          {((MeasurableEquiv.piUnique (fun _ : Iic 0 => A)).symm a : Iic 0 → A)} = {a} :=
          by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            exact (MeasurableEquiv.piUnique (fun _ : Iic 0 => A)).symm.injective.eq_iff
        rw [hp,hρ,cz]; simp
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (fun hh => hz (List.length_eq_zero_iff.mp hh))
        let u : Iic n → A := fun i => v.get ⟨i.1, by have := mem_Iic.mp i.2; omega⟩
        have hc : C v = {x | frestrictLe n x = u} := by
          ext x
          constructor
          · intro hx; funext i; exact hx ⟨i.1, by have := mem_Iic.mp i.2; omega⟩
          · intro hx i
            exact congrFun hx ⟨i.1, mem_Iic.mpr (by have := i.2; omega)⟩
        have hu : List.ofFn (fun i : Fin (n+1) => u ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩) = v := by
          apply List.ext_getElem
          · simp [hn]
          · intro i hi hj
            simp only [List.getElem_ofFn]
            rfl
        rw [cs,hc,hn]
        simpa only [hu, Set.mem_ofPred_eq] using step n u a
    have actual : trajectoryLaw q hqr = μ := rfl
    have product (w : List A) : μ (C w) = w.reverseRecOn (1 : ℝ≥0∞)
        (fun v a t => t * ENNReal.ofReal (q v a)) := by
      induction w using List.reverseRecOn with
      | nil => simpa only [cz, List.reverseRecOn_nil] using (measure_univ : μ Set.univ = 1)
      | append_singleton v a ih => rw [recurrence, ih, List.reverseRecOn_concat]
    have conversion (w : List A) : w.reverseRecOn (1 : ℝ≥0∞)
        (fun v a t => t * ENNReal.ofReal (q v a)) = ENNReal.ofReal (m q w) := by
      induction w using List.reverseRecOn with
      | nil => simp [m]
      | append_singleton v a ih =>
        simp only [List.reverseRecOn_concat]
        rw [ih]
        simp only [m, List.reverseRecOn_concat, ENNReal.ofReal_mul' (hq v a)]
    refine ⟨actual.symm ▸ inferInstance, fun w => ?_⟩
    rw [actual]
    exact (product w).trans (conversion w)
  have mnonneg (q : List A → A → ℝ) (hq : ∀ v a, 0 ≤ q v a) (w : List A) : 0 ≤ m q w := by
    induction w using List.reverseRecOn with
    | nil => simp [m]
    | append_singleton v a ih => simpa only [m, List.reverseRecOn_concat] using mul_nonneg ih (hq v a)
  have mproduct (q : List A → A → ℝ) (w : List A) :
      m q w = ∏ i : Fin w.length, q (w.take i.1) (w.get i) := by
    induction w using List.reverseRecOn with
    | nil => simp [m]
    | append_singleton v a ih =>
      have array : List.ofFn (fun i : Fin (v ++ [a]).length =>
          q ((v ++ [a]).take i.1) ((v ++ [a]).get i)) =
          List.ofFn (fun i : Fin v.length => q (v.take i.1) (v.get i)) ++ [q v a] := by
        apply List.ext_getElem
        · simp only [List.length_ofFn, List.length_append, List.length_singleton]
        · intro i hi hj
          by_cases hil : i < v.length
          · simp only [List.getElem_ofFn, List.get_eq_getElem]
            rw [List.take_append_of_le_length hil.le, List.getElem_append_left hil]
            rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hil)]
            simp only [List.getElem_ofFn, List.get_eq_getElem]
          · have he : i = v.length := by
              simp only [List.length_ofFn, List.length_append, List.length_singleton] at hi
              omega
            subst i
            simp only [List.getElem_ofFn, List.get_eq_getElem, List.take_append_length]
            rw [List.getElem_append_right (Nat.le_refl v.length)]
            rw [List.getElem_append_right (by simp only [List.length_ofFn]; exact le_rfl)]
            simp only [List.length_ofFn, Nat.sub_self, List.getElem_cons_zero]
      rw [← List.prod_ofFn, array]
      simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, List.prod_ofFn]
      simpa only [m, List.reverseRecOn_concat] using congrArg (fun t => t * q v a) ih
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hex : 0 ≤ 1 - (Fintype.card A : ℝ) * δ := by
    have := (le_div_iff₀ hc).mp hδmax
    nlinarith
  have hp (a : A) : 0 < p a := by dsimp [p,extremalVector]; split_ifs <;> nlinarith
  have hplo (a : A) : δ ≤ p a := by dsimp [p,extremalVector]; split_ifs <;> nlinarith
  have hpsum : ∑ a, p a = 1 := by
    dsimp [p,extremalVector]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  obtain ⟨hG,_,_⟩ := depth_budget_iid_greedy_optimality p hp hpsum b tie
  change Legal b G at hG
  let hiid : NormalizedRows (fun _ : List A => p) := ⟨fun _ a => (hp a).le,fun _ => hpsum⟩
  let ν := trajectoryLaw (fun _ : List A => p) hiid
  have νprob : IsProbabilityMeasure ν := (lawmass _ hiid).1
  letI := νprob
  have iidmass (w : List A) : m (fun _ : List A => p) w = wordMass p w := by
    induction w using List.reverseRecOn with
    | nil => simp [m,wordMass]
    | append_singleton v a ih => simpa only [m,wordMass,List.reverseRecOn_concat,List.map_append,
        List.map_cons,List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,mul_one] using congrArg (fun t => t * p a) ih
  have finite_conversion (q : List A → A → ℝ) (hq : NormalizedRows q) (F : Set (List A))
      (hF : IsPrefixFree F) (N : ℕ) :
      (trajectoryLaw q hq) (deletedSet {w | w ∈ F ∧ w.length ≤ N}) =
        ENNReal.ofReal (∑ n ∈ Finset.range (N+1), ∑ w ∈ level F n, m q w) := by
    have cb := (codebridge (trajectoryLaw q hq) F hF).2.1 N
    change (trajectoryLaw q hq) (deletedSet {w | w ∈ F ∧ w.length ≤ N}) =
      ∑ n ∈ Finset.range (N+1), ∑ w ∈ level F n, (trajectoryLaw q hq) (wordCylinder w) at cb
    rw [cb]
    simp_rw [(lawmass q hq).2]
    have inner (n : ℕ) : (∑ w ∈ level F n, ENNReal.ofReal (m q w)) =
        ENNReal.ofReal (∑ w ∈ level F n, m q w) :=
      (ENNReal.ofReal_sum_of_nonneg (fun w _ => mnonneg q hq.1 w)).symm
    simp_rw [inner]
    exact (ENNReal.ofReal_sum_of_nonneg (fun n _ => Finset.sum_nonneg (fun w _ => mnonneg q hq.1 w))).symm
  have upper (q : List A → A → ℝ) (hq : NormalizedRows q) (hlo : ∀ v a, δ ≤ q v a)
      (F : Set (List A)) (hF : Legal b F) (N : ℕ) :
      (trajectoryLaw q hq) (deletedSet {w | w ∈ F ∧ w.length ≤ N}) ≤ ENNReal.ofReal (truncatedMass p G N) := by
    rw [finite_conversion q hq F hF.1 N]
    exact ENNReal.ofReal_le_ofReal (core a₀ δ hδ hd hδmax q hlo hq.2 b tie F hF N)
  have iidfinite (F : Set (List A)) (hF : IsPrefixFree F) (N : ℕ) :
      ν (deletedSet {w | w ∈ F ∧ w.length ≤ N}) = ENNReal.ofReal (truncatedMass p F N) := by
    rw [finite_conversion _ hiid F hF N]
    simp_rw [iidmass]
    rfl
  have iidtotal (F : Set (List A)) (hF : IsPrefixFree F) : ν (deletedSet F) = codeMass p F := by
    have cb := (codebridge ν F hF).1
    change ν (deletedSet F) = _ at cb
    rw [cb]
    apply tsum_congr
    intro w
    exact ((lawmass _ hiid).2 w).trans (congrArg ENNReal.ofReal (iidmass w))
  have totalupper (q : List A → A → ℝ) (hq : NormalizedRows q) (hlo : ∀ v a, δ ≤ q v a)
      (F : Set (List A)) (hF : Legal b F) : (trajectoryLaw q hq) (deletedSet F) ≤ codeMass p G := by
    rw [← iidtotal G hG.1]
    have hqUnion := (codebridge (trajectoryLaw q hq) F hF.1).2.2
    have hgUnion := (codebridge ν G hG.1).2.2
    change (trajectoryLaw q hq) (deletedSet F) =
      ⨆ N, (trajectoryLaw q hq) (deletedSet {w | w ∈ F ∧ w.length ≤ N}) at hqUnion
    change ν (deletedSet G) = ⨆ N, ν (deletedSet {w | w ∈ G ∧ w.length ≤ N}) at hgUnion
    rw [hqUnion,hgUnion]
    apply iSup_mono
    intro N
    exact (upper q hq hlo F hF N).trans_eq (iidfinite G hG.1 N).symm
  have joint : IsGreatest {x : ℝ≥0∞ | ∃ (q : List A → A → ℝ) (hq : NormalizedRows q), (∀ v a, δ ≤ q v a) ∧
      ∃ (F : Set (List A)), Legal b F ∧ x = (trajectoryLaw q hq) (deletedSet F)} (codeMass p G) := by
    refine ⟨⟨(fun _ => p),hiid,(fun _ a=>hplo a),G,hG,(iidtotal G hG.1).symm⟩,?_⟩
    rintro x ⟨q,hq,hlo,F,hF,rfl⟩
    exact totalupper q hq hlo F hF
  have realjoint : IsGreatest {x : ℝ | ∃ (q : List A → A → ℝ) (hq : NormalizedRows q), (∀ v a, δ ≤ q v a) ∧
      ∃ (F : Set (List A)), Legal b F ∧ x = ((trajectoryLaw q hq) (deletedSet F)).toReal} (codeMass p G).toReal := by
    refine ⟨⟨(fun _ => p),hiid,(fun _ a=>hplo a),G,hG,congrArg ENNReal.toReal (iidtotal G hG.1).symm⟩,?_⟩
    rintro x ⟨q,hq,hlo,F,hF,rfl⟩
    apply ENNReal.toReal_mono _ (totalupper q hq hlo F hF)
    rw [← iidtotal G hG.1]
    exact measure_ne_top ν _
  refine ⟨hG,?_,?_,hiid,(fun _ a=>hplo a),(iidfinite G hG.1),iidtotal G hG.1,joint,realjoint,?_⟩
  · intro q hq
    refine ⟨(lawmass q hq).1,fun w => ?_⟩
    exact ((lawmass q hq).2 w).trans (congrArg ENNReal.ofReal (mproduct q w))
  · exact upper
  · unfold historicalGap
    rw [realjoint.csSup_eq]

#print axioms historical_depth_budget_joint_extremum

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HistoricalDepthBudgetJointExtremum

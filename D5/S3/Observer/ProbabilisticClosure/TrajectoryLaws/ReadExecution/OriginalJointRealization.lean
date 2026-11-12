/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite joint operations admit common fresh tables on the actual source product. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalObserverNormalization
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalHistoryLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalRenewalLaws

/-! Original joint stochastic operations and their common fresh innovation realization. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalJointRealization
open OriginalObserverNormalization ActualRenewalPrefixLaw

section Product
variable {I S R : Type*} [MeasurableSpace I] [MeasurableSpace S] [MeasurableSpace R]
    (κ : Measure I) (ρ : Measure R) [IsProbabilityMeasure κ] [IsProbabilityMeasure ρ]

private theorem finite_coordinates (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ρ)).map
      (fun z => fun j : Fin n => z j.val) = Measure.pi (fun _ : Fin n => ρ) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Fin.ext h),
    Measure.infinitePi_eq_pi]

private theorem separated_blocks (l r : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ρ)).map
      (fun z => (fun j : Fin l => z j.val, fun j : Fin r => z (l + j.val))) =
      (Measure.pi fun _ : Fin l => ρ).prod (Measure.pi fun _ : Fin r => ρ) := by
  apply (Measure.prod_eq fun D B hD hB => ?_).symm
  rw [Measure.map_apply (by fun_prop) (hD.prod hB)]
  have he : (fun z : ℕ → R =>
      (fun j : Fin l => z j.val, fun j : Fin r => z (l + j.val))) ⁻¹' (D ×ˢ B) =
      (fun z => fun j : Fin l => z j.val) ⁻¹' D ∩
        FreshServiceRestart.shift l ⁻¹'
          ((fun z : ℕ → R => fun j : Fin r => z j.val) ⁻¹' B) := by
    ext z
    simp [FreshServiceRestart.shift, Nat.add_comm]
  rw [he, FreshServiceRestart.prefix_suffix_independent ρ l D hD _
    (hB.preimage (by fun_prop)),
    ← Measure.map_apply (by fun_prop) hD, finite_coordinates,
    ← Measure.map_apply (by fun_prop) hB, finite_coordinates]

private theorem seed_blocks (initial : I → S) (h : Measurable initial) (l r : ℕ) :
    (κ.prod (Measure.infinitePi (fun _ : ℕ => ρ))).map
      (fun p => ((initial p.1, fun j : Fin l => p.2 j.val),
        fun j : Fin r => p.2 (l + j.val))) =
      ((κ.map initial).prod (Measure.pi fun _ : Fin l => ρ)).prod
        (Measure.pi fun _ : Fin r => ρ) := by
  have he : (fun p : I × (ℕ → R) =>
      ((initial p.1, fun j : Fin l => p.2 j.val), fun j : Fin r => p.2 (l + j.val))) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map initial
        (fun z : ℕ → R => (fun j : Fin l => z j.val,
          fun j : Fin r => z (l + j.val))) := rfl
  rw [he, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
    ← Measure.map_prod_map _ _ h (by fun_prop), separated_blocks,
    ← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]

/-- The source coordinates and all observer randomness inhabit one product.
    The initial map is chosen independently of the source label. -/
def productLaw (w f : PMF ℕ) : Measure ((ℕ × (ℕ → ℕ)) × (I × (ℕ → R))) :=
  (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)).prod
    (κ.prod (Measure.infinitePi fun _ : ℕ => ρ))

private theorem product_primitive (initial : I → S) (h : Measurable initial)
    (w f : PMF ℕ) :
    Primitive (productLaw κ ρ w f) (fun ω => initial ω.2.1)
      (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2.2) (κ.map initial) w f ρ := by
  intro n a l r D B hD hB
  let G : Set (ℕ × (ℕ → ℕ)) :=
    {g | g.1 = a.1 ∧ ∀ j : Fin n, g.2 j.val = a.2 j}
  let E : Set (I × (ℕ → R)) :=
    (fun p => ((initial p.1, fun j : Fin l => p.2 j.val),
      fun j : Fin r => p.2 (l + j.val))) ⁻¹' (D ×ˢ B)
  have he : sourceSlice (fun ω : (ℕ × (ℕ → ℕ)) × (I × (ℕ → R)) => ω.1.1)
      (fun ω => ω.1.2) n a ∩
      rawPrefix (fun ω => initial ω.2.1) (fun ω => ω.2.2) l ⁻¹' D ∩
      rawBlock (fun ω => ω.2.2) l r ⁻¹' B = G ×ˢ E := by
    ext ω
    change (((ω.1.1 = a.1 ∧ ∀ j : Fin n, ω.1.2 j.val = a.2 j) ∧
      (initial ω.2.1, fun j : Fin l => ω.2.2 j.val) ∈ D) ∧
      (fun j : Fin r => ω.2.2 (l + j.val)) ∈ B) ↔ _
    simp only [G, E, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_preimage]
    tauto
  rw [he, productLaw, Measure.prod_prod]
  have hG : (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)) G =
      w a.1 * ∏ j, f (a.2 j) := by
    have hGset : G = {a.1} ×ˢ
        ((fun z : ℕ → ℕ => fun j : Fin n => z j.val) ⁻¹' {a.2}) := by
      ext g
      simp [G, funext_iff]
    rw [hGset, Measure.prod_prod,
      ← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      finite_coordinates f.toMeasure,
      Measure.pi_singleton]
    simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have hE : (κ.prod (Measure.infinitePi fun _ : ℕ => ρ)) E =
      ((κ.map initial).prod (Measure.pi fun _ : Fin l => ρ)) D *
        (Measure.pi fun _ : Fin r => ρ) B := by
    dsimp only [E]
    rw [← Measure.map_apply (by fun_prop) (hD.prod hB), seed_blocks κ ρ initial h,
      Measure.prod_prod]
  simp only [hG, hE, mul_assoc]

end Product

namespace Stochastic
variable (O : Stochastic C)
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

private theorem infinite_execution_law (source : ℕ → Bool) (n : ℕ) :
    (O.seedLaw.prod (Measure.infinitePi fun _ : ℕ => O.innovationLaw)).map
      (fun p => O.develop source p.1 n (fun j => p.2 j.val)) =
        (O.executionLaw source n).toMeasure := by
  have he : (fun p : O.Outcome × (ℕ → O.Innovation) =>
      O.develop source p.1 n (fun j => p.2 j.val)) =
      (fun p => O.develop source p.1 n p.2) ∘
        Prod.map id (fun z : ℕ → O.Innovation => fun j : Fin n => z j.val) := rfl
  rw [he, ← Measure.map_map (measurable_of_countable _) (by fun_prop),
    ← Measure.map_prod_map _ _ measurable_id (by fun_prop),
    Measure.map_id, finite_coordinates, O.finite_execution_law]

private theorem develop_actions (seed : O.Outcome) (coins : ℕ → O.Innovation)
    (u : ℕ) (K : ℕ → ℕ) (n : ℕ) (j : Fin (n + 1)) :
    (O.develop (ActualRenewalStopping.sourceBit u K) seed n (fun t => coins t.val) j).2 =
      (O.machine.execute seed (ActualRenewalStopping.sourceBit u K) coins j.val).action := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [develop, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
      have hi := ih (Fin.last n)
      cases ha : (O.machine.execute seed (ActualRenewalStopping.sourceBit u K) coins n).action with
      | emit c d hd =>
        have hh : (O.develop (ActualRenewalStopping.sourceBit u K) seed n
            (fun t => coins t.val) (Fin.last n)).2 = Action.emit c d hd := hi.trans ha
        simp only [advance, hh, Machine.execute, ha]
        rfl
      | read c =>
        have hh : (O.develop (ActualRenewalStopping.sourceBit u K) seed n
            (fun t => coins t.val) (Fin.last n)).2 = Action.read c := hi.trans ha
        have hlen := (O.machine.execution_normalization seed coins u K n).2.2
          (by simp only [ha, Action.output])
        simp only [advance, hh, Machine.execute, ha, hlen]
        rfl
    · simpa only [develop, Fin.snoc_castSucc, Fin.val_castSucc] using ih k

private theorem source_bit_measurable (t : ℕ) :
    Measurable (fun g : ℕ × (ℕ → ℕ) => ActualRenewalStopping.sourceBit g.1 g.2 t) := by
  have hc (j : ℕ) : Measurable (fun g : ℕ × (ℕ → ℕ) =>
      ActualRenewalStopping.clock g.1 g.2 j) := by
    induction j with
    | zero => exact measurable_fst.add_const 1
    | succ j ih => exact (ih.add ((measurable_pi_apply j).comp measurable_snd)).add_const 1
  have hs : MeasurableSet {g : ℕ × (ℕ → ℕ) |
      ∃ j ∈ Finset.range (t + 1), ActualRenewalStopping.clock g.1 g.2 j = t + 1} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    by_cases hj : j ∈ Finset.range (t + 1)
    · simpa only [hj, true_and, Set.preimage, Set.mem_singleton_iff] using (hc j) (measurableSet_singleton (t + 1))
    · simp only [hj, false_and, Set.ofPred_false, MeasurableSet.empty]
  convert (measurable_const.ite hs measurable_const : Measurable
    (fun g : ℕ × (ℕ → ℕ) => if ∃ j ∈ Finset.range (t + 1),
      ActualRenewalStopping.clock g.1 g.2 j = t + 1 then true else false)) using 1
  funext g
  by_cases h : ∃ j ∈ Finset.range (t + 1),
      ActualRenewalStopping.clock g.1 g.2 j = t + 1 <;>
    simp [ActualRenewalStopping.sourceBit, h]

private theorem parameterized_develop_measurable {G : Type*} [MeasurableSpace G]
    (bits : G → ℕ → Bool) (hb : ∀ t, Measurable (fun g => bits g t)) (n : ℕ) :
    Measurable (fun p : G × (O.Outcome × (ℕ → O.Innovation)) =>
      O.develop (bits p.1) p.2.1 n (fun j => p.2.2 j.val)) := by
  induction n with
  | zero =>
    exact (measurable_of_countable (fun seed : O.Outcome => fun _ : Fin 1 => seed)).comp
      (measurable_fst.comp measurable_snd)
  | succ n ih =>
    have hm : Measurable (fun p : (Fin (n + 1) → O.Outcome) × Bool × O.Innovation =>
        (Fin.snoc p.1 (O.advance (p.1 (Fin.last n)) p.2.1 p.2.2) :
          Fin (n + 2) → O.Outcome)) := measurable_of_countable _
    convert hm.comp (ih.prodMk (((hb n).comp measurable_fst).prodMk
      ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd)))) using 1
    funext p
    simp only [develop, Fin.val_castSucc, Fin.val_last, Function.comp_apply]

private theorem joint_execution_cylinder (w f : PMF ℕ) (n : ℕ)
    (D : Set (ℕ × (ℕ → ℕ))) (hD : MeasurableSet D)
    (B : Set (Fin (n + 1) → O.Outcome)) (hB : MeasurableSet B) :
    productLaw O.seedLaw O.innovationLaw w f
      {ω | ω.1 ∈ D ∧ O.develop (ActualRenewalStopping.sourceBit ω.1.1 ω.1.2)
        ω.2.1 n (fun j => ω.2.2 j.val) ∈ B} =
      ∫⁻ g, (if g ∈ D then
        (O.executionLaw (ActualRenewalStopping.sourceBit g.1 g.2) n).toMeasure B else 0)
        ∂(w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)) := by
  have hm := O.parameterized_develop_measurable
    (fun g : ℕ × (ℕ → ℕ) => ActualRenewalStopping.sourceBit g.1 g.2)
    source_bit_measurable n
  have hE : MeasurableSet {ω : (ℕ × (ℕ → ℕ)) × (O.Outcome × (ℕ → O.Innovation)) |
      ω.1 ∈ D ∧ O.develop (ActualRenewalStopping.sourceBit ω.1.1 ω.1.2)
        ω.2.1 n (fun j => ω.2.2 j.val) ∈ B} :=
    (hD.preimage measurable_fst).inter (hB.preimage hm)
  rw [productLaw, Measure.prod_apply hE]
  apply lintegral_congr
  intro g
  by_cases hg : g ∈ D
  · simp only [hg, ↓reduceIte, Set.preimage_ofPred_eq, true_and]
    have hmg : Measurable (fun p : O.Outcome × (ℕ → O.Innovation) =>
        O.develop (ActualRenewalStopping.sourceBit g.1 g.2) p.1 n (fun j => p.2 j.val)) :=
      hm.comp (measurable_const.prodMk measurable_id)
    have hL := congrArg (fun μ : Measure (Fin (n + 1) → O.Outcome) => μ B)
      (O.infinite_execution_law (ActualRenewalStopping.sourceBit g.1 g.2) n)
    rw [Measure.map_apply hmg hB] at hL
    exact hL
  · simp only [hg, ↓reduceIte, Set.preimage_ofPred_eq, false_and,
      Set.ofPred_false, measure_empty]

/-- A finite original trace records its first emission without an external
    decoder. Every earlier action is a paid read. -/
def emissionCylinder (n : ℕ) (d : Bool) : Set (Fin (n + 1) → O.Outcome) :=
  {x | (x (Fin.last n)).2.output = some d ∧
    ∀ j : Fin n, (x j.castSucc).2.output = none}

private theorem stopped_cylinder_law (u : ℕ) (K : ℕ → ℕ) (n : ℕ) (d : Bool) :
    (O.seedLaw.prod (Measure.infinitePi fun _ : ℕ => O.innovationLaw))
      {p | O.machine.stopIndex p.1 (ActualRenewalStopping.sourceBit u K) p.2 = some n ∧
        (O.machine.execute p.1 (ActualRenewalStopping.sourceBit u K) p.2 n).action.output =
          some d} =
      (O.executionLaw (ActualRenewalStopping.sourceBit u K) n).toMeasure
        (O.emissionCylinder n d) := by
  have he : {p : O.Outcome × (ℕ → O.Innovation) |
      O.machine.stopIndex p.1 (ActualRenewalStopping.sourceBit u K) p.2 = some n ∧
        (O.machine.execute p.1 (ActualRenewalStopping.sourceBit u K) p.2 n).action.output =
          some d} =
      (fun p => O.develop (ActualRenewalStopping.sourceBit u K) p.1 n
        (fun j => p.2 j.val)) ⁻¹' O.emissionCylinder n d := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, emissionCylinder,
      O.develop_actions, O.machine.stop_spec, Fin.val_last, Fin.val_castSucc]
    constructor
    · rintro ⟨⟨_, hpre⟩, hd⟩
      exact ⟨hd, fun j => hpre j.val j.isLt⟩
    · rintro ⟨hd, hpre⟩
      have hn : (O.machine.execute p.1 (ActualRenewalStopping.sourceBit u K) p.2 n).action.output
          ≠ none := by
        intro h
        have hh : (some d : Option Bool) = none := hd.symm.trans h
        cases hh
      exact ⟨⟨hn, fun k hk => hpre ⟨k, hk⟩⟩, hd⟩
  rw [he, ← Measure.map_apply (by
    have hf : Measurable (fun p : O.Outcome × (ℕ → O.Innovation) =>
        (p.1, fun j : Fin n => p.2 j.val)) := by fun_prop
    exact (measurable_of_countable (fun p =>
      O.develop (ActualRenewalStopping.sourceBit u K) p.1 n p.2)).comp hf)
    (Set.to_countable _).measurableSet, O.infinite_execution_law]

private theorem stopped_receipt_law (u : ℕ) (K : ℕ → ℕ) (n : ℕ) (d : Bool) :
    (O.seedLaw.prod (Measure.infinitePi fun _ : ℕ => O.innovationLaw))
      {p | O.machine.stopIndex p.1 (ActualRenewalStopping.sourceBit u K) p.2 = some n ∧
        O.machine.result p.1 (ActualRenewalStopping.sourceBit u K) p.2 =
          some ((List.range n).map (ActualRenewalStopping.sourceBit u K), d)} =
      (O.executionLaw (ActualRenewalStopping.sourceBit u K) n).toMeasure
        (O.emissionCylinder n d) := by
  have hr (p : O.Outcome × (ℕ → O.Innovation))
      (ht : O.machine.stopIndex p.1 (ActualRenewalStopping.sourceBit u K) p.2 = some n) :
      O.machine.result p.1 (ActualRenewalStopping.sourceBit u K) p.2 =
        (O.machine.execute p.1 (ActualRenewalStopping.sourceBit u K) p.2 n).action.output.map
          (fun d => ((List.range n).map (ActualRenewalStopping.sourceBit u K), d)) := by
    have htrace := (O.machine.execution_normalization p.1 p.2 u K n).2.1
    rw [O.machine.stop_length _ _ _ _ ht] at htrace
    rw [Machine.result, ht]
    change (O.machine.execute p.1 (ActualRenewalStopping.sourceBit u K) p.2 n).action.output.map
      (fun d => ((O.machine.execute p.1 (ActualRenewalStopping.sourceBit u K) p.2 n).acquired, d)) = _
    rw [htrace]
  have he : {p : O.Outcome × (ℕ → O.Innovation) |
      O.machine.stopIndex p.1 (ActualRenewalStopping.sourceBit u K) p.2 = some n ∧
        O.machine.result p.1 (ActualRenewalStopping.sourceBit u K) p.2 =
          some ((List.range n).map (ActualRenewalStopping.sourceBit u K), d)} =
      {p | O.machine.stopIndex p.1 (ActualRenewalStopping.sourceBit u K) p.2 = some n ∧
        (O.machine.execute p.1 (ActualRenewalStopping.sourceBit u K) p.2 n).action.output =
          some d} := by
    ext p
    constructor
    · rintro ⟨ht, hd⟩
      rw [hr p ht] at hd
      obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp hd
      have he' : b = d := congrArg Prod.snd he
      exact ⟨ht, he' ▸ hb⟩
    · rintro ⟨ht, hd⟩
      exact ⟨ht, by rw [hr p ht, hd]; rfl⟩
  rw [he]
  exact O.stopped_cylinder_law u K n d

end Stochastic

namespace Stochastic
variable (O : Stochastic C)
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

abbrev Space := (ℕ × (ℕ → ℕ)) × (O.Outcome × (ℕ → O.Innovation))

/-- One source coordinate and one source-independent observer realization.
    The same seed and innovation measures are used for both true labels. -/
def law (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (i : Bool) : Measure O.Space :=
  productLaw O.seedLaw O.innovationLaw
    (OriginalRenewalLaws.waitLaw q hq hq1 i) (OriginalRenewalLaws.gapLaw q hq hq1 i)

/-- Exact compatibility of the original operational laws with the actual
    renewal history consumers, all on the same source/seed/table product. -/
structure Realization (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (M : ℕ)
    (η : PMF O.machine.Boundary) (A B : O.machine.Boundary → PMF O.machine.Boundary) : Prop where
  seed : O.seedLaw.map (fun seed => O.machine.boundary (O.machine.initial seed)) = η.toMeasure
  row : ∀ s b, O.innovationLaw.map
    (effective O.machine.labels O.machine.normalizedUpdate s b) =
      (if b then B s else A s).toMeasure
  absorbing : ∀ d, A (Sum.inr d) = PMF.pure (Sum.inr d) ∧
    B (Sum.inr d) = PMF.pure (Sum.inr d)
  budget : Fintype.card O.machine.Boundary ≤ M
  finite : ∀ source n,
    (O.seedLaw.prod (Measure.infinitePi fun _ : ℕ => O.innovationLaw)).map
      (fun p => O.develop source p.1 n (fun j => p.2 j.val)) =
        (O.executionLaw source n).toMeasure
  joint : ∀ i n (D : Set (ℕ × (ℕ → ℕ))) (_ : MeasurableSet D)
      (B : Set (Fin (n + 1) → O.Outcome)) (_ : MeasurableSet B),
    O.law q hq hq1 i
      {ω | ω.1 ∈ D ∧ O.develop (ActualRenewalStopping.sourceBit ω.1.1 ω.1.2)
        ω.2.1 n (fun j => ω.2.2 j.val) ∈ B} =
      ∫⁻ g, (if g ∈ D then
        (O.executionLaw (ActualRenewalStopping.sourceBit g.1 g.2) n).toMeasure B else 0)
        ∂((OriginalRenewalLaws.waitLaw q hq hq1 i).toMeasure.prod
          (Measure.infinitePi fun _ : ℕ => (OriginalRenewalLaws.gapLaw q hq hq1 i).toMeasure))
  actions : ∀ seed coins u K n (j : Fin (n + 1)),
    (O.develop (ActualRenewalStopping.sourceBit u K) seed n (fun t => coins t.val) j).2 =
      (O.machine.execute seed (ActualRenewalStopping.sourceBit u K) coins j.val).action
  stopped : ∀ u K n d,
    (O.seedLaw.prod (Measure.infinitePi fun _ : ℕ => O.innovationLaw))
      {p | O.machine.stopIndex p.1 (ActualRenewalStopping.sourceBit u K) p.2 = some n ∧
        O.machine.result p.1 (ActualRenewalStopping.sourceBit u K) p.2 =
          some ((List.range n).map (ActualRenewalStopping.sourceBit u K), d)} =
      (O.executionLaw (ActualRenewalStopping.sourceBit u K) n).toMeasure
        (O.emissionCylinder n d)
  primitive : ∀ i, Primitive (O.law q hq hq1 i)
    (fun ω => O.machine.boundary (O.machine.initial ω.2.1))
    (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2.2) η.toMeasure
    (OriginalRenewalLaws.waitLaw q hq hq1 i) (OriginalRenewalLaws.gapLaw q hq hq1 i)
    O.innovationLaw
  source_cylinders : ∀ i n (a : ℕ × (Fin n → ℕ)) (x : Fin (n + 1) → O.machine.Boundary),
    O.law q hq hq1 i
      (ActualRenewalHistoryLaw.observedHistory O.machine.labels O.machine.normalizedUpdate
        (fun ω => O.machine.boundary (O.machine.initial ω.2.1))
        (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2.2) n ⁻¹' {(a, x)}) =
      OriginalRenewalLaws.waitLaw q hq hq1 i a.1 *
        (η.bind fun s => (zeroRow A a.1 s).bind B) (x 0) *
        ∏ j : Fin n, (OriginalRenewalLaws.gapLaw q hq hq1 i (a.2 j) *
          ((zeroRow A (a.2 j) (x j.castSucc)).bind B) (x j.succ))
  state_prefix : ∀ i l (x : Fin l → O.machine.Boundary),
    O.law q hq hq1 i {ω | ∀ j : Fin l,
      ActualRenewalStopping.epoch O.machine.labels O.machine.normalizedUpdate
        (O.machine.boundary (O.machine.initial ω.2.1)) ω.2.2 ω.1.1 ω.1.2 j.val = x j} =
      ActualRenewalHistoryLaw.prefixMass
        ((OriginalRenewalLaws.waitLaw q hq hq1 i).bind fun u =>
          η.bind fun s => (zeroRow A u s).bind B)
        (fun s => (OriginalRenewalLaws.gapLaw q hq hq1 i).bind fun k =>
          (zeroRow A k s).bind B) l x
  ordinary_past : ∀ i n (H : Set (Fin (n + 1) → O.machine.Boundary))
      (_ : MeasurableSet H) (T : Set O.machine.Boundary) (_ : MeasurableSet T),
    O.law q hq hq1 i
      ({ω | ActualRenewalHistoryLaw.epochHistory O.machine.labels O.machine.normalizedUpdate
        (fun ω => O.machine.boundary (O.machine.initial ω.2.1))
        (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2.2) n ω ∈ H} ∩
      {ω | ActualRenewalStopping.epoch O.machine.labels O.machine.normalizedUpdate
        (O.machine.boundary (O.machine.initial ω.2.1)) ω.2.2 ω.1.1 ω.1.2 (n + 1) ∈ T}) =
    ∑' s, O.law q hq hq1 i
      ({ω | ActualRenewalHistoryLaw.epochHistory O.machine.labels O.machine.normalizedUpdate
        (fun ω => O.machine.boundary (O.machine.initial ω.2.1))
        (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2.2) n ω ∈ H} ∩
      {ω | ActualRenewalStopping.epoch O.machine.labels O.machine.normalizedUpdate
        (O.machine.boundary (O.machine.initial ω.2.1)) ω.2.2 ω.1.1 ω.1.2 n = s}) *
        ((OriginalRenewalLaws.gapLaw q hq hq1 i).bind fun k =>
          (zeroRow A k s).bind B).toMeasure T
  stopping : ∀ seed coins u K,
    let bits := ActualRenewalStopping.sourceBit u K
    let Z := ActualRenewalStopping.run O.machine.labels O.machine.normalizedUpdate
      (O.machine.boundary (O.machine.initial seed)) coins u K
    let Y := ActualRenewalStopping.epoch O.machine.labels O.machine.normalizedUpdate
      (O.machine.boundary (O.machine.initial seed)) coins u K
    O.machine.stopIndex seed bits coins = FreshServiceRestart.firstHit O.machine.labels Z ∧
    O.machine.paidCost seed bits coins = FreshServiceRestart.firstHit O.machine.labels Z ∧
    O.machine.decision seed bits coins = (FreshServiceRestart.firstHit O.machine.labels Z).bind
      (fun t => O.machine.output (Z t)) ∧
    O.machine.result seed bits coins = (FreshServiceRestart.firstHit O.machine.labels Z).bind
      (fun t => (O.machine.output (Z t)).map fun d => ((List.range t).map bits, d)) ∧
    (∀ T, O.machine.stopIndex seed bits coins = some T → ∃ N d,
      O.machine.result seed bits coins = some ((List.range T).map bits, d) ∧
      FreshServiceRestart.firstHit O.machine.labels Y = some N ∧ Y N = Sum.inr d ∧
      N ≤ ActualRenewalStopping.paidTicks u K T ∧
      ActualRenewalStopping.paidTicks u K T ≤ T ∧ (N = 0 ↔ T ≤ u + 1))

/-- Every original finite stochastic observer has one lawful common innovation
    realization, with its entire original law and original stopped cylinders. -/
theorem original_realization (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (M : ℕ) (hM : Fintype.card C ≤ M) :
    ∃ (η : PMF O.machine.Boundary) (A B : O.machine.Boundary → PMF O.machine.Boundary),
      O.Realization q hq hq1 M η A B := by
  obtain ⟨η, A, B, hη, _, heff, hrow, habs, hbudget, hstop⟩ :=
    O.machine.stopping_normalization O.seedLaw O.innovationLaw
      (measurable_of_countable _) (fun _ _ => measurable_of_countable _) M hM
  have hp (i : Bool) : Primitive (O.law q hq hq1 i)
      (fun ω => O.machine.boundary (O.machine.initial ω.2.1))
      (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2.2) η.toMeasure
      (OriginalRenewalLaws.waitLaw q hq hq1 i) (OriginalRenewalLaws.gapLaw q hq hq1 i)
      O.innovationLaw := by
    rw [← hη]
    exact product_primitive O.seedLaw O.innovationLaw
      (fun seed => O.machine.boundary (O.machine.initial seed)) (measurable_of_countable _)
      _ _
  have hI : Measurable (fun ω : O.Space =>
      O.machine.boundary (O.machine.initial ω.2.1)) :=
    (measurable_of_countable (fun seed => O.machine.boundary (O.machine.initial seed))).comp
      (measurable_fst.comp measurable_snd)
  have hτ : Measurable (fun ω : O.Space => ω.1.1) := measurable_fst.comp measurable_fst
  have hK (j : ℕ) : Measurable (fun ω : O.Space => ω.1.2 j) := by fun_prop
  have hξ (j : ℕ) : Measurable (fun ω : O.Space => ω.2.2 j) := by fun_prop
  refine ⟨η, A, B, ⟨hη, hrow, habs, hbudget, O.infinite_execution_law,
    (fun i => O.joint_execution_cylinder _ _), O.develop_actions, O.stopped_receipt_law, hp, ?_, ?_, ?_, hstop⟩⟩
  · intro i n a x
    exact ActualRenewalHistoryLaw.actual_source_cylinders O.machine.labels
      O.machine.normalizedUpdate (O.law q hq hq1 i) _ _ _ _ η _ _ O.innovationLaw
      A B heff hrow hI hτ hK hξ (hp i) n a x
  · intro i l x
    exact ActualRenewalHistoryLaw.actual_state_prefix O.machine.labels
      O.machine.normalizedUpdate (O.law q hq hq1 i) _ _ _ _ η _ _ O.innovationLaw
      A B heff hrow hI hτ hK hξ (hp i) l x
  · intro i n H hH T hT
    exact ActualRenewalHistoryLaw.actual_ordinary_past O.machine.labels
      O.machine.normalizedUpdate (O.law q hq hq1 i) _ _ _ _ η _ _ O.innovationLaw
      A B heff hrow hI hτ hK hξ (hp i) n H hH T hT

end Stochastic

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalJointRealization

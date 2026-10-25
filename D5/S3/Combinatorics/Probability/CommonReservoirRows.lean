/- GID: D5/S3/Combinatorics/Probability/CommonReservoirRows
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/CommonReservoirRows
   mirror-E: none(waiver:symbolic-product-probability-estimate)
   anchors: []
   utility: none
   digest: Independent actual star rows and sparse upper tails on one tagged reservoir law. -/

import D5.S3.Combinatorics.Probability.TripleReservoir
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Actual retained and lost star rows in one tagged product space. -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.CommonReservoirRows

open TripleReservoir

variable {V C A : Type*} [Fintype V] [Fintype C] [Fintype A]

def pairEvent (v : V) (c : C) : Set ((V ⊕ C) → Bool) :=
  {ω | ω (Sum.inl v) = true ∧ ω (Sum.inr c) = true}

def lossEvent (v : V) (c : C) : Set ((V ⊕ C) → Bool) :=
  {ω | ω (Sum.inl v) = true ∨ ω (Sum.inr c) = true}

def pairCount (vertex : A → V) (colour : A → C) (ω : (V ⊕ C) → Bool) : ℝ :=
  ∑ i, (pairEvent (vertex i) (colour i)).indicator (fun _ => (1 : ℝ)) ω

def lossCount (vertex : A → V) (colour : A → C) (ω : (V ⊕ C) → Bool) : ℝ :=
  ∑ i, (lossEvent (vertex i) (colour i)).indicator (fun _ => (1 : ℝ)) ω

omit [Fintype A] in
private theorem pair_rows (p : Set.Icc (0 : ℝ) 1) (vertex : A → V) (colour : A → C)
    (hv : Function.Injective vertex) (hc : Function.Injective colour) (b : Bool) :
    let E := fun i => {ω : (V ⊕ C) → Bool |
      ω (Sum.inl (vertex i)) = b ∧ ω (Sum.inr (colour i)) = b}
    iIndepFun (fun i => (E i).indicator (fun _ => (1 : ℝ))) (reservoirLaw p) ∧
    (∀ i, ∫ ω, (E i).indicator (fun _ => (1 : ℝ)) ω ∂reservoirLaw p =
      (if b then (p : ℝ) else 1 - (p : ℝ)) ^ 2) := by
  classical
  let R := V ⊕ C
  let P : Measure (R → Bool) := reservoirLaw p
  let E := fun i => {ω : R → Bool |
    ω (Sum.inl (vertex i)) = b ∧ ω (Sum.inr (colour i)) = b}
  let S : A → Finset R := fun i => {Sum.inl (vertex i), Sum.inr (colour i)}
  let B : R → Set (R → Bool) := fun r => {ω | ω r = b}
  have hP : IsProbabilityMeasure P := by dsimp [P, reservoirLaw]; infer_instance
  let := hP
  have hm (r : R) : MeasurableSet (B r) := (Set.toFinite _).measurableSet
  have he (i : A) : E i = ⋂ r ∈ S i, B r := by ext ω; simp [E, S, B]
  have hind : iIndepFun (fun (r : R) (ω : R → Bool) => ω r) P :=
    iIndepFun_pi (X := fun (_ : R) (x : Bool) => x) (fun _ => measurable_id.aemeasurable)
  have hB : iIndepSet B P := by
    apply (iIndepSet_iff_meas_biInter hm).2
    intro T
    exact hind.measure_inter_preimage_eq_mul T
      (sets := fun _ => ({b} : Set Bool)) (fun _ _ => measurableSet_singleton b)
  have hbp (r : R) : P.real (B r) = if b then (p : ℝ) else 1 - (p : ℝ) := by
    have ht : P.real {ω : R → Bool | ω r = true} = (p : ℝ) := by
      have h := (measurePreserving_eval (fun _ : R => bernoulliMeasure true false p) r).measure_preimage
        (measurableSet_singleton true).nullMeasurableSet
      change P {ω : R → Bool | ω r = true} = _ at h
      rw [measureReal_def, h, bernoulliMeasure_apply_of_mem_of_notMem p
        (measurableSet_singleton true) (by simp) (by simp)]
      simp
    cases b with
    | true => exact ht
    | false =>
      have heq : B r = {ω : R → Bool | ω r = true}ᶜ := by
        ext ω; cases h : ω r <;> simp [B, h]
      rw [heq, measureReal_compl ((Set.toFinite _).measurableSet), probReal_univ, ht]
      simp
  have hmean (i : A) : ∫ ω, (E i).indicator (fun _ => (1 : ℝ)) ω ∂P =
      (if b then (p : ℝ) else 1 - (p : ℝ)) ^ 2 := by
    change (∫ ω, (E i).indicator (1 : (R → Bool) → ℝ) ω ∂P) = _
    rw [integral_indicator_one ((Set.toFinite _).measurableSet), he, measureReal_def,
      hB.meas_biInter]
    simp only [ENNReal.toReal_prod]
    change (∏ r ∈ S i, P.real (B r)) = _
    simp_rw [hbp]
    simp [S, pow_two]
  refine ⟨?_, hmean⟩
  apply iIndepSet.iIndepFun_indicator
  apply (iIndepSet_iff_meas_biInter (fun i => (Set.toFinite (E i)).measurableSet)).2
  intro T
  have hd : Set.PairwiseDisjoint (↑T) S := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro r hri hrj
    simp only [S, mem_insert, mem_singleton] at hri hrj
    rcases hri with hri | hri <;> rcases hrj with hrj | hrj
    · exact hij (hv (Sum.inl.inj (hri.symm.trans hrj)))
    · cases hri.symm.trans hrj
    · cases hri.symm.trans hrj
    · exact hij (hc (Sum.inr.inj (hri.symm.trans hrj)))
  have hu : (⋂ i ∈ T, E i) = ⋂ r ∈ T.biUnion S, B r := by
    ext ω
    simp only [he, Set.mem_iInter, mem_biUnion]
    aesop
  rw [hu, hB.meas_biInter, prod_biUnion hd]
  apply prod_congr rfl
  intro i hi
  rw [he, hB.meas_biInter]

/-- The actual incoming or outgoing star has independent Bernoulli-p² retained rows.
Only distinct other vertices and distinct literal colours are required. -/
theorem pair_lower_tail (p : Set.Icc (0 : ℝ) 1) (vertex : A → V) (colour : A → C)
    (hv : Function.Injective vertex) (hc : Function.Injective colour)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (reservoirLaw p).real {ω | pairCount vertex colour ω ≤
      (1 - δ) * ((p : ℝ) ^ 2 * Fintype.card A)} ≤
      Real.exp (-(δ ^ 2 * ((p : ℝ) ^ 2 * Fintype.card A)) / 2) := by
  classical
  let P : Measure ((V ⊕ C) → Bool) := reservoirLaw p
  have hp : IsProbabilityMeasure P := by dsimp [P, reservoirLaw]; infer_instance
  let := hp
  let X := fun i => (pairEvent (vertex i) (colour i)).indicator (fun _ => (1 : ℝ))
  have hr := pair_rows p vertex colour hv hc true
  have hb (i : A) : ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall fun ω => by
      by_cases h : ω ∈ pairEvent (vertex i) (colour i) <;> simp [X, h]
  have hw (j : Fin 1) : iIndepFun (fun i : {i : A // (0 : Fin 1) = j} => X i.val) P := by
    exact hr.1.precomp Subtype.val_injective
  have ht := FiniteColourLowerTail.lower_tail P X 1 (by omega) (fun _ => 0)
    (fun i => (measurable_of_countable _).aemeasurable) hb hw δ hδ
  have he : (∑ i, ∫ ω, X i ω ∂P) = (p : ℝ) ^ 2 * Fintype.card A := by
    have hm (i : A) : ∫ ω, X i ω ∂P = (p : ℝ) ^ 2 := hr.2 i
    simp_rw [hm]; simp [mul_comm]
  rw [he] at ht
  simpa [pairCount, X] using ht

private theorem bounded_independent_upper {Ω I : Type*} [Finite Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → ℝ)
    (hind : iIndepFun X P) (hb : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (t ε : ℝ) (ht : 0 ≤ t) :
    P.real {ω | ε ≤ ∑ i, X i ω} ≤
      Real.exp (-t * ε + (∑ i, ∫ ω, X i ω ∂P) * (Real.exp t - 1)) := by
  have hw (j : Fin 1) : iIndepFun (fun i : {i : I // (0 : Fin 1) = j} => X i.val) P :=
    hind.precomp Subtype.val_injective
  have hmgf := FiniteColourLowerTail.mgf_sum_le P X 1 (by omega) (fun _ => 0)
    (fun _ => (measurable_of_countable _).aemeasurable)
    (fun i => Filter.Eventually.of_forall (hb i)) hw t
  calc
    _ ≤ Real.exp (-t * ε) * mgf (fun ω => ∑ i, X i ω) P t :=
      measure_ge_le_exp_mul_mgf ε ht Integrable.of_finite
    _ ≤ Real.exp (-t * ε) *
        Real.exp ((∑ i, ∫ ω, X i ω ∂P) * (Real.exp t - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa using hmgf
    _ = _ := (Real.exp_add _ _).symm

/-- Actual star losses use OR, with mean (2p-p²)d. Their rows are independent on
the same product law used by all the retained pair and triple counts. -/
theorem pair_loss_upper_tail (p : Set.Icc (0 : ℝ) 1) (vertex : A → V) (colour : A → C)
    (hv : Function.Injective vertex) (hc : Function.Injective colour) :
    (reservoirLaw p).real {ω | 3 * (p : ℝ) * Fintype.card A ≤ lossCount vertex colour ω} ≤
      Real.exp (-((p : ℝ) * Fintype.card A) / 5) := by
  classical
  let P : Measure ((V ⊕ C) → Bool) := reservoirLaw p
  have hp : IsProbabilityMeasure P := by dsimp [P, reservoirLaw]; infer_instance
  let := hp
  let X := fun i => (lossEvent (vertex i) (colour i)).indicator (fun _ => (1 : ℝ))
  let Y := fun i => ({ω : (V ⊕ C) → Bool |
    ω (Sum.inl (vertex i)) = false ∧ ω (Sum.inr (colour i)) = false}).indicator
      (fun _ => (1 : ℝ))
  have hr := pair_rows p vertex colour hv hc false
  have heq : X = fun i ω => 1 - Y i ω := by
    funext i ω
    cases h₁ : ω (Sum.inl (vertex i)) <;>
      cases h₂ : ω (Sum.inr (colour i)) <;> simp [X, Y, lossEvent, h₁, h₂]
  have hind : iIndepFun X P := by
    rw [heq]
    exact hr.1.comp (fun (_ : A) (x : ℝ) => 1 - x)
      (fun _ => measurable_const.sub measurable_id)
  have hb (i : A) (ω) : X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : ω ∈ lossEvent (vertex i) (colour i) <;> simp [X, h]
  have hm (i : A) : ∫ ω, X i ω ∂P = 2 * (p : ℝ) - (p : ℝ) ^ 2 := by
    rw [heq, integral_sub (integrable_const 1) Integrable.of_finite]
    have hY : ∫ ω, Y i ω ∂P = (1 - (p : ℝ)) ^ 2 := hr.2 i
    rw [hY, integral_const]; simp; ring
  have hs : (∑ i, ∫ ω, X i ω ∂P) =
      (2 * (p : ℝ) - (p : ℝ) ^ 2) * Fintype.card A := by
    simp_rw [hm]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    ring
  have hl : (2 / 5 : ℝ) ≤ Real.log (3 / 2) := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
    norm_num at h ⊢; exact h
  have ht : 0 ≤ Real.log (3 / 2 : ℝ) := le_trans (by norm_num) hl
  have hh := bounded_independent_upper P X hind hb (Real.log (3 / 2))
    (3 * (p : ℝ) * Fintype.card A) ht
  rw [hs, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] at hh
  refine hh.trans (Real.exp_le_exp.mpr ?_)
  have hd : 0 ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  have hl' := mul_le_mul_of_nonneg_right hl
    (show 0 ≤ 3 * (p : ℝ) * Fintype.card A from
      mul_nonneg (mul_nonneg (by norm_num) p.property.1) (Nat.cast_nonneg _))
  nlinarith [sq_nonneg (p : ℝ), mul_nonneg (sq_nonneg (p : ℝ)) hd]

def vertexCount (ω : (V ⊕ C) → Bool) : ℝ :=
  ∑ v : V, ({ω : (V ⊕ C) → Bool | ω (Sum.inl v) = true}).indicator
    (fun _ => (1 : ℝ)) ω

/-- The common vertex reservoir has upper tail exp(-pn/3) at 2pn. -/
theorem vertex_upper_tail (p : Set.Icc (0 : ℝ) 1) :
    (reservoirLaw p).real {ω : (V ⊕ C) → Bool |
      2 * (p : ℝ) * Fintype.card V ≤ vertexCount ω} ≤
      Real.exp (-((p : ℝ) * Fintype.card V) / 3) := by
  classical
  let R := V ⊕ C
  let P : Measure (R → Bool) := reservoirLaw p
  have hp : IsProbabilityMeasure P := by dsimp [P, reservoirLaw]; infer_instance
  let := hp
  let E := fun v : V => {ω : R → Bool | ω (Sum.inl v) = true}
  let X := fun v => (E v).indicator (fun _ => (1 : ℝ))
  have hind : iIndepFun (fun (r : R) (ω : R → Bool) => ω r) P :=
    iIndepFun_pi (X := fun (_ : R) (x : Bool) => x) (fun _ => measurable_id.aemeasurable)
  have heind : iIndepSet E P := by
    apply (iIndepSet_iff_meas_biInter (fun _ => (Set.toFinite _).measurableSet)).2
    intro T
    exact (hind.precomp Sum.inl_injective).measure_inter_preimage_eq_mul T
      (sets := fun _ => ({true} : Set Bool)) (fun _ _ => measurableSet_singleton true)
  have hm (v : V) : ∫ ω, X v ω ∂P = (p : ℝ) := by
    change (∫ ω, (E v).indicator (1 : (R → Bool) → ℝ) ω ∂P) = _
    rw [integral_indicator_one ((Set.toFinite _).measurableSet), measureReal_def]
    have h := (measurePreserving_eval (fun _ : R => bernoulliMeasure true false p)
      (Sum.inl v)).measure_preimage (measurableSet_singleton true).nullMeasurableSet
    change P (E v) = _ at h
    rw [h, bernoulliMeasure_apply_of_mem_of_notMem p
      (measurableSet_singleton true) (by simp) (by simp)]
    simp
  have hb (v : V) (ω) : X v ω ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : ω ∈ E v <;> simp [X, h]
  have hl : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
    norm_num at h ⊢; exact h
  have hh := bounded_independent_upper P X heind.iIndepFun_indicator hb (Real.log 2)
    (2 * (p : ℝ) * Fintype.card V) (le_trans (by norm_num) hl)
  simp_rw [hm] at hh
  simp only [sum_const, card_univ, nsmul_eq_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
  refine hh.trans (Real.exp_le_exp.mpr ?_)
  have hl' := mul_le_mul_of_nonneg_right hl
    (show 0 ≤ 2 * (p : ℝ) * Fintype.card V from
      mul_nonneg (mul_nonneg (by norm_num) p.property.1) (Nat.cast_nonneg _))
  nlinarith

end D5.S3.Combinatorics.Probability.CommonReservoirRows

/- GID: D5/S3/Combinatorics/Probability/TripleReservoir
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/TripleReservoir
   mirror-E: none(waiver:symbolic-product-probability-estimate)
   anchors: []
   utility: none
   digest: Actual triple-selection events in independent tagged vertex and colour reservoirs. -/

import D5.S3.Combinatorics.Probability.FiniteColourLowerTail
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Three-coordinate reservoir event counts
The deterministic interface supplies only a three-colouring with disjoint supports in each
fibre. All probabilities and all mutual independence assertions are proved from the product law.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.TripleReservoir

/-- Bernoulli-p selections of every coordinate; tagging keeps vertices and colours distinct. -/
def reservoirLaw {R : Type*} [Fintype R] (p : Set.Icc (0 : ℝ) 1) :
    Measure (R → Bool) := Measure.pi (fun _ : R => bernoulliMeasure true false p)

/-- A retained choice succeeds exactly when its vertex and both literal colours are selected. -/
def tripleEvent {V C : Type*} (v : V) (c d : C) : Set ((V ⊕ C) → Bool) :=
  {ω | ω (Sum.inl v) = true ∧ ω (Sum.inr c) = true ∧ ω (Sum.inr d) = true}

/-- The exact three tagged coordinates on which a choice depends. -/
def tripleSupport {V C : Type*} [DecidableEq V] [DecidableEq C]
    (v : V) (c d : C) : Finset (V ⊕ C) :=
  {Sum.inl v, Sum.inr c, Sum.inr d}

/-- Sparse-mean lower tail of the actual triple-success count.
The supplied colouring/disjointness is deterministic; there is no supplied probability,
independence or moment-generating-function certificate. -/
theorem triple_reservoir_lower_tail {V C A : Type*}
    [Fintype V] [Fintype C] [Fintype A] [DecidableEq V] [DecidableEq C]
    (p : Set.Icc (0 : ℝ) 1) (vertex : A → V) (left right : A → C)
    (hcol : ∀ i, left i ≠ right i) (colour : A → Fin 3)
    (hdisj : ∀ i j, colour i = colour j → i ≠ j →
      Disjoint (tripleSupport (vertex i) (left i) (right i))
        (tripleSupport (vertex j) (left j) (right j)))
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (reservoirLaw p).real
      {ω | (∑ i, (tripleEvent (vertex i) (left i) (right i)).indicator
        (fun _ => (1 : ℝ)) ω) ≤ (1 - δ) * ((p : ℝ) ^ 3 * Fintype.card A)} ≤
      Real.exp (-(δ ^ 2 * ((p : ℝ) ^ 3 * Fintype.card A)) / 6) := by
  classical
  let R := V ⊕ C
  let P : Measure (R → Bool) := reservoirLaw p
  let S : A → Finset R := fun i => tripleSupport (vertex i) (left i) (right i)
  let E : A → Set (R → Bool) := fun i => tripleEvent (vertex i) (left i) (right i)
  let B : R → Set (R → Bool) := fun r => {ω | ω r = true}
  have hP : IsProbabilityMeasure P := by dsimp [P, reservoirLaw]; infer_instance
  let := hP
  have hB (r : R) : MeasurableSet (B r) := by
    exact measurableSet_eq_fun (measurable_pi_apply r) measurable_const
  have hE (i : A) : MeasurableSet (E i) := by
    exact (hB (Sum.inl (vertex i))).inter
      ((hB (Sum.inr (left i))).inter (hB (Sum.inr (right i))))
  have hS (i : A) : (S i).card = 3 := by
    have hn : (Sum.inr (left i) : V ⊕ C) ≠ Sum.inr (right i) :=
      fun h => hcol i (Sum.inr.inj h)
    dsimp [S, tripleSupport]
    rw [card_insert_of_notMem (by simp), card_pair hn]
  have heq (i : A) : E i = ⋂ r ∈ S i, B r := by
    ext ω
    simp [E, S, B, tripleEvent, tripleSupport]
    rfl
  have hind : iIndepFun (fun (r : R) (ω : R → Bool) => ω r) P := by
    exact iIndepFun_pi (X := fun (_ : R) (b : Bool) => b)
      (fun _ => measurable_id.aemeasurable)
  have hbind : iIndepSet B P := by
    apply (iIndepSet_iff_meas_biInter hB).2
    intro T
    exact hind.measure_inter_preimage_eq_mul T
      (sets := fun _ => ({true} : Set Bool)) (fun _ _ => measurableSet_singleton true)
  have hbp (r : R) : P (B r) = ENNReal.ofReal (p : ℝ) := by
    have h := (measurePreserving_eval
      (fun _ : R => bernoulliMeasure true false p) r).measure_preimage
      (measurableSet_singleton true).nullMeasurableSet
    change P (B r) = _ at h
    rw [h]
    rw [bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton true)
      (by simp) (by simp)]
    exact ENNReal.ofReal_coe_nnreal.symm
  have hprob (T : Finset R) : P (⋂ r ∈ T, B r) = ENNReal.ofReal (p : ℝ) ^ T.card := by
    rw [hbind.meas_biInter]
    simp_rw [hbp]
    exact prod_const _
  have hmean (i : A) : ∫ ω, (E i).indicator (fun _ => (1 : ℝ)) ω ∂P = (p : ℝ) ^ 3 := by
    change (∫ ω, (E i).indicator (1 : (R → Bool) → ℝ) ω ∂P) = _
    rw [integral_indicator_one (hE i), measureReal_def, heq, hprob, hS,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal p.property.1]
  have hwithin (j : Fin 3) :
      iIndepFun (fun i : {i : A // colour i = j} =>
        (E i.val).indicator (fun _ => (1 : ℝ))) P := by
    apply iIndepSet.iIndepFun_indicator
    apply (iIndepSet_iff_meas_biInter (fun i : {i : A // colour i = j} => hE i.val)).2
    intro T
    have hd : Set.PairwiseDisjoint (↑T)
        (fun i : {i : A // colour i = j} => S i.val) := by
      intro a ha b hb hab
      exact hdisj a.val b.val (a.property.trans b.property.symm)
        (fun h => hab (Subtype.ext h))
    have hu : (⋂ i ∈ T, E i.val) =
        ⋂ r ∈ T.biUnion (fun i => S i.val), B r := by
      ext ω
      simp only [Set.mem_iInter]
      constructor
      · intro h r hr
        obtain ⟨i, hi, hr⟩ := mem_biUnion.mp hr
        have hh := h i hi
        rw [heq] at hh
        exact Set.mem_iInter₂.mp hh r hr
      · intro h i hi
        rw [heq]
        exact Set.mem_iInter₂.mpr fun r hr => h r (mem_biUnion.mpr ⟨i, hi, hr⟩)
    rw [hu, hbind.meas_biInter, Finset.prod_biUnion hd]
    apply prod_congr rfl
    intro i hi
    rw [heq, hbind.meas_biInter]
  have hX (i : A) : AEMeasurable ((E i).indicator (fun _ => (1 : ℝ))) P :=
    (measurable_const.indicator (hE i)).aemeasurable
  have h01 (i : A) : ∀ᵐ ω ∂P,
      (E i).indicator (fun _ => (1 : ℝ)) ω ∈ Set.Icc (0 : ℝ) 1 := by
    exact Filter.Eventually.of_forall fun ω => by
      by_cases h : ω ∈ E i <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hm : (∑ i, ∫ ω, (E i).indicator (fun _ => (1 : ℝ)) ω ∂P) =
      (p : ℝ) ^ 3 * Fintype.card A := by simp_rw [hmean]; simp [mul_comm]
  have ht := FiniteColourLowerTail.lower_tail P
    (fun i => (E i).indicator (fun _ => (1 : ℝ))) 3 (by norm_num) colour hX h01 hwithin δ hδ
  rw [hm] at ht
  norm_num only [Nat.cast_ofNat, mul_one, Nat.reduceMul] at ht
  exact ht

end D5.S3.Combinatorics.Probability.TripleReservoir

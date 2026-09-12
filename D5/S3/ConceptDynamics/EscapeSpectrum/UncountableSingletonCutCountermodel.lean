/- GID: D5/S3/ConceptDynamics/EscapeSpectrum/UncountableSingletonCutCountermodel
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/EscapeSpectrum/UncountableSingletonCutCountermodel
   mirror-E: none(waiver:infinite-classical-countermodel)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Constructions.UnitInterval]
   utility: none
   digest: Lebesgue singleton cuts separate every finite residual from the blind kernel. -/
import D5.S3.ConceptDynamics.EscapeSpectrum.BudgetEnvelopeCompletion
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.EscapeSpectrum.UncountableSingletonCutCountermodel
open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.EscapeSpectrum.BudgetEnvelopeCompletion
open MeasureTheory Set Filter
open scoped ENNReal
attribute [local instance] Classical.propDecidable

abbrev State := unitInterval × Bool
abbrev Pair := State × State
def q : State → unitInterval := Prod.fst
def target : State → Bool := Prod.snd
def language : Set unitInterval := univ
def definitions (t : unitInterval) (x : State) : Bool := if x.1 = t then x.2 else false
def unitCost (_ : unitInterval) : ℝ := 1
def edge (b : Bool) (t : unitInterval) : Pair := ((t, b), (t, !b))
local notation "μ" => (volume : Measure unitInterval)
local notation "E" => defectRelation q target
local notation "U" => (fun i : language =>
  E ∩ (conceptKernel (fun j : language => definitions (Subtype.val j)) i)ᶜ)
local notation "B" => (E ∩ jointKernel (fun i : language => definitions (Subtype.val i)))
local notation "R" => (fun S : Finset language =>
  defectRelation (conceptJoin q (finiteSelectionSupplement language definitions S)) target)
local notation "removed" => (fun S : Finset language => Subtype.val '' (S : Set language))

/-- All supported sets whose two sections are measurable for completed Lebesgue measure. -/
def sectionAlgebra : Set (Set Pair) := {C | C ⊆ E ∧ ∀ b, NullMeasurableSet (edge b ⁻¹' C) μ}
private def scalarMass (C : Set Pair) : NNReal :=
  (1 / 2 : NNReal) * (μ (edge false ⁻¹' C)).toNNReal +
  (1 / 2 : NNReal) * (μ (edge true ⁻¹' C)).toNNReal

private theorem edge_mem (b : Bool) (t : unitInterval) : edge b t ∈ E := by
  cases b <;> simp [edge, defectRelation, q, target]

private theorem baseline_section (b : Bool) : edge b ⁻¹' E = univ :=
  eq_univ_of_forall (edge_mem b)

private theorem geometry : E = range (edge false) ∪ range (edge true) := by
  ext ⟨⟨s, b⟩, ⟨t, c⟩⟩
  cases b <;> cases c <;> simp [defectRelation, q, target, edge, eq_comm]

private theorem lebesgue_sections (A : Set unitInterval) :
    (NullMeasurableSet A μ ↔
      NullMeasurableSet ((Subtype.val : unitInterval → ℝ) '' A) volume) ∧
    μ A = volume ((Subtype.val : unitInterval → ℝ) '' A) := by
  refine ⟨⟨fun h => Measure.NullMeasurableSet.subtype_coe nullMeasurableSet_Icc h, ?_⟩,
    unitInterval.volume_apply⟩
  intro h
  simpa only [preimage_image_eq _ Subtype.val_injective] using
    (h.mono_ac Measure.absolutelyContinuous_restrict).preimage
      unitInterval.measurePreserving_coe.quasiMeasurePreserving

private theorem section_ring : IsSetRing sectionAlgebra where
  empty_mem := ⟨empty_subset _, fun _ => by simp⟩
  union_mem {C D} hC hD := ⟨union_subset hC.1 hD.1, fun b => (hC.2 b).union (hD.2 b)⟩
  sdiff_mem {C D} hC hD := ⟨sdiff_subset.trans hC.1, fun b => (hC.2 b).diff (hD.2 b)⟩

private theorem baseline_mem : E ∈ sectionAlgebra :=
  ⟨Subset.rfl, fun b => by rw [baseline_section]; exact nullMeasurableSet_univ⟩

private theorem scalar_add {C D : Set Pair} (_hC : C ∈ sectionAlgebra)
    (hD : D ∈ sectionAlgebra) (h : Disjoint C D) :
    scalarMass (C ∪ D) = scalarMass C + scalarMass D := by
  have section_add (b : Bool) : (μ (edge b ⁻¹' (C ∪ D))).toNNReal =
      (μ (edge b ⁻¹' C)).toNNReal + (μ (edge b ⁻¹' D)).toNNReal := by
    rw [preimage_union, measure_union₀ (hD.2 b) (h.preimage _).aedisjoint,
      ENNReal.toNNReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [scalarMass, section_add]
  ring

/-- The half-sum formula on all ambient sets, additive on the full section algebra. -/
def edgeCharge : AddContent NNReal sectionAlgebra :=
  section_ring.addContent_of_union scalarMass (by simp [scalarMass]) scalar_add

/-- The real coercion of the same charge used by the canonical finite-selection spectrum. -/
def escapeWeight : EscapeWeight Pair where
  mass C := (edgeCharge C : ℝ)
  empty_mass := by simp
  mass_nonnegative C := (edgeCharge C).coe_nonneg

private theorem charge_mono : Monotone (fun C : Set Pair => edgeCharge C) := by
  intro C D h
  have hb (b : Bool) : (μ (edge b ⁻¹' C)).toNNReal ≤ (μ (edge b ⁻¹' D)).toNNReal :=
    ENNReal.toNNReal_mono (measure_ne_top _ _) (measure_mono (preimage_mono h))
  exact add_le_add (mul_le_mul_of_nonneg_left (hb false) (by positivity))
    (mul_le_mul_of_nonneg_left (hb true) (by positivity))

private theorem weight_mono : Monotone escapeWeight.mass :=
  fun _ _ h => NNReal.coe_le_coe.mpr (charge_mono h)

private theorem baseline_charge : edgeCharge E = 1 := by
  change scalarMass E = 1
  norm_num [scalarMass, baseline_section]

private theorem cut_identity (i : language) : U i = {edge false i.1, edge true i.1} := by
  ext ⟨⟨s, b⟩, ⟨t, c⟩⟩
  cases b <;> cases c <;> by_cases hs : s = i.1 <;> by_cases ht : t = i.1 <;>
    simp_all [defectRelation, conceptKernel, q, target, definitions, edge, eq_comm]

private theorem cut_section (i : language) (b : Bool) : edge b ⁻¹' U i = {i.1} := by
  rw [cut_identity]
  ext t
  cases b <;> simp [edge]

private theorem cut_mem (i : language) : U i ∈ sectionAlgebra :=
  ⟨inter_subset_left, fun b => by rw [cut_section]; exact nullMeasurableSet_singleton _⟩

private theorem cover : (⋃ i : language, U i) = E := by
  apply Subset.antisymm (iUnion_subset fun _ => inter_subset_left)
  intro p hp
  rw [geometry] at hp
  rcases hp with (⟨t, rfl⟩ | ⟨t, rfl⟩) <;>
    exact mem_iUnion.mpr ⟨⟨t, mem_univ t⟩,
      edge_mem _ _, by simp [conceptKernel, definitions, edge]⟩

private theorem blind_empty : B = ∅ :=
  (finite_cover_laws language definitions q target).1.mpr cover

private theorem residual_identity (S : Finset language) : R S = E \ (⋃ i ∈ S, U i) := by
  ext p
  simp only [defectRelation, conceptJoin, mem_ofPred_eq, Prod.mk.injEq,
    finiteSelectionSupplement, funext_iff, Set.mem_sdiff, mem_iUnion, mem_inter_iff,
    mem_compl_iff, conceptKernel]
  constructor
  · rintro ⟨⟨hq, hS⟩, ht⟩
    refine ⟨⟨hq, ht⟩, ?_⟩
    rintro ⟨i, hi, -, hn⟩
    exact hn (Option.some.inj (by simpa [hi] using hS i))
  · rintro ⟨⟨hq, ht⟩, hS⟩
    refine ⟨⟨hq, fun i => ?_⟩, ht⟩
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte, Option.some.injEq]
      by_contra hn
      exact hS ⟨i, hi, ⟨hq, ht⟩, hn⟩
    · simp [hi]

private theorem cut_union_section (S : Finset language) (b : Bool) :
    edge b ⁻¹' (⋃ i ∈ S, U i) = removed S := by
  ext t
  simp only [preimage_iUnion, cut_section, mem_iUnion, mem_singleton_iff, mem_image,
    Finset.mem_coe]
  simp only [eq_comm]
  exact ⟨fun ⟨i, hi, ht⟩ => ⟨i, hi, ht⟩, fun ⟨i, hi, ht⟩ => ⟨i, hi, ht⟩⟩

private theorem residual_section (S : Finset language) (b : Bool) :
    edge b ⁻¹' R S = (removed S)ᶜ := by
  rw [residual_identity, preimage_sdiff, baseline_section, cut_union_section, compl_eq_univ_sdiff]

private theorem removed_null (S : Finset language) : μ (removed S) = 0 :=
  (S.finite_toSet.image Subtype.val).measure_zero μ

private theorem residual_charge (S : Finset language) : edgeCharge (R S) = 1 := by
  have h (b : Bool) : μ (edge b ⁻¹' R S) = 1 := by
    rw [residual_section, measure_of_measure_compl_eq_zero (by simpa using removed_null S)]
    exact measure_univ
  change scalarMass (R S) = 1
  norm_num [scalarMass, h]

/-- Every actual finite selection deletes finitely many Lebesgue-null basepoints. -/
theorem finite_residual_mass_eq_one (S : Finset language) :
    finiteResidualMass language definitions q target escapeWeight S = 1 := by
  change (edgeCharge (R S) : ℝ) = 1
  rw [residual_charge, NNReal.coe_one]

private theorem language_laws : ¬ language.Countable ∧ language.Nonempty ∧
    Function.Injective (fun i : language => definitions i.1) ∧
    ¬ (range (fun i : language => definitions i.1)).Countable := by
  have hunc : Uncountable unitInterval := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [unitInterval, Cardinal.mk_Icc_real zero_lt_one]
    exact Cardinal.aleph0_lt_continuum)
  have hn : ¬ language.Countable := not_countable_univ_iff.mpr hunc
  have hi : Function.Injective (fun i : language => definitions i.1) := by
    intro i j hij
    apply Subtype.ext
    have h := congrFun hij (i.1, true)
    by_contra hne
    simp [definitions, hne] at h
  refine ⟨hn, ⟨0, mem_univ _⟩, hi, fun hr => hn ?_⟩
  have hpre := hr.preimage hi
  exact countable_coe_iff.mp (countable_univ_iff.mp (by simpa using hpre))

/-- The complete continuum countermodel, including the full section algebra and every budget. -/
theorem uncountable_singleton_cut_countermodel :
    ¬ language.Countable ∧ language.Nonempty ∧
    Function.Injective (fun i : language => definitions i.1) ∧
    ¬ (Set.range (fun i : language => definitions i.1)).Countable ∧
    E = Set.range (edge false) ∪ Set.range (edge true) ∧
    (∀ A : Set unitInterval,
      (NullMeasurableSet A μ ↔
        NullMeasurableSet ((Subtype.val : unitInterval → ℝ) '' A) volume) ∧
      μ A = volume ((Subtype.val : unitInterval → ℝ) '' A)) ∧
    (∀ C : Set Pair, C ∈ sectionAlgebra ↔ C ⊆ E ∧ ∀ b : Bool,
      NullMeasurableSet ((Subtype.val : unitInterval → ℝ) '' (edge b ⁻¹' C)) volume) ∧
    (∀ D : Set E, (Subtype.val : E → Pair) ⁻¹'
      ((Subtype.val : E → Pair) '' D) = D) ∧
    (∀ C : Set Pair, C ⊆ E → (Subtype.val : E → Pair) ''
      ((Subtype.val : E → Pair) ⁻¹' C) = C) ∧
    IsSetRing sectionAlgebra ∧ (∅ : Set Pair) ∈ sectionAlgebra ∧
    E ∈ sectionAlgebra ∧ (∀ C ∈ sectionAlgebra, E \ C ∈ sectionAlgebra) ∧
    (∀ C : Set Pair, edgeCharge C =
      (1 / 2 : NNReal) * (μ (edge false ⁻¹' C)).toNNReal +
      (1 / 2 : NNReal) * (μ (edge true ⁻¹' C)).toNNReal) ∧
    (∀ C : Set Pair, escapeWeight.mass C = (edgeCharge C : ℝ)) ∧
    edgeCharge ∅ = 0 ∧ edgeCharge E = 1 ∧
    (∀ C : Set Pair, 0 ≤ escapeWeight.mass C) ∧
    Monotone (fun C : Set Pair => edgeCharge C) ∧ Monotone escapeWeight.mass ∧
    (∀ C D : Set Pair, C ∈ sectionAlgebra → D ∈ sectionAlgebra → Disjoint C D →
      edgeCharge (C ∪ D) = edgeCharge C + edgeCharge D) ∧
    (∀ C : Set Pair, edgeCharge C = edgeCharge (C ∩ E)) ∧
    0 < escapeWeight.mass E ∧ (edgeCharge E : ENNReal) < ∞ ∧
    (∀ i : language, U i = {edge false i.1, edge true i.1} ∧ U i ∈ sectionAlgebra) ∧
    (⋃ i : language, U i) = E ∧ B = E \ (⋃ i : language, U i) ∧
    B = ∅ ∧ B ∈ sectionAlgebra ∧
    (∀ S : Finset language,
      (removed S).Finite ∧ μ (removed S) = 0 ∧
      R S = E \ (⋃ i ∈ S, U i) ∧
      (∀ b : Bool, edge b ⁻¹' R S = (removed S)ᶜ) ∧
      (⋃ i ∈ S, U i) ∈ sectionAlgebra ∧ R S ∈ sectionAlgebra ∧
      R S \ B ∈ sectionAlgebra ∧ edgeCharge (⋃ i ∈ S, U i) = 0 ∧
      B ⊆ R S ∧ edgeCharge (R S) = 1 ∧
      edgeCharge (R S) = edgeCharge B + edgeCharge (R S \ B) ∧
      finiteResidualMass language definitions q target escapeWeight S = 1) ∧
    (∀ t ∈ language, 0 < unitCost t) ∧
    (∀ S : Finset language, finiteSelectionCost language unitCost S = (S.card : ℝ)) ∧
    (∀ L : NNReal, finiteSelectionCost language unitCost ∅ ≤ (L : ℝ) ∧
      finiteBudgetMassValues language definitions q target unitCost escapeWeight L = {1} ∧
      finiteEscapeSpectrum language definitions q target unitCost escapeWeight L = 1) ∧
    allFiniteResidualInfimum language definitions q target escapeWeight = 1 ∧
    Tendsto (finiteEscapeSpectrum language definitions q target unitCost escapeWeight)
      atTop (nhds (1 : ℝ)) ∧
    escapeWeight.mass B / escapeWeight.mass E = 0 ∧
    (1 : ℝ) ≠ escapeWeight.mass B / escapeWeight.mass E := by
  have hbase : escapeWeight.mass E = 1 := by
    change (edgeCharge E : ℝ) = 1
    rw [baseline_charge, NNReal.coe_one]
  have hpos : 0 < escapeWeight.mass E := by rw [hbase]; norm_num
  have hvalues (L : NNReal) :
      finiteBudgetMassValues language definitions q target unitCost escapeWeight L = {1} := by
    apply Subset.antisymm
    · rintro x ⟨S, _, rfl⟩
      exact mem_singleton_iff.mpr (finite_residual_mass_eq_one S)
    · rintro x (rfl : x = 1)
      exact ⟨∅, by simp [finiteSelectionCost],
        finite_residual_mass_eq_one ∅⟩
  have hinf : allFiniteResidualInfimum language definitions q target escapeWeight = 1 := by
    have hm := funext finite_residual_mass_eq_one
    simp [allFiniteResidualInfimum, hm]
  have hlimit := (budget_envelope_infimum_and_limit language definitions q target
    unitCost escapeWeight hpos weight_mono).2.2.2.2.2
  rw [hinf, hbase, div_one] at hlimit
  have hblind : escapeWeight.mass B / escapeWeight.mass E = 0 := by
    rw [blind_empty, escapeWeight.empty_mass, zero_div]
  refine ⟨language_laws.1, language_laws.2.1, language_laws.2.2.1,
    language_laws.2.2.2, geometry, lebesgue_sections, ?_, ?_, ?_, section_ring,
    section_ring.empty_mem, baseline_mem, fun _ hC => section_ring.sdiff_mem baseline_mem hC,
    fun _ => rfl, fun _ => rfl, addContent_empty, baseline_charge,
    escapeWeight.mass_nonnegative, charge_mono, weight_mono, ?_, ?_, hpos, by simp,
    fun i => ⟨cut_identity i, cut_mem i⟩, cover, ?_, blind_empty,
    by rw [blind_empty]; exact section_ring.empty_mem, ?_,
    by intro t ht; norm_num [unitCost], ?_, ?_, hinf, hlimit, hblind, by rw [hblind]; norm_num⟩
  · intro C
    exact and_congr_right fun _ => forall_congr' fun b => (lebesgue_sections _).1
  · exact fun D => preimage_image_eq D Subtype.val_injective
  · intro C hC
    ext p
    exact ⟨fun ⟨_, hx, heq⟩ => heq ▸ hx, fun hp => ⟨⟨p, hC hp⟩, hp, rfl⟩⟩
  · exact fun C D hC hD h => addContent_union section_ring hC hD h
  · intro C
    change scalarMass C = scalarMass (C ∩ E)
    simp [scalarMass, preimage_inter, baseline_section]
  · rw [cover, Set.sdiff_self, blind_empty]
  · intro S
    have hm : R S ∈ sectionAlgebra := ⟨by rw [residual_identity]; exact sdiff_subset,
      fun b => by rw [residual_section]; exact (NullMeasurableSet.of_null (removed_null S)).compl⟩
    have hz : edgeCharge (⋃ i ∈ S, U i) = 0 := by
      change scalarMass _ = 0
      simp only [scalarMass, cut_union_section, removed_null, ENNReal.toNNReal_zero,
        mul_zero, add_zero]
    exact ⟨S.finite_toSet.image _, removed_null S, residual_identity S, residual_section S,
      section_ring.biUnion_mem S (fun i _ => cut_mem i), hm, by simpa [blind_empty] using hm,
      hz, by simp [blind_empty], residual_charge S, by simp [blind_empty],
      finite_residual_mass_eq_one S⟩
  · intro S
    simp [finiteSelectionCost, unitCost]
  · intro L
    refine ⟨by simp [finiteSelectionCost], hvalues L, ?_⟩
    simp [finiteEscapeSpectrum, finiteBudgetEnvelope, hvalues, hbase]

end D5.S3.ConceptDynamics.EscapeSpectrum.UncountableSingletonCutCountermodel

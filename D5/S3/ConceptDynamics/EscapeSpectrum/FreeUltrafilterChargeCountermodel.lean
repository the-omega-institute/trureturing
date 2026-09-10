/- GID: D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel
   mirror-E: none(waiver:infinite-classical-countermodel)
   anchors: [mathlib/module/Mathlib.Order.Filter.Ultrafilter.Basic, mathlib/module/Mathlib.MeasureTheory.Measure.AddContent]
   utility: none
   digest: Free ultrafilter charge separates finite escape from blind mass and continuity. -/
/-
Copyright (c) 2025 Patrick S. Mahon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import D5.S3.ConceptDynamics.EscapeSpectrum.BlindResidualChargeDecomposition
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.ENNReal.Operations

/- Modified file: scalar charge closure transplanted from the immutable source
identified in Library/ConceptDynamics/mahon2026ultrafilter.md, which preserves
both license texts. Other constructions below specialize to the two-sign model.
The ordered D5, pinned Mathlib and external searches found this scalar hit;
canonical residual APIs and Mathlib AddContent and hyperfilter laws are reused. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.EscapeSpectrum.FreeUltrafilterChargeCountermodel
open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.EscapeSpectrum.BudgetEnvelopeCompletion
open D5.S3.ConceptDynamics.EscapeSpectrum.BlindResidualChargeDecomposition
open MeasureTheory Set Filter
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- The `{0,1}`-valued charge on `Set ℕ` induced by an ultrafilter `U`:
    `ultrafilterCharge U A = 1` iff `A ∈ U`. -/
private def ultrafilterCharge (U : Ultrafilter ℕ) (A : Set ℕ) : ℝ≥0∞ :=
  if A ∈ U then 1 else 0

@[simp]
private theorem ultrafilterCharge_mem {U : Ultrafilter ℕ} {A : Set ℕ} (h : A ∈ U) :
    ultrafilterCharge U A = 1 :=
  show (if A ∈ U then 1 else 0) = 1 from if_pos h

@[simp]
private theorem ultrafilterCharge_notMem {U : Ultrafilter ℕ} {A : Set ℕ} (h : A ∉ U) :
    ultrafilterCharge U A = 0 :=
  show (if A ∈ U then 1 else 0) = 0 from if_neg h

private theorem ultrafilterCharge_empty (U : Ultrafilter ℕ) :
    ultrafilterCharge U ∅ = 0 :=
  ultrafilterCharge_notMem (fun h => U.neBot.ne (empty_mem_iff_bot.mp h))

private theorem ultrafilterCharge_univ (U : Ultrafilter ℕ) :
    ultrafilterCharge U Set.univ = 1 :=
  ultrafilterCharge_mem univ_mem

-- Helper to avoid repeating the ∅ ∈ U → False pattern
private theorem empty_not_mem_ultrafilter (U : Ultrafilter ℕ) : ∅ ∉ U :=
  fun h => U.neBot.ne (empty_mem_iff_bot.mp h)

/-- The ultrafilter charge is finitely additive on disjoint sets. -/
private theorem ultrafilterCharge_union_of_disjoint (U : Ultrafilter ℕ) {A B : Set ℕ}
    (hd : Disjoint A B) :
    ultrafilterCharge U (A ∪ B) = ultrafilterCharge U A + ultrafilterCharge U B := by
  rcases U.mem_or_compl_mem A with hA | hAc
  · -- A ∈ U, so B ∉ U (since A ∩ B = ∅ and U is a filter)
    have hB : B ∉ U := fun hB =>
      empty_not_mem_ultrafilter U (hd.inter_eq ▸ Filter.inter_mem hA hB)
    have hAB : A ∪ B ∈ U := Filter.mem_of_superset hA Set.subset_union_left
    rw [ultrafilterCharge_mem hAB, ultrafilterCharge_mem hA, ultrafilterCharge_notMem hB]
    norm_num
  · -- Aᶜ ∈ U, so A ∉ U
    have hA : A ∉ U := U.compl_mem_iff_notMem.mp hAc
    rcases U.mem_or_compl_mem B with hB | hBc
    · have hAB : A ∪ B ∈ U := Filter.mem_of_superset hB Set.subset_union_right
      rw [ultrafilterCharge_mem hAB, ultrafilterCharge_notMem hA, ultrafilterCharge_mem hB]
      norm_num
    · have hB : B ∉ U := U.compl_mem_iff_notMem.mp hBc
      have hAB : A ∪ B ∉ U := by
        intro h
        have hc : (A ∪ B)ᶜ ∈ U.toFilter := Set.compl_union A B ▸ Filter.inter_mem hAc hBc
        exact empty_not_mem_ultrafilter U (Set.inter_compl_self (A ∪ B) ▸ Filter.inter_mem h hc)
      rw [ultrafilterCharge_notMem hAB, ultrafilterCharge_notMem hA, ultrafilterCharge_notMem hB]
      norm_num

abbrev State := ℕ × Bool
abbrev Pair := State × State
def q : State → ℕ := Prod.fst
def target : State → Bool := Prod.snd
def language : Set ℕ := {n | 1 ≤ n}
def definitions (n : ℕ) (x : State) : Bool := if x.1 ≤ n then x.2 else false
def unitCost (_ : ℕ) : ℝ := 1
def edge (b : Bool) (k : ℕ) : Pair := ((k,b),(k,!b))

/-- The finite-valued scalar charge, converted from the ENNReal primitive. -/
def mu (C : Set ℕ) : NNReal := (ultrafilterCharge (hyperfilter ℕ) C).toNNReal

private lemma scalar_finite (C : Set ℕ) : ultrafilterCharge (hyperfilter ℕ) C ≠ ∞ := by
  unfold ultrafilterCharge
  split <;> simp

/-- Membership in the free ultrafilter is exactly the scalar charge formula. -/
theorem mu_formula (C : Set ℕ) : mu C = if C ∈ hyperfilter ℕ then 1 else 0 := by
  unfold mu ultrafilterCharge
  split <;> simp_all

private lemma mu_add {C D : Set ℕ} (h : Disjoint C D) : mu (C ∪ D) = mu C + mu D := by
  unfold mu
  rw [ultrafilterCharge_union_of_disjoint _ h,
    ENNReal.toNNReal_add (scalar_finite C) (scalar_finite D)]

private lemma full_ring : IsSetRing (Set.univ : Set (Set Pair)) :=
  ⟨Set.mem_univ _, fun _ _ _ _ => Set.mem_univ _, fun _ _ _ _ => Set.mem_univ _⟩

/-- The average of the two edge pullbacks is additive on the full powerset. -/
def edgeCharge : AddContent NNReal (Set.univ : Set (Set Pair)) :=
  full_ring.addContent_of_union
    (fun C => (1/2 : NNReal) * mu (edge false ⁻¹' C) + (1/2 : NNReal) * mu (edge true ⁻¹' C))
    (by
      have hz : mu ∅ = 0 := congrArg ENNReal.toNNReal (ultrafilterCharge_empty _)
      simp [hz]) (by
      intro C D _ _ h
      simp only [Set.preimage_union, mu_add (h.preimage (edge false)),
        mu_add (h.preimage (edge true)), mul_add]
      ac_rfl)

theorem edge_charge_formula (C : Set Pair) :
    edgeCharge C = (1/2 : NNReal) * mu (edge false ⁻¹' C) +
      (1/2 : NNReal) * mu (edge true ⁻¹' C) := rfl

private lemma edge_mem (b : Bool) (k : ℕ) : edge b k ∈ defectRelation q target := by
  cases b <;> simp [edge, defectRelation, q, target]

private lemma edge_preimage : ∀ b, edge b ⁻¹' defectRelation q target = Set.univ := by
  intro b
  exact Set.eq_univ_of_forall (edge_mem b)

theorem edge_charge_supported (C : Set Pair) :
    edgeCharge C = edgeCharge (C ∩ defectRelation q target) := by
  simp only [edge_charge_formula, Set.preimage_inter, edge_preimage, Set.inter_univ]

private lemma baseline_mass : edgeCharge (defectRelation q target) = 1 := by
  norm_num [edge_charge_formula, edge_preimage, mu, ultrafilterCharge_univ]

private lemma charge_mono : Monotone (fun C : Set Pair => edgeCharge C) :=
  fun _ _ h => addContent_mono full_ring.isSetSemiring (Set.mem_univ _) (Set.mem_univ _) h

/-- The canonical real mass retains the full additive content. -/
def escapeWeight : EscapeWeight Pair where
  mass C := (edgeCharge C : ℝ)
  empty_mass := by simp
  mass_nonnegative C := (edgeCharge C).coe_nonneg

abbrev R (S : Finset language) : Set Pair :=
  defectRelation (conceptJoin q (finiteSelectionSupplement language definitions S)) target
abbrev B : Set Pair := defectRelation q target ∩ jointKernel (fun i : language => definitions i.1)
def F (n : ℕ) : Finset language := (Finset.range n).image
  (fun j => (⟨j+1, Nat.succ_le_succ (Nat.zero_le j)⟩ : language))
abbrev A (n : ℕ) : Set Pair := R (F (n+1))

private lemma residual_difference (S : Finset language) :
    R S = defectRelation q target \ ⋃ i ∈ S, defectRelation q target ∩
      (conceptKernel (fun j : language => definitions j.1) i)ᶜ :=
  (blind_residual_charge_decomposition language definitions q target unitCost 0 S
    Set.univ full_ring edgeCharge (Set.to_countable _) (by intros; norm_num [unitCost])
    (by norm_num) (by rw [baseline_mass]; norm_num)
    (Set.mem_univ _) (Set.mem_univ _) (fun _ => Set.mem_univ _)).2.1

/-- A finite selection leaves exactly those indices exceeding every selected cutoff. -/
theorem residual_edge_preimage (S : Finset language) (b : Bool) :
    edge b ⁻¹' R S = {k : ℕ | ∀ j ∈ S, j.val < k} := by
  rw [residual_difference]
  ext k
  cases b <;> simp [edge, defectRelation, q, target, conceptKernel, definitions, not_le]

theorem tail_survives (S : Finset language) (b : Bool) :
    Set.Ioi (S.sup (fun i => i.1)) ⊆ edge b ⁻¹' R S := by
  rw [residual_edge_preimage]
  exact fun _ hk j hj => lt_of_le_of_lt (Finset.le_sup hj) hk

private lemma residual_charge (S : Finset language) : edgeCharge (R S) = 1 := by
  have h (b : Bool) : edge b ⁻¹' R S ∈ hyperfilter ℕ :=
    Filter.mem_of_superset (Nat.hyperfilter_le_atTop (Ioi_mem_atTop _)) (tail_survives S b)
  norm_num [edge_charge_formula, mu_formula, h]

theorem finite_residual_mass_eq_one (S : Finset language) :
    finiteResidualMass language definitions q target escapeWeight S = 1 := by
  change (edgeCharge (R S) : ℝ) = 1
  rw [residual_charge]
  rfl

theorem baseline_edges :
    defectRelation q target = Set.range (edge false) ∪ Set.range (edge true) := by
  ext ⟨⟨k,b⟩,⟨l,c⟩⟩
  cases b <;> cases c <;> simp [defectRelation, q, target, edge, Prod.ext_iff]

private lemma definitions_injective : Function.Injective (fun i : language => definitions i.1) := by
  intro i j h
  apply Subtype.ext
  apply Nat.le_antisymm
  · by_contra hij
    have := congrFun h (i.val,true)
    simp [definitions, hij] at this
  · by_contra hji
    have := congrFun h (j.val,true)
    simp [definitions, hji] at this

private lemma selection_cost (S : Finset language) :
    finiteSelectionCost language unitCost S = (S.card : ℝ) := by
  simp [finiteSelectionCost, unitCost]

private lemma mem_F (i : language) (n : ℕ) : i ∈ F n ↔ i.val ≤ n := by
  constructor
  · intro h
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp h
    have he := congrArg Subtype.val hji
    have hjn := Finset.mem_range.mp hj
    change j+1 = i.val at he
    omega
  · intro hi
    have ip : 1 ≤ i.val := i.property
    refine Finset.mem_image.mpr ⟨i.val-1, Finset.mem_range.mpr (by omega), ?_⟩
    apply Subtype.ext
    change i.val-1+1 = i.val
    omega

/-- The positive initial segment leaves precisely the two directed tails. -/
theorem initial_residual_eq_tail (n : ℕ) (hn : 1 ≤ n) :
    R (F n) = edge false '' Set.Ioi n ∪ edge true '' Set.Ioi n := by
  have pre (b : Bool) : edge b ⁻¹' R (F n) = Set.Ioi n := by
    rw [residual_edge_preimage]
    ext k
    constructor
    · intro h
      exact h ⟨n,hn⟩ ((mem_F _ _).mpr le_rfl)
    · intro h j hj
      exact lt_of_le_of_lt ((mem_F _ _).mp hj) h
  apply Set.Subset.antisymm
  · intro p hp
    have hE : p ∈ defectRelation q target := by
      rw [residual_difference] at hp
      exact hp.1
    rw [baseline_edges] at hE
    rcases hE with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · exact Or.inl ⟨k, pre false ▸ hp, rfl⟩
    · exact Or.inr ⟨k, pre true ▸ hp, rfl⟩
  · rintro p (⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩)
    · exact show k ∈ edge false ⁻¹' R (F n) from (pre false).symm ▸ hk
    · exact show k ∈ edge true ⁻¹' R (F n) from (pre true).symm ▸ hk

private lemma prefixes_monotone : Monotone F := by
  intro n m h i hi
  exact (mem_F i m).mpr (((mem_F i n).mp hi).trans h)

private lemma prefixes_exhaust (i : language) : ∃ n : ℕ, i ∈ F (n+1) :=
  ⟨i.val, (mem_F _ _).mpr (Nat.le_succ _)⟩

theorem blind_empty : B = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hE,hB⟩
  rw [baseline_edges] at hE
  rcases hE with ⟨k,rfl⟩ | ⟨k,rfl⟩ <;>
    have h := Set.mem_iInter.mp hB (⟨k+1, Nat.succ_le_succ (Nat.zero_le k)⟩ : language) <;>
    simp [conceptKernel, definitions, edge] at h

private lemma chain_antitone : Antitone A := by
  intro n m h
  change R (F (m+1)) ⊆ R (F (n+1))
  rw [initial_residual_eq_tail _ (by omega), initial_residual_eq_tail _ (by omega)]
  exact Set.union_subset_union
    (Set.image_mono (Set.Ioi_subset_Ioi (Nat.add_le_add_right h 1)))
    (Set.image_mono (Set.Ioi_subset_Ioi (Nat.add_le_add_right h 1)))

private lemma chain_inter_empty : (⋂ n : ℕ, A n) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := Set.mem_iInter.mp hp p.1.1
  change p ∈ R (F (p.1.1+1)) at h
  rw [initial_residual_eq_tail _ (by omega)] at h
  rcases h with ⟨k,hk,he⟩ | ⟨k,hk,he⟩ <;>
    have he' := congrArg (fun z : Pair => z.1.1) he <;>
    change p.1.1+1 < k at hk <;>
    change k = p.1.1 at he' <;> omega

private lemma chain_not_continuous :
    ¬Tendsto (fun n : ℕ => (edgeCharge (A n) : ℝ)) atTop
      (nhds ((edgeCharge ∅ : NNReal) : ℝ)) := by
  simp [A, residual_charge, tendsto_const_nhds_iff]

/-- Every nonnegative budget admits the empty selection and only mass one. -/
theorem finite_budget_values_eq_singleton (L : NNReal) :
    finiteBudgetMassValues language definitions q target unitCost escapeWeight L = {1} := by
  ext x
  constructor
  · rintro ⟨S,_,rfl⟩
    exact finite_residual_mass_eq_one S
  · rintro rfl
    exact ⟨∅, by simp [selection_cost, L.coe_nonneg],
      finite_residual_mass_eq_one ∅⟩

theorem finite_spectrum_eq_one (L : NNReal) :
    finiteEscapeSpectrum language definitions q target unitCost escapeWeight L = 1 := by
  change sInf (finiteBudgetMassValues language definitions q target unitCost escapeWeight L) /
    (edgeCharge (defectRelation q target) : ℝ) = 1
  rw [finite_budget_values_eq_singleton, baseline_mass]
  simp

/-- A free full-powerset charge separates finite escape from blind mass and continuity. -/
theorem free_ultrafilter_charge_countermodel :
    language.Countable ∧ language.Nonempty ∧
    Function.Injective (fun i : language => definitions i.1) ∧
    (∀ i ∈ language, 0 < unitCost i) ∧
    (∀ S : Finset language, finiteSelectionCost language unitCost S = (S.card : ℝ)) ∧
    (defectRelation q target = Set.range (edge false) ∪ Set.range (edge true)) ∧
    ((↑(hyperfilter ℕ) : Filter ℕ) ≤ Filter.cofinite) ∧
    (∀ C : Set ℕ, C.Finite → C ∉ hyperfilter ℕ) ∧
    (∀ C : Set ℕ, mu C = if C ∈ hyperfilter ℕ then (1 : NNReal) else 0) ∧
    (∀ C : Set Pair, edgeCharge C = (1/2 : NNReal) * mu (edge false ⁻¹' C) +
      (1/2 : NNReal) * mu (edge true ⁻¹' C)) ∧
    (∀ C : Set Pair, edgeCharge C = edgeCharge (C ∩ defectRelation q target)) ∧
    (edgeCharge ∅ = 0) ∧ Monotone (fun C : Set Pair => edgeCharge C) ∧
    (∀ C : Set Pair, 0 ≤ (edgeCharge C : ℝ)) ∧
    (∀ C D : Set Pair, Disjoint C D → edgeCharge (C ∪ D) = edgeCharge C + edgeCharge D) ∧
    (edgeCharge (defectRelation q target) = 1) ∧ (B = ∅) ∧
    (∀ S : Finset language, finiteResidualMass language definitions q target escapeWeight S = 1) ∧
    (∀ n : ℕ, 1 ≤ n → R (F n) = edge false '' Set.Ioi n ∪ edge true '' Set.Ioi n) ∧
    Monotone F ∧ (∀ i : language, ∃ n : ℕ, i ∈ F (n+1)) ∧
    Antitone A ∧ ((⋂ n : ℕ, A n) = ∅) ∧
    (¬Tendsto (fun n : ℕ => (edgeCharge (A n) : ℝ)) atTop
      (nhds ((edgeCharge ∅ : NNReal) : ℝ))) ∧
    (∀ L : NNReal,
      finiteEscapeSpectrum language definitions q target unitCost escapeWeight L = 1) := by
  refine ⟨Set.to_countable _, ⟨1, by norm_num [language]⟩, definitions_injective,
    (by intros; norm_num [unitCost]), selection_cost, baseline_edges,
    Filter.hyperfilter_le_cofinite, (fun _ h => Filter.notMem_hyperfilter_of_finite h),
    mu_formula, edge_charge_formula, edge_charge_supported, by simp, charge_mono,
    (fun C => (edgeCharge C).coe_nonneg), ?_, baseline_mass, blind_empty,
    finite_residual_mass_eq_one, initial_residual_eq_tail, prefixes_monotone,
    prefixes_exhaust, chain_antitone, chain_inter_empty, chain_not_continuous,
    finite_spectrum_eq_one⟩
  exact fun _ _ h => addContent_union full_ring (Set.mem_univ _) (Set.mem_univ _) h

end D5.S3.ConceptDynamics.EscapeSpectrum.FreeUltrafilterChargeCountermodel

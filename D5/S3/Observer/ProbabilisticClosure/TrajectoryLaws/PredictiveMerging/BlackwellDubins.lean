/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PredictiveMerging/BlackwellDubins
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PredictiveMerging/BlackwellDubins
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolutely continuous predictive opinions merge on the full infinite future. -/

import Mathlib.Probability.Kernel.IonescuTulcea.Maps
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.Probability.Process.Filtration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.JointConditionalDominatedConvergence
import D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins

attribute [local instance] Classical.propDecidable

universe u v w

section Coordinates

variable (X : ℕ → Type u) [∀ i, MeasurableSpace (X i)]

/-- The entire history with its product measurable space. -/
abbrev History := ∀ i, X i

/-- The coordinates `0, …, n`, equivalently the natural indices below `n + 1`. -/
abbrev Past (n : ℕ) := ∀ i : Iic n, X i

/-- The entire infinite future after coordinate `n`. -/
abbrev Future (n : ℕ) := ∀ j : ℕ, X (n + 1 + j)

/-- The actual dependent tail reindexing. -/
def tailIndex (n : ℕ) : ℕ ≃ Ioi n where
  toFun j := ⟨n + 1 + j, Set.mem_Ioi.mpr
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right (n + 1) j))⟩
  invFun i := i.1 - (n + 1)
  left_inv j := Nat.add_sub_cancel_left (n + 1) j
  right_inv i := Subtype.ext
    (Nat.add_sub_of_le (Nat.succ_le_of_lt (Set.mem_Ioi.mp i.2)))

/-- The tail index equivalence acts on dependent measurable products. -/
def tailReindex (n : ℕ) : (∀ i : Ioi n, X i) ≃ᵐ Future X n :=
  (MeasurableEquiv.piCongrLeft (fun i : Ioi n => X i) (tailIndex n)).symm

/-- Reindex the finite prefix by the identical set of natural coordinates. -/
private def prefixReindex (n : ℕ) : (∀ i : Finset.Iic n, X i) ≃ᵐ Past X n :=
  (MeasurableEquiv.piCongrLeft (fun i : Finset.Iic n => X i)
    (Equiv.IicFinsetSet n).symm).symm

/-- Split a history into its actual prefix and the reindexed infinite tail. -/
def split (n : ℕ) : History X ≃ᵐ Past X n × Future X n :=
  (MeasurableEquiv.IicProdIoi (X := X) n).symm.trans
    ((prefixReindex X n).prodCongr (tailReindex X n))

/-- Prefix projection on histories. -/
def past (n : ℕ) (ω : History X) : Past X n := fun i => ω i

private theorem past_measurable (n : ℕ) : Measurable (past X n) := by
  exact Measurable.of_eval fun i => measurable_pi_apply (i : ℕ)

private theorem split_fst_map (n : ℕ) (R : Measure (History X)) :
    (R.map (split X n)).fst = R.map (past X n) := by
  change (R.map (split X n)).map Prod.fst = R.map (past X n)
  rw [Measure.map_map measurable_fst (split X n).measurable]
  have hfst : Prod.fst ∘ split X n = past X n := by
    funext ω i
    rfl
  rw [hfst]

end Coordinates

section RowNormalization

variable {A : Type v} {B : Type w} [MeasurableSpace A] [MeasurableSpace B]

/-- The extended nonnegative mass of a row. It may be zero or infinite. -/
def rowMass (κ : Kernel A B) (h : A × B → ℝ≥0∞) (a : A) : ℝ≥0∞ :=
  ∫⁻ b, h (a, b) ∂κ a

/-- Exactly the rows admitting ordinary positive finite normalization. -/
def goodRows (κ : Kernel A B) (h : A × B → ℝ≥0∞) : Set A :=
  {a | 0 < rowMass κ h a ∧ rowMass κ h a < ∞}

/-- Bad rows retain the original probability row, including infinite-mass rows. -/
def rowDensity (κ : Kernel A B) (h : A × B → ℝ≥0∞) (a : A) (b : B) : ℝ≥0∞ :=
  if a ∈ goodRows κ h then h (a, b) / rowMass κ h a else 1

/-- A totalized density change, with no chosen default point in the future space. -/
def normalizedKernel (κ : Kernel A B) [IsSFiniteKernel κ]
    (h : A × B → ℝ≥0∞) : Kernel A B :=
  κ.withDensity (rowDensity κ h)

private theorem row_mass_measurable (κ : Kernel A B) [IsSFiniteKernel κ]
    {h : A × B → ℝ≥0∞} (hh : Measurable h) : Measurable (rowMass κ h) :=
  hh.lintegral_kernel_prod_right'

private theorem good_rows_measurable (κ : Kernel A B) [IsSFiniteKernel κ]
    {h : A × B → ℝ≥0∞} (hh : Measurable h) : MeasurableSet (goodRows κ h) :=
  (measurableSet_lt measurable_const (row_mass_measurable κ hh)).inter
    (measurableSet_lt (row_mass_measurable κ hh) measurable_const)

private theorem row_density_measurable (κ : Kernel A B) [IsSFiniteKernel κ]
    {h : A × B → ℝ≥0∞} (hh : Measurable h) :
    Measurable (Function.uncurry (rowDensity κ h)) := by
  exact (hh.div ((row_mass_measurable κ hh).comp measurable_fst)).ite
    ((good_rows_measurable κ hh).preimage measurable_fst) measurable_const

private theorem row_density_ne_top (κ : Kernel A B)
    {h : A × B → ℝ≥0∞} (hfinite : ∀ p, h p ≠ ∞) (a : A) (b : B) :
    rowDensity κ h a b ≠ ∞ := by
  classical
  by_cases ha : a ∈ goodRows κ h
  · simp only [rowDensity, ha, ite_true]
    exact ENNReal.div_ne_top (hfinite (a, b)) ha.1.ne'
  · simp [rowDensity, ha]

private theorem row_density_integral (κ : Kernel A B) [IsMarkovKernel κ]
    {h : A × B → ℝ≥0∞} (hh : Measurable h) (a : A) :
    (∫⁻ b, rowDensity κ h a b ∂κ a) = 1 := by
  classical
  by_cases ha : a ∈ goodRows κ h
  · simp only [rowDensity, ha, ite_true, div_eq_mul_inv]
    exact (lintegral_mul_const (μ := κ a) (f := fun b : B => h (a, b))
      (rowMass κ h a)⁻¹ (hh.comp measurable_prodMk_left)).trans
      (ENNReal.mul_inv_cancel ha.1.ne' ha.2.ne)
  · simp [rowDensity, ha]

private theorem normalized_is_markov (κ : Kernel A B) [IsMarkovKernel κ]
    {h : A × B → ℝ≥0∞} (hh : Measurable h) :
    IsMarkovKernel (normalizedKernel κ h) where
  isProbabilityMeasure a := ⟨by
    rw [normalizedKernel, Kernel.withDensity_apply _ (row_density_measurable κ hh),
      withDensity_apply _ MeasurableSet.univ]
    simpa only [Measure.restrict_univ] using row_density_integral κ hh a⟩

/-- Reconstruction discards infinite rows only in an almost-everywhere density identity.
Zero rows require the separate zero-integral argument. -/
private theorem normalized_comp_prod (μ : Measure A) [SFinite μ]
    (κ : Kernel A B) [IsMarkovKernel κ]
    {h : A × B → ℝ≥0∞} (hh : Measurable h) (hfinite : ∀ p, h p ≠ ∞)
    (hint : (∫⁻ p, h p ∂(μ ⊗ₘ κ)) ≠ ∞) :
    (μ.withDensity (rowMass κ h)) ⊗ₘ normalizedKernel κ h =
      (μ ⊗ₘ κ).withDensity h := by
  classical
  have hm := row_mass_measurable κ hh
  have hd := row_density_measurable κ hh
  letI : IsSFiniteKernel (κ.withDensity (rowDensity κ h)) :=
    Kernel.IsSFiniteKernel.withDensity κ (row_density_ne_top κ hfinite)
  have hfin : ∀ᵐ a ∂μ, rowMass κ h a < ∞ := by
    apply ae_lt_top hm
    simpa only [Measure.lintegral_compProd hh, rowMass] using hint
  have hfactor : (fun p : A × B => rowMass κ h p.1 * rowDensity κ h p.1 p.2)
      =ᵐ[μ ⊗ₘ κ] h := by
    apply (Measure.ae_compProd_iff
      (measurableSet_eq_fun ((hm.comp measurable_fst).mul hd) hh)).mpr
    filter_upwards [hfin] with a ha
    change ∀ᵐ b ∂κ a, rowMass κ h a * rowDensity κ h a b = h (a, b)
    by_cases hz : rowMass κ h a = 0
    · have hzero : (fun b => h (a, b)) =ᵐ[κ a] 0 :=
        (lintegral_eq_zero_iff (hh.comp measurable_prodMk_left)).mp hz
      filter_upwards [hzero] with b hb
      simpa only [hz, zero_mul, Pi.zero_apply] using hb.symm
    · have hg : a ∈ goodRows κ h := ⟨pos_iff_ne_zero.mpr hz, ha⟩
      exact ae_of_all _ fun b => by
        simp only [rowDensity, hg, ite_true]
        exact ENNReal.mul_div_cancel hz ha.ne
  change (μ.withDensity (rowMass κ h)) ⊗ₘ κ.withDensity (rowDensity κ h) = _
  rw [Measure.withDensity_compProd_withDensity (μ := μ) (κ := κ)
    (f := rowMass κ h) (g := rowDensity κ h) hm hd]
  exact withDensity_congr_ae hfactor

end RowNormalization

section FiniteDensity

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A finite-valued real representative of the Radon–Nikodym density. -/
def likelihood (P Q : Measure Ω) (ω : Ω) : ℝ := (Q.rnDeriv P ω).toReal

/-- Totalizing the real representative also removes the RN infinity null set. -/
def finiteDensity (P Q : Measure Ω) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (likelihood P Q ω)

private theorem finite_density_measurable (P Q : Measure Ω) :
    Measurable (finiteDensity P Q) :=
  (Measure.measurable_rnDeriv Q P).ennreal_toReal.ennreal_ofReal

private theorem finite_density_eq (P Q : Measure Ω) [IsFiniteMeasure Q] :
    finiteDensity P Q =ᵐ[P] Q.rnDeriv P := by
  filter_upwards [Measure.rnDeriv_ne_top Q P] with ω hω
  exact ENNReal.ofReal_toReal hω

private theorem finite_density_measure (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hQP : Q ≪ P) :
    P.withDensity (finiteDensity P Q) = Q := by
  rw [withDensity_congr_ae (finite_density_eq P Q)]
  exact Measure.withDensity_rnDeriv_eq Q P hQP

end FiniteDensity

section PredictiveChangeOfMeasure

variable (X : ℕ → Type u) [∀ i, MeasurableSpace (X i)]

/-- The constructed density in actual prefix/future coordinates. -/
def splitDensity (P Q : Measure (History X)) (n : ℕ) : Past X n × Future X n → ℝ≥0∞ :=
  fun p => finiteDensity P Q ((split X n).symm p)

/-- The Q predictive kernel constructed after choosing the P predictive kernel. -/
def changedKernel (P Q : Measure (History X)) (n : ℕ)
    (κ : Kernel (Past X n) (Future X n)) [IsSFiniteKernel κ] :
    Kernel (Past X n) (Future X n) :=
  normalizedKernel κ (splitDensity X P Q n)

/-- Absolute continuity preserves predictiveness for the chosen P kernel versions.
Normalization holds on every row; positivity and finite row mass are derived only almost
everywhere under the Q prefix marginal. No regularity of the coordinate spaces is required. -/
theorem predictive_change_of_measure
    (P Q : Measure (History X)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P)
    (κ : (n : ℕ) → Kernel (Past X n) (Future X n)) [∀ n, IsMarkovKernel (κ n)]
    (hκ : ∀ n, P.map (split X n) = (P.map (past X n)) ⊗ₘ κ n) :
    Measurable (likelihood P Q) ∧
    (∀ ω, 0 ≤ likelihood P Q ω) ∧
    Integrable (likelihood P Q) P ∧
    (∫ ω, likelihood P Q ω ∂P) = 1 ∧
    P.withDensity (finiteDensity P Q) = Q ∧
    (∀ᵐ ω ∂Q, 0 < likelihood P Q ω) ∧
    ∀ n, Measurable (rowMass (κ n) (splitDensity X P Q n)) ∧
      Measurable (Function.uncurry (rowDensity (κ n) (splitDensity X P Q n))) ∧
      (∀ a b, rowDensity (κ n) (splitDensity X P Q n) a b ≠ ∞) ∧
      (∀ a, (∫⁻ b, rowDensity (κ n) (splitDensity X P Q n) a b ∂κ n a) = 1) ∧
      IsMarkovKernel (changedKernel X P Q n (κ n)) ∧
      Q.map (past X n) =
        (P.map (past X n)).withDensity (rowMass (κ n) (splitDensity X P Q n)) ∧
      (∫⁻ a, rowMass (κ n) (splitDensity X P Q n) a ∂P.map (past X n)) = 1 ∧
      Q.map (split X n) = (Q.map (past X n)) ⊗ₘ changedKernel X P Q n (κ n) ∧
      ((fun ω => (rowMass (κ n) (splitDensity X P Q n) (past X n ω)).toReal)
        =ᵐ[P] P[likelihood P Q | Filtration.piLE (X := X) n]) ∧
      (∀ᵐ a ∂Q.map (past X n), a ∈ goodRows (κ n) (splitDensity X P Q n)) := by
  have hfm := finite_density_measurable P Q
  have hfd := finite_density_measure P Q hQP
  have hpos : ∀ᵐ ω ∂Q, 0 < likelihood P Q ω := by
    filter_upwards [Measure.rnDeriv_pos hQP, hQP.ae_le (Measure.rnDeriv_ne_top Q P)]
      with ω hp ht
    exact ENNReal.toReal_pos hp.ne' ht
  refine ⟨(Measure.measurable_rnDeriv Q P).ennreal_toReal,
    fun ω => ENNReal.toReal_nonneg, Measure.integrable_toReal_rnDeriv, ?_, hfd, hpos, ?_⟩
  · simpa only [likelihood, probReal_univ] using Measure.integral_toReal_rnDeriv hQP
  · intro n
    let μ := P.map (past X n)
    let h := splitDensity X P Q n
    have hh : Measurable h := hfm.comp (split X n).symm.measurable
    have hf : ∀ p, h p ≠ ∞ := fun p => ENNReal.ofReal_ne_top
    have hm := row_mass_measurable (κ n) hh
    have hd := row_density_measurable (κ n) hh
    have hsplit : Q.map (split X n) = (μ ⊗ₘ κ n).withDensity h := by
      have hRN : h =ᵐ[P.map (split X n)]
          (Q.map (split X n)).rnDeriv (P.map (split X n)) := by
        rw [Filter.EventuallyEq, (split X n).measurableEmbedding.ae_map_iff]
        filter_upwards [finite_density_eq P Q,
          (split X n).measurableEmbedding.rnDeriv_map Q P] with ω hω hr
        simpa only [h, splitDensity, (split X n).symm_apply_apply] using hω.trans hr.symm
      calc
        Q.map (split X n) = (P.map (split X n)).withDensity
            ((Q.map (split X n)).rnDeriv (P.map (split X n))) :=
          (Measure.withDensity_rnDeriv_eq _ _ (hQP.map (split X n).measurable)).symm
        _ = (P.map (split X n)).withDensity h := withDensity_congr_ae hRN.symm
        _ = (μ ⊗ₘ κ n).withDensity h := by rw [hκ n]
    have hint : (∫⁻ p, h p ∂(μ ⊗ₘ κ n)) = 1 := by
      calc
        (∫⁻ p, h p ∂(μ ⊗ₘ κ n)) = ((μ ⊗ₘ κ n).withDensity h) univ := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        _ = (Q.map (split X n)) univ :=
          congrArg (fun R : Measure (Past X n × Future X n) => R univ) hsplit.symm
        _ = 1 := measure_univ
    have hnorm := normalized_comp_prod μ (κ n) hh hf (hint.trans_ne ENNReal.one_ne_top)
    letI : IsMarkovKernel (changedKernel X P Q n (κ n)) := normalized_is_markov (κ n) hh
    have hsplit' : Q.map (split X n) =
        (μ.withDensity (rowMass (κ n) h)) ⊗ₘ changedKernel X P Q n (κ n) :=
      hsplit.trans hnorm.symm
    have hmarg : Q.map (past X n) = μ.withDensity (rowMass (κ n) h) := by
      calc
        Q.map (past X n) = (Q.map (split X n)).fst := (split_fst_map X n Q).symm
        _ = ((μ.withDensity (rowMass (κ n) h)) ⊗ₘ
            changedKernel X P Q n (κ n)).fst := congrArg Measure.fst hsplit'
        _ = μ.withDensity (rowMass (κ n) h) := Measure.fst_compProd _ _
    have hmass : (∫⁻ a, rowMass (κ n) h a ∂μ) = 1 := by
      calc
        (∫⁻ a, rowMass (κ n) h a ∂μ) = (μ.withDensity (rowMass (κ n) h)) univ := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        _ = (Q.map (past X n)) univ :=
          congrArg (fun R : Measure (Past X n) => R univ) hmarg.symm
        _ = 1 := measure_univ
    have hfinP : ∀ᵐ a ∂μ, rowMass (κ n) h a < ∞ :=
      ae_lt_top hm (hmass.trans_ne ENNReal.one_ne_top)
    have hfinQ : ∀ᵐ a ∂Q.map (past X n), rowMass (κ n) h a < ∞ :=
      (hQP.map (past_measurable X n)).ae_le hfinP
    have hposQ : ∀ᵐ a ∂Q.map (past X n), 0 < rowMass (κ n) h a := by
      rw [hmarg, ae_withDensity_iff hm]
      exact ae_of_all _ fun a ha => ha.pos
    have hrn : (Q.map (past X n)).rnDeriv μ =ᵐ[μ] rowMass (κ n) h := by
      rw [hmarg]
      exact Measure.rnDeriv_withDensity μ hm
    have hce : (fun ω => (rowMass (κ n) h (past X n ω)).toReal)
        =ᵐ[P] P[likelihood P Q | Filtration.piLE (X := X) n] := by
      filter_upwards [ae_of_ae_map (past_measurable X n).aemeasurable hrn,
        toReal_rnDeriv_map hQP (past_measurable X n)] with ω hr hc
      rw [← hr]
      exact hc
    refine ⟨hm, hd, row_density_ne_top (κ n) hf,
      row_density_integral (κ n) hh, inferInstance, hmarg, hmass, ?_, hce, ?_⟩
    · rw [hmarg]
      exact hsplit'
    · filter_upwards [hposQ, hfinQ] with a ha hb
      exact ⟨ha, hb⟩

end PredictiveChangeOfMeasure

section ConditionalOverlap

variable (X : ℕ → Type u) [∀ i, MeasurableSpace (X i)]

private theorem full_prefix_filtration :
    (⨆ n : ℕ, Filtration.piLE (X := X) n) =
      (inferInstance : MeasurableSpace (History X)) := by
  apply le_antisymm (iSup_le fun n => Filtration.piLE.le n)
  have hid : @Measurable (History X) (History X)
      (⨆ n : ℕ, Filtration.piLE (X := X) n) inferInstance id := by
    apply measurable_pi_iff.mpr
    intro n
    have hc : Measurable[Filtration.piLE (X := X) n]
        (fun ω : History X => ω n) :=
      (measurable_pi_apply (X := fun i : Iic n => X i.1) ⟨n, le_rfl⟩).comp
        (comap_measurable (Preorder.restrictLe (π := X) n))
    exact hc.mono (le_iSup (fun n : ℕ => Filtration.piLE (X := X) n) n) le_rfl
  simpa only [MeasurableSpace.comap_id] using hid.comap_le

/-- The supplied predictive law identifies scalar row integrals with conditional means.
Only prefix-almost-everywhere integrability of the original rows is used. -/
private theorem conditional_row_integral
    (P : Measure (History X)) [IsProbabilityMeasure P] (n : ℕ)
    (κ : Kernel (Past X n) (Future X n)) [IsMarkovKernel κ]
    (hκ : P.map (split X n) = (P.map (past X n)) ⊗ₘ κ)
    (f : History X → ℝ) (hfm : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfi : Integrable f P) :
    (fun ω => ∫ v, f ((split X n).symm (past X n ω, v)) ∂κ (past X n ω))
      =ᵐ[P] P[f | Filtration.piLE (X := X) n] := by
  let μ := P.map (past X n)
  let z : Past X n × Future X n → ℝ := fun p => f ((split X n).symm p)
  let a : Past X n → ℝ := fun u => ∫ v, z (u, v) ∂κ u
  have hzm : Measurable z := hfm.comp (split X n).symm.measurable
  have hzi : Integrable z (μ ⊗ₘ κ) := by
    rw [← hκ]
    apply (split X n).measurableEmbedding.integrable_map_iff.mpr
    simpa only [z, Function.comp_def, (split X n).symm_apply_apply] using hfi
  have ham : StronglyMeasurable a := hzm.stronglyMeasurable.integral_kernel_prod_right'
  have hai : Integrable a μ := by
    have hi := ((Measure.integrable_compProd_iff hzm.aestronglyMeasurable).mp hzi).2
    have heq : (fun u => ∫ v, ‖z (u, v)‖ ∂κ u) = a := by
      funext u
      apply integral_congr_ae
      exact ae_of_all _ fun v => Real.norm_of_nonneg (hf0 _)
    rwa [heq] at hi
  have hp := past_measurable X n
  have hpi : Filtration.piLE (X := X) n =
      (inferInstance : MeasurableSpace (Past X n)).comap (past X n) := rfl
  rw [hpi]
  refine ae_eq_condExp_of_forall_setIntegral_eq hp.comap_le hfi
    (fun _ _ _ => (hai.comp_measurable hp).integrableOn) ?_
    (ham.comp_measurable (comap_measurable (past X n))).aestronglyMeasurable
  intro s hs _
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  calc
    (∫ ω in (past X n) ⁻¹' t, a (past X n ω) ∂P) = ∫ u in t, a u ∂μ :=
      (setIntegral_map ht ham.aestronglyMeasurable hp.aemeasurable).symm
    _ = ∫ p in t ×ˢ univ, z p ∂(μ ⊗ₘ κ) := by
      simpa only [a, Measure.restrict_univ] using
        (Measure.setIntegral_compProd ht MeasurableSet.univ hzi.integrableOn).symm
    _ = ∫ p in t ×ˢ univ, z p ∂P.map (split X n) := by rw [hκ]
    _ = ∫ ω in (past X n) ⁻¹' t, f ω ∂P := by
      rw [setIntegral_map_equiv]
      have hs : (split X n) ⁻¹' (t ×ˢ univ) = (past X n) ⁻¹' t := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] <;> rfl
      simp only [hs, z, (split X n).symm_apply_apply]

/-- The scalar overlap numerator in the actual infinite-future row. -/
def overlapNumerator (P Q : Measure (History X)) (n : ℕ)
    (κ : Kernel (Past X n) (Future X n)) (u : Past X n) : ℝ :=
  ∫ v, min (likelihood P Q ((split X n).symm (u, v)))
    (rowMass κ (splitDensity X P Q n) u).toReal ∂κ u

private theorem overlap_limits
    (P Q : Measure (History X)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P)
    (κ : (n : ℕ) → Kernel (Past X n) (Future X n)) [∀ n, IsMarkovKernel (κ n)]
    (hκ : ∀ n, P.map (split X n) = (P.map (past X n)) ⊗ₘ κ n) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => (rowMass (κ n) (splitDensity X P Q n) (past X n ω)).toReal)
        atTop (𝓝 (likelihood P Q ω)) ∧
      Tendsto (fun n => overlapNumerator X P Q n (κ n) (past X n ω))
        atTop (𝓝 (likelihood P Q ω)) := by
  obtain ⟨hqm, hq0, hqi, _, _, _, hn⟩ :=
    predictive_change_of_measure X P Q hQP κ hκ
  let c : (n : ℕ) → Past X n → ℝ :=
    fun n u => (rowMass (κ n) (splitDensity X P Q n) u).toReal
  have hcm (n : ℕ) : Measurable (c n) := (hn n).1.ennreal_toReal
  have hc0 (n : ℕ) (u : Past X n) : 0 ≤ c n u := ENNReal.toReal_nonneg
  have hce (n : ℕ) : (fun ω => c n (past X n ω))
      =ᵐ[P] P[likelihood P Q | Filtration.piLE (X := X) n] :=
    (hn n).2.2.2.2.2.2.2.2.1
  have hfull := full_prefix_filtration X
  have hqs : StronglyMeasurable[⨆ n, Filtration.piLE (X := X) n] (likelihood P Q) := by
    rw [hfull]
    exact hqm.stronglyMeasurable
  have hcLim : ∀ᵐ ω ∂P, Tendsto (fun n => c n (past X n ω))
      atTop (𝓝 (likelihood P Q ω)) := by
    filter_upwards [hqi.tendsto_ae_condExp hqs, ae_all_iff.mpr hce] with ω hl he
    exact hl.congr' (Eventually.of_forall fun n => (he n).symm)
  let y : ℕ → History X → ℝ := fun n ω => min (likelihood P Q ω) (c n (past X n ω))
  have hym (n : ℕ) : Measurable (y n) := hqm.min ((hcm n).comp (past_measurable X n))
  have hy0 (n : ℕ) (ω : History X) : 0 ≤ y n ω := le_min (hq0 ω) (hc0 n _)
  have hyb (n : ℕ) : ∀ᵐ ω ∂P, |y n ω| ≤ likelihood P Q ω :=
    ae_of_all _ fun ω => by rw [abs_of_nonneg (hy0 n ω)]; exact min_le_left _ _
  have hyi (n : ℕ) : Integrable (y n) P :=
    hqi.mono' (hym n).aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hyb n)
  have hyLim : ∀ᵐ ω ∂P, Tendsto (fun n => y n ω) atTop (𝓝 (likelihood P Q ω)) := by
    filter_upwards [hcLim] with ω hω
    have hconst : Tendsto (fun _ : ℕ => likelihood P Q ω) atTop
        (𝓝 (likelihood P Q ω)) := tendsto_const_nhds
    simpa only [min_self] using hconst.min hω
  have hjoint :=
    D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.JointConditionalDominatedConvergence.
      tendsto_condExp_of_dominated_convergence (Filtration.piLE (X := X))
        y (likelihood P Q) (likelihood P Q) hym hqm hyLim hqi hyb
  have hdiag : ∀ᵐ ω ∂P, Tendsto
      (fun n => P[y n | Filtration.piLE (X := X) n] ω) atTop (𝓝 (likelihood P Q ω)) := by
    have htop : P[likelihood P Q | ⨆ n, Filtration.piLE (X := X) n] = likelihood P Q := by
      rw [hfull]
      exact condExp_of_stronglyMeasurable le_rfl hqm.stronglyMeasurable hqi
    filter_upwards [hjoint.1] with ω hω
    simpa only [htop] using hω.comp tendsto_atTop_diagonal
  have ha (n : ℕ) : (fun ω => overlapNumerator X P Q n (κ n) (past X n ω))
      =ᵐ[P] P[y n | Filtration.piLE (X := X) n] := by
    have he := conditional_row_integral X P n (κ n) (hκ n) (y n) (hym n) (hy0 n) (hyi n)
    have hcoord (u : Past X n) (v : Future X n) :
        past X n ((split X n).symm (u, v)) = u := by
      have hh := congrArg Prod.fst ((split X n).apply_symm_apply (u, v))
      exact hh
    simpa only [y, overlapNumerator, hcoord, c] using he
  filter_upwards [hcLim, hdiag, ae_all_iff.mpr ha] with ω hc ha he
  exact ⟨hc, ha.congr' (Eventually.of_forall fun n => (he n).symm)⟩

end ConditionalOverlap

section EventOverlap

open D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling

/-- The existing individual-law common-part identity, evaluated at a normalized row. -/
private theorem row_overlap_identity
    {Y : Type v} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : Y → ℝ) (hgm : Measurable g) (hg0 : ∀ v, 0 ≤ g v)
    (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ∞)
    (hν : ν = μ.withDensity (fun v => ENNReal.ofReal (g v) / r)) :
    D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling.tvDist μ ν =
      1 - (∫ v, min (g v) r.toReal ∂μ) / r.toReal := by
  let d : Y → ℝ≥0∞ := fun v => ENNReal.ofReal (g v) / r
  have hdm : Measurable d := hgm.ennreal_ofReal.div_const r
  have hdf (v : Y) : d v ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hr0
  have hac : ν ≪ μ := by
    rw [hν]
    exact withDensity_absolutelyContinuous _ _
  have hrn : ν.rnDeriv μ =ᵐ[μ] d := by
    rw [hν]
    exact Measure.rnDeriv_withDensity μ hdm
  have hcommon : rnCommonPart μ ν μ = μ.withDensity (fun v => min 1 (d v)) := by
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_self μ, hrn] with v hμ hν
    simp only [hμ, hν]
  have hmass := congrArg ENNReal.toReal
    (rnCommonPart_mass_eq_one_sub_tvDist μ ν μ Measure.AbsolutelyContinuous.rfl hac)
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (tvDist_le_one (μ := μ) (ν := ν))),
    hcommon, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  have hc : 0 < r.toReal := ENNReal.toReal_pos hr0 hrt
  have hreal : (∫⁻ v, min 1 (d v) ∂μ).toReal =
      (∫ v, min (g v) r.toReal ∂μ) / r.toReal := by
    rw [← integral_toReal (measurable_const.min hdm).aemeasurable
      (ae_of_all _ fun v => (min_le_left 1 (d v)).trans_lt ENNReal.one_lt_top),
      ← integral_div]
    apply integral_congr_ae
    exact ae_of_all _ fun v => by
      dsimp only [d]
      rw [ENNReal.toReal_min ENNReal.one_ne_top (hdf v), ENNReal.toReal_one,
        ENNReal.toReal_div, ENNReal.toReal_ofReal (hg0 v), min_comm]
      simpa only [div_self hc.ne'] using min_div_div_right hc.le (g v) r.toReal
  rw [hreal] at hmass
  linarith

end EventOverlap

section PredictiveMerging

variable (X : ℕ → Type u) [∀ i, MeasurableSpace (X i)]

/-- Blackwell–Dubins merging for every chosen predictive P-kernel sequence.
The existential Q kernels use exactly the same prefix and infinite-future spaces.
The supremum over all measurable future events converges on one Q-full set of histories. -/
theorem blackwell_dubins_predictive_merging
    (P Q : Measure (History X)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P)
    (κ : (n : ℕ) → Kernel (Past X n) (Future X n)) [∀ n, IsMarkovKernel (κ n)]
    (hκ : ∀ n, P.map (split X n) = (P.map (past X n)) ⊗ₘ κ n) :
    ∃ eta : (n : ℕ) → Kernel (Past X n) (Future X n),
      (∀ n, IsMarkovKernel (eta n)) ∧
      (∀ n, Q.map (split X n) = (Q.map (past X n)) ⊗ₘ eta n) ∧
      ∀ᵐ ω ∂Q, Tendsto
        (fun n => sSup (Set.range (fun C : {C : Set (Future X n) // MeasurableSet C} =>
          |(κ n (past X n ω)).real C.val - (eta n (past X n ω)).real C.val|)))
        atTop (𝓝 0) := by
  obtain ⟨_, _, _, _, _, hpos, hn⟩ := predictive_change_of_measure X P Q hQP κ hκ
  let eta : (n : ℕ) → Kernel (Past X n) (Future X n) :=
    fun n => changedKernel X P Q n (κ n)
  have heta (n : ℕ) : IsMarkovKernel (eta n) := (hn n).2.2.2.2.1
  refine ⟨eta, heta, fun n => (hn n).2.2.2.2.2.2.2.1, ?_⟩
  have hgood : ∀ᵐ ω ∂Q, ∀ n,
      past X n ω ∈ goodRows (κ n) (splitDensity X P Q n) :=
    ae_all_iff.mpr fun n => ae_of_ae_map (past_measurable X n).aemeasurable
      (hn n).2.2.2.2.2.2.2.2.2
  have hlimits := hQP.ae_le (overlap_limits X P Q hQP κ hκ)
  filter_upwards [hpos, hgood, hlimits] with ω hq hg hl
  have heq (n : ℕ) :
      sSup (Set.range (fun C : {C : Set (Future X n) // MeasurableSet C} =>
        |(κ n (past X n ω)).real C.val - (eta n (past X n ω)).real C.val|)) =
      1 - overlapNumerator X P Q n (κ n) (past X n ω) /
        (rowMass (κ n) (splitDensity X P Q n) (past X n ω)).toReal := by
    letI : IsMarkovKernel (eta n) := heta n
    have hh : Measurable (splitDensity X P Q n) :=
      (finite_density_measurable P Q).comp (split X n).symm.measurable
    have hrow : eta n (past X n ω) = (κ n (past X n ω)).withDensity
        (fun v => ENNReal.ofReal (likelihood P Q ((split X n).symm (past X n ω, v))) /
          rowMass (κ n) (splitDensity X P Q n) (past X n ω)) := by
      change ((κ n).withDensity (rowDensity (κ n) (splitDensity X P Q n))) _ = _
      rw [Kernel.withDensity_apply _ (row_density_measurable (κ n) hh)]
      congr 1
      funext v
      exact if_pos (hg n)
    have hid := row_overlap_identity (κ n (past X n ω)) (eta n (past X n ω))
      (fun v => likelihood P Q ((split X n).symm (past X n ω, v)))
      (((Measure.measurable_rnDeriv Q P).ennreal_toReal.comp
        (split X n).symm.measurable).comp measurable_prodMk_left)
      (fun _ => ENNReal.toReal_nonneg)
      (rowMass (κ n) (splitDensity X P Q n) (past X n ω))
      (hg n).1.ne' (hg n).2.ne hrow
    exact hid
  have hratio := hl.2.div hl.1 hq.ne'
  have hzero : Tendsto
      (fun n => 1 - overlapNumerator X P Q n (κ n) (past X n ω) /
        (rowMass (κ n) (splitDensity X P Q n) (past X n ω)).toReal)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [div_self hq.ne', sub_self] using hconst.sub hratio
  exact hzero.congr' (Eventually.of_forall fun n => (heq n).symm)

end PredictiveMerging

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins

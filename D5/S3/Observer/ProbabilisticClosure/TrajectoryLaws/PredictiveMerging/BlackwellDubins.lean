/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PredictiveMerging/BlackwellDubins
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PredictiveMerging/BlackwellDubins
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute continuity transports predictive kernels by totalized row normalization. -/

import Mathlib.Probability.Kernel.IonescuTulcea.Maps
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.Probability.Process.Filtration

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
  toFun j := ⟨n + 1 + j, by change n < n + 1 + j; omega⟩
  invFun i := i.1 - (n + 1)
  left_inv j := by omega
  right_inv i := by
    apply Subtype.ext
    have hi := i.2
    dsimp only [mem_Ioi] at hi
    dsimp
    omega

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

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins

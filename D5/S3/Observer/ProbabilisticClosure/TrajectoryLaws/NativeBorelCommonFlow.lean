/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full legal-tail probability descriptors and acquired common-flow coordinate iteration. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Disintegration.Basic
import Mathlib.Probability.Kernel.WithDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open FourthSegmentStoppedLaw NativeFullResidual
open NativeConditionalControl.Tail

def lowerRate : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
def upperRate : unitInterval := ⟨2 / 5, by constructor <;> norm_num⟩
def lower : ℝ≥0∞ := 1 / 3
def upper : ℝ≥0∞ := 2 / 5
def tailRate : ℝ≥0∞ := 4 / 15
def endpointRate : ℝ≥0∞ := 6 / 25
def endpointCompletion : ℝ≥0∞ := 9 / 25

def pAtom (n : ℕ) (i : Letter) : ValidTail .p :=
  ⟨some (pWord n i), ⟨i, n, rfl⟩⟩
def betaAtom (n : ℕ) (i : Letter) : ValidTail .beta :=
  ⟨some (0 :: pWord n i), ⟨i, Or.inr ⟨n, rfl⟩⟩⟩
def betaStop : ValidTail .beta := ⟨some [1], ⟨1, Or.inl ⟨rfl, rfl⟩⟩⟩
def infinity (s : ActivePhase) : ValidTail s := ⟨none, trivial⟩

/-- Restore the beta Read deleted at p, retaining noncompletion. -/
def prependB (t : ValidTail .beta) : ValidTail .p := by
  rcases t with ⟨t, ht⟩
  cases t with
  | none => exact infinity .p
  | some w =>
    refine ⟨some (1 :: w), ?_⟩
    obtain ⟨i, hi⟩ := ht
    rcases hi with ⟨rfl, rfl⟩ | ⟨n, rfl⟩
    · exact ⟨1, 0, rfl⟩
    · exact ⟨i, n + 1, (p_word_succ n i).symm⟩

/-- Restore the alpha return Read deleted at suspension. -/
def prependA (t : ValidTail .p) : ValidTail .beta := by
  rcases t with ⟨t, ht⟩
  cases t with
  | none => exact infinity .beta
  | some w =>
    refine ⟨some (0 :: w), ?_⟩
    obtain ⟨i, n, rfl⟩ := ht
    exact ⟨i, Or.inr ⟨n, rfl⟩⟩

private theorem prependB_injective : Function.Injective prependB := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply Subtype.ext
  have h := congrArg Subtype.val h
  cases x <;> cases y <;> simp [prependB, infinity] at h ⊢
  simpa using h

private theorem prependA_injective : Function.Injective prependA := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply Subtype.ext
  have h := congrArg Subtype.val h
  cases x <;> cases y <;> simp [prependA, infinity] at h ⊢
  simpa using h

def tailSet (s : ActivePhase) (j : ℕ) : Set (ValidTail s) :=
  match s with
  | .p => {t | t = infinity .p ∨ ∃ n ≥ j, ∃ i, t = pAtom n i}
  | .beta => {t | t = infinity .beta ∨ ∃ n ≥ j, ∃ i, t = betaAtom n i}

def emission (s : ActivePhase) (D : ProbabilityMeasure (ValidTail s)) : ℝ≥0∞ :=
  match s with
  | .p => (D : Measure _) {pAtom 0 0}
  | .beta => 1 - (D : Measure _) {betaStop}

/-- Exact source regularity; residuals are not required to satisfy this predicate. -/
def Regular (s : ActivePhase) (D : ProbabilityMeasure (ValidTail s)) : Prop :=
  lower ≤ emission s D ∧ emission s D ≤ upper ∧
    ∀ j, (D : Measure _) (tailSet s j) ≤
      (match s with | .p => 1 | .beta => upper) * tailRate ^ j

abbrev RegularDescriptor (s : ActivePhase) := {D : ProbabilityMeasure (ValidTail s) // Regular s D}
abbrev PDescriptor := RegularDescriptor .p
abbrev BDescriptor := RegularDescriptor .beta

def law {s : ActivePhase} (D : RegularDescriptor s) : Measure (ValidTail s) := D.val
instance {s : ActivePhase} (D : RegularDescriptor s) : IsProbabilityMeasure (law D) :=
  D.val.property

def u (Q : PDescriptor) : ℝ≥0∞ := emission .p Q.val
def v (W : BDescriptor) : ℝ≥0∞ := emission .beta W.val
def coordinate (n : ℕ) (i : Letter) (Q : PDescriptor) : ℝ≥0∞ := law Q {pAtom n i}
def g : PDescriptor → ℝ≥0∞ := coordinate 0 1

def residualB (Q : PDescriptor) : Measure (ValidTail .beta) :=
  (1 - u Q)⁻¹ • (law Q).comap prependB
def residualA (W : BDescriptor) : Measure (ValidTail .p) :=
  (v W)⁻¹ • (law W).comap prependA

theorem measurable_law (s : ActivePhase) :
    Measurable (@law s) := measurable_subtype_coe.comp measurable_subtype_coe
theorem measurable_coordinate (n : ℕ) (i : Letter) :
    Measurable (coordinate n i) :=
  (Measure.measurable_coe (measurableSet_singleton _)).comp (measurable_law .p)
theorem measurable_u : Measurable u := measurable_coordinate 0 0
theorem measurable_v : Measurable v :=
  measurable_const.sub ((Measure.measurable_coe (measurableSet_singleton _)).comp
    (measurable_law .beta))

def lawKernel (s : ActivePhase) : Kernel (RegularDescriptor s) (ValidTail s) :=
  ⟨law, measurable_law s⟩

def EndpointBox {s : ActivePhase} (D : RegularDescriptor s) : Prop :=
  ∀ t : ValidTail s,
    min (explicitStoppedWordLaw s lowerRate {t.val})
      (explicitStoppedWordLaw s upperRate {t.val}) ≤ law D {t} ∧
    law D {t} ≤ max (explicitStoppedWordLaw s lowerRate {t.val})
      (explicitStoppedWordLaw s upperRate {t.val})

/-- The original flows and their exhibited disintegrations, with both normalized
residuals equal to full opposite-law barycenters. -/
structure CommonFlow where
  nuP : Measure PDescriptor
  nuB : Measure BDescriptor
  probP : IsProbabilityMeasure nuP
  probB : IsProbabilityMeasure nuB
  GammaB : Measure (PDescriptor × BDescriptor)
  GammaA : Measure (BDescriptor × PDescriptor)
  probGammaB : IsProbabilityMeasure GammaB
  probGammaA : IsProbabilityMeasure GammaA
  B : Kernel PDescriptor BDescriptor
  A : Kernel BDescriptor PDescriptor
  markovB : IsMarkovKernel B
  markovA : IsMarkovKernel A
  disintegrateB : GammaB.IsCondKernel B
  disintegrateA : GammaA.IsCondKernel A
  marginB₁ : GammaB.fst = nuP
  marginB₂ : GammaB.snd = nuB
  marginA₁ : GammaA.fst = nuB
  marginA₂ : GammaA.snd = nuP
  normalizedB : ∀ᵐ Q ∂nuP, residualB Q = (lawKernel .beta) ∘ₘ B Q
  normalizedA : ∀ᵐ W ∂nuB, residualA W = (lawKernel .p) ∘ₘ A W
  boxP : ∀ᵐ Q ∂nuP, EndpointBox Q
  boxB : ∀ᵐ W ∂nuB, EndpointBox W

instance (F : CommonFlow) : IsProbabilityMeasure F.nuP := F.probP
instance (F : CommonFlow) : IsProbabilityMeasure F.nuB := F.probB
instance (F : CommonFlow) : IsProbabilityMeasure F.GammaB := F.probGammaB
instance (F : CommonFlow) : IsProbabilityMeasure F.GammaA := F.probGammaA
instance (F : CommonFlow) : IsMarkovKernel F.B := F.markovB
instance (F : CommonFlow) : IsMarkovKernel F.A := F.markovA

theorem prependB_embedding : MeasurableEmbedding prependB :=
  ⟨prependB_injective, measurable_of_countable _, fun _ _ => Set.Countable.measurableSet
    (Set.to_countable _)⟩
theorem prependA_embedding : MeasurableEmbedding prependA :=
  ⟨prependA_injective, measurable_of_countable _, fun _ _ => Set.Countable.measurableSet
    (Set.to_countable _)⟩

theorem p_partition (t : ValidTail .p) :
    t = pAtom 0 0 ∨ ∃ w, t = prependB w := by
  rcases t with ⟨t, ht⟩
  cases t with
  | none => exact Or.inr ⟨infinity .beta, rfl⟩
  | some w =>
    obtain ⟨i, n, rfl⟩ := ht
    cases n with
    | zero =>
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr ⟨betaStop, rfl⟩
    | succ n =>
      refine Or.inr ⟨betaAtom n i, ?_⟩
      apply Subtype.ext
      exact congrArg some (p_word_succ n i)

theorem b_partition (t : ValidTail .beta) :
    t = betaStop ∨ ∃ q, t = prependA q := by
  rcases t with ⟨t, ht⟩
  cases t with
  | none => exact Or.inr ⟨infinity .p, rfl⟩
  | some w =>
    obtain ⟨i, hi⟩ := ht
    rcases hi with ⟨rfl, rfl⟩ | ⟨n, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨pAtom n i, rfl⟩

theorem p_not_prefix (w : ValidTail .beta) : prependB w ≠ pAtom 0 0 := by
  rintro h
  have h := congrArg Subtype.val h
  rcases w with ⟨w, hw⟩
  cases w <;> simp [prependB, infinity, pAtom, pWord, loopWord] at h

theorem b_not_prefix (q : ValidTail .p) : prependA q ≠ betaStop := by
  rintro h
  have h := congrArg Subtype.val h
  rcases q with ⟨q, hq⟩
  cases q <;> simp [prependA, infinity, betaStop] at h

theorem partition_reconstruct {s t : ActivePhase}
    (f : ValidTail s → ValidTail t) (hf : MeasurableEmbedding f)
    (a : ValidTail t) (hne : ∀ x, f x ≠ a)
    (hcover : ∀ y, y = a ∨ ∃ x, y = f x) (D : Measure (ValidTail t)) :
    D = D {a} • Measure.dirac a + (D.comap f).map f := by
  apply Measure.ext_of_singleton
  intro y
  rcases hcover y with rfl | ⟨x, rfl⟩
  · rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _
      (measurableSet_singleton _), hf.map_apply]
    have he : f ⁻¹' {y} = ∅ := by ext x; simp [hne x]
    simp [he]
  · rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _
      (measurableSet_singleton _), hf.map_apply]
    have he : f ⁻¹' {f x} = {x} := by ext y; simp [hf.injective.eq_iff]
    rw [he, hf.comap_apply]
    simp [(hne x).symm]

private theorem CommonFlow.residualB (F : CommonFlow) : ∀ᵐ Q ∂F.nuP, law Q =
    u Q • Measure.dirac (pAtom 0 0) +
      (1 - u Q) • ((lawKernel .beta) ∘ₘ F.B Q).map prependB := by
  have hu : upper < 1 := (ENNReal.toReal_lt_toReal (by unfold upper; finiteness)
    (by simp)).mp (by norm_num [upper])
  filter_upwards [F.normalizedB] with Q hQ
  have hpos : 1 - u Q ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr (Q.property.2.1.trans_lt hu))
  have hfin : 1 - u Q ≠ ⊤ := ENNReal.sub_ne_top (by simp)
  rw [← hQ, NativeBorelCommonFlow.residualB, Measure.map_smul, smul_smul,
    ENNReal.mul_inv_cancel hpos hfin, one_smul]
  exact partition_reconstruct _ prependB_embedding _ p_not_prefix p_partition _

private theorem CommonFlow.residualA (F : CommonFlow) : ∀ᵐ W ∂F.nuB, law W =
    (1 - v W) • Measure.dirac betaStop +
      v W • ((lawKernel .p) ∘ₘ F.A W).map prependA := by
  have hl : 0 < lower := by norm_num [lower]
  filter_upwards [F.normalizedA] with W hW
  have hpos : v W ≠ 0 := ne_of_gt (hl.trans_le W.property.1)
  have hfin : v W ≠ ⊤ := ENNReal.sub_ne_top (by simp)
  rw [← hW, NativeBorelCommonFlow.residualA, Measure.map_smul, smul_smul,
    ENNReal.mul_inv_cancel hpos hfin, one_smul]
  have hv : 1 - v W = law W {betaStop} :=
    ENNReal.sub_sub_cancel (by simp) prob_le_one
  rw [hv]
  exact partition_reconstruct _ prependA_embedding _ b_not_prefix b_partition _

def CommonFlow.C (F : CommonFlow) : Kernel PDescriptor PDescriptor := F.A ∘ₖ F.B
instance (F : CommonFlow) : IsMarkovKernel F.C := inferInstanceAs (IsMarkovKernel (F.A ∘ₖ F.B))
def CommonFlow.weightedA (F : CommonFlow) : Kernel BDescriptor PDescriptor :=
  F.A.withDensity (fun W _ => v W)
instance (F : CommonFlow) : IsFiniteKernel F.weightedA :=
  Kernel.isFiniteKernel_withDensity_of_bounded F.A (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (fun W _ => (tsub_le_self : 1 - law W {betaStop} ≤ 1))
def CommonFlow.L (F : CommonFlow) : Kernel PDescriptor PDescriptor :=
  (F.weightedA ∘ₖ F.B).withDensity (fun Q _ => 1 - u Q)

def iterate (K : Kernel PDescriptor PDescriptor) (f : PDescriptor → ℝ≥0∞) :
    ℕ → PDescriptor → ℝ≥0∞
  | 0 => f
  | n + 1 => fun Q => ∫⁻ R, iterate K f n R ∂K Q

private theorem stationary (F : CommonFlow) : F.C ∘ₘ F.nuP = F.nuP := by
  have hB : F.B ∘ₘ F.nuP = F.nuB := by
    rw [← F.marginB₁, ← Measure.snd_compProd, F.disintegrateB.disintegrate, F.marginB₂]
  have hA : F.A ∘ₘ F.nuB = F.nuP := by
    rw [← F.marginA₁, ← Measure.snd_compProd, F.disintegrateA.disintegrate, F.marginA₂]
  rw [CommonFlow.C, ← Measure.comp_assoc, hB, hA]

theorem L_integral (F : CommonFlow) (f : PDescriptor → ℝ≥0∞)
    (hf : Measurable f) (Q : PDescriptor) :
    (∫⁻ R, f R ∂F.L Q) = (1 - u Q) *
      ∫⁻ W, v W * ∫⁻ R, f R ∂F.A W ∂F.B Q := by
  have hd : Measurable (Function.uncurry (fun (Q : PDescriptor) (_ : PDescriptor) =>
      1 - u Q)) := measurable_const.sub (measurable_u.comp measurable_fst)
  rw [CommonFlow.L, Kernel.lintegral_withDensity _ hd _ hf,
    lintegral_const_mul _ hf, Kernel.lintegral_comp _ _ _ hf]
  congr 1
  apply lintegral_congr
  intro W
  change (∫⁻ R, f R ∂F.A.withDensity (fun W _ => v W) W) = _
  exact (Kernel.lintegral_withDensity F.A (f := fun W _ => v W)
    (measurable_v.comp measurable_fst) W hf).trans
    (lintegral_const_mul _ hf)

private theorem map_atom {s t : ActivePhase} (f : ValidTail s → ValidTail t)
    (hf : Function.Injective f) (D : Measure (ValidTail s)) (x : ValidTail s) :
    D.map f {f x} = D {x} := by
  rw [Measure.map_apply (measurable_of_countable f) (measurableSet_singleton _)]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hf.eq_iff]

private theorem B_completion (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, g Q = (1 - u Q) * ∫⁻ W, (1 - v W) ∂F.B Q := by
  filter_upwards [F.residualB] with Q hQ
  have h := congrArg (fun D : Measure (ValidTail .p) => D {pAtom 0 1}) hQ
  have hb : prependB betaStop = pAtom 0 1 := rfl
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, ← hb,
    map_atom _ prependB_injective] at h
  have he : pAtom 0 0 ≠ prependB betaStop := by
    intro h; have := congrArg Subtype.val h; simp [pAtom, pWord, loopWord, prependB,
      betaStop] at this
  rw [Measure.dirac_apply' _ (measurableSet_singleton _)] at h
  simp only [Set.indicator_apply, Set.mem_singleton_iff, he, if_false,
    smul_eq_mul, mul_zero, zero_add] at h
  rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)] at h
  have hi : (∫⁻ W, (1 - v W) ∂F.B Q) =
      ∫⁻ W, law W {betaStop} ∂F.B Q := by
    apply lintegral_congr
    intro W
    change 1 - (1 - law W {betaStop}) = law W {betaStop}
    exact ENNReal.sub_sub_cancel (by simp) prob_le_one
  rw [hi]
  simpa only [hb, g, coordinate, lawKernel, Kernel.coe_mk] using h

private theorem A_coordinate (F : CommonFlow) (n : ℕ) (i : Letter) :
    ∀ᵐ W ∂F.nuB, law W {betaAtom n i} =
      v W * ∫⁻ Q, coordinate n i Q ∂F.A W := by
  filter_upwards [F.residualA] with W hW
  have h := congrArg (fun D : Measure (ValidTail .beta) => D {betaAtom n i}) hW
  have ha : prependA (pAtom n i) = betaAtom n i := rfl
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, ← ha,
    map_atom _ prependA_injective] at h
  have he : betaStop ≠ prependA (pAtom n i) := by
    intro h; have := congrArg Subtype.val h
    simp [prependA, pAtom, betaStop] at this
  rw [Measure.dirac_apply' _ (measurableSet_singleton _)] at h
  simp only [Set.indicator_apply, Set.mem_singleton_iff, he, if_false,
    smul_eq_mul, mul_zero, zero_add] at h
  rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)] at h
  simpa only [ha, lawKernel, Kernel.coe_mk, coordinate] using h

private theorem B_coordinate (F : CommonFlow) (n : ℕ) (i : Letter) :
    ∀ᵐ Q ∂F.nuP, coordinate (n + 1) i Q =
      (1 - u Q) * ∫⁻ W, law W {betaAtom n i} ∂F.B Q := by
  filter_upwards [F.residualB] with Q hQ
  have h := congrArg (fun D : Measure (ValidTail .p) => D {pAtom (n + 1) i}) hQ
  have hb : prependB (betaAtom n i) = pAtom (n + 1) i := by
    apply Subtype.ext
    simp only [prependB, betaAtom, pAtom]
    exact congrArg some (p_word_succ n i).symm
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, ← hb,
    map_atom _ prependB_injective] at h
  have he : pAtom 0 0 ≠ prependB (betaAtom n i) := by
    intro h; have := congrArg Subtype.val h
    simp [pAtom, pWord, loopWord, prependB, betaAtom] at this
  rw [Measure.dirac_apply' _ (measurableSet_singleton _)] at h
  simp only [Set.indicator_apply, Set.mem_singleton_iff, he, if_false,
    smul_eq_mul, mul_zero, zero_add] at h
  rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)] at h
  simpa only [hb, lawKernel, Kernel.coe_mk, coordinate] using h

private theorem coordinate_step (F : CommonFlow) (n : ℕ) (i : Letter) :
    ∀ᵐ Q ∂F.nuP, coordinate (n + 1) i Q = ∫⁻ R, coordinate n i R ∂F.L Q := by
  have hB : F.B ∘ₘ F.nuP = F.nuB := by
    rw [← F.marginB₁, ← Measure.snd_compProd, F.disintegrateB.disintegrate, F.marginB₂]
  have hA := Measure.ae_ae_of_ae_comp (κ := F.B)
    (hB.symm ▸ A_coordinate F n i)
  filter_upwards [B_coordinate F n i, hA] with Q hQ hA
  rw [hQ, L_integral _ _ (measurable_coordinate n i)]
  congr 1
  exact lintegral_congr_ae hA

theorem L_le_C (F : CommonFlow) (Q : PDescriptor) : F.L Q ≤ F.C Q := by
  apply Measure.le_iff.mpr
  intro s hs
  have hd : Measurable (Function.uncurry (fun (Q : PDescriptor) (_ : PDescriptor) =>
      1 - u Q)) := measurable_const.sub (measurable_u.comp measurable_fst)
  rw [CommonFlow.L, Kernel.withDensity_apply _ hd, withDensity_const,
    Measure.smul_apply, smul_eq_mul]
  calc
    (1 - u Q) * (F.weightedA ∘ₖ F.B) Q s ≤ (F.weightedA ∘ₖ F.B) Q s :=
      mul_le_of_le_one_left' tsub_le_self
    _ ≤ F.C Q s := by
      rw [CommonFlow.C, Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ hs]
      apply lintegral_mono
      intro W
      change F.A.withDensity (fun W _ => v W) W s ≤ F.A W s
      rw [Kernel.withDensity_apply F.A (f := fun W _ => v W)
        (measurable_v.comp measurable_fst),
        withDensity_const, Measure.smul_apply, smul_eq_mul]
      exact mul_le_of_le_one_left' tsub_le_self

instance (F : CommonFlow) : IsFiniteKernel F.L := by
  refine ⟨⟨1, by simp, ?_⟩⟩
  intro Q
  exact (L_le_C F Q Set.univ).trans (by simp)

instance (F : CommonFlow) : IsSFiniteKernel F.L := by
  refine ⟨fun n => if n = 0 then F.L else 0, ?_, ?_⟩
  · intro n
    by_cases h : n = 0
    · simpa [h] using (inferInstance : IsFiniteKernel F.L)
    · refine ⟨⟨0, by simp, ?_⟩⟩
      intro Q
      simp [h]
  · ext Q s hs
    rw [Kernel.sum_apply, Measure.sum_apply _ hs, tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]

private theorem coordinate_iterate (F : CommonFlow) (n : ℕ) (i : Letter) :
    ∀ᵐ Q ∂F.nuP, coordinate n i Q = iterate F.L (coordinate 0 i) n Q := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    have hc := Measure.ae_ae_of_ae_comp (κ := F.C) ((stationary F).symm ▸ ih)
    filter_upwards [coordinate_step F n i, hc] with Q hQ hc
    rw [hQ, iterate]
    exact lintegral_congr_ae ((L_le_C F Q).absolutelyContinuous.ae_le hc)

/-- The complete residual equations generate both entire word families on the
same acquired return chain, whose original unweighted margin is stationary. -/
theorem common_flow_word_iteration (F : CommonFlow) :
    F.C ∘ₘ F.nuP = F.nuP ∧
      (∀ᵐ Q ∂F.nuP, ∀ n i, coordinate n i Q = iterate F.L (coordinate 0 i) n Q) ∧
      (∀ᵐ Q ∂F.nuP, g Q = (1 - u Q) * ∫⁻ W, (1 - v W) ∂F.B Q) := by
  refine ⟨stationary F, ?_, B_completion F⟩
  exact (ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun i => coordinate_iterate F n i)))

theorem L_apply (F : CommonFlow) (Q : PDescriptor) (s : Set PDescriptor)
    (hs : MeasurableSet s) :
    F.L Q s = (1 - u Q) * ∫⁻ W, v W * F.A W s ∂F.B Q := by
  have hd : Measurable (Function.uncurry (fun (Q : PDescriptor) (_ : PDescriptor) =>
      1 - u Q)) := measurable_const.sub (measurable_u.comp measurable_fst)
  rw [CommonFlow.L, Kernel.withDensity_apply _ hd, withDensity_const,
    Measure.smul_apply, smul_eq_mul, Kernel.comp_apply' _ _ _ hs]
  congr 1
  apply lintegral_congr
  intro W
  change F.A.withDensity (fun W _ => v W) W s = v W * F.A W s
  rw [Kernel.withDensity_apply F.A (f := fun W _ => v W)
    (measurable_v.comp measurable_fst), withDensity_const,
    Measure.smul_apply, smul_eq_mul]

theorem one_sub_upper : (1 - upper : ℝ≥0∞) = 3 / 5 := by
  have hu : upper ≤ 1 := (ENNReal.toReal_le_toReal (by unfold upper; finiteness) (by simp)).mp
    (by norm_num [upper])
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le hu (by simp)]
  norm_num [upper]

private theorem one_sub_lower : (1 - lower : ℝ≥0∞) = 2 / 3 := by
  have hu : lower ≤ 1 := (ENNReal.toReal_le_toReal (by simp [lower]) (by simp)).mp
    (by norm_num [lower])
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le hu (by simp)]
  norm_num [lower]

private theorem completion_bounds (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, endpointCompletion ≤ g Q ∧ g Q ≤ (4 / 9 : ℝ≥0∞) := by
  filter_upwards [B_completion F] with Q hQ
  have hu := Q.property
  have hv (W : BDescriptor) := W.property
  have hlo : (1 - upper : ℝ≥0∞) ≤ ∫⁻ W, (1 - v W) ∂F.B Q := by
    calc
      1 - upper = ∫⁻ _ : BDescriptor, (1 - upper) ∂F.B Q := by simp
      _ ≤ _ := lintegral_mono (fun W => tsub_le_tsub_left (hv W).2.1 1)
  have hhi : (∫⁻ W, (1 - v W) ∂F.B Q) ≤ 1 - lower := by
    calc
      _ ≤ ∫⁻ _ : BDescriptor, (1 - lower) ∂F.B Q :=
        lintegral_mono (fun W => tsub_le_tsub_left (hv W).1 1)
      _ = _ := by simp
  rw [hQ]
  constructor
  · calc
      endpointCompletion = (1 - upper) * (1 - upper) := by
        rw [one_sub_upper]
        apply (ENNReal.toReal_eq_toReal_iff' (by unfold endpointCompletion; finiteness)
          (by finiteness)).mp
        norm_num [endpointCompletion]
      _ ≤ _ := mul_le_mul' (tsub_le_tsub_left hu.2.1 1) hlo
  · calc
      _ ≤ (1 - lower) * (1 - lower) := mul_le_mul' (tsub_le_tsub_left hu.1 1) hhi
      _ = _ := by
        rw [one_sub_lower]
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num


private theorem L_bounds (F : CommonFlow) (Q : PDescriptor) :
    (1 / 5 : ℝ≥0∞) • F.C Q ≤ F.L Q ∧
      F.L Q ≤ (4 / 15 : ℝ≥0∞) • F.C Q := by
  have hu := Q.property
  constructor
  · apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, L_apply _ _ _ hs,
      CommonFlow.C, Kernel.comp_apply' _ _ _ hs]
    calc
      (1 / 5 : ℝ≥0∞) * (∫⁻ W, F.A W s ∂F.B Q) =
          (1 - upper) * (lower * ∫⁻ W, F.A W s ∂F.B Q) := by
            have hn : (1 - upper) * lower = (1 / 5 : ℝ≥0∞) := by
              rw [one_sub_upper]
              apply (ENNReal.toReal_eq_toReal_iff' (by simp [lower]; finiteness)
                (by finiteness)).mp
              norm_num [lower]
            rw [← mul_assoc, hn]
      _ ≤ (1 - u Q) * ∫⁻ W, v W * F.A W s ∂F.B Q := by
        apply mul_le_mul' (tsub_le_tsub_left hu.2.1 1)
        rw [← lintegral_const_mul _ (F.A.measurable_coe hs)]
        exact lintegral_mono (fun W => mul_le_mul' W.property.1 le_rfl)
  · apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, L_apply _ _ _ hs,
      CommonFlow.C, Kernel.comp_apply' _ _ _ hs]
    calc
      _ ≤ (1 - lower) * (upper * ∫⁻ W, F.A W s ∂F.B Q) := by
        apply mul_le_mul' (tsub_le_tsub_left hu.1 1)
        rw [← lintegral_const_mul _ (F.A.measurable_coe hs)]
        exact lintegral_mono (fun W => mul_le_mul' W.property.2.1 le_rfl)
      _ = _ := by
        have hn : (1 - lower) * upper = (4 / 15 : ℝ≥0∞) := by
          rw [one_sub_lower]
          apply (ENNReal.toReal_eq_toReal_iff' (by simp [upper]; finiteness)
            (by finiteness)).mp
          norm_num [upper]
        rw [← mul_assoc, hn]

private theorem native_word_mass (r : unitInterval) (n : ℕ) (i : Letter) :
    explicitStoppedWordLaw .p r {(pAtom n i).val} =
      (if i = 0 then alphaMass r else betaMass r ^ 2) *
        (alphaMass r * betaMass r) ^ n := by
  rw [pAtom, explicit_finite_mass, if_pos ⟨i, n, rfl⟩, p_word_mass]

/-- Row comparison and the upper complete-word box hold on the original
descriptor marginal and use the same two acquired kernels. -/
theorem common_flow_operator_bounds (F : CommonFlow) :
    (∀ Q, (1 / 5 : ℝ≥0∞) • F.C Q ≤ F.L Q ∧
      F.L Q ≤ (4 / 15 : ℝ≥0∞) • F.C Q) ∧
    (∀ᵐ Q ∂F.nuP, endpointCompletion ≤ g Q ∧ g Q ≤ (4 / 9 : ℝ≥0∞) ∧
      iterate F.L g 3 Q ≤ endpointCompletion * endpointRate ^ 3) := by
  refine ⟨L_bounds F, ?_⟩
  filter_upwards [completion_bounds F, (common_flow_word_iteration F).2.1, F.boxP]
    with Q hg hi hb
  refine ⟨hg.1, hg.2, ?_⟩
  change iterate F.L (coordinate 0 1) 3 Q ≤ _
  rw [← hi 3 1]
  have h := (hb (pAtom 3 1)).2
  rw [native_word_mass, native_word_mass] at h
  have ha : betaMass lowerRate ^ 2 *
      (alphaMass lowerRate * betaMass lowerRate) ^ 3 ≤
        endpointCompletion * endpointRate ^ 3 := by
    apply (ENNReal.toReal_le_toReal (by simp [alphaMass, betaMass]; finiteness)
      (by simp [endpointCompletion, endpointRate]; finiteness)).mp
    simp only [alphaMass, betaMass, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.coe_toReal]
    simp only [unitInterval.coe_toNNReal]
    norm_num [lowerRate, unitInterval.symm, endpointCompletion, endpointRate]
  have hb : betaMass upperRate ^ 2 *
      (alphaMass upperRate * betaMass upperRate) ^ 3 =
        endpointCompletion * endpointRate ^ 3 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp [alphaMass, betaMass]; finiteness)
      (by simp [endpointCompletion, endpointRate]; finiteness)).mp
    simp only [alphaMass, betaMass, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.coe_toReal]
    simp only [unitInterval.coe_toNNReal]
    norm_num [upperRate, unitInterval.symm, endpointCompletion, endpointRate]
  simp only [Fin.reduceEq, if_false] at h
  exact h.trans (max_le ha hb.le)

def goodP (F : CommonFlow) (Q : PDescriptor) : Prop :=
  residualB Q = (lawKernel .beta) ∘ₘ F.B Q ∧ EndpointBox Q ∧
    (∀ n i, coordinate n i Q = iterate F.L (coordinate 0 i) n Q) ∧
    g Q = (1 - u Q) * ∫⁻ W, (1 - v W) ∂F.B Q ∧
    endpointCompletion ≤ g Q ∧ g Q ≤ (4 / 9 : ℝ≥0∞) ∧
    iterate F.L g 3 Q ≤ endpointCompletion * endpointRate ^ 3
def goodB (F : CommonFlow) (W : BDescriptor) : Prop :=
  residualA W = (lawKernel .p) ∘ₘ F.A W ∧ EndpointBox W

private def goodPSet (F : CommonFlow) : Set PDescriptor :=
  (toMeasurable F.nuP {Q | ¬ goodP F Q})ᶜ
private def goodBSet (F : CommonFlow) : Set BDescriptor :=
  (toMeasurable F.nuB {W | ¬ goodB F W})ᶜ

private def coreSequence (F : CommonFlow) : ℕ → Set PDescriptor × Set BDescriptor
  | 0 => (goodPSet F, goodBSet F)
  | n + 1 =>
    ((coreSequence F n).1 ∩ {Q | F.B Q ((coreSequence F n).2)ᶜ = 0},
     (coreSequence F n).2 ∩ {W | F.A W ((coreSequence F n).1)ᶜ = 0})

private theorem core_measurable (F : CommonFlow) (n : ℕ) :
    MeasurableSet (coreSequence F n).1 ∧ MeasurableSet (coreSequence F n).2 := by
  induction n with
  | zero => exact ⟨(measurableSet_toMeasurable _ _).compl,
      (measurableSet_toMeasurable _ _).compl⟩
  | succ n ih => exact ⟨ih.1.inter ((F.B.measurable_coe ih.2.compl)
      (measurableSet_singleton 0)), ih.2.inter ((F.A.measurable_coe ih.1.compl)
      (measurableSet_singleton 0))⟩

private theorem core_conull (F : CommonFlow) (n : ℕ) :
    (∀ᵐ Q ∂F.nuP, Q ∈ (coreSequence F n).1) ∧
    (∀ᵐ W ∂F.nuB, W ∈ (coreSequence F n).2) := by
  have hB : F.B ∘ₘ F.nuP = F.nuB := by
    rw [← F.marginB₁, ← Measure.snd_compProd, F.disintegrateB.disintegrate, F.marginB₂]
  have hA : F.A ∘ₘ F.nuB = F.nuP := by
    rw [← F.marginA₁, ← Measure.snd_compProd, F.disintegrateA.disintegrate, F.marginA₂]
  induction n with
  | zero =>
    constructor
    · change ∀ᵐ Q ∂F.nuP, Q ∈ (toMeasurable F.nuP {Q | ¬goodP F Q})ᶜ
      rw [ae_iff]
      simpa only [Set.mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable,
        goodP, goodB] using
        (ae_iff.mp (F.normalizedB.and (F.boxP.and
          ((common_flow_word_iteration F).2.1.and
            ((common_flow_word_iteration F).2.2.and (common_flow_operator_bounds F).2)))))
    · change ∀ᵐ W ∂F.nuB, W ∈ (toMeasurable F.nuB {W | ¬goodB F W})ᶜ
      rw [ae_iff]
      simpa only [Set.mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable,
        goodP, goodB] using
        (ae_iff.mp (F.normalizedA.and F.boxB))
  | succ n ih =>
    have hp := Measure.ae_ae_of_ae_comp (κ := F.B) (hB.symm ▸ ih.2)
    have hb := Measure.ae_ae_of_ae_comp (κ := F.A) (hA.symm ▸ ih.1)
    constructor
    · filter_upwards [ih.1, hp] with Q hQ hp
      exact ⟨hQ, ae_iff.mp hp⟩
    · filter_upwards [ih.2, hb] with W hW hb
      exact ⟨hW, ae_iff.mp hb⟩

/-- The residual equations, both boxes, word recursions and completion bounds
admit measurable conull sets closed under the same acquired transitions. -/
theorem common_flow_conull_core (F : CommonFlow) :
    ∃ (P : Set PDescriptor) (S : Set BDescriptor),
      MeasurableSet P ∧ MeasurableSet S ∧
      (∀ᵐ Q ∂F.nuP, Q ∈ P) ∧ (∀ᵐ W ∂F.nuB, W ∈ S) ∧
      (∀ Q ∈ P, goodP F Q ∧ ∀ᵐ W ∂F.B Q, W ∈ S) ∧
      (∀ W ∈ S, goodB F W ∧ ∀ᵐ Q ∂F.A W, Q ∈ P) := by
  let P := ⋂ n, (coreSequence F n).1
  let S := ⋂ n, (coreSequence F n).2
  refine ⟨P, S, MeasurableSet.iInter (fun n => (core_measurable F n).1),
    MeasurableSet.iInter (fun n => (core_measurable F n).2), ?_, ?_, ?_, ?_⟩
  · exact (ae_all_iff.mpr (fun n => (core_conull F n).1)).mono
      (fun _ h => Set.mem_iInter.mpr h)
  · exact (ae_all_iff.mpr (fun n => (core_conull F n).2)).mono
      (fun _ h => Set.mem_iInter.mpr h)
  · intro Q hQ
    have hn := Set.mem_iInter.mp hQ
    constructor
    · have h0 : Q ∉ toMeasurable F.nuP {Q | ¬goodP F Q} := hn 0
      by_contra hbad
      exact h0 (subset_toMeasurable _ _ hbad)
    · have he : ∀ n, ∀ᵐ W ∂F.B Q, W ∈ (coreSequence F n).2 := fun n =>
        ae_iff.mpr (hn (n + 1)).2
      exact (ae_all_iff.mpr he).mono (fun _ h => Set.mem_iInter.mpr h)
  · intro W hW
    have hn := Set.mem_iInter.mp hW
    constructor
    · have h0 : W ∉ toMeasurable F.nuB {W | ¬goodB F W} := hn 0
      by_contra hbad
      exact h0 (subset_toMeasurable _ _ hbad)
    · have he : ∀ n, ∀ᵐ Q ∂F.A W, Q ∈ (coreSequence F n).1 := fun n =>
        ae_iff.mpr (hn (n + 1)).2
      exact (ae_all_iff.mpr he).mono (fun _ h => Set.mem_iInter.mpr h)

/-! The next definitions keep the source's normalization by the upper endpoint
rate explicit.  They are functions of the already acquired `L` operator; no
new observer state or finite-state reduction is introduced. -/

def normalizedIterate (F : CommonFlow) (f : PDescriptor → ℝ≥0∞) (n : ℕ)
    (Q : PDescriptor) : ℝ≥0∞ := endpointRate⁻¹ ^ n * iterate F.L f n Q

/-! The normalized action is kept as an operator on the same acquired return
kernel.  This is the representation used by the later localization argument;
it does not install a new observer register or replace the unweighted flow. -/
def normalizedAction (F : CommonFlow) (f : PDescriptor → ℝ≥0∞)
    (Q : PDescriptor) : ℝ≥0∞ :=
  endpointRate⁻¹ * ∫⁻ R, f R ∂F.L Q

theorem measurable_iterate (F : CommonFlow)
    (f : PDescriptor → ℝ≥0∞) (hf : Measurable f) :
    ∀ n, Measurable (iterate F.L f n) := by
  intro n
  induction n with
  | zero => simpa [iterate] using hf
  | succ n ih =>
      apply Measurable.lintegral_kernel_prod_right
      exact ih.comp measurable_snd

theorem measurable_normalizedIterate (F : CommonFlow)
    (f : PDescriptor → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    Measurable (normalizedIterate F f n) := by
  unfold normalizedIterate
  exact measurable_const.mul (measurable_iterate F f hf n)

theorem normalizedIterate_succ (F : CommonFlow) (f : PDescriptor → ℝ≥0∞)
    (hf : Measurable f) (n : ℕ) (Q : PDescriptor) :
    normalizedIterate F f (n + 1) Q =
      normalizedAction F (normalizedIterate F f n) Q := by
  change endpointRate⁻¹ ^ (n + 1) *
      (∫⁻ R, iterate F.L f n R ∂F.L Q) =
    endpointRate⁻¹ *
      (∫⁻ R, endpointRate⁻¹ ^ n * iterate F.L f n R ∂F.L Q)
  rw [pow_succ, lintegral_const_mul _ (measurable_iterate F f hf n)]
  ring

theorem normalizedAction_add (F : CommonFlow)
    (f₁ f₂ : PDescriptor → ℝ≥0∞) (hf₁ : Measurable f₁)
    (Q : PDescriptor) :
    normalizedAction F (fun R => f₁ R + f₂ R) Q =
      normalizedAction F f₁ Q + normalizedAction F f₂ Q := by
  unfold normalizedAction
  rw [lintegral_add_left hf₁, mul_add]

def threeStepAverage (F : CommonFlow) (Q : PDescriptor) : ℝ≥0∞ :=
  (g Q + normalizedIterate F g 1 Q + normalizedIterate F g 2 Q) / 3

def threeStepDefect (F : CommonFlow) (Q : PDescriptor) : ℝ≥0∞ :=
  (g Q - normalizedIterate F g 3 Q) / 3

theorem measurable_g : Measurable g := measurable_coordinate 0 1

theorem normalizedAction_threeStepAverage (F : CommonFlow) (Q : PDescriptor) :
    normalizedAction F (fun R => threeStepAverage F R) Q =
      (normalizedIterate F g 1 Q + normalizedIterate F g 2 Q +
        normalizedIterate F g 3 Q) / 3 := by
  have h1 := measurable_normalizedIterate F g measurable_g 1
  have h2 := measurable_normalizedIterate F g measurable_g 2
  have hsum : Measurable (fun R => g R + normalizedIterate F g 1 R +
      normalizedIterate F g 2 R) := (measurable_g.add h1).add h2
  have ha := normalizedAction_add F g (normalizedIterate F g 1) measurable_g Q
  have hb := normalizedAction_add F (fun R => g R + normalizedIterate F g 1 R)
    (normalizedIterate F g 2) (measurable_g.add h1) Q
  have hc := normalizedIterate_succ F g measurable_g 0 Q
  have hd := normalizedIterate_succ F g measurable_g 1 Q
  have he := normalizedIterate_succ F g measurable_g 2 Q
  have hc' : normalizedIterate F g 1 Q = endpointRate⁻¹ *
      (∫⁻ R, g R ∂F.L Q) := by simpa [normalizedAction, normalizedIterate, iterate] using hc
  have hd' : normalizedIterate F g 2 Q = endpointRate⁻¹ *
      (∫⁻ R, normalizedIterate F g 1 R ∂F.L Q) := by
    simpa [normalizedAction] using hd
  have he' : normalizedIterate F g 3 Q = endpointRate⁻¹ *
      (∫⁻ R, normalizedIterate F g 2 R ∂F.L Q) := by
    simpa [normalizedAction] using he
  unfold threeStepAverage normalizedAction at *
  simp only [ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul _ hsum]
  calc
    _ = 3⁻¹ * (endpointRate⁻¹ *
        (∫⁻ R, g R + normalizedIterate F g 1 R +
          normalizedIterate F g 2 R ∂F.L Q)) := by ring
    _ = 3⁻¹ * (endpointRate⁻¹ *
        (∫⁻ R, g R + normalizedIterate F g 1 R ∂F.L Q) +
          endpointRate⁻¹ * (∫⁻ R, normalizedIterate F g 2 R ∂F.L Q)) := by
      rw [hb]
    _ = 3⁻¹ * (endpointRate⁻¹ * (∫⁻ R, g R ∂F.L Q) +
          endpointRate⁻¹ * (∫⁻ R, normalizedIterate F g 1 R ∂F.L Q) +
          endpointRate⁻¹ * (∫⁻ R, normalizedIterate F g 2 R ∂F.L Q)) := by
      rw [ha]
    _ = _ := by rw [← hc', ← hd', ← he']

theorem common_flow_normalized_third_step (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, normalizedIterate F g 3 Q ≤ endpointCompletion := by
  filter_upwards [(common_flow_operator_bounds F).2] with Q hQ
  rw [normalizedIterate]
  calc
    endpointRate⁻¹ ^ 3 * iterate F.L g 3 Q ≤
        endpointRate⁻¹ ^ 3 * (endpointCompletion * endpointRate ^ 3) :=
      mul_le_mul_of_nonneg_left hQ.2.2 (by positivity)
    _ = endpointCompletion := by
      have hr : endpointRate ≠ ∞ := by
        exact ENNReal.div_ne_top (by simp) (by norm_num)
      have hr0 : endpointRate ≠ 0 := by norm_num [endpointRate]
      have hc : endpointCompletion ≠ ∞ := by
        exact ENNReal.div_ne_top (by simp) (by norm_num)
      have hleft : endpointRate⁻¹ ^ 3 *
          (endpointCompletion * endpointRate ^ 3) ≠ ∞ := by
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hr0))
          (ENNReal.mul_ne_top hc (ENNReal.pow_ne_top hr))
      apply (ENNReal.toReal_eq_toReal_iff' hleft hc).mp
      simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_mul,
        ENNReal.coe_toReal]
      norm_num [endpointRate, endpointCompletion]

/-- The three-step block supplies a nonnegative defect on the same conull
core as the endpoint box.  This is the finite block input for the later
sixth-power localization argument. -/
theorem common_flow_three_step_defect_nonneg (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, 0 ≤ threeStepDefect F Q := by
  filter_upwards [common_flow_normalized_third_step F,
    (common_flow_operator_bounds F).2] with Q _ _
  exact bot_le

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow

/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unweighted all-live cemetery prefixes and actual same-flow Radon-Nikodym products. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
import Mathlib.Probability.Kernel.CompProdEqIff

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal Topology
attribute [local instance] Classical.propDecidable
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelEndpointIdentification
open NativeBorelRepresentation NativeBorelNativeLaws NativeBorelStationaryLocalization NativeBorelKilledPaths

/-- The actual unnormalized iterated kernel product through time n. -/
def finiteProduct {S : Type*} [MeasurableSpace S] (μ : Measure S) (K : Kernel S S) :
    (n : ℕ) → Measure (Fin (n + 1) → S)
  | 0 => μ.map (fun x _ => x)
  | n + 1 => ((finiteProduct μ K n) ⊗ₘ
      K.comap (fun w => w (Fin.last n)) (measurable_pi_apply _)).map
        (fun p => Fin.snoc p.1 p.2)

private theorem snoc_measurable {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (fun p : (Fin (n + 1) → S) × S =>
      (Fin.snoc p.1 p.2 : Fin (n + 2) → S)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (Prod.snd :
      (Fin (n + 1) → S) × S → S))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply j (X := fun _ : Fin (n + 1) => S)).comp
        (measurable_fst : Measurable (Prod.fst : (Fin (n + 1) → S) × S → (Fin (n + 1) → S)))

private instance finiteProduct_finite {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (K : Kernel S S) [IsFiniteKernel K] (n : ℕ) :
    IsFiniteMeasure (finiteProduct μ K n) := by
  induction n with
  | zero => unfold finiteProduct; exact Measure.isFiniteMeasure_map _ _
  | succ n ih =>
    letI := ih
    unfold finiteProduct
    exact Measure.isFiniteMeasure_map _ _

/-- Each factor is the Radon-Nikodym derivative of the actual same-flow row. -/
def finiteDensity (F : CommonFlow) (M : Kernel PDescriptor PDescriptor) (n : ℕ)
    (w : Fin (n + 1) → PDescriptor) : ℝ≥0∞ :=
  ∏ i : Fin n, M.rnDeriv F.C (w i.castSucc) (w i.succ)

private theorem finiteDensity_measurable (F : CommonFlow)
    (M : Kernel PDescriptor PDescriptor) (n : ℕ) : Measurable (finiteDensity F M n) := by
  unfold finiteDensity
  apply Finset.measurable_prod
  intro i hi
  have hm : Measurable (fun w : Fin (n + 1) → PDescriptor => (w i.castSucc, w i.succ)) := by fun_prop
  exact (Kernel.measurable_rnDeriv M F.C).comp hm

private theorem finiteDensity_snoc (F : CommonFlow) (M : Kernel PDescriptor PDescriptor)
    (n : ℕ) (w : Fin (n + 1) → PDescriptor) (R : PDescriptor) :
    finiteDensity F M (n + 1) (Fin.snoc w R) =
      finiteDensity F M n w * M.rnDeriv F.C (w (Fin.last n)) R := by
  unfold finiteDensity
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [show i.castSucc.succ = i.succ.castSucc from rfl, Fin.snoc_castSucc]
  · simp

private theorem compProd_density {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    (K J : Kernel X Y) [IsFiniteKernel K] [IsFiniteKernel J]
    (d : X → ℝ≥0∞) (hd : Measurable d)
    (a : X → Y → ℝ≥0∞) (ha : Measurable (Function.uncurry a))
    (hμ : μ = ν.withDensity d) (hK : ∀ x, K x = (J x).withDensity (a x)) :
    μ ⊗ₘ K = (ν ⊗ₘ J).withDensity (fun p => d p.1 * a p.1 p.2) := by
  ext E hE
  rw [Measure.compProd_apply hE, hμ,
    lintegral_withDensity_eq_lintegral_mul _ hd (K.measurable_kernel_prodMk_left hE),
    withDensity_apply _ hE, ← lintegral_indicator hE,
    Measure.lintegral_compProd (show Measurable (E.indicator
      (fun p : X × Y => d p.1 * a p.1 p.2)) from
      ((hd.comp measurable_fst).mul ha).indicator hE)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  rw [hK x, withDensity_apply _ (measurable_prodMk_left hE),
    ← lintegral_indicator (measurable_prodMk_left hE)]
  rw [← lintegral_const_mul _ (show Measurable ((Prod.mk x ⁻¹' E).indicator (a x)) from
    (ha.comp measurable_prodMk_left).indicator (measurable_prodMk_left hE))]
  apply lintegral_congr
  intro y
  by_cases hy : (x,y) ∈ E <;> simp [Set.indicator, hy]

private theorem finiteProduct_density (F : CommonFlow)
    (M : Kernel PDescriptor PDescriptor) [IsFiniteKernel M]
    (hAC : ∀ Q, M Q ≪ F.C Q) (n : ℕ) :
    finiteProduct F.nuP M n = (finiteProduct F.nuP F.C n).withDensity (finiteDensity F M n) := by
  induction n with
  | zero =>
    rw [show finiteDensity F M 0 = (fun _ => 1) by funext w; simp [finiteDensity],
      show ((finiteProduct F.nuP F.C 0).withDensity (fun _ => 1)) =
        finiteProduct F.nuP F.C 0 from withDensity_one]
    rfl
  | succ n ih =>
    let K := M.comap (fun w : Fin (n + 1) → PDescriptor => w (Fin.last n))
      (measurable_pi_apply _)
    let J := F.C.comap (fun w : Fin (n + 1) → PDescriptor => w (Fin.last n))
      (measurable_pi_apply _)
    let a := fun w : Fin (n + 1) → PDescriptor => M.rnDeriv F.C (w (Fin.last n))
    have ha : Measurable (Function.uncurry a) := by
      have hm : Measurable (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
          (p.1 (Fin.last n), p.2)) := by fun_prop
      exact (Kernel.measurable_rnDeriv M F.C).comp hm
    have hrow (w : Fin (n + 1) → PDescriptor) : K w = (J w).withDensity (a w) := by
      exact (Kernel.withDensity_rnDeriv_eq (hAC (w (Fin.last n)))).symm.trans
        (Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv M F.C) _)
    have hp := compProd_density (finiteProduct F.nuP M n) (finiteProduct F.nuP F.C n)
      K J (finiteDensity F M n) (finiteDensity_measurable F M n) a ha ih hrow
    change ((finiteProduct F.nuP M n) ⊗ₘ K).map _ = _
    rw [hp]
    have he : (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
        finiteDensity F M n p.1 * a p.1 p.2) =
        (fun p => finiteDensity F M (n + 1) (Fin.snoc p.1 p.2)) := by
      funext p
      exact (finiteDensity_snoc F M n p.1 p.2).symm
    rw [he, map_terminal_density _ _ (snoc_measurable n) _
      (finiteDensity_measurable F M (n + 1))]
    rfl

private theorem homogeneous_prefix_pair {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) :
    (homogeneousLaw μ K).map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) =
      ((homogeneousLaw μ K).map (fun x (i : Fin (n + 1)) => x i.1)) ⊗ₘ
        K.comap (fun w => w (Fin.last n)) (measurable_pi_apply _) := by
  let e : ((i : Finset.Iic n) → S) → (Fin (n + 1) → S) :=
    fun w i => w ⟨i.1, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩
  have he : Measurable e := by fun_prop
  have hk := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => S) (μ₀ := μ) (κ := homogeneousStep K) (a := n)
  have hmap : ( ((homogeneousLaw μ K).map (frestrictLe n)) ⊗ₘ homogeneousStep K n).map
      (Prod.map e id) =
      ((homogeneousLaw μ K).map (fun x (i : Fin (n + 1)) => x i.1)) ⊗ₘ
        K.comap (fun w => w (Fin.last n)) (measurable_pi_apply _) := by
    ext E hE
    rw [Measure.map_apply (he.prodMap measurable_id) hE,
      Measure.compProd_apply (hE.preimage (he.prodMap measurable_id)),
      Measure.compProd_apply hE, lintegral_map
        ((K.comap (fun w : Fin (n + 1) → S => w (Fin.last n))
          (measurable_pi_apply _)).measurable_kernel_prodMk_left hE) (by fun_prop),
      lintegral_map ((homogeneousStep K n).measurable_kernel_prodMk_left
        (hE.preimage (he.prodMap measurable_id))) (measurable_frestrictLe n)]
    rfl
  rw [show (homogeneousLaw μ K).map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) =
    ((homogeneousLaw μ K).map (fun x => (frestrictLe n x, x (n + 1)))).map (Prod.map e id) by
      rw [Measure.map_map (he.prodMap measurable_id) (by fun_prop)]; rfl,
    homogeneousLaw, ← hk]
  exact hmap

private theorem homogeneous_prefix_product {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) :
    (homogeneousLaw μ K).map (fun x (i : Fin (n + 1)) => x i.1) = finiteProduct μ K n := by
  induction n with
  | zero =>
    rw [show (fun x : ℕ → S => fun i : Fin 1 => x i.1) =
      (fun Q _ => Q) ∘ (fun x : ℕ → S => x 0) by funext x i; rw [Fin.eq_zero i]; rfl,
      ← Measure.map_map (f := fun x : ℕ → S => x 0)
        (g := fun Q : S => fun _ : Fin 1 => Q) (by fun_prop) (measurable_pi_apply 0),
      homogeneous_initial]
    rfl
  | succ n ih =>
    rw [show (fun x : ℕ → S => fun i : Fin (n + 2) => x i.1) =
      (fun p => Fin.snoc p.1 p.2) ∘
        (fun x : ℕ → S => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) by
          funext x i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp,
      ← Measure.map_map
        (f := fun x : ℕ → S => ((fun i : Fin (n + 1) => x i.1), x (n + 1)))
        (g := fun p : (Fin (n + 1) → S) × S => (Fin.snoc p.1 p.2 : Fin (n + 2) → S))
        (snoc_measurable n) (by fun_prop), homogeneous_prefix_pair, ih]
    rfl


/-- All coordinates through the specified finite time are live. -/
def allLive (n : ℕ) : Set (Fin (n + 1) → Cemetery) := {w | ∀ i, w i ≠ Sum.inr ()}

private theorem allLive_measurable (n : ℕ) : MeasurableSet (allLive n) := by
  have he : allLive n = ⋂ i : Fin (n + 1), {w : Fin (n + 1) → Cemetery | w i ≠ Sum.inr ()} := by
    ext w; simp only [allLive, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun i => ((measurableSet_singleton (Sum.inr () : Cemetery)).preimage
    (measurable_pi_apply i)).compl)

private theorem allLive_snoc (n : ℕ) (w : Fin (n + 1) → Cemetery) (y : Cemetery) :
    Fin.snoc w y ∈ allLive (n + 1) ↔ w ∈ allLive n ∧ y ≠ Sum.inr () := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.snoc_castSucc] using h i.castSucc,
      by simpa only [Fin.snoc_last] using h (Fin.last (n + 1))⟩
  · rintro ⟨hw, hy⟩ i
    exact Fin.lastCases (by simpa only [Fin.snoc_last] using hy)
      (fun j => by simpa only [Fin.snoc_castSucc] using hw j) i

private theorem cemetery_live_integral (M : Kernel PDescriptor PDescriptor)
    (hsub : ∀ Q, M Q Set.univ ≤ 1) (Q : PDescriptor)
    (f : Cemetery → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, {y : Cemetery | y ≠ Sum.inr ()}.indicator f y ∂cemetery M (Sum.inl Q)) =
      ∫⁻ R, f (Sum.inl R) ∂M Q := by
  letI := cemetery_markov M hsub
  haveI : IsFiniteKernel M := ⟨⟨1, by simp, hsub⟩⟩
  have hset : MeasurableSet {y : Cemetery | y ≠ Sum.inr ()} :=
    (measurableSet_singleton (Sum.inr () : Cemetery)).compl
  change (∫⁻ y, _ ∂((M.map (Sum.inl : PDescriptor → Cemetery)) Q +
      (1 - M Q Set.univ) • Measure.dirac (Sum.inr ()))) = _
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  simp only [Set.indicator_of_notMem (show Sum.inr () ∉ {y : Cemetery | y ≠ Sum.inr ()} by simp),
    smul_eq_mul, mul_zero, add_zero]
  rw [Kernel.map_apply _ measurable_inl, lintegral_map (hf.indicator hset) measurable_inl]
  apply lintegral_congr
  intro R
  exact Set.indicator_of_mem Sum.inl_ne_inr f

private theorem finiteProduct_live_integral (μ : Measure PDescriptor) [IsProbabilityMeasure μ]
    (M : Kernel PDescriptor PDescriptor) (hsub : ∀ Q, M Q Set.univ ≤ 1)
    (n : ℕ) (f : (Fin (n + 1) → Cemetery) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, (allLive n).indicator f w ∂finiteProduct (μ.map Sum.inl) (cemetery M) n) =
      ∫⁻ w, f (fun i => Sum.inl (w i)) ∂finiteProduct μ M n := by
  letI := cemetery_markov M hsub
  haveI : IsFiniteKernel M := ⟨⟨1, by simp, hsub⟩⟩
  induction n with
  | zero =>
    rw [finiteProduct, lintegral_map ((hf.indicator (allLive_measurable 0))) (by fun_prop),
      lintegral_map (show Measurable (fun y : Cemetery =>
        (allLive 0).indicator f (fun _ : Fin 1 => y)) from
        (hf.indicator (allLive_measurable 0)).comp (by fun_prop)) measurable_inl,
      finiteProduct, lintegral_map
        (show Measurable (fun w : Fin 1 → PDescriptor => f (fun i => Sum.inl (w i))) from
          hf.comp (by fun_prop))
        (show Measurable (fun Q : PDescriptor => fun _ : Fin 1 => Q) by fun_prop)]
    apply lintegral_congr
    intro Q
    exact Set.indicator_of_mem
      (show (fun _ : Fin 1 => (Sum.inl Q : Cemetery)) ∈ allLive 0 from fun _ => Sum.inl_ne_inr) f
  | succ n ih =>
    have hs := snoc_measurable (S := Cemetery) n
    let t : (Fin (n + 1) → Cemetery) × Cemetery → ℝ≥0∞ :=
      fun p => (allLive (n + 1)).indicator f (Fin.snoc p.1 p.2)
    have ht : Measurable t := (hf.indicator (allLive_measurable (n + 1))).comp hs
    let K := (cemetery M).comap (fun w : Fin (n + 1) → Cemetery => w (Fin.last n))
      (measurable_pi_apply _)
    let g : (Fin (n + 1) → Cemetery) → ℝ≥0∞ := fun w => ∫⁻ y, t (w,y) ∂K w
    have hg : Measurable g := Measurable.lintegral_kernel_prod_right ht
    have hgmask : g = (allLive n).indicator g := by
      funext w
      by_cases hw : w ∈ allLive n
      · exact (Set.indicator_of_mem hw g).symm
      · rw [Set.indicator_of_notMem hw]
        change (∫⁻ y, t (w,y) ∂K w) = 0
        have he : (fun y => t (w,y)) = 0 := by
          funext y
          exact Set.indicator_of_notMem (fun h => hw ((allLive_snoc n w y).mp h).1) f
        rw [he]
        exact lintegral_zero
    rw [finiteProduct, lintegral_map (hf.indicator (allLive_measurable (n + 1))) hs,
      Measure.lintegral_compProd ht]
    change (∫⁻ w, g w ∂finiteProduct (μ.map Sum.inl) (cemetery M) n) = _
    rw [hgmask, ih g hg, finiteProduct,
      lintegral_map
        (show Measurable (fun w : Fin (n + 2) → PDescriptor => f (fun i => Sum.inl (w i))) from
          hf.comp (by fun_prop)) (snoc_measurable (S := PDescriptor) n),
      Measure.lintegral_compProd
        (show Measurable (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
          f (fun i => Sum.inl ((Fin.snoc p.1 p.2 : Fin (n + 2) → PDescriptor) i))) from
          (hf.comp (show Measurable (fun w : Fin (n + 2) → PDescriptor =>
            fun i => (Sum.inl (w i) : Cemetery)) by fun_prop)).comp
              (snoc_measurable (S := PDescriptor) n))]
    apply lintegral_congr
    intro w
    change (∫⁻ y, t ((fun i => Sum.inl (w i)),y)
      ∂cemetery M (Sum.inl (w (Fin.last n)))) = _
    have he : (fun y => t ((fun i => Sum.inl (w i)),y)) =
      {y : Cemetery | y ≠ Sum.inr ()}.indicator (fun y => f (Fin.snoc (fun i => Sum.inl (w i)) y)) := by
      funext y
      have hw : (fun i => Sum.inl (w i)) ∈ allLive n := fun _ => Sum.inl_ne_inr
      by_cases hy : y ≠ Sum.inr ()
      · rw [Set.indicator_of_mem hy]
        exact Set.indicator_of_mem ((allLive_snoc n _ y).mpr ⟨hw,hy⟩) f
      · rw [Set.indicator_of_notMem hy]
        exact Set.indicator_of_notMem (fun h => hy ((allLive_snoc n _ y).mp h).2) f
    have hfc : Measurable (fun y : Cemetery =>
        f (Fin.snoc (fun i => (Sum.inl (w i) : Cemetery)) y)) :=
      by
      have hm : Measurable (fun y : Cemetery =>
          ((fun i : Fin (n + 1) => (Sum.inl (w i) : Cemetery)), y)) := by fun_prop
      have hh := (snoc_measurable (S := Cemetery) n).comp hm
      exact hf.comp hh
    rw [he, cemetery_live_integral M hsub (w (Fin.last n))
      (fun y => f (Fin.snoc (fun i => (Sum.inl (w i) : Cemetery)) y)) hfc]
    apply lintegral_congr
    intro R
    congr 1
    funext i
    exact Fin.lastCases (by simp) (fun j => by simp) i

/-- The unweighted surviving prefix is the actual substochastic product law;
its density relative to the original finite C history is the product of the
same-row Radon-Nikodym derivatives. -/
theorem common_flow_finite_product (F : CommonFlow) :
    ∃ (G : Set PDescriptor) (hsub : ∀ Q, doob F G Q Set.univ ≤ 1),
      MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
      ∀ n : ℕ,
        ((killedTrajectory F (doob F G) hsub).map
          (fun x (i : Fin (n + 1)) => x i.1)).restrict (allLive n) =
          (finiteProduct F.nuP (doob F G) n).map (fun w i => Sum.inl (w i)) ∧
        finiteProduct F.nuP (doob F G) n =
          ((originalTrajectory F).map (fun x (i : Fin (n + 1)) => x i.1)).withDensity
            (finiteDensity F (doob F G) n) ∧
        finiteProduct F.nuP (doob F G) n ≪
          (originalTrajectory F).map (fun x (i : Fin (n + 1)) => x i.1) := by
  obtain ⟨G, hsub, hmG, haG, hm, hp, hac, hc, hconj, hlim, hpos, hk, hdist⟩ :=
    common_flow_doob_survival F
  letI := cemetery_markov (doob F G) hsub
  haveI : IsFiniteKernel (doob F G) := ⟨⟨1, by simp, hsub⟩⟩
  haveI : IsProbabilityMeasure (F.nuP.map (Sum.inl : PDescriptor → Cemetery)) :=
    Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  refine ⟨G, hsub, hmG, haG, fun n => ⟨?_, ?_, ?_⟩⟩
  · change ((homogeneousLaw (F.nuP.map Sum.inl) (cemetery (doob F G))).map _).restrict _ = _
    rw [homogeneous_prefix_product]
    ext E hE
    rw [Measure.restrict_apply hE, Measure.map_apply (by fun_prop) hE]
    have hf := finiteProduct_live_integral F.nuP (doob F G) hsub n
      (E.indicator (fun _ => 1)) (measurable_const.indicator hE)
    rw [show (fun w : Fin (n + 1) → Cemetery =>
        (allLive n).indicator (E.indicator (fun _ => (1 : ℝ≥0∞))) w) =
        (E ∩ allLive n).indicator (fun _ => 1) by
          funext w; by_cases hw : w ∈ allLive n <;> by_cases he : w ∈ E <;>
            simp [Set.indicator, hw, he], show (∫⁻ w, (E ∩ allLive n).indicator (fun _ => (1 : ℝ≥0∞)) w
        ∂finiteProduct (F.nuP.map Sum.inl) (cemetery (doob F G)) n) =
        finiteProduct (F.nuP.map Sum.inl) (cemetery (doob F G)) n (E ∩ allLive n) from
          lintegral_indicator_one (hE.inter (allLive_measurable n)),
      show (fun w : Fin (n + 1) → PDescriptor => E.indicator (fun _ => (1 : ℝ≥0∞))
          (fun i => Sum.inl (w i))) =
        ((fun w i => Sum.inl (w i)) ⁻¹' E).indicator (fun _ => 1) by rfl,
      show (∫⁻ w, ((fun w : Fin (n + 1) → PDescriptor => fun i => (Sum.inl (w i) : Cemetery)) ⁻¹' E).indicator
        (fun _ => (1 : ℝ≥0∞)) w ∂finiteProduct F.nuP (doob F G) n) =
        finiteProduct F.nuP (doob F G) n
          ((fun w : Fin (n + 1) → PDescriptor => fun i => (Sum.inl (w i) : Cemetery)) ⁻¹' E) from
          lintegral_indicator_one (hE.preimage (by fun_prop))] at hf
    exact hf
  · rw [originalTrajectory, homogeneous_prefix_product]
    exact finiteProduct_density F (doob F G) hac n
  · rw [originalTrajectory, homogeneous_prefix_product,
      finiteProduct_density F (doob F G) hac n]
    exact withDensity_absolutelyContinuous _ _

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts

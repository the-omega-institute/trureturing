/- GID: D5/S3/TotalVariation/ParryInducedEntropy
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParryInducedEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy of the induced bilateral Parry return system. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31572. -/

import D5.S3.TotalVariation.ParryFirstReturn
import D5.S3.Entropy.KolmogorovSinai.Bernoulli

/-! Finite observations of the induced bilateral Parry return system. -/

namespace D5.S3.TotalVariation.ParryInducedEntropy

open Function MeasurableSpace MeasureTheory Set
open D5.S3.TotalVariation.ParryBilateralLaw
open D5.S3.TotalVariation.ParryFirstReturn
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.Entropy.KolmogorovSinai
open D5.S3.Entropy.BernoulliShift (negMulLog_prod_eq_sum sum_prod_mul_neg_log_eq_sum_negMulLog)
open scoped ENNReal

variable {k : ℕ}

private noncomputable def elapsed (r : RelationPath k) : ℕ → ℕ
  | 0 => 0
  | n + 1 => returnTime r + elapsed (returnMap r) n

private theorem bit_before_return (r : RelationPath k) (i : ℕ) (hi : i < returnTime r) :
    r.val (i : ℤ) = decide (i + 1 < returnTime r) := by
  have coordinate : -1 + ((i + 1 : ℕ) : ℤ) = (i : ℤ) := by omega
  by_cases hlt : i + 1 < returnTime r
  · have hn := (returnTime_spec r).2.2.2 (i + 1) (by omega) hlt
    have ht : r.val (i : ℤ) ≠ false := by
      intro hz
      apply hn
      change (relationShift^[i + 1] r).val (-1) = false
      rwa [shift_iterate, coordinate]
    simpa [hlt] using Bool.eq_true_of_ne_false ht
  · have heq : returnTime r = i + 1 := by omega
    have hzero := (returnTime_spec r).2.2.1
    change (relationShift^[returnTime r] r).val (-1) = false at hzero
    rw [heq, shift_iterate, coordinate] at hzero
    simpa [hlt] using hzero

private theorem bits_eq_of_return_durations (r s : RelationPath k) (m : ℕ)
    (h : ∀ i < m, returnTime (returnMap^[i] r) = returnTime (returnMap^[i] s)) :
    elapsed r m = elapsed s m ∧ ∀ i < elapsed r m, r.val (i : ℤ) = s.val (i : ℤ) := by
  induction m generalizing r s with
  | zero => simp [elapsed]
  | succ m ih =>
    have hfirst : returnTime r = returnTime s := by simpa using h 0 (by omega)
    have htail (i : ℕ) (hi : i < m) :
        returnTime (returnMap^[i] (returnMap r)) =
          returnTime (returnMap^[i] (returnMap s)) := by
      simpa only [Function.iterate_succ_apply] using h (i + 1) (by omega)
    obtain ⟨hsame, hbits⟩ := ih (returnMap r) (returnMap s) htail
    refine ⟨by simp only [elapsed, hfirst, hsame], ?_⟩
    intro i hi
    by_cases hlt : i < returnTime r
    · rw [bit_before_return r i hlt, bit_before_return s i (hfirst ▸ hlt), hfirst]
    · have hi' : i - returnTime r < elapsed (returnMap r) m := by
        simp only [elapsed] at hi
        omega
      have hbit := hbits _ hi'
      simp only [returnMap, shift_iterate] at hbit
      have hleft : ((i - returnTime r : ℕ) : ℤ) + returnTime r = (i : ℤ) := by omega
      rw [← hfirst, hleft] at hbit
      exact hbit

private theorem elapsed_iterate (r : RelationPath k) (m : ℕ) (t : ℤ) :
    (returnMap^[m] r).val t = r.val (t + elapsed r m) := by
  induction m generalizing r with
  | zero => simp [elapsed]
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [elapsed, returnMap, shift_iterate, add_left_comm, add_comm]

private theorem elapsed_add (r : RelationPath k) (a b : ℕ) :
    elapsed r (a + b) = elapsed r a + elapsed (returnMap^[a] r) b := by
  induction a generalizing r with
  | zero => simp [elapsed]
  | succ a ih =>
    rw [Nat.succ_add, elapsed, Function.iterate_succ_apply, ih]
    simp [elapsed, Nat.add_assoc]

private theorem elapsed_ge (r : RelationPath k) (m : ℕ) : m ≤ elapsed r m := by
  induction m generalizing r with
  | zero => simp
  | succ m ih =>
    rw [elapsed]
    have hpos := (returnTime_spec r).1
    have htail := ih (returnMap r)
    omega

private theorem window_names_eq (r s : RelationPath k) (radius length : ℕ)
    (past : ∀ j : ℤ, -(radius : ℤ) ≤ j → j < 0 → r.val j = s.val j)
    (gaps : ∀ j < length + radius,
      returnTime (returnMap^[j] r) = returnTime (returnMap^[j] s)) :
    ∀ i < length, ∀ t : ℤ, -(radius : ℤ) ≤ t → t ≤ (radius : ℤ) →
      (returnMap^[i] r).val t = (returnMap^[i] s).val t := by
  intro i hi t htLeft htRight
  have eqElapsed := (bits_eq_of_return_durations r s i fun j hj =>
    gaps j (by omega)).1
  rw [elapsed_iterate, elapsed_iterate, ← eqElapsed]
  let j : ℤ := t + elapsed r i
  change r.val j = s.val j
  by_cases hj : j < 0
  · exact past j (by dsimp [j]; omega) hj
  · let offset := length + radius - i
    have hadd : i + offset = length + radius := by dsimp [offset]; omega
    have total : elapsed r (length + radius) =
        elapsed r i + elapsed (returnMap^[i] r) offset := by
      rw [← hadd, elapsed_add]
    have hlo := elapsed_ge (returnMap^[i] r) offset
    have hjlt : j.toNat < elapsed r (length + radius) := by
      dsimp [j, offset] at *
      omega
    have eqAt := (bits_eq_of_return_durations r s (length + radius) gaps).2 j.toNat hjlt
    simpa only [Int.toNat_of_nonneg (le_of_not_gt hj)] using eqAt

private theorem relationPath_standardBorel : StandardBorelSpace (RelationPath k) := by
  have h : {r : ℤ → Bool | Admissible k r}
      = ⋂ t : ℤ, ⋃ i : Fin k, {r : ℤ → Bool | r (t + i.val) = false} := by
    ext r
    simp [Admissible]
  have hm : MeasurableSet {r : ℤ → Bool | Admissible k r} := by
    rw [h]
    refine MeasurableSet.iInter fun t => MeasurableSet.iUnion fun i => ?_
    have heval : Measurable (fun r : ℤ → Bool => r (t + i.val)) := measurable_pi_apply _
    exact heval (measurableSet_singleton false)
  exact hm.standardBorel

private noncomputable def fiberPartition {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) : MeasurePartition μ β where
  cells := fun i => f ⁻¹' {i}
  measurable := fun i => hf (measurableSet_singleton i)
  aedisjoint := by
    intro i j hij
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun x hi hj => hij ?_)
    exact (Set.mem_singleton_iff.mp hi).symm.trans (Set.mem_singleton_iff.mp hj)
  cover := Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨f x, rfl⟩

private def window (radius : ℕ) (r : RelationPath k) (i : Fin (2 * radius + 1)) : Bool :=
  r.val ((i.val : ℤ) - radius)

private theorem measurable_window (radius : ℕ) : Measurable (@window k radius) :=
  Measurable.of_eval fun i =>
    (measurable_pi_apply ((i.val : ℤ) - radius)).comp measurable_subtype_coe

private noncomputable def returnSymbol (r : RelationPath k) : Fin k :=
  ⟨returnTime r - 1, by
    have hp := (returnTime_spec r).1
    have hk := (returnTime_spec r).2.1
    omega⟩

private theorem returnSymbol_succ (r : RelationPath k) :
    (returnSymbol r).val + 1 = returnTime r := by
  have hp := (returnTime_spec r).1
  change returnTime r - 1 + 1 = returnTime r
  omega

private theorem measurable_returnSymbol : Measurable (@returnSymbol k) := by
  refine measurable_to_countable' fun i => ?_
  have heq : returnSymbol ⁻¹' {i} = returnTime ⁻¹' {i.val + 1} := by
    ext r
    simp only [mem_preimage, mem_singleton_iff, ← returnSymbol_succ r]
    exact ⟨fun h => by rw [h], fun h => Fin.ext (Nat.add_right_cancel h)⟩
  rw [heq]
  exact measurable_returnTime (measurableSet_singleton _)

private def pastName (radius : ℕ) (r : RelationPath k) (i : Fin radius) : Bool :=
  r.val ((i.val : ℤ) - radius)

private noncomputable def gapName (length : ℕ) (r : RelationPath k) (i : Fin length) : Fin k :=
  returnSymbol (returnMap^[i.val] r)

private noncomputable def windowName (radius length : ℕ) (r : RelationPath k)
    (i : Fin length) : Fin (2 * radius + 1) → Bool :=
  window radius (returnMap^[i.val] r)

private theorem measurable_pastName (radius : ℕ) : Measurable (@pastName k radius) :=
  Measurable.of_eval fun i =>
    (measurable_pi_apply ((i.val : ℤ) - radius)).comp measurable_subtype_coe

private theorem measurable_gapName (length : ℕ) (hreturn : Measurable (@returnMap k)) :
    Measurable (@gapName k length) :=
  Measurable.of_eval fun i => measurable_returnSymbol.comp (hreturn.iterate i.val)

private theorem measurable_windowName (radius length : ℕ)
    (hreturn : Measurable (@returnMap k)) : Measurable (@windowName k radius length) :=
  Measurable.of_eval fun i => (measurable_window radius).comp (hreturn.iterate i.val)

private theorem windowName_factors (radius length : ℕ) :
    (windowName (k := k) radius length).FactorsThrough
      (fun r => (pastName radius r, gapName (length + radius) r)) := by
  intro r s h
  have hpast := congrArg Prod.fst h
  have hgaps := congrArg Prod.snd h
  have equality := window_names_eq r s radius length
    (fun j hlo hhi => by
      let i : Fin radius := ⟨(j + radius).toNat, by omega⟩
      have hindex : (i.val : ℤ) - radius = j := by dsimp [i]; omega
      simpa only [pastName, hindex] using congrFun hpast i)
    (fun j hj => by
      have heq := congrFun hgaps ⟨j, hj⟩
      change returnSymbol (returnMap^[j] r) = returnSymbol (returnMap^[j] s) at heq
      simpa only [returnSymbol_succ] using congrArg (fun i : Fin k => i.val + 1) heq)
  funext i t
  apply equality i.val i.isLt
  · omega
  · have ht := t.isLt
    omega

private theorem windowName_entropy_le (μ : Measure (RelationPath k))
    [IsProbabilityMeasure μ] (hreturn : Measurable (@returnMap k)) (radius length : ℕ) :
    entropy μ (fiberPartition μ (windowName radius length)
      (measurable_windowName radius length hreturn)).cells ≤
    (radius : ℝ) * Real.log 2 + entropy μ
      (fiberPartition μ (gapName (length + radius))
        (measurable_gapName (length + radius) hreturn)).cells := by
  let P := fiberPartition μ (windowName radius length) (measurable_windowName radius length hreturn)
  let Q := fiberPartition μ (pastName radius) (measurable_pastName radius)
  let R := fiberPartition μ (gapName (length + radius))
    (measurable_gapName (length + radius) hreturn)
  let S := fiberPartition μ (fun r => (pastName radius r, gapName (length + radius) r))
    ((measurable_pastName radius).prodMk (measurable_gapName (length + radius) hreturn))
  obtain ⟨reconstruct, hcomp⟩ := (Function.factorsThrough_iff _).1 (windowName_factors (k := k) radius length)
  have hrefine (j : (Fin radius → Bool) × (Fin (length + radius) → Fin k)) :
      S.cells j ≤ᵐ[μ] P.cells (reconstruct j) := by
    refine Filter.Eventually.of_forall fun x hx => ?_
    change (pastName radius x, gapName (length + radius) x) = j at hx
    change windowName radius length x = reconstruct j
    rw [congrFun hcomp x, Function.comp_apply, hx]
  have hcells : S.cells = joinCells Q.cells R.cells := by
    funext j
    ext x
    simp [S, Q, R, fiberPartition, joinCells_apply, Prod.ext_iff]
  have hcard : entropy μ Q.cells ≤ (radius : ℝ) * Real.log 2 := by
    calc
      entropy μ Q.cells ≤ Real.log (Fintype.card (Fin radius → Bool)) :=
        entropy_le_log_card_partition Q
      _ = _ := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
        Real.log_pow]; norm_num
  exact (entropy_le_of_partition_refinement P S reconstruct hrefine).trans
    (hcells ▸ (entropy_join_le Q R).trans (add_le_add hcard le_rfl))

private theorem generatedSigma_fiberPartition {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) :
    generatedSigmaAlgebra μ (fiberPartition μ f hf) = MeasurableSpace.comap f inferInstance := by
  refine le_antisymm (generateFrom_le ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨{i}, measurableSet_singleton i, rfl⟩
  · rw [MeasurableSpace.comap_eq_generateFrom]
    refine generateFrom_le ?_
    rintro _ ⟨s, _, rfl⟩
    rw [← Set.biUnion_preimage_singleton]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ : i ∈ s =>
      measurableSet_generateFrom ⟨i, rfl⟩

private noncomputable def windowPartition (μ : Measure (RelationPath k)) (radius : ℕ) :=
  fiberPartition μ (window radius) (measurable_window radius)

private theorem window_saturations (μ : Measure (RelationPath k))
    (hreturn : MeasurePreserving (@returnMap k) μ μ) :
    let σ (radius : ℕ) := ⨆ n : ℕ,
      generatedSigmaAlgebra μ (ksJoin hreturn (windowPartition μ radius) n)
    Monotone σ ∧ (⨆ radius, σ radius) = (inferInstance : MeasurableSpace (RelationPath k)) := by
  let σ (radius : ℕ) := ⨆ n : ℕ,
    MeasurableSpace.comap (returnMap^[n])
      (generatedSigmaAlgebra μ (windowPartition μ radius))
  have hσ (radius : ℕ) : (⨆ n : ℕ,
      generatedSigmaAlgebra μ (ksJoin hreturn (windowPartition μ radius) n)) = σ radius :=
    iSup_generatedSigmaAlgebra_ksJoin_eq hreturn (windowPartition μ radius)
  dsimp only
  simp_rw [hσ]
  constructor
  · intro a b hab
    refine iSup_mono fun n => MeasurableSpace.comap_mono ?_
    unfold windowPartition
    rw [generatedSigma_fiberPartition, generatedSigma_fiberPartition]
    let index (i : Fin (2 * a + 1)) : Fin (2 * b + 1) :=
      ⟨i.val + (b - a), by have := i.isLt; omega⟩
    let select (f : Fin (2 * b + 1) → Bool) (i : Fin (2 * a + 1)) := f (index i)
    have hselect : Measurable select :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    have hcomp : (window a : RelationPath k → _) = select ∘ window b := by
      funext r i
      change r.val ((i.val : ℤ) - a) = r.val ((index i).val - (b : ℤ))
      apply congrArg r.val
      change (i.val : ℤ) - a = ((i.val + (b - a) : ℕ) : ℤ) - b
      omega
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hselect.comap_le
  · refine le_antisymm (iSup_le fun r => ?_) ?_
    · rw [← hσ]
      exact iSup_le fun n => generatedSigmaAlgebra_le _
    · change MeasurableSpace.comap (Subtype.val : RelationPath k → ℤ → Bool) _ ≤ _
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      refine iSup_le fun t => ?_
      let radius := t.natAbs
      let index : Fin (2 * radius + 1) := ⟨(t + radius).toNat, by omega⟩
      have hcoord : (fun r : ℤ → Bool => r t) ∘ Subtype.val =
          (fun f => f index) ∘ (window radius : RelationPath k → _) := by
        funext r
        change r.val t = r.val ((index.val : ℤ) - radius)
        apply congrArg r.val
        change t = ((t + (t.natAbs : ℤ)).toNat : ℤ) - t.natAbs
        omega
      rw [hcoord, ← MeasurableSpace.comap_comp]
      refine le_trans (MeasurableSpace.comap_mono (measurable_pi_apply index).comap_le) ?_
      refine le_trans ?_ (le_iSup σ radius)
      rw [← generatedSigma_fiberPartition μ _ (measurable_window radius)]
      change generatedSigmaAlgebra μ (windowPartition μ radius) ≤
        ⨆ n : ℕ, MeasurableSpace.comap (returnMap^[n])
          (generatedSigmaAlgebra μ (windowPartition μ radius))
      simpa only [Function.iterate_zero, MeasurableSpace.comap_id] using le_iSup
        (fun n : ℕ => MeasurableSpace.comap (returnMap^[n])
        (generatedSigmaAlgebra μ (windowPartition μ radius))) 0

private theorem ksJoin_fiber_cells {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [Fintype β] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (observe : α → β) (hobs : Measurable observe) (n : ℕ) :
    (ksJoin hT (fiberPartition μ observe hobs) n).cells =
      (fiberPartition μ (fun x (i : Fin n) => observe (T^[i.val] x))
        (Measurable.of_eval fun i => hobs.comp (hT.measurable.iterate i.val))).cells := by
  funext name
  ext x
  simp [ksJoin_cells, ksJoinCells_apply, fiberPartition, funext_iff]

private theorem ksEntropy_eq_of_linear_gap_entropy (μ : Measure (RelationPath k))
    [IsProbabilityMeasure μ] (hreturn : MeasurePreserving (@returnMap k) μ μ)
    (h : ℝ) (hgap : ∀ n : ℕ, entropy μ
      (fiberPartition μ (gapName n) (measurable_gapName n hreturn.measurable)).cells
        = (n : ℝ) * h) :
    ksEntropy hreturn = (h : EReal) := by
  have : StandardBorelSpace (RelationPath k) := relationPath_standardBorel
  apply le_antisymm
  · have hsaturation := window_saturations μ hreturn
    refine ksEntropy_le_of_increasing_partition_saturations hreturn (windowPartition μ)
      hsaturation.1 hsaturation.2 h ?_
    intro radius
    have hbound (n : ℕ) : ksEntropySeq hreturn (windowPartition μ radius) n ≤
        (n : ℝ) * h + ((radius : ℝ) * Real.log 2 + (radius : ℝ) * h) := by
      rw [ksEntropySeq, windowPartition, ksJoin_fiber_cells]
      change entropy μ (fiberPartition μ (windowName radius n)
        (measurable_windowName radius n hreturn.measurable)).cells ≤ _
      have hw := windowName_entropy_le μ hreturn.measurable radius n
      rw [hgap] at hw
      change entropy μ _ ≤ _ at hw
      push_cast at hw
      linarith only [hw]
    let constant : ℝ := (radius : ℝ) * Real.log 2 + (radius : ℝ) * h
    have hlim : Filter.Tendsto (fun n : ℕ => h + constant / (n : ℝ))
        Filter.atTop (nhds h) := by
      simpa using (tendsto_const_nhds (x := h)).add
        (tendsto_const_div_atTop_nhds_zero_nat constant)
    refine le_of_tendsto_of_tendsto (tendsto_ksEntropySeq hreturn (windowPartition μ radius))
      hlim ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc ksEntropySeq hreturn (windowPartition μ radius) n / (n : ℝ)
        ≤ ((n : ℝ) * h + constant) / n := div_le_div_of_nonneg_right (hbound n) hnpos.le
      _ = h + constant / n := by rw [add_div, mul_comm (n : ℝ), mul_div_cancel_right₀ _ hnpos.ne']
  · let P := fiberPartition μ returnSymbol measurable_returnSymbol
    have heq : ksEntropyPartition hreturn P = h := by
      have hlim : Filter.Tendsto (fun n : ℕ => ksEntropySeq hreturn P n / (n : ℝ))
          Filter.atTop (nhds h) := by
        apply (tendsto_const_nhds (x := h)).congr'
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hnonzero : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        have hseq : ksEntropySeq hreturn P n = (n : ℝ) * h := by
          dsimp only [ksEntropySeq, P]
          rw [ksJoin_fiber_cells]
          exact hgap n
        rw [hseq, mul_comm (n : ℝ), mul_div_cancel_right₀ _ hnonzero]
      exact tendsto_nhds_unique (tendsto_ksEntropySeq hreturn P) hlim
    rw [← heq]
    exact le_ksEntropy hreturn P

private theorem ksEntropy_eq_of_geometric_gap_mass (hk : 2 ≤ k)
    (μ : Measure (RelationPath k)) [IsProbabilityMeasure μ]
    (hreturn : MeasurePreserving (@returnMap k) μ μ)
    (hcyl : ∀ (n : ℕ) (f : Fin n → Fin k), μ {r | gapName n r = f} =
      ENNReal.ofReal (∏ i : Fin n, parryParameter k ^ ((f i).val + 1))) :
    ksEntropy hreturn = ((∑ a : Fin k, Real.negMulLog
      (parryParameter k ^ (a.val + 1)) : ℝ) : EReal) := by
  let p (a : Fin k) := parryParameter k ^ (a.val + 1)
  have hp : ∑ a, p a = 1 := by
    change (∑ a : Fin k, parryParameter k ^ (a.val + 1)) = 1
    exact (Fin.sum_univ_eq_sum_range (fun i => parryParameter k ^ (i + 1)) k).trans
      (parry_stationary_law k hk).1.2.2
  have hpos : 0 < parryParameter k := by
    linarith [(parry_stationary_law k hk).1.1]
  refine ksEntropy_eq_of_linear_gap_entropy μ hreturn (∑ a, Real.negMulLog (p a)) ?_
  intro n
  rw [entropy_def]
  have hcell (f : Fin n → Fin k) :
      (μ ((fiberPartition μ (gapName n) (measurable_gapName n hreturn.measurable)).cells f)).toReal
        = ∏ i : Fin n, p (f i) := by
    change (μ {r | gapName n r = f}).toReal = _
    rw [hcyl, ENNReal.toReal_ofReal]
    exact Finset.prod_nonneg fun i _ => pow_nonneg hpos.le _
  simp_rw [hcell, negMulLog_prod_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_prod_mul_neg_log_eq_sum_negMulLog p hp]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem matchesReturnTimes_ofFn_iff (r : RelationPath k) (n : ℕ) (f : Fin n → Fin k) :
    matchesReturnTimes r (List.ofFn f) = true ↔ gapName n r = f := by
  induction n generalizing r with
  | zero =>
    simp [matchesReturnTimes, funext_iff]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [matchesReturnTimes, Bool.and_eq_true, decide_eq_true_eq]
    rw [ih (returnMap r)]
    simp only [funext_iff, Fin.forall_fin_succ]
    constructor
    · rintro ⟨hfirst, hrest⟩
      refine ⟨Fin.ext ?_, fun i => ?_⟩
      · have hz := returnSymbol_succ r
        change (returnSymbol r).val = (f 0).val
        omega
      · change returnSymbol (returnMap^[i.val + 1] r) = f i.succ
        simpa only [gapName, Function.iterate_succ_apply] using hrest i
    · rintro ⟨hfirst, hrest⟩
      refine ⟨?_, fun i => ?_⟩
      · change returnSymbol r = f 0 at hfirst
        simpa only [hfirst] using (returnSymbol_succ r).symm
      · have hi := hrest i
        change returnSymbol (returnMap^[i.val + 1] r) = f i.succ at hi
        simpa only [gapName, Function.iterate_succ_apply] using hi

private theorem weighted_suffix_sum (p : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, p ^ j * ∑ i ∈ Finset.range (n - j), p ^ (i + 1)) =
      ∑ i ∈ Finset.range n, (i + 1 : ℕ) * p ^ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hsum : (∑ j ∈ Finset.range n, p ^ j * ∑ i ∈ Finset.range (n + 1 - j), p ^ (i + 1)) =
        Finset.sum (Finset.range n)
          (fun j => p ^ j * (∑ i ∈ Finset.range (n - j), p ^ (i + 1)) + p ^ (n + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn := Finset.mem_range.mp hj
      rw [show n + 1 - j = n - j + 1 by omega, Finset.sum_range_succ, mul_add, ← pow_add]
      rw [show j + (n - j + 1) = n + 1 by omega]
    rw [hsum, Finset.sum_add_distrib, ih]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [show n + 1 - n = 1 by omega]
    simp [pow_succ]
    ring

private theorem geometric_duration_entropy (hk : 2 ≤ k) :
    (∑ a : Fin k, Real.negMulLog (parryParameter k ^ (a.val + 1))) =
      (-Real.log (parryParameter k)) * normalizer k := by
  let p := parryParameter k
  have hsum : normalizer k =
      ∑ a : Fin k, (a.val + 1 : ℕ) * p ^ (a.val + 1) := by
    calc normalizer k =
        ∑ j ∈ Finset.range k, p ^ j * ∑ i ∈ Finset.range (k - j), p ^ (i + 1) :=
          Fin.sum_univ_eq_sum_range
            (fun j => p ^ j * ∑ i ∈ Finset.range (k - j), p ^ (i + 1)) k
      _ = ∑ a : Fin k, (a.val + 1 : ℕ) * p ^ (a.val + 1) :=
        (weighted_suffix_sum p k).trans
          (Fin.sum_univ_eq_sum_range (fun i => (i + 1 : ℕ) * p ^ (i + 1)) k).symm
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.negMulLog, Real.log_pow]
  ring

/-- The Kolmogorov–Sinai entropy of the native zero-section return map of the
bilateral Parry source is the Shannon entropy of its geometric return law. -/
theorem actual_return_entropy (hk : 2 ≤ k)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (μ : ProbabilityMeasure (RelationPath k))
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (hμ : (μ : Measure (RelationPath k)).map relationShift = μ)
    (hcylinder : ∀ (ell : ℤ) (m : ℕ) (v : Fin (m + 1) → Fin k),
      (μ : Measure (RelationPath k))
        {r | (fun i : Fin (m + 1) => ((e (false, r)).val (ell + i.val)).2) = v} =
        ENNReal.ofReal (suffixLaw k (v 0)) * ∏ i : Fin m,
          ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ))) :
    ∃ hprob : IsProbabilityMeasure (sectionMeasure (μ : Measure (RelationPath k))),
      ∃ hreturn : MeasurePreserving returnMap (sectionMeasure (μ : Measure (RelationPath k)))
          (sectionMeasure (μ : Measure (RelationPath k))),
        @ksEntropy (RelationPath k) _ _ hprob _ hreturn =
          ((∑ a : Fin k, Real.negMulLog (parryParameter k ^ (a.val + 1)) : ℝ) : EReal) ∧
        @ksEntropy (RelationPath k) _ _ hprob _ hreturn =
          ((-Real.log (parryParameter k) /
            ((μ : Measure (RelationPath k)) (zeroSection k)).toReal : ℝ) : EReal) := by
  obtain ⟨_, hmass, _, hprob, hreturn, _, _⟩ := actual_first_return_system hk e μ hsuffix hμ hcylinder
  have hentropy := ksEntropy_eq_of_geometric_gap_mass hk _ hreturn (fun n f => by
    have hcyl := return_time_cylinder_probability hk e μ hsuffix hμ hcylinder (List.ofFn f)
    simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_apply,
      matchesReturnTimes_ofFn_iff] using hcyl)
  refine ⟨hprob, hreturn, hentropy, ?_⟩
  have hnormalizer : 0 < normalizer k :=
    lt_of_lt_of_le zero_lt_one (parry_stationary_law k hk).2.2.1
  rw [hentropy, geometric_duration_entropy hk, hmass,
    ENNReal.toReal_ofReal (one_div_nonneg.mpr hnormalizer.le), one_div, div_inv_eq_mul]

end D5.S3.TotalVariation.ParryInducedEntropy

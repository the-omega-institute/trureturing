/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual finite raw history determines every epoch prefix and its cylinder law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset Function
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalHistoryLaw
open ActualRenewalStopping ActualRenewalPrefixLaw

variable {S R Ω : Type*}

private def fillGaps {n : ℕ} (v : Fin n → ℕ) (j : ℕ) : ℕ :=
  if h : j < n then v ⟨j, h⟩ else 0

private def clippedIndex {n : ℕ} (u : ℕ) (v : Fin n → ℕ) (t : ℕ) : Fin (cut u v) :=
  if h : t < cut u v then ⟨t, h⟩ else ⟨0, by unfold cut; omega⟩

/-- The literal epoch prefix, including epoch zero. -/
def epochHistory (labels : Set S) (update : S → Bool → R → S)
    (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    (n : ℕ) (ω : Ω) : Fin (n + 1) → S :=
  fun j => epoch labels update (I ω) (ξ ω) (τ ω) (K ω) j.val

private def localHistory (labels : Set S) (update : S → Bool → R → S)
    (n : ℕ) (a : ℕ × (Fin n → ℕ)) (p : S × (Fin (cut a.1 a.2) → R)) :
    Fin (n + 1) → S :=
  fun j => epoch labels update p.1 (fun t => p.2 (clippedIndex a.1 a.2 t))
    a.1 (fillGaps a.2) j.val

private theorem local_history_eq (labels : Set S) (update : S → Bool → R → S)
    (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    (n : ℕ) (a : ℕ × (Fin n → ℕ)) (ω : Ω)
    (ha : ω ∈ sourceSlice τ K n a) :
    localHistory labels update n a (rawPrefix I ξ (cut a.1 a.2) ω) =
      epochHistory labels update I τ K ξ n ω := by
  have hgap (j : ℕ) (hj : j < n) : fillGaps a.2 j = K ω j := by
    simp only [fillGaps, dif_pos hj]
    exact (ha.2 ⟨j, hj⟩).symm
  have hc (j : ℕ) (hj : j ≤ n) :
      clock a.1 (fillGaps a.2) j = clock (τ ω) (K ω) j := by
    induction j with
    | zero => simp only [clock, ha.1]
    | succ j ih => rw [clock, clock, ih (by omega), hgap j (by omega)]
  have hcut : clock (τ ω) (K ω) n = cut a.1 a.2 := by
    rw [clock_cut, ha.1]
    congr 1
    exact funext ha.2
  have hcoin (t : ℕ) (ht : t < cut a.1 a.2) :
      (rawPrefix I ξ (cut a.1 a.2) ω).2 (clippedIndex a.1 a.2 t) = ξ ω t := by
    simp only [rawPrefix, clippedIndex, dif_pos ht]
  have hstate (j : ℕ) (hj : j ≤ n) :
      epoch labels update (I ω)
          (fun t => (rawPrefix I ξ (cut a.1 a.2) ω).2 (clippedIndex a.1 a.2 t))
          a.1 (fillGaps a.2) j =
        epoch labels update (I ω) (ξ ω) (τ ω) (K ω) j := by
    induction j with
    | zero =>
      rw [(actual_words labels update _ _ _ _).1,
        (actual_words labels update _ _ _ _).1, ha.1]
      congr 1
      funext t
      apply hcoin
      have : a.1 + 1 ≤ cut a.1 a.2 := by unfold cut; omega
      omega
    | succ j ih =>
      rw [(actual_words labels update _ _ _ _).2,
        (actual_words labels update _ _ _ _).2,
        hgap j (by omega), ih (by omega)]
      congr 1
      funext t
      rw [hc j (by omega)]
      apply hcoin
      have hb := (clock_strict (τ ω) (K ω)).monotone hj
      simp only [clock] at hb
      omega
  funext j
  exact hstate j.val (by omega)

section Measurability
variable [MeasurableSpace S] [MeasurableSpace R]
    (labels : Set S) (update : S → Bool → R → S)
    (heff : ∀ b, Measurable (fun p : S × R => effective labels update p.1 b p.2))

include heff in
private theorem local_history_measurable (n : ℕ) (a : ℕ × (Fin n → ℕ)) :
    Measurable (localHistory labels update n a) := by
  have hr (t : ℕ) : Measurable (fun p : S × (Fin (cut a.1 a.2) → R) =>
      run labels update p.1 (fun t => p.2 (clippedIndex a.1 a.2 t))
        a.1 (fillGaps a.2) t) := by
    induction t with
    | zero => exact measurable_fst
    | succ t ih =>
      exact (heff (sourceBit a.1 (fillGaps a.2) t)).comp
        (ih.prodMk ((measurable_pi_apply (clippedIndex a.1 a.2 t)).comp measurable_snd))
  exact measurable_pi_iff.mpr fun j => hr _

include heff in
/-- On each finite source slice every ordinary epoch-history event is an event
    of the initial state and coins strictly before the actual next-block cut.
    Source coordinates may also be observed; the next gap is excluded. -/
theorem actual_history_locality
    (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    (n : ℕ) (B : Set ((ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S)))
    (hB : MeasurableSet B) :
    ∃ D : (a : ℕ × (Fin n → ℕ)) → Set (S × (Fin (cut a.1 a.2) → R)),
      (∀ a, MeasurableSet (D a)) ∧
      {ω | ((τ ω, fun j : Fin n => K ω j.val),
          epochHistory labels update I τ K ξ n ω) ∈ B} =
        pastEvent I τ K ξ n D := by
  let D := fun a : ℕ × (Fin n → ℕ) =>
    (fun p => (a, localHistory labels update n a p)) ⁻¹' B
  refine ⟨D, fun a => hB.preimage
    (measurable_const.prodMk (local_history_measurable labels update heff n a)), ?_⟩
  ext ω
  simp only [pastEvent, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_setOf_eq]
  constructor
  · intro h
    let a : ℕ × (Fin n → ℕ) := (τ ω, fun j => K ω j.val)
    have ha : ω ∈ sourceSlice τ K n a := ⟨rfl, fun _ => rfl⟩
    refine ⟨a, ha, ?_⟩
    change (a, localHistory labels update n a (rawPrefix I ξ (cut a.1 a.2) ω)) ∈ B
    rw [local_history_eq labels update I τ K ξ n a ω ha]
    exact h
  · rintro ⟨a, ha, h⟩
    change (a, localHistory labels update n a (rawPrefix I ξ (cut a.1 a.2) ω)) ∈ B at h
    rw [local_history_eq labels update I τ K ξ n a ω ha] at h
    have he : (τ ω, fun j : Fin n => K ω j.val) = a :=
      Prod.ext ha.1 (funext ha.2)
    rwa [he]

end Measurability
section Probability
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace R]
    [Countable S] [MeasurableSingletonClass S]
    (labels : Set S) (update : S → Bool → R → S)
    (P : Measure Ω) (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    (η : PMF S) (w f : PMF ℕ) (ρ : Measure R) [IsProbabilityMeasure ρ]
    (A C : S → PMF S)
    (heff : ∀ b, Measurable (fun p : S × R => effective labels update p.1 b p.2))
    (hrow : ∀ s b, ρ.map (effective labels update s b) = (if b then C s else A s).toMeasure)
    (hI : Measurable I) (hτ : Measurable τ)
    (hK : ∀ j, Measurable (fun ω => K ω j))
    (hξ : ∀ j, Measurable (fun ω => ξ ω j))
    (hprimitive : Primitive P I τ K ξ η.toMeasure w f ρ)

/-- Joint observation of just the past source coordinates and actual states. -/
def observedHistory (n : ℕ) (ω : Ω) :
    (ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S) :=
  ((τ ω, fun j => K ω j.val), epochHistory labels update I τ K ξ n ω)

include heff hI hτ hK hξ in
private theorem history_event_measurable (n : ℕ)
    (B : Set ((ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S)))
    (hB : MeasurableSet B) :
    MeasurableSet (observedHistory labels update I τ K ξ n ⁻¹' B) := by
  obtain ⟨D, hD, hE⟩ := actual_history_locality labels update heff I τ K ξ n B hB
  change MeasurableSet {ω | ((τ ω, fun j : Fin n => K ω j.val),
    epochHistory labels update I τ K ξ n ω) ∈ B}
  rw [hE]
  exact MeasurableSet.iUnion fun a =>
    (slice_measurable τ K hτ hK n a).inter
      ((hD a).preimage (hI.prodMk (measurable_pi_iff.mpr fun j => hξ j.val)))

include heff hI hτ hK hξ in
private theorem epoch_event_measurable (n : ℕ) (T : Set S) (hT : MeasurableSet T) :
    MeasurableSet {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n ∈ T} := by
  exact history_event_measurable labels update I τ K ξ heff hI hτ hK hξ n
    ((fun p => p.2 (Fin.last n)) ⁻¹' T)
    (hT.preimage ((measurable_pi_apply (Fin.last n)).comp measurable_snd))

include heff hrow hI hτ hK hξ hprimitive in
private theorem history_fixed_gap_step (n : ℕ)
    (B : Set ((ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S)))
    (hB : MeasurableSet B) (s : S)
    (hstate : ∀ ω ∈ observedHistory labels update I τ K ξ n ⁻¹' B,
      epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n = s)
    (k : ℕ) (T : Set S) (hT : MeasurableSet T) :
    P ((observedHistory labels update I τ K ξ n ⁻¹' B) ∩ {ω | K ω n = k} ∩
      {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ T}) =
    P (observedHistory labels update I τ K ξ n ⁻¹' B) * f k *
      ((zeroRow A k s).bind C).toMeasure T := by
  obtain ⟨D, hD, hE⟩ := actual_history_locality labels update heff I τ K ξ n B hB
  change observedHistory labels update I τ K ξ n ⁻¹' B = _ at hE
  have hs : ∀ ω ∈ pastEvent I τ K ξ n D,
      epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n = s := by
    rw [← hE]
    exact hstate
  simpa only [← hE] using actual_past_step P I τ K ξ labels update η.toMeasure w f ρ
    A C heff hrow hI hτ hK hξ hprimitive n D hD s hs k T hT

include heff hrow hI hτ hK hξ hprimitive in
/-- Summing all gaps gives the ordinary-past row identity for the same actual
    execution. The history can also retain every previous source gap. -/
theorem actual_history_step (n : ℕ)
    (B : Set ((ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S)))
    (hB : MeasurableSet B) (s : S)
    (hstate : ∀ ω ∈ observedHistory labels update I τ K ξ n ⁻¹' B,
      epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n = s)
    (T : Set S) (hT : MeasurableSet T) :
    P ((observedHistory labels update I τ K ξ n ⁻¹' B) ∩
      {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ T}) =
    P (observedHistory labels update I τ K ξ n ⁻¹' B) *
      (f.bind fun k => (zeroRow A k s).bind C).toMeasure T := by
  let E := observedHistory labels update I τ K ξ n ⁻¹' B
  let F := fun k => E ∩ {ω | K ω n = k} ∩
    {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ T}
  have hF (k : ℕ) : MeasurableSet (F k) :=
    ((history_event_measurable labels update I τ K ξ heff hI hτ hK hξ n B hB).inter
      ((hK n) (measurableSet_singleton k))).inter
      (epoch_event_measurable labels update I τ K ξ heff hI hτ hK hξ (n + 1) T hT)
  have hdis : Pairwise (Disjoint on F) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨_, hk⟩, _⟩ ⟨⟨_, hl⟩, _⟩
    exact hkl (hk.symm.trans hl)
  have hUnion : (⋃ k, F k) = E ∩
      {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ T} := by
    ext ω
    simp only [F, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, ⟨hE, _⟩, hT⟩; exact ⟨hE, hT⟩
    · rintro ⟨hE, hT⟩; exact ⟨K ω n, ⟨hE, rfl⟩, hT⟩
  rw [← hUnion, measure_iUnion hdis hF, PMF.toMeasure_bind_apply _ _ _ hT]
  simp_rw [show ∀ k, P (F k) = P E * f k * ((zeroRow A k s).bind C).toMeasure T from
    fun k => history_fixed_gap_step labels update P I τ K ξ η w f ρ A C heff hrow
      hI hτ hK hξ hprimitive n B hB s hstate k T hT, mul_assoc]
  exact ENNReal.tsum_mul_left

include heff hrow hI hτ hK hξ hprimitive in
/-- The ordinary-past integral identity, written as a countable state sum.
    It holds for every measurable history event, including null histories. -/
theorem actual_ordinary_past (n : ℕ)
    (H : Set (Fin (n + 1) → S)) (hH : MeasurableSet H)
    (T : Set S) (hT : MeasurableSet T) :
    P ({ω | epochHistory labels update I τ K ξ n ω ∈ H} ∩
      {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ T}) =
    ∑' s, P ({ω | epochHistory labels update I τ K ξ n ω ∈ H} ∩
      {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n = s}) *
        (f.bind fun k => (zeroRow A k s).bind C).toMeasure T := by
  let B := fun s : S => (Prod.snd ⁻¹' H) ∩
    (fun p : (ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S) => p.2 (Fin.last n)) ⁻¹' {s}
  have hB (s : S) : MeasurableSet (B s) :=
    (hH.preimage measurable_snd).inter ((measurableSet_singleton s).preimage
      ((measurable_pi_apply (Fin.last n)).comp measurable_snd))
  let E := fun s : S => observedHistory labels update I τ K ξ n ⁻¹' B s
  let F := fun s : S => E s ∩
    {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ T}
  have hF (s : S) : MeasurableSet (F s) :=
    (history_event_measurable labels update I τ K ξ heff hI hτ hK hξ n (B s) (hB s)).inter
      (epoch_event_measurable labels update I τ K ξ heff hI hτ hK hξ (n + 1) T hT)
  have hdis : Pairwise (Disjoint on F) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨_, hs⟩, _⟩ ⟨⟨_, ht⟩, _⟩
    exact hst (hs.symm.trans ht)
  have hUnion : (⋃ s, F s) =
      {ω | epochHistory labels update I τ K ξ n ω ∈ H} ∩
        {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ T} := by
    ext ω
    simp only [Set.mem_iUnion, F, E, B, observedHistory, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    change (∃ s, (_ ∧ _ = s) ∧ _) ↔ _ ∧ _
    constructor
    · rintro ⟨s, ⟨h, _⟩, ht⟩; exact ⟨h, ht⟩
    · rintro ⟨h, ht⟩
      exact ⟨epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n, ⟨h, rfl⟩, ht⟩
  rw [← hUnion, measure_iUnion hdis hF]
  apply tsum_congr
  intro s
  exact actual_history_step labels update P I τ K ξ η w f ρ A C heff hrow
    hI hτ hK hξ hprimitive n (B s) (hB s) s (fun ω h => h.2) T hT

/-- Nonnegative mass of a finite state word; length zero is the empty prefix. -/
def prefixMass (ν : PMF S) (U : S → PMF S) : (l : ℕ) → (Fin l → S) → ℝ≥0∞
  | 0, _ => 1
  | n + 1, x => ν (x 0) * ∏ j : Fin n, U (x j.castSucc) (x j.succ)

include heff hrow hI hτ hK hξ hprimitive in
/-- Every finite actual state prefix, including the empty one, has the row
    product derived from the first wait and subsequent gaps. No process law is
    assumed in addition to the primitive deterministic-coordinate interface. -/
theorem actual_state_prefix (l : ℕ) (x : Fin l → S) :
    P {ω | ∀ j : Fin l, epoch labels update (I ω) (ξ ω) (τ ω) (K ω) j.val = x j} =
      prefixMass (w.bind fun u => η.bind fun s => (zeroRow A u s).bind C)
        (fun s => f.bind fun k => (zeroRow A k s).bind C) l x := by
  have hp : ∀ (n : ℕ) (x : Fin (n + 1) → S),
      P {ω | epochHistory labels update I τ K ξ n ω = x} =
        (w.bind fun u => η.bind fun s => (zeroRow A u s).bind C) (x 0) *
          ∏ j : Fin n, (f.bind fun k => (zeroRow A k (x j.castSucc)).bind C) (x j.succ) := by
    intro n
    induction n with
    | zero =>
      intro x
      have he : {ω : Ω | epochHistory labels update I τ K ξ 0 ω = x} =
          {ω : Ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) 0 ∈ ({x 0} : Set S)} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro h; exact congrFun h 0
        · intro h; funext j; have : j = 0 := Fin.ext (by omega); subst j; exact h
      rw [he, actual_initial_law P I τ K ξ labels update η w f ρ A C heff hrow
        hI hτ hξ hprimitive {x 0} (measurableSet_singleton _)]
      simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        Fin.prod_univ_zero, mul_one]
    | succ n ih =>
      intro x
      let xp : Fin (n + 1) → S := fun j => x j.castSucc
      let B : Set ((ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S)) :=
        Prod.snd ⁻¹' {xp}
      have hB : MeasurableSet B := (measurableSet_singleton xp).preimage measurable_snd
      have hstate : ∀ ω ∈ observedHistory labels update I τ K ξ n ⁻¹' B,
          epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n = xp (Fin.last n) := by
        intro ω hω
        exact congrFun hω (Fin.last n)
      have he : {ω | epochHistory labels update I τ K ξ (n + 1) ω = x} =
          (observedHistory labels update I τ K ξ n ⁻¹' B) ∩
            {ω : Ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈
              ({x (Fin.last (n + 1))} : Set S)} := by
        ext ω
        change (_ = x) ↔ (_ = xp) ∧ _ = _
        constructor
        · intro h; exact ⟨funext fun j => congrFun h j.castSucc, congrFun h (Fin.last _)⟩
        · rintro ⟨h, ht⟩
          funext j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · exact ht
          · exact congrFun h j
      rw [he, actual_history_step labels update P I τ K ξ η w f ρ A C heff hrow
        hI hτ hK hξ hprimitive n B hB (xp (Fin.last n)) hstate
        {x (Fin.last (n + 1))} (measurableSet_singleton _)]
      change P {ω | epochHistory labels update I τ K ξ n ω = xp} * _ = _
      rw [ih xp, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        Fin.prod_univ_castSucc]
      simp only [xp, Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last, mul_assoc]
  cases l with
  | zero =>
    have hmass : P Set.univ = 1 := by
      simpa only [Set.mem_univ, Set.setOf_true, measure_univ] using
        actual_initial_law P I τ K ξ labels update η w f ρ A C heff hrow
          hI hτ hξ hprimitive Set.univ MeasurableSet.univ
    simpa only [prefixMass, Fin.forall_fin_zero, Set.setOf_true] using hmass
  | succ n =>
    have he : {ω | ∀ j : Fin (n + 1),
        epoch labels update (I ω) (ξ ω) (τ ω) (K ω) j.val = x j} =
        {ω | epochHistory labels update I τ K ξ n ω = x} := by
      ext ω
      exact ⟨fun h => funext h, fun h => congrFun h⟩
    rw [he]
    exact hp n x

include heff hrow hI hτ hK hξ hprimitive in
/-- Every joint source/state cylinder on the actual run has its literal
    first-wait factor and all of its subsequent gap/word factors. -/
theorem actual_source_cylinders (n : ℕ) (a : ℕ × (Fin n → ℕ))
    (x : Fin (n + 1) → S) :
    P (observedHistory labels update I τ K ξ n ⁻¹' {(a, x)}) =
      w a.1 * (η.bind fun s => (zeroRow A a.1 s).bind C) (x 0) *
        ∏ j : Fin n, (f (a.2 j) * ((zeroRow A (a.2 j) (x j.castSucc)).bind C) (x j.succ)) := by
  induction n with
  | zero =>
    let D : Set (S × (Fin (a.1 + 1) → R)) :=
      (fun p => word labels update a.1 p.1 p.2) ⁻¹' {x 0}
    have hD : MeasurableSet D := (word_measurable labels update heff a.1)
      (measurableSet_singleton _)
    have he : observedHistory labels update I τ K ξ 0 ⁻¹' {(a, x)} =
        sourceSlice τ K 0 a ∩ rawPrefix I ξ (a.1 + 1) ⁻¹' D := by
      ext ω
      constructor
      · intro hω
        change observedHistory labels update I τ K ξ 0 ω = (a, x) at hω
        have hu := congrArg (fun p : (ℕ × (Fin 0 → ℕ)) × (Fin (0 + 1) → S) => p.1.1) hω
        change τ ω = a.1 at hu
        have hx := congrFun (congrArg Prod.snd hω) 0
        change epoch labels update (I ω) (ξ ω) (τ ω) (K ω) 0 = x 0 at hx
        rw [(actual_words labels update _ _ _ _).1, hu] at hx
        exact ⟨⟨hu, fun j => Fin.elim0 j⟩, hx⟩
      · intro hω
        have hu : τ ω = a.1 := hω.1.1
        have hx : word labels update a.1 (I ω) (fun j => ξ ω j.val) = x 0 := hω.2
        change observedHistory labels update I τ K ξ 0 ω = (a, x)
        apply Prod.ext
        · exact Prod.ext hu (funext fun j => Fin.elim0 j)
        · funext j
          have hj : j = 0 := Fin.ext (by omega)
          subst j
          change epoch labels update (I ω) (ξ ω) (τ ω) (K ω) 0 = x 0
          rw [(actual_words labels update _ _ _ _).1, hu]
          exact hx
    have hp := hprimitive 0 a (a.1 + 1) 0 D Set.univ hD MeasurableSet.univ
    have hw := congrArg (fun μ : Measure S => μ {x 0})
      (initial_word_law labels update ρ A C heff hrow η a.1)
    rw [Measure.map_apply (word_measurable labels update heff a.1)
      (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at hw
    change (η.toMeasure.prod (Measure.pi fun _ : Fin (a.1 + 1) => ρ)) D = _ at hw
    rw [he]
    simpa only [rawBlock, Set.preimage_univ, Set.inter_univ, measure_univ,
      Fin.prod_univ_zero, mul_one, hw] using hp
  | succ n ih =>
    let ap : ℕ × (Fin n → ℕ) := (a.1, fun j => a.2 j.castSucc)
    let xp : Fin (n + 1) → S := fun j => x j.castSucc
    let B : Set ((ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S)) := {(ap, xp)}
    have hB : MeasurableSet B := measurableSet_singleton _
    have hstate : ∀ ω ∈ observedHistory labels update I τ K ξ n ⁻¹' B,
        epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n = xp (Fin.last n) := by
      intro ω hω
      exact congrFun (congrArg Prod.snd hω) (Fin.last n)
    have he : observedHistory labels update I τ K ξ (n + 1) ⁻¹' {(a, x)} =
        (observedHistory labels update I τ K ξ n ⁻¹' B) ∩
          {ω | K ω n = a.2 (Fin.last n)} ∩
          {ω : Ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈
            ({x (Fin.last (n + 1))} : Set S)} := by
      ext ω
      constructor
      · intro hω
        change observedHistory labels update I τ K ξ (n + 1) ω = (a, x) at hω
        have hu : τ ω = a.1 := congrArg (fun p => p.1.1) hω
        have hv : (fun j : Fin (n + 1) => K ω j.val) = a.2 :=
          congrArg (fun p => p.1.2) hω
        have hx : epochHistory labels update I τ K ξ (n + 1) ω = x :=
          congrArg Prod.snd hω
        refine ⟨⟨?_, congrFun hv (Fin.last n)⟩, congrFun hx (Fin.last (n + 1))⟩
        change observedHistory labels update I τ K ξ n ω = (ap, xp)
        exact Prod.ext (Prod.ext hu (funext fun j => congrFun hv j.castSucc))
          (funext fun j => congrFun hx j.castSucc)
      · rintro ⟨⟨hp, hk⟩, hy⟩
        change observedHistory labels update I τ K ξ n ω = (ap, xp) at hp
        have hu : τ ω = a.1 := congrArg (fun p => p.1.1) hp
        have hv : (fun j : Fin n => K ω j.val) = (fun j => a.2 j.castSucc) :=
          congrArg (fun p => p.1.2) hp
        have hx : epochHistory labels update I τ K ξ n ω = xp :=
          congrArg Prod.snd hp
        change observedHistory labels update I τ K ξ (n + 1) ω = (a, x)
        apply Prod.ext
        · apply Prod.ext hu
          funext j
          exact Fin.lastCases hk (fun j => congrFun hv j) j
        · funext j
          exact Fin.lastCases hy (fun j => congrFun hx j) j
    rw [he, history_fixed_gap_step labels update P I τ K ξ η w f ρ A C heff hrow
      hI hτ hK hξ hprimitive n B hB (xp (Fin.last n)) hstate
      (a.2 (Fin.last n)) {x (Fin.last (n + 1))} (measurableSet_singleton _)]
    rw [show P (observedHistory labels update I τ K ξ n ⁻¹' B) = _ from ih ap xp,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      Fin.prod_univ_castSucc]
    simp only [ap, xp, Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last, mul_assoc]

end Probability
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalHistoryLaw

/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual raw renewal words and deterministic source slices pay random-cut freshness. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset Function
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw
open ActualRenewalStopping

variable {S R : Type*}

/-- The effective update is exactly the branch used by the saved raw execution. -/
def effective (labels : Set S) (update : S → Bool → R → S)
    (s : S) (b : Bool) (r : R) : S :=
  if s ∈ labels then s else update s b r

/-- A finite zero word, with its original chronological raw coins. -/
def zeros (labels : Set S) (update : S → Bool → R → S) :
    (k : ℕ) → S → (Fin k → R) → S
  | 0, s, _ => s
  | k + 1, s, r => effective labels update
      (zeros labels update k s (fun j => r j.castSucc)) false (r (Fin.last k))

/-- The closing tick consumes the last coin of the same word, including k=0. -/
def word (labels : Set S) (update : S → Bool → R → S)
    (k : ℕ) (s : S) (r : Fin (k + 1) → R) : S :=
  effective labels update (zeros labels update k s (fun j => r j.castSucc))
    true (r (Fin.last k))

/-- Both the initial word and every subsequent word are calculated on the
    original run, including stops inside a zero segment. -/
theorem actual_words (labels : Set S) (update : S → Bool → R → S)
    (initial : S) (coins : ℕ → R) (wait : ℕ) (gaps : ℕ → ℕ) :
    epoch labels update initial coins wait gaps 0 =
      word labels update wait initial (fun j => coins j.val) ∧
    ∀ n, epoch labels update initial coins wait gaps (n + 1) =
      word labels update (gaps n) (epoch labels update initial coins wait gaps n)
        (fun j => coins (clock wait gaps n + j.val)) := by
  have hz : ∀ m, m ≤ wait → run labels update initial coins wait gaps m =
      zeros labels update m initial (fun j => coins j.val) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [run, ih (by omega), (source_words wait gaps).1 m (by omega)]
      rfl
  have hg : ∀ n m, m ≤ gaps n →
      run labels update initial coins wait gaps (clock wait gaps n + m) =
        zeros labels update m (epoch labels update initial coins wait gaps n)
          (fun j => coins (clock wait gaps n + j.val)) := by
    intro n m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hb := (source_words wait gaps).2.2.1 n m (by omega)
      have hne : m ≠ gaps n := by omega
      simp only [hne, decide_false] at hb
      rw [Nat.add_succ, run, ih (by omega), hb]
      rfl
  constructor
  · change run labels update initial coins wait gaps (wait + 1) = _
    rw [run, hz wait le_rfl, (source_words wait gaps).2.1]
    rfl
  · intro n
    change run labels update initial coins wait gaps
      (clock wait gaps n + gaps n + 1) = _
    rw [run, hg n (gaps n) le_rfl]
    have hb := (source_words wait gaps).2.2.1 n (gaps n) le_rfl
    simp only [decide_true] at hb
    rw [hb]
    rfl

/-- Finite raw source coordinates determine the cut before the next gap. -/
def cut {n : ℕ} (u : ℕ) (v : Fin n → ℕ) : ℕ :=
  u + 1 + ∑ j, (v j + 1)

theorem clock_cut (u : ℕ) (K : ℕ → ℕ) (n : ℕ) :
    clock u K n = cut u (fun j : Fin n => K j.val) := by
  induction n with
  | zero => simp [clock, cut]
  | succ n ih => simp [clock, cut, Fin.sum_univ_castSucc, ih, Nat.add_assoc]

/-- Distributional iteration of the same zero row; it defines no trajectory. -/
def zeroRow (A : S → PMF S) : ℕ → S → PMF S
  | 0, s => PMF.pure s
  | k + 1, s => (zeroRow A k s).bind A

section FiniteIntegration
variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    [MeasurableSpace R]
    (labels : Set S) (update : S → Bool → R → S)
    (ρ : Measure R) [IsProbabilityMeasure ρ]
    (A C : S → PMF S)
    (heff : ∀ b, Measurable (fun p : S × R => effective labels update p.1 b p.2))
    (hrow : ∀ s b, ρ.map (effective labels update s b) = (if b then C s else A s).toMeasure)

include heff in
private theorem zeros_measurable (k : ℕ) :
    Measurable (fun p : S × (Fin k → R) => zeros labels update k p.1 p.2) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    exact (heff false).comp
      ((ih.comp (measurable_fst.prodMk (measurable_pi_iff.mpr fun j =>
        (measurable_pi_apply j.castSucc).comp measurable_snd))).prodMk
        ((measurable_pi_apply (Fin.last k)).comp measurable_snd))

include heff in
theorem word_measurable (k : ℕ) :
    Measurable (fun p : S × (Fin (k + 1) → R) => word labels update k p.1 p.2) :=
  (heff true).comp
    (((zeros_measurable labels update heff k).comp
      (measurable_fst.prodMk (measurable_pi_iff.mpr fun j =>
        (measurable_pi_apply j.castSucc).comp measurable_snd))).prodMk
      ((measurable_pi_apply (Fin.last k)).comp measurable_snd))

private theorem split_last (k : ℕ) :
    (Measure.pi fun _ : Fin (k + 1) => ρ).map
      (fun r => (fun j : Fin k => r j.castSucc, r (Fin.last k))) =
    (Measure.pi fun _ : Fin k => ρ).prod ρ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => R) (Fin.last k)
  have hh := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => ρ) (Fin.last k)).map_eq
  have hc : (fun r : (Fin (k + 1) → R) =>
      (fun j : Fin k => r j.castSucc, r (Fin.last k))) = Prod.swap ∘ e := by
    funext r
    simp [e, MeasurableEquiv.piFinSuccAbove, Fin.succAbove_last, Fin.init]
    all_goals first | rfl | (funext j; rfl)
  rw [hc, ← Measure.map_map measurable_swap e.measurable, hh, Measure.prod_swap]

include heff hrow in
private theorem integrate_step (ν : PMF S) (b : Bool) :
    (ν.toMeasure.prod ρ).map (fun p => effective labels update p.1 b p.2) =
      (ν.bind (fun s => if b then C s else A s)).toMeasure := by
  ext B hB
  rw [Measure.map_apply (heff b) hB, Measure.prod_apply ((heff b) hB),
    PMF.toMeasure_bind_apply _ _ _ hB, lintegral_countable']
  apply tsum_congr
  intro s
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have hh := congrArg (fun μ : Measure S => μ B) (hrow s b)
  have hm : Measurable (effective labels update s b) :=
    (heff b).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hm hB] at hh
  change ρ (effective labels update s b ⁻¹' B) * ν s = _
  rw [hh, mul_comm]

include heff hrow in
private theorem finite_word_law (k : ℕ) (s : S) :
    (Measure.pi fun _ : Fin (k + 1) => ρ).map (word labels update k s) =
      ((zeroRow A k s).bind C).toMeasure := by
  have hsplit (k : ℕ) : Measurable (fun r : Fin (k + 1) → R =>
      ((fun j : Fin k => r j.castSucc), r (Fin.last k))) :=
    (measurable_pi_iff.mpr fun j : Fin k => measurable_pi_apply j.castSucc).prodMk
      (measurable_pi_apply (Fin.last k))
  have hpair (k : ℕ) (s : S) (hm : Measurable (zeros labels update k s)) :
      Measurable (fun r : Fin (k + 1) → R =>
        (zeros labels update k s (fun j => r j.castSucc), r (Fin.last k))) :=
    (hm.comp (measurable_pi_iff.mpr fun j : Fin k => measurable_pi_apply j.castSucc)).prodMk
      (measurable_pi_apply (Fin.last k))
  have hz : ∀ k s, (Measure.pi fun _ : Fin k => ρ).map (zeros labels update k s) =
      (zeroRow A k s).toMeasure := by
    intro k
    induction k with
    | zero => intro s; simp [zeros, zeroRow, PMF.toMeasure_pure]
    | succ k ih =>
      intro s
      have hm : Measurable (zeros labels update k s) :=
        (zeros_measurable labels update heff k).comp
        (show Measurable (fun r : Fin k → R => (s, r)) from
        measurable_const.prodMk measurable_id)
      have hp : (Measure.pi fun _ : Fin (k + 1) => ρ).map
          (fun r => (zeros labels update k s (fun j => r j.castSucc), r (Fin.last k))) =
          (zeroRow A k s).toMeasure.prod ρ := by
        rw [show (fun r : (Fin (k + 1) → R) =>
            (zeros labels update k s (fun j => r j.castSucc), r (Fin.last k))) =
            (Prod.map (zeros labels update k s) id) ∘
              (fun r => (fun j : Fin k => r j.castSucc, r (Fin.last k))) from rfl,
          ← Measure.map_map (hm.prodMap measurable_id)
            (hsplit k),
          split_last ρ k, ← Measure.map_prod_map _ _ hm measurable_id, ih, Measure.map_id]
      change (Measure.pi fun _ : Fin (k + 1) => ρ).map
        ((fun p : S × R => effective labels update p.1 false p.2) ∘
          (fun r => (zeros labels update k s (fun j => r j.castSucc), r (Fin.last k)))) = _
      rw [← Measure.map_map (heff false)
        (hpair k s hm), hp]
      exact integrate_step labels update ρ A C heff hrow (zeroRow A k s) false
  have hm : Measurable (zeros labels update k s) :=
    (zeros_measurable labels update heff k).comp
    (show Measurable (fun r : Fin k → R => (s, r)) from
        measurable_const.prodMk measurable_id)
  have hp : (Measure.pi fun _ : Fin (k + 1) => ρ).map
      (fun r => (zeros labels update k s (fun j => r j.castSucc), r (Fin.last k))) =
      (zeroRow A k s).toMeasure.prod ρ := by
    rw [show (fun r : (Fin (k + 1) → R) =>
        (zeros labels update k s (fun j => r j.castSucc), r (Fin.last k))) =
        (Prod.map (zeros labels update k s) id) ∘
          (fun r => (fun j : Fin k => r j.castSucc, r (Fin.last k))) from rfl,
      ← Measure.map_map (hm.prodMap measurable_id)
        (hsplit k),
      split_last ρ k, ← Measure.map_prod_map _ _ hm measurable_id, hz, Measure.map_id]
  change (Measure.pi fun _ : Fin (k + 1) => ρ).map
    ((fun p : S × R => effective labels update p.1 true p.2) ∘
      (fun r => (zeros labels update k s (fun j => r j.castSucc), r (Fin.last k)))) = _
  rw [← Measure.map_map (heff true)
    (hpair k s hm), hp]
  exact integrate_step labels update ρ A C heff hrow (zeroRow A k s) true

include heff hrow in
theorem initial_word_law (η : PMF S) (k : ℕ) :
    (η.toMeasure.prod (Measure.pi fun _ : Fin (k + 1) => ρ)).map
      (fun p => word labels update k p.1 p.2) =
      (η.bind fun s => (zeroRow A k s).bind C).toMeasure := by
  ext B hB
  rw [Measure.map_apply (word_measurable labels update heff k) hB,
    Measure.prod_apply ((word_measurable labels update heff k) hB),
    PMF.toMeasure_bind_apply _ _ _ hB, lintegral_countable']
  apply tsum_congr
  intro s
  have hh := congrArg (fun μ : Measure S => μ B)
    (finite_word_law labels update ρ A C heff hrow k s)
  have hm : Measurable (word labels update k s) :=
    (word_measurable labels update heff k).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hm hB] at hh
  change (Measure.pi fun _ : Fin (k + 1) => ρ) (word labels update k s ⁻¹' B) *
    η.toMeasure {s} = _
  rw [hh, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

end FiniteIntegration

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace R]
    (P : Measure Ω) (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)

/-- This source slice excludes K(n); the next gap is never a past coordinate. -/
def sourceSlice (n : ℕ) (a : ℕ × (Fin n → ℕ)) : Set Ω :=
  {ω | τ ω = a.1 ∧ ∀ j, K ω j.val = a.2 j}

/-- A deterministic-length prefix of the original initialization and coin tape. -/
def rawPrefix (l : ℕ) (ω : Ω) : S × (Fin l → R) :=
  (I ω, fun j => ξ ω j.val)

/-- A deterministic-offset block, before any random cut substitution. -/
def rawBlock (l r : ℕ) (ω : Ω) : Fin r → R := fun j => ξ ω (l + j.val)

/-- An arbitrary event of the exact raw history, specified separately on each
    countable source slice. Coin fibers need not be countable or atomic. -/
def pastEvent (n : ℕ)
    (D : (a : ℕ × (Fin n → ℕ)) → Set (S × (Fin (cut a.1 a.2) → R))) : Set Ω :=
  ⋃ a, sourceSlice τ K n a ∩ rawPrefix I ξ (cut a.1 a.2) ⁻¹' D a

/-- Only primitive deterministic-coordinate laws appear in this interface.
    The two coin intervals have fixed lengths and fixed offset l. No clock,
    epoch, observer transition or random cut occurs in its statement. -/
def Primitive (η : Measure S) (w f : PMF ℕ) (ρ : Measure R) : Prop :=
  ∀ (n : ℕ) (a : ℕ × (Fin n → ℕ)) (l r : ℕ)
    (D : Set (S × (Fin l → R))) (B : Set (Fin r → R)),
    MeasurableSet D → MeasurableSet B →
    P (sourceSlice τ K n a ∩ rawPrefix I ξ l ⁻¹' D ∩ rawBlock ξ l r ⁻¹' B) =
      (w a.1 * ∏ j, f (a.2 j)) *
        (η.prod (Measure.pi fun _ : Fin l => ρ)) D *
        (Measure.pi fun _ : Fin r => ρ) B

theorem slice_measurable (hτ : Measurable τ) (hK : ∀ j, Measurable (fun ω => K ω j))
    (n : ℕ) (a : ℕ × (Fin n → ℕ)) : MeasurableSet (sourceSlice τ K n a) :=
  (hτ (measurableSet_singleton _)).inter (by
    have he : {ω | ∀ j : Fin n, K ω j.val = a.2 j} =
        ⋂ j : Fin n, (fun ω => K ω j.val) ⁻¹' {a.2 j} := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact (congrArg (fun B : Set Ω => MeasurableSet B) he).mpr
      (MeasurableSet.iInter fun j : Fin n => (hK j.val) (measurableSet_singleton (a.2 j))))

private theorem slices_disjoint (n : ℕ) :
    Pairwise (Disjoint on sourceSlice τ K n) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro ω ⟨hu, hv⟩ ⟨hu', hv'⟩
  apply hab
  exact Prod.ext (hu.symm.trans hu') (funext fun j => (hv j).symm.trans (hv' j))

/-- Random-cut freshness for every exact raw past event. Countable source
    slices fix the cut before deterministic coordinate independence is used;
    neither history masses nor zero entries are divided out. -/
theorem random_cut_freshness (η : Measure S) (w f : PMF ℕ) (ρ : Measure R)
    [IsProbabilityMeasure ρ]
    (hI : Measurable I) (hτ : Measurable τ)
    (hK : ∀ j, Measurable (fun ω => K ω j))
    (hξ : ∀ j, Measurable (fun ω => ξ ω j))
    (hprimitive : Primitive P I τ K ξ η w f ρ)
    (n : ℕ)
    (D : (a : ℕ × (Fin n → ℕ)) → Set (S × (Fin (cut a.1 a.2) → R)))
    (hD : ∀ a, MeasurableSet (D a)) (k : ℕ) (B : Set (Fin (k + 1) → R))
    (hB : MeasurableSet B) :
    P (pastEvent I τ K ξ n D ∩ {ω | K ω n = k} ∩
      (fun ω j => ξ ω (clock (τ ω) (K ω) n + j.val)) ⁻¹' B) =
    P (pastEvent I τ K ξ n D) * f k * (Measure.pi fun _ : Fin (k + 1) => ρ) B := by
  let E := fun a : ℕ × (Fin n → ℕ) =>
    sourceSlice τ K n a ∩ rawPrefix I ξ (cut a.1 a.2) ⁻¹' D a
  let F := fun a : ℕ × (Fin n → ℕ) =>
    sourceSlice τ K (n + 1) (a.1, Fin.snoc a.2 k) ∩
      rawPrefix I ξ (cut a.1 a.2) ⁻¹' D a ∩
      rawBlock ξ (cut a.1 a.2) (k + 1) ⁻¹' B
  have hE (a) : MeasurableSet (E a) :=
    (slice_measurable τ K hτ hK n a).inter
      ((hD a).preimage (hI.prodMk (measurable_pi_iff.mpr fun j => hξ j.val)))
  have hF (a) : MeasurableSet (F a) :=
    ((slice_measurable τ K hτ hK (n + 1) (a.1, Fin.snoc a.2 k)).inter
      ((hD a).preimage (hI.prodMk (measurable_pi_iff.mpr fun j => hξ j.val)))).inter
      (hB.preimage (measurable_pi_iff.mpr fun j => hξ (cut a.1 a.2 + j.val)))
  have hdisE : Pairwise (Disjoint on E) := fun a b hab =>
    (slices_disjoint τ K n hab).mono Set.inter_subset_left Set.inter_subset_left
  have hsplit (a : ℕ × (Fin n → ℕ)) :
      F a = E a ∩ {ω | K ω n = k} ∩
        (fun ω j => ξ ω (clock (τ ω) (K ω) n + j.val)) ⁻¹' B := by
    have hs (ω : Ω) :
        ω ∈ sourceSlice τ K (n + 1) (a.1, Fin.snoc a.2 k) ↔
          ω ∈ sourceSlice τ K n a ∧ K ω n = k := by
      simp only [sourceSlice, Set.mem_setOf_eq, Prod.fst, Prod.snd]
      constructor
      · rintro ⟨hu, hv⟩
        exact ⟨⟨hu, fun j => by simpa using hv j.castSucc⟩,
          by simpa using hv (Fin.last n)⟩
      · rintro ⟨⟨hu, hv⟩, hk⟩
        refine ⟨hu, ?_⟩
        intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using hk
        · simpa using hv j
    ext ω
    by_cases ha : ω ∈ sourceSlice τ K n a
    · have hc : clock (τ ω) (K ω) n = cut a.1 a.2 := by
        rw [clock_cut, ha.1]
        congr 1
        exact funext ha.2
      simp only [F, E, Set.mem_inter_iff, hs, rawBlock, hc, Set.mem_preimage]
      tauto
    · simp only [F, E, Set.mem_inter_iff, hs]
      tauto
  have hdisF : Pairwise (Disjoint on F) := by
    intro a b hab
    change Disjoint (F a) (F b)
    rw [hsplit a, hsplit b]
    exact (hdisE hab).mono
      (Set.Subset.trans Set.inter_subset_left Set.inter_subset_left)
      (Set.Subset.trans Set.inter_subset_left Set.inter_subset_left)
  have hmassE (a : ℕ × (Fin n → ℕ)) :
      P (E a) = (w a.1 * ∏ j, f (a.2 j)) *
        (η.prod (Measure.pi fun _ : Fin (cut a.1 a.2) => ρ)) (D a) := by
    simpa [E, rawBlock] using
      hprimitive n a (cut a.1 a.2) 0 (D a) Set.univ (hD a) MeasurableSet.univ
  have hmassF (a : ℕ × (Fin n → ℕ)) :
      P (F a) = P (E a) * f k * (Measure.pi fun _ : Fin (k + 1) => ρ) B := by
    rw [hmassE]
    have hh := hprimitive (n + 1) (a.1, Fin.snoc a.2 k)
      (cut a.1 a.2) (k + 1) (D a) B (hD a) hB
    simpa [F, Fin.prod_univ_castSucc, mul_assoc, mul_left_comm, mul_comm] using hh
  have hUnion : (⋃ a, F a) = pastEvent I τ K ξ n D ∩ {ω | K ω n = k} ∩
      (fun ω j => ξ ω (clock (τ ω) (K ω) n + j.val)) ⁻¹' B := by
    simp only [hsplit, pastEvent, E, Set.iUnion_inter]
  rw [← hUnion, measure_iUnion hdisF hF]
  simp_rw [hmassF]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
    ← measure_iUnion hdisE hE]
  rfl

/-- Initialization is integrated from the actual first wait word. The first
    PMF is w, independently of the subsequent gap PMF f, and wait zero is kept. -/
theorem actual_initial_law [Countable S] [MeasurableSingletonClass S]
    (labels : Set S) (update : S → Bool → R → S)
    (η : PMF S) (w f : PMF ℕ) (ρ : Measure R) [IsProbabilityMeasure ρ]
    (A C : S → PMF S)
    (heff : ∀ b, Measurable (fun p : S × R => effective labels update p.1 b p.2))
    (hrow : ∀ s b, ρ.map (effective labels update s b) = (if b then C s else A s).toMeasure)
    (hI : Measurable I) (hτ : Measurable τ)
    (hξ : ∀ j, Measurable (fun ω => ξ ω j))
    (hprimitive : Primitive P I τ K ξ η.toMeasure w f ρ)
    (B : Set S) (hB : MeasurableSet B) :
    P {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) 0 ∈ B} =
      (w.bind fun u => η.bind fun s => (zeroRow A u s).bind C).toMeasure B := by
  let D := fun u : ℕ => (fun p : S × (Fin (u + 1) → R) =>
    word labels update u p.1 p.2) ⁻¹' B
  let E := fun u : ℕ => {ω | τ ω = u} ∩ rawPrefix I ξ (u + 1) ⁻¹' D u
  have hD (u) : MeasurableSet (D u) := (word_measurable labels update heff u) hB
  have hE (u) : MeasurableSet (E u) := (hτ (measurableSet_singleton u)).inter
    ((hD u).preimage (hI.prodMk (measurable_pi_iff.mpr fun j => hξ j.val)))
  have hdis : Pairwise (Disjoint on E) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    rintro ω ⟨hu, _⟩ ⟨hv, _⟩
    exact huv (hu.symm.trans hv)
  have hUnion : (⋃ u, E u) =
      {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) 0 ∈ B} := by
    ext ω
    simp only [Set.mem_iUnion, E, D, rawPrefix, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_preimage]
    rw [(actual_words labels update (I ω) (ξ ω) (τ ω) (K ω)).1]
    constructor
    · rintro ⟨u, hu, hw⟩
      subst u
      exact hw
    · intro hw
      exact ⟨τ ω, rfl, hw⟩
  have hmass (u : ℕ) : P (E u) =
      w u * (η.bind fun s => (zeroRow A u s).bind C).toMeasure B := by
    have hp := hprimitive 0 (u, fun j => Fin.elim0 j) (u + 1) 0
      (D u) Set.univ (hD u) MeasurableSet.univ
    have hw := congrArg (fun μ : Measure S => μ B)
      (initial_word_law labels update ρ A C heff hrow η u)
    rw [Measure.map_apply (word_measurable labels update heff u) hB] at hw
    simpa [E, D, sourceSlice, rawBlock, hw] using hp
  rw [← hUnion, measure_iUnion hdis hE, PMF.toMeasure_bind_apply _ _ _ hB]
  exact tsum_congr hmass

/-- Integrate the next actual variable-length word on an exact raw history
    event fixing its current state. The event restriction is deterministic;
    the next-state law is a conclusion, including null and absorbed histories. -/
theorem actual_past_step [Countable S] [MeasurableSingletonClass S]
    (labels : Set S) (update : S → Bool → R → S)
    (η : Measure S) (w f : PMF ℕ) (ρ : Measure R) [IsProbabilityMeasure ρ]
    (A C : S → PMF S)
    (heff : ∀ b, Measurable (fun p : S × R => effective labels update p.1 b p.2))
    (hrow : ∀ s b, ρ.map (effective labels update s b) = (if b then C s else A s).toMeasure)
    (hI : Measurable I) (hτ : Measurable τ)
    (hK : ∀ j, Measurable (fun ω => K ω j))
    (hξ : ∀ j, Measurable (fun ω => ξ ω j))
    (hprimitive : Primitive P I τ K ξ η w f ρ)
    (n : ℕ)
    (D : (a : ℕ × (Fin n → ℕ)) → Set (S × (Fin (cut a.1 a.2) → R)))
    (hD : ∀ a, MeasurableSet (D a)) (s : S)
    (hstate : ∀ ω ∈ pastEvent I τ K ξ n D,
      epoch labels update (I ω) (ξ ω) (τ ω) (K ω) n = s)
    (k : ℕ) (B : Set S) (hB : MeasurableSet B) :
    P (pastEvent I τ K ξ n D ∩ {ω | K ω n = k} ∩
      {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ B}) =
      P (pastEvent I τ K ξ n D) * f k * ((zeroRow A k s).bind C).toMeasure B := by
  let V := word labels update k s ⁻¹' B
  have hm : Measurable (word labels update k s) :=
    (word_measurable labels update heff k).comp
      (measurable_const.prodMk measurable_id)
  have hV : MeasurableSet V := hm hB
  have hh := random_cut_freshness P I τ K ξ η w f ρ hI hτ hK hξ
    hprimitive n D hD k V hV
  have hevent : pastEvent I τ K ξ n D ∩ {ω | K ω n = k} ∩
      {ω | epoch labels update (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ B} =
      pastEvent I τ K ξ n D ∩ {ω | K ω n = k} ∩
        (fun ω j => ξ ω (clock (τ ω) (K ω) n + j.val)) ⁻¹' V := by
    ext ω
    by_cases hE : ω ∈ pastEvent I τ K ξ n D
    · by_cases hk : K ω n = k
      · have hy := (actual_words labels update (I ω) (ξ ω) (τ ω) (K ω)).2 n
        rw [hk, hstate ω hE] at hy
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hE, hk, true_and,
          Set.mem_preimage, V, hy]
      · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hk, false_and, and_false]
    · simp only [Set.mem_inter_iff, hE, false_and]
  have hw := congrArg (fun μ : Measure S => μ B)
    (finite_word_law labels update ρ A C heff hrow k s)
  rw [Measure.map_apply hm hB] at hw
  rw [hevent, hh, hw]

end Probability
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw

/- GID: D5/S3/Observer/MetricGeometry/AutonomousPredictionEntropy
   generality: I
   mirror-B: D5/B/S3/Observer/MetricGeometry/AutonomousPredictionEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Autonomous finite-state prediction has the same ordered entropy as centered observation covers. -/

import D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
import D5.S3.ObserverMemory.PredictionPseudometrics.FiniteHorizonPredictionPseudometric
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace D5.S3.Observer.MetricGeometry.AutonomousPredictionEntropy

open Set Filter Dynamics ExpGrowth
open scoped Topology Uniformity ENNReal
open D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw (HasFiniteHorizonPredictor)
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability (futureReadoutWord)

variable {X Y : Type*} [MetricSpace Y]

/-- Closed observation relation; centers remain points of the original state space. -/
def observationEntourage (o : X → Y) (ε : ℝ) : SetRel X X :=
  {p | dist (o p.1) (o p.2) ≤ ε}

/-- The response-centered closed-cover minimum, expressed through the existing orbit-cover API.
The response-image minimum and positive finite attainment are proved below. -/
noncomputable def responseCoverCount (F : X → X) (o : X → Y) (H : ℕ) (ε : ℝ) : ℕ :=
  (coverMincard F univ (observationEntourage o ε) (H + 1)).toNat

/-- Least budget for the existing autonomous finite-horizon predictor predicate.
The fallback is immaterial at positive radii on compact continuous systems. -/
noncomputable def autonomousStateCount (F : X → X) (o : X → Y) (H : ℕ) (ε : ℝ) : ℕ :=
  by
    classical
    exact if h : ∃ s, HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε s then Nat.find h else 0

/-- Observation entropy; the two ordered limit statements below justify this supremum form. -/
noncomputable def observationEntropy (F : X → X) (o : X → Y) : EReal :=
  ⨆ ε > 0, expGrowthSup (fun H => (responseCoverCount F o H ε : ℝ≥0∞))

private theorem autonomous_run {Z : Type*} (F : Z → Z) (w : List Unit) (x : Z) :
    runWord (fun _ : Unit => F) w x = (F^[w.length]) x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
      simpa only [runWord, List.length_cons, Function.iterate_succ_apply] using ih (F x)

private theorem cover_iff (F : X → X) (o : X → Y) (H : ℕ) (ε : ℝ) (s : Finset X) :
    IsDynCoverOf F univ (observationEntourage o ε) (H + 1) s ↔
      ∀ x, ∃ y ∈ s, ∀ k ≤ H, dist (o ((F^[k]) x)) (o ((F^[k]) y)) ≤ ε := by
  simp only [IsDynCoverOf, SetRel.IsCover, Set.mem_univ, true_implies,
    mem_dynEntourage, observationEntourage, Set.mem_setOf_eq,
    Finset.mem_coe, Nat.lt_succ_iff]

private theorem cover_from_predictor [Nonempty X]
    (F : X → X) (o : X → Y) (H : ℕ) (ε : ℝ) (s : ℕ)
    (hs : HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε s) :
    coverMincard F univ (observationEntourage o (2 * ε)) (H + 1) ≤ s := by
  classical
  rcases hs with ⟨S, finiteS, hn, hcard, e, G, h, herr⟩
  letI : Fintype S := finiteS
  let representative : S → X := fun q =>
    if hq : ∃ x, e x = q then Classical.choose hq else Classical.choice ‹Nonempty X›
  have rep_init (x : X) : e (representative (e x)) = e x := by
    simp only [representative, dif_pos (show ∃ y, e y = e x from ⟨x, rfl⟩)]
    exact Classical.choose_spec (show ∃ y, e y = e x from ⟨x, rfl⟩)
  let centers := Finset.univ.image representative
  have hc : IsDynCoverOf F univ (observationEntourage o (2 * ε)) (H + 1) centers := by
    apply (cover_iff F o H (2 * ε) centers).2
    intro x
    refine ⟨representative (e x), Finset.mem_image.mpr ⟨e x, Finset.mem_univ _, rfl⟩, ?_⟩
    intro k hk
    let w := List.replicate k ()
    have hw : w.length ≤ H := by simpa [w] using hk
    have hx := herr x w hw
    have hy := herr (representative (e x)) w hw
    rw [rep_init x] at hy
    rw [autonomous_run, List.length_replicate] at hx hy
    calc
      _ ≤ dist (o ((F^[k]) x)) (h (runWord G w (e x))) +
          dist (h (runWord G w (e x))) (o ((F^[k]) (representative (e x)))) := dist_triangle _ _ _
      _ ≤ ε + ε := add_le_add (by simpa only [dist_comm] using hx) hy
      _ = 2 * ε := by ring
  exact hc.coverMincard_le_card.trans <| by
    exact_mod_cast (Finset.card_image_le.trans (by simpa using hcard))

private theorem predictor_from_cover [Nonempty X]
    (F : X → X) (o : X → Y) (H : ℕ) (ε : ℝ)
    (s : Finset X) (hs : IsDynCoverOf F univ (observationEntourage o ε) (H + 1) s) :
    HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε ((H + 1) * s.card) := by
  classical
  have hsne : s.Nonempty := by
    simpa only [Finset.coe_nonempty] using hs.nonempty (Set.univ_nonempty : (univ : Set X).Nonempty)
  letI : Nonempty s := hsne.coe_sort
  let label : Fin s.card ≃ s := (Finset.equivFin s).symm
  have pick (x : X) : ∃ i : Fin s.card, ∀ k ≤ H,
      dist (o ((F^[k]) x)) (o ((F^[k]) (label i))) ≤ ε := by
    obtain ⟨y, hy, hxy⟩ := (cover_iff F o H ε s).1 hs x
    exact ⟨label.symm ⟨y, hy⟩, by simpa using hxy⟩
  let Q := Fin s.card × Fin (H + 1)
  let G : Unit → Q → Q := fun _ q =>
    (q.1, ⟨min (q.2.val + 1) H, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
  have run_label (w : List Unit) (q : Q) : (runWord G w q).1 = q.1 := by
    induction w generalizing q with
    | nil => rfl
    | cons a w ih => exact ih (G a q)
  have run_time (w : List Unit) (q : Q) (hw : q.2.val + w.length ≤ H) :
      (runWord G w q).2.val = q.2.val + w.length := by
    induction w generalizing q with
    | nil => simp only [runWord, List.length_nil, Nat.add_zero]
    | cons a w ih =>
        have hstep : q.2.val + 1 ≤ H := by simp only [List.length_cons] at hw; omega
        have hv : (G a q).2.val = q.2.val + 1 := Nat.min_eq_left hstep
        change (runWord G w (G a q)).2.val = _
        rw [ih (G a q) (by rw [hv]; simp only [List.length_cons] at hw; omega), hv]
        simp only [List.length_cons]; omega
  have hcard : Fintype.card Q ≤ (H + 1) * s.card := by simp [Q, Nat.mul_comm]
  haveI : Nonempty (Fin s.card) := ⟨⟨0, hsne.card_pos⟩⟩
  refine ⟨Q, inferInstance, inferInstance, hcard,
    (fun x => (Classical.choose (pick x), 0)), G,
    (fun q => o ((F^[q.2.val]) (label q.1))), ?_⟩
  intro x w hw
  have ht := run_time w (Classical.choose (pick x), 0) (by simpa using hw)
  have hl := run_label w (Classical.choose (pick x), 0)
  simp only [Fin.val_zero, Nat.zero_add] at ht
  dsimp only
  rw [ht, hl, autonomous_run]
  simpa only [dist_comm] using Classical.choose_spec (pick x) w.length hw

private theorem state_count_le (F : X → X) (o : X → Y) (H : ℕ) (ε : ℝ) (s : ℕ)
    (hs : HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε s) :
    autonomousStateCount F o H ε ≤ s := by
  classical
  unfold autonomousStateCount
  rw [dif_pos (show ∃ t, HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε t from ⟨s, hs⟩)]
  exact Nat.find_min' _ hs

section Compact
variable [MetricSpace X] [CompactSpace X] [Nonempty X]
variable (F : X → X) (o : X → Y) (hF : Continuous F) (ho : Continuous o)

include ho in
private theorem observation_entourage_mem (ε : ℝ) (hε : 0 < ε) :
    observationEntourage o ε ∈ 𝓤 X :=
  uniformContinuous_def.1 (CompactSpace.uniformContinuous_of_continuous ho) _ (Metric.uniformity_basis_dist_le.mem_of_mem hε)

include hF ho in
private theorem cover_finite (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    coverMincard F univ (observationEntourage o ε) (H + 1) < ⊤ :=
  coverMincard_finite_of_isCompact_uniformContinuous isCompact_univ (CompactSpace.uniformContinuous_of_continuous hF)
    (observation_entourage_mem o ho ε hε) (H + 1)

include hF ho in
private theorem cover_count_cast (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (responseCoverCount F o H ε : ℕ∞) = coverMincard F univ (observationEntourage o ε) (H + 1) :=
  ENat.natCast_toNat (cover_finite F o hF ho H ε hε).ne

include hF ho in
private theorem minimal_cover (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset X, IsDynCoverOf F univ (observationEntourage o ε) (H + 1) s ∧
      s.card = responseCoverCount F o H ε := by
  obtain ⟨s, hs, hc⟩ := (coverMincard_finite_iff F univ (observationEntourage o ε) (H + 1)).1
    (cover_finite F o hF ho H ε hε)
  refine ⟨s, hs, ?_⟩
  exact_mod_cast hc.trans (cover_count_cast F o hF ho H ε hε).symm

include hF ho in
private theorem state_exists (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s, HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε s := by
  obtain ⟨s, hs, _⟩ := minimal_cover F o hF ho H ε hε
  exact ⟨_, predictor_from_cover F o H ε s hs⟩

include hF ho in
private theorem state_minimum (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsLeast {s | HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε s}
      (autonomousStateCount F o H ε) := by
  classical
  have he := state_exists F o hF ho H ε hε
  constructor
  · change HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε _
    simpa only [autonomousStateCount, dif_pos he] using Nat.find_spec he
  · intro s hs; exact state_count_le F o H ε s hs

include hF ho in
private theorem counts_positive (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < responseCoverCount F o H ε ∧ 0 < autonomousStateCount F o H ε := by
  have hc : (1 : ℕ∞) ≤ responseCoverCount F o H ε := by
    rw [cover_count_cast F o hF ho H ε hε]
    exact (one_le_coverMincard_iff F univ _ _).2 Set.univ_nonempty
  have hmin := (state_minimum F o hF ho H ε hε).1
  rcases hmin with ⟨S, finiteS, hn, hcard, _⟩
  letI := finiteS
  letI := hn
  constructor
  · have hc' : 1 ≤ responseCoverCount F o H ε := by exact_mod_cast hc
    omega
  · exact lt_of_lt_of_le Fintype.card_pos hcard

include hF ho in
private theorem cardinality_comparison (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    responseCoverCount F o H (2 * ε) ≤ autonomousStateCount F o H ε ∧
      autonomousStateCount F o H ε ≤ (H + 1) * responseCoverCount F o H ε := by
  constructor
  · have h := cover_from_predictor F o H ε _ (state_minimum F o hF ho H ε hε).1
    rw [← cover_count_cast F o hF ho H (2 * ε) (by positivity)] at h
    exact_mod_cast h
  · obtain ⟨s, hs, hc⟩ := minimal_cover F o hF ho H ε hε
    simpa only [hc] using state_count_le F o H ε _ (predictor_from_cover F o H ε s hs)

include hF ho in
private theorem response_minimum (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsLeast {n : ℕ | ∃ s : Finset (Fin (H + 1) → Y),
      (↑s : Set _) ⊆ Set.range (futureReadoutWord F o H) ∧
      (∀ x, ∃ c ∈ s, dist (futureReadoutWord F o H x) c ≤ ε) ∧ s.card = n}
      (responseCoverCount F o H ε) := by
  classical
  have word_close (x y : X) :
      dist (futureReadoutWord F o H x) (futureReadoutWord F o H y) ≤ ε ↔
        ∀ k ≤ H, dist (o ((F^[k]) x)) (o ((F^[k]) y)) ≤ ε := by
    rw [dist_pi_le_iff hε.le]
    constructor
    · intro h k hk; exact h ⟨k, Nat.lt_succ_of_le hk⟩
    · intro h k; exact h k.val (Nat.le_of_lt_succ k.isLt)
  have pull (s : Finset (Fin (H + 1) → Y))
      (hs : (↑s : Set _) ⊆ Set.range (futureReadoutWord F o H))
      (hc : ∀ x, ∃ c ∈ s, dist (futureReadoutWord F o H x) c ≤ ε) :
      responseCoverCount F o H ε ≤ s.card := by
    have rep (c : s) : ∃ x, futureReadoutWord F o H x = c := hs c.property
    let lift : s → X := fun c => Classical.choose (rep c)
    let t := Finset.univ.image lift
    have ht : IsDynCoverOf F univ (observationEntourage o ε) (H + 1) t := by
      apply (cover_iff F o H ε t).2
      intro x; obtain ⟨c, hcs, hxc⟩ := hc x
      refine ⟨lift ⟨c, hcs⟩, Finset.mem_image.mpr ⟨⟨c, hcs⟩, Finset.mem_univ _, rfl⟩, ?_⟩
      apply (word_close x _).1
      simpa only [lift, Classical.choose_spec (rep ⟨c, hcs⟩)] using hxc
    have hb := ht.coverMincard_le_card
    rw [← cover_count_cast F o hF ho H ε hε] at hb
    have hb' : responseCoverCount F o H ε ≤ t.card := by exact_mod_cast hb
    exact hb'.trans (Finset.card_image_le.trans (by simp))
  constructor
  · obtain ⟨t, ht, hcard⟩ := minimal_cover F o hF ho H ε hε
    let s := t.image (futureReadoutWord F o H)
    have hs : (↑s : Set _) ⊆ Set.range (futureReadoutWord F o H) := by
      intro c hc; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc; exact ⟨x, rfl⟩
    have hc : ∀ x, ∃ c ∈ s, dist (futureReadoutWord F o H x) c ≤ ε := by
      intro x; obtain ⟨y, hy, hxy⟩ := (cover_iff F o H ε t).1 ht x
      exact ⟨_, Finset.mem_image.mpr ⟨y, hy, rfl⟩, (word_close x y).2 hxy⟩
    exact ⟨s, hs, hc, le_antisymm (Finset.card_image_le.trans_eq hcard) (pull s hs hc)⟩
  · rintro n ⟨s, hs, hc, rfl⟩; exact pull s hs hc

include hF ho in
private theorem actual_state_attainment (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Type) (finiteS : Fintype S), Nonempty S ∧
      @Fintype.card S finiteS = autonomousStateCount F o H ε ∧
      ∃ (e : X → S) (G : S → S) (h : S → Y),
        ∀ x t, t ≤ H → dist (h ((G^[t]) (e x))) (o ((F^[t]) x)) ≤ ε := by
  rcases (state_minimum F o hF ho H ε hε).1 with ⟨S, finiteS, hn, hcard, e, G, h, herr⟩
  letI := finiteS
  have hs : HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε (Fintype.card S) :=
    ⟨S, finiteS, hn, le_rfl, e, G, h, herr⟩
  refine ⟨S, finiteS, hn, le_antisymm hcard (state_count_le F o H ε _ hs), e, G (), h, ?_⟩
  intro x t ht
  have he := herr x (List.replicate t ()) (by simpa using ht)
  have hG : G = fun _ : Unit => G () := by funext u; cases u; rfl
  rw [hG] at he
  simpa only [autonomous_run, List.length_replicate] using he

include hF ho in
private theorem cover_radius_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (H : ℕ) :
    responseCoverCount F o H b ≤ responseCoverCount F o H a := by
  have h := coverMincard_antitone F univ (H + 1)
    (show observationEntourage o a ⊆ observationEntourage o b from fun _ hp => hp.trans hab)
  change coverMincard F univ (observationEntourage o b) (H + 1) ≤
    coverMincard F univ (observationEntourage o a) (H + 1) at h
  rw [← cover_count_cast F o hF ho H a ha,
    ← cover_count_cast F o hF ho H b (ha.trans_le hab)] at h
  exact_mod_cast h

include hF ho in
private theorem state_radius_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (H : ℕ) :
    autonomousStateCount F o H b ≤ autonomousStateCount F o H a := by
  rcases (state_minimum F o hF ho H a ha).1 with ⟨S, fS, hn, hc, e, G, h, he⟩
  apply state_count_le F o H b
  exact ⟨S, fS, hn, hc, e, G, h, fun x w hw => (he x w hw).trans hab⟩

private theorem natural_log_growth (a : ℕ → ℕ) (ha : ∀ H, 0 < a H) :
    expGrowthSup (fun H => (a H : ℝ≥0∞)) =
      limsup (fun H => ((Real.log (a H : ℝ) / H : ℝ) : EReal)) atTop := by
  apply limsup_congr
  exact Eventually.of_forall fun H => by
    change ENNReal.log (a H : ℝ≥0∞) / (H : EReal) = _
    rw [ENNReal.log_pos_real (by exact_mod_cast (ha H).ne') (by simp),
      ENNReal.toReal_natCast]
    simp only [EReal.coe_div, EReal.coe_natCast]

private theorem clock_growth : expGrowthSup (fun H => ((H + 1 : ℕ) : ℝ≥0∞)) = 0 := by
  unfold expGrowthSup
  have hr : Tendsto (fun H : ℕ => Real.log (H + 1 : ℝ) / (H + 1 : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun H : ℕ => (H + 1 : ℝ) / H) atTop (𝓝 1) := by
    have he : (fun H : ℕ => (H + 1 : ℝ) / H) =ᶠ[atTop] (fun H : ℕ => 1 + 1 / (H : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with H hH
      have hne : (H : ℝ) ≠ 0 := by exact_mod_cast (by omega : H ≠ 0)
      field_simp
    have hh : Tendsto (fun H : ℕ => 1 + 1 / (H : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using
        (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from
          tendsto_const_nhds).add tendsto_one_div_atTop_nhds_zero_nat
    exact hh.congr' he.symm
  have hv := (hr.mul ht)
  have hz : Tendsto (fun H : ℕ => ((Real.log (H + 1 : ℝ) / H : ℝ) : EReal)) atTop (𝓝 0) := by
    apply EReal.tendsto_coe.2
    simpa only [zero_mul] using hv.congr (fun H => by
      have hne : (H + 1 : ℝ) ≠ 0 := by positivity
      exact div_mul_div_cancel₀ hne)
  apply Tendsto.limsup_eq
  refine hz.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with H hH
  rw [ENNReal.log_pos_real (by positivity) (by simp), ENNReal.toReal_natCast]
  simp only [Nat.cast_add, Nat.cast_one, EReal.coe_div, EReal.coe_natCast]

include hF ho in
private theorem growth_comparison (ε : ℝ) (hε : 0 < ε) :
    expGrowthSup (fun H => (responseCoverCount F o H (2 * ε) : ℝ≥0∞)) ≤
      expGrowthSup (fun H => (autonomousStateCount F o H ε : ℝ≥0∞)) ∧
    expGrowthSup (fun H => (autonomousStateCount F o H ε : ℝ≥0∞)) ≤
      expGrowthSup (fun H => (responseCoverCount F o H ε : ℝ≥0∞)) := by
  constructor
  · apply expGrowthSup_monotone; intro H
    change (responseCoverCount F o H (2 * ε) : ℝ≥0∞) ≤
      (autonomousStateCount F o H ε : ℝ≥0∞)
    exact_mod_cast (cardinality_comparison F o hF ho H ε hε).1
  · have hb : (fun H => (autonomousStateCount F o H ε : ℝ≥0∞)) ≤
        (fun H => ((H + 1 : ℕ) : ℝ≥0∞)) * (fun H => (responseCoverCount F o H ε : ℝ≥0∞)) := by
      intro H; simpa only [Pi.mul_apply, Nat.cast_mul] using
        (show (autonomousStateCount F o H ε : ℝ≥0∞) ≤ ((H + 1) * responseCoverCount F o H ε : ℕ) from
          by exact_mod_cast (cardinality_comparison F o hF ho H ε hε).2)
    refine (expGrowthSup_monotone hb).trans ?_
    have h := expGrowthSup_mul_le (u := fun H => ((H + 1 : ℕ) : ℝ≥0∞))
      (v := fun H => (responseCoverCount F o H ε : ℝ≥0∞))
      (Or.inl (by rw [clock_growth]; exact EReal.zero_ne_bot))
      (Or.inl (by rw [clock_growth]; exact EReal.zero_ne_top))
    simpa only [clock_growth, zero_add] using h

private theorem radius_limit (f : ℝ → EReal)
    (hf : ∀ a b, 0 < a → a ≤ b → f b ≤ f a) :
    Tendsto f (𝓝[>] 0) (𝓝 (⨆ ε > 0, f ε)) := by
  have hf' : AntitoneOn f (Ioi 0) := fun a ha b _ hab => hf a b ha hab
  have ht := hf'.tendsto_nhdsGT (OrderTop.bddAbove (f '' Ioi 0))
  have he : sSup (f '' Ioi 0) = ⨆ ε > 0, f ε := by
    apply le_antisymm
    · apply sSup_le
      rintro z ⟨ε, hε, rfl⟩
      exact le_iSup_of_le ε (le_iSup_of_le hε le_rfl)
    · apply iSup₂_le
      intro ε hε
      exact le_sSup ⟨ε, hε, rfl⟩
  simpa only [he] using ht

include hF ho in
private theorem entropy_limits :
    Tendsto (fun ε => expGrowthSup (fun H => (responseCoverCount F o H ε : ℝ≥0∞)))
      (𝓝[>] 0) (𝓝 (observationEntropy F o)) ∧
    Tendsto (fun ε => expGrowthSup (fun H => (autonomousStateCount F o H ε : ℝ≥0∞)))
      (𝓝[>] 0) (𝓝 (observationEntropy F o)) := by
  have hc : ∀ a b, 0 < a → a ≤ b →
      expGrowthSup (fun H => (responseCoverCount F o H b : ℝ≥0∞)) ≤
      expGrowthSup (fun H => (responseCoverCount F o H a : ℝ≥0∞)) := by
    intro a b ha hab; apply expGrowthSup_monotone; intro H
    change (responseCoverCount F o H b : ℝ≥0∞) ≤ (responseCoverCount F o H a : ℝ≥0∞)
    exact_mod_cast cover_radius_antitone F o hF ho ha hab H
  have hs : ∀ a b, 0 < a → a ≤ b →
      expGrowthSup (fun H => (autonomousStateCount F o H b : ℝ≥0∞)) ≤
      expGrowthSup (fun H => (autonomousStateCount F o H a : ℝ≥0∞)) := by
    intro a b ha hab; apply expGrowthSup_monotone; intro H
    change (autonomousStateCount F o H b : ℝ≥0∞) ≤ (autonomousStateCount F o H a : ℝ≥0∞)
    exact_mod_cast state_radius_antitone F o hF ho ha hab H
  have heq : (⨆ ε > 0, expGrowthSup (fun H => (autonomousStateCount F o H ε : ℝ≥0∞))) =
      observationEntropy F o := by
    unfold observationEntropy
    apply le_antisymm
    · apply iSup₂_le; intro ε hε
      exact (growth_comparison F o hF ho ε hε).2.trans (le_iSup_of_le ε (le_iSup_of_le hε le_rfl))
    · apply iSup₂_le; intro ε hε
      have h := (growth_comparison F o hF ho (ε / 2) (by positivity)).1
      have he : 2 * (ε / 2) = ε := by ring
      rw [he] at h
      exact h.trans (le_iSup_of_le (ε / 2) (le_iSup_of_le (show 0 < ε / 2 by positivity) le_rfl))
  exact ⟨radius_limit _ hc, heq ▸ radius_limit _ hs⟩

include hF ho in
private theorem horizon_shift (ε : ℝ) (hε : 0 < ε) :
    expGrowthSup (fun H => (responseCoverCount F o H ε : ℝ≥0∞)) =
      coverEntropyEntourage F univ (observationEntourage o ε) := by
  let u : ℕ → ℝ≥0∞ := fun n => coverMincard F univ (observationEntourage o ε) n
  have hu : Monotone u := fun a b hab => ENat.toENNReal_mono (coverMincard_monotone_time F univ _ hab)
  have ht : Tendsto (fun H : ℕ => ((H + 1 : ℕ) : EReal) / H) atTop (𝓝 1) := by
    have he : (fun H : ℕ => ((H + 1 : ℕ) : ℝ) / H) =ᶠ[atTop] (fun H : ℕ => 1 + 1 / (H : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with H hH
      have hne : (H : ℝ) ≠ 0 := by exact_mod_cast (by omega : H ≠ 0)
      push_cast
      field_simp
    have hr : Tendsto (fun H : ℕ => ((H + 1 : ℕ) : ℝ) / H) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).congr' he.symm
    simpa only [EReal.coe_div, EReal.coe_natCast, EReal.coe_one] using (EReal.tendsto_coe.2 hr)
  have hs := hu.expGrowthSup_comp ht one_ne_zero
    (by simpa only [EReal.coe_one] using EReal.coe_ne_top (1 : ℝ))
  have hc : (fun H => (responseCoverCount F o H ε : ℝ≥0∞)) = u ∘ (fun H => H + 1) := by
    funext H
    change ((responseCoverCount F o H ε : ℕ∞) : ℝ≥0∞) = _
    rw [cover_count_cast F o hF ho H ε hε]
    rfl
  rw [hc, hs, one_mul]
  rfl

include hF ho in
private theorem embedding_entropy (he : Topology.IsEmbedding o) :
    let m : MetricSpace X := he.comapMetricSpace o
    (∀ x y, @dist X m.toDist x y = dist (o x) (o y)) ∧
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X) ∧
      observationEntropy F o = @coverEntropy X m.toPseudoMetricSpace.toUniformSpace F univ := by
  dsimp only
  let m : MetricSpace X := he.comapMetricSpace o
  refine ⟨fun _ _ => rfl, rfl, ?_⟩
  have hb := @Metric.uniformity_basis_dist_le X m.toPseudoMetricSpace
  have h := @coverEntropy_eq_iSup_basis X m.toPseudoMetricSpace.toUniformSpace ℝ (fun ε => 0 < ε)
    (fun ε => observationEntourage o ε) hb F univ
  rw [h]
  unfold observationEntropy
  apply iSup_congr
  intro ε
  apply iSup_congr
  intro hε
  exact horizon_shift F o hF ho ε hε

include hF ho in
/-- On a nonempty compact metric space, continuous autonomous dynamics and an arbitrary continuous
metric observation have actual positive attained cover and machine minima. The exact clock-charged
cardinality bounds give the ordered extended-real entropy identity; an embedding supplies the
compatible pullback metric and its topological-entropy interpretation. -/
theorem autonomous_prediction_entropy :
    (∀ H ε, 0 < ε →
      0 < responseCoverCount F o H ε ∧ 0 < autonomousStateCount F o H ε ∧
      IsLeast {n : ℕ | ∃ s : Finset (Fin (H + 1) → Y),
        (↑s : Set _) ⊆ Set.range (futureReadoutWord F o H) ∧
        (∀ x, ∃ c ∈ s, dist (futureReadoutWord F o H x) c ≤ ε) ∧ s.card = n}
        (responseCoverCount F o H ε) ∧
      IsLeast {s | HasFiniteHorizonPredictor (fun _ : Unit => F) o H ε s}
        (autonomousStateCount F o H ε) ∧
      (∃ (S : Type) (finiteS : Fintype S), Nonempty S ∧
        @Fintype.card S finiteS = autonomousStateCount F o H ε ∧
        ∃ (e : X → S) (G : S → S) (h : S → Y),
          ∀ x t, t ≤ H → dist (h ((G^[t]) (e x))) (o ((F^[t]) x)) ≤ ε) ∧
      responseCoverCount F o H (2 * ε) ≤ autonomousStateCount F o H ε ∧
        autonomousStateCount F o H ε ≤ (H + 1) * responseCoverCount F o H ε) ∧
    Tendsto (fun ε => limsup (fun H =>
      ((Real.log (responseCoverCount F o H ε : ℝ) / H : ℝ) : EReal)) atTop)
      (𝓝[>] 0) (𝓝 (observationEntropy F o)) ∧
    Tendsto (fun ε => limsup (fun H =>
      ((Real.log (autonomousStateCount F o H ε : ℝ) / H : ℝ) : EReal)) atTop)
      (𝓝[>] 0) (𝓝 (observationEntropy F o)) ∧
    (∀ he : Topology.IsEmbedding o,
      let m : MetricSpace X := Topology.IsEmbedding.comapMetricSpace o he
      (∀ x y, @dist X m.toDist x y = dist (o x) (o y)) ∧
        m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X) ∧
        observationEntropy F o = @coverEntropy X m.toPseudoMetricSpace.toUniformSpace F univ) := by
  have hc := (entropy_limits F o hF ho).1
  have hs := (entropy_limits F o hF ho).2
  have hc' : Tendsto (fun ε => limsup (fun H =>
      ((Real.log (responseCoverCount F o H ε : ℝ) / H : ℝ) : EReal)) atTop)
      (𝓝[>] 0) (𝓝 (observationEntropy F o)) := by
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact natural_log_growth _ (fun H => (counts_positive F o hF ho H ε hε).1)
  have hs' : Tendsto (fun ε => limsup (fun H =>
      ((Real.log (autonomousStateCount F o H ε : ℝ) / H : ℝ) : EReal)) atTop)
      (𝓝[>] 0) (𝓝 (observationEntropy F o)) := by
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact natural_log_growth _ (fun H => (counts_positive F o hF ho H ε hε).2)
  refine ⟨?_, hc', hs', ?_⟩
  · intro H ε hε
    exact ⟨(counts_positive F o hF ho H ε hε).1,
      (counts_positive F o hF ho H ε hε).2,
      response_minimum F o hF ho H ε hε,
      state_minimum F o hF ho H ε hε,
      actual_state_attainment F o hF ho H ε hε,
      (cardinality_comparison F o hF ho H ε hε).1,
      (cardinality_comparison F o hF ho H ε hε).2⟩
  · intro he; exact embedding_entropy F o hF ho he

#print axioms autonomous_prediction_entropy

end Compact
end D5.S3.Observer.MetricGeometry.AutonomousPredictionEntropy

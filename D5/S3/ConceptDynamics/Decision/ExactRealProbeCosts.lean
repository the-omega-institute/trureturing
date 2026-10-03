/- GID: D5/S3/ConceptDynamics/Decision/ExactRealProbeCosts
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Decision/ExactRealProbeCosts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact probes separate certificates from discovery costs. -/

import D5.S3.ConceptDynamics.Experiment.AdaptiveReadOnlyExecution
import D5.S3.ConceptDynamics.EscapeSpectrum.UncountableSingletonCutCountermodel
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
The source is the exact real probe interface in definition and theorem 22.3 of
FIB_SCALE_READOUT_PERMISSION_GEOMETRY. Parameters retain their exact values.
Sources reuse the unit-interval Boolean state carrier of the singleton-cut
countermodel. Histories reuse the dependent passive history carrier, and controllers
instantiate the shared read-only execution core. Finite runs have no uniform depth
bound; repeated parameters are allowed and charged once. A stall has no finite
run witness, as does an infinite query execution. Neither source identity nor
its Boolean task label is available to the controller.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.ExactRealProbeCosts

open unitInterval
open MeasureTheory Filter
open scoped ENNReal
open D5.S3.ConceptDynamics.Experiment
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)
open D5.S3.ConceptDynamics.EscapeSpectrum.UncountableSingletonCutCountermodel (State)

noncomputable section

local notation "Source" => State
abbrev History := Hist (fun _ : I => Bool)
abbrev Controller := AdaptiveReadOnlyExecution.Controller (fun _ : I => Bool) Bool

/-- A probe flips the task bit exactly at the source coordinate. -/
def response (a : I) (s : Source) : Bool :=
  if a = s.1 then !s.2 else s.2

/-- Every recorded response is the actual response of the specified source. -/
abbrev Consistent (h : History) (s : Source) : Prop :=
  AdaptiveReadOnlyExecution.Consistent response h s

/-- The complete compatibility fiber forces the returned task bit. -/
def Sound (h : History) (b : Bool) : Prop :=
  ∀ s, Consistent h s → s.2 = b

/-- The finite set of different exact query parameters in a history. -/
abbrev parameters (h : History) : Finset I := by
  classical
  exact AdaptiveReadOnlyExecution.queries h

/-- Repeated queries contribute no extra charge. -/
abbrev queryCount (h : History) : Nat := by
  classical
  exact AdaptiveReadOnlyExecution.queryCount h

/-- Finite execution from a given prefix, retaining its additional ordered record.
There is no constructor for a stall and no depth bound on finite executions. -/
abbrev Run (π : Controller) (s : Source) : History → History → Bool → Prop :=
  AdaptiveReadOnlyExecution.Run response π s

/-- Total correctness on the whole source domain. -/
abbrev Correct (π : Controller) : Prop :=
  AdaptiveReadOnlyExecution.Correct response (fun s : Source => s.2) π

/-- Extended execution cost. The infimum is over finite run witnesses; it is
infinite when none exists. Determinism makes all finite witnesses identical. -/
abbrev cost (π : Controller) (s : Source) : ENNReal := by
  classical
  exact AdaptiveReadOnlyExecution.cost response π s

/-- Two initial parameters, followed by a third only when the responses differ. -/
def threeProbe (a c d : I) : Controller := fun h =>
  match h with
  | [] => some (.inl a)
  | [_] => some (.inl c)
  | [p, q] => if p.2 = q.2 then some (.inr p.2) else some (.inl d)
  | _ :: _ :: p :: _ => some (.inr p.2)

/-- A Borel action carrier distinguishes query, return, and stall. -/
abbrev CodedAction := (I ⊕ Bool) ⊕ Unit

/-- An equivalent action coding with the standard sum measurable structure. -/
def actionCode : Option (Sum I Bool) → CodedAction
  | none => .inr ()
  | some a => .inl a

/-- On every finite record length, the seed-record control map is Borel.
The tuple representation gives the disjoint union of finite product spaces. -/
def ControlsMeasurably {Ω : Type} [MeasurableSpace Ω] (π : Ω → Controller) : Prop :=
  ∀ n : Nat, Measurable (fun z : Ω × (Fin n → I × Bool) =>
    actionCode (π z.1 (List.ofFn (fun i => ⟨(z.2 i).1, (z.2 i).2⟩))))

/-- Worst cost, then infimum over measurable globally correct controllers. -/
def deterministicValue : ENNReal :=
  ⨅ π : Controller, ⨅ (_ : Correct π),
    ⨅ (_ : ControlsMeasurably (fun _ : Unit => π)), ⨆ s : Source, cost π s

/-- Sourcewise measurability required by both random contracts. -/
def MeasurableStrategy {Ω : Type} [MeasurableSpace Ω] (π : Ω → Controller) : Prop :=
  ControlsMeasurably π ∧
  (∀ s, Measurable (fun ω => cost (π ω) s)) ∧
  (∀ s, MeasurableSet {ω | ∃ h b, Run (π ω) s [] h b}) ∧
  (∀ s, MeasurableSet {ω | ∃ h b, Run (π ω) s [] h b ∧ b ≠ s.2})

/-- Each strategy uses its own input-independent probability law. -/
def randomizedValueOn (Ω : Type) [MeasurableSpace Ω] (strong : Bool) : ENNReal :=
  ⨅ μ : Measure Ω, ⨅ (_ : IsProbabilityMeasure μ),
    ⨅ π : Ω → Controller, ⨅ (_ : MeasurableStrategy π),
      ⨅ (_ : if strong then ∀ ω, Correct (π ω)
        else ∀ s, ∀ᵐ ω ∂μ, ∃ h, Run (π ω) s [] h s.2),
        ⨆ s : Source, ∫⁻ ω, cost (π ω) s ∂μ

/-- Infimum over all seed spaces and their measurable structures and laws. -/
def randomizedValue (strong : Bool) : ENNReal :=
  ⨅ Ω : Type, ⨅ m : MeasurableSpace Ω, @randomizedValueOn Ω m strong

/-- The midpoint is a legal exact query parameter. -/
def midpoint : I := ⟨1 / 2, by constructor <;> norm_num⟩

/-- Uniform single-query controller: every source terminates after one query. -/
def oneProbe (u : I) : Controller := fun h =>
  match h with
  | [] => some (.inl u)
  | p :: _ => some (.inr p.2)

/-- Half-open unit-interval seeds include every declared seed below one. -/
abbrev StrongSeed := Set.Iio (1 : I)

/-- Half-period pairing, including both half-interval endpoints. -/
def shift (u : StrongSeed) : StrongSeed :=
  if h : (u.1 : ℝ) < 1 / 2 then
    ⟨⟨(u.1 : ℝ) + 1 / 2, by constructor <;> linarith [u.1.2.1]⟩,
      by change (u.1 : ℝ) + 1 / 2 < 1; linarith⟩
  else
    ⟨⟨(u.1 : ℝ) - 1 / 2, by constructor <;> linarith [u.1.2.2]⟩,
      by change (u.1 : ℝ) - 1 / 2 < 1; linarith [u.1.2.2]⟩

noncomputable instance : MeasureSpace StrongSeed := Measure.Subtype.measureSpace

/-- Every source has a sound certificate of exactly two different parameters;
no compatible sound history can use fewer parameters. -/
theorem result :
    (∀ s : Source,
      (∀ h, Consistent h s → Sound h s.2 → 2 ≤ queryCount h) ∧
      ∃ h, Consistent h s ∧ Sound h s.2 ∧ queryCount h = 2) ∧
    (∀ π : Controller, Correct π →
      ∃ s h, Run π s [] h s.2 ∧ 3 ≤ queryCount h) ∧
    Correct (threeProbe 0 midpoint 1) ∧
    (∀ s, ∃ h, Run (threeProbe 0 midpoint 1) s [] h s.2 ∧ queryCount h ≤ 3) ∧
    deterministicValue = 3 ∧
    (⨆ s : Source, cost (threeProbe 0 midpoint 1) s) = 3 ∧
    (∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ π : Ω → Controller,
      (∀ s, ∀ᵐ ω ∂μ, ∃ h, Run (π ω) s [] h s.2) →
      ∀ s, (1 : ENNReal) ≤ ∫⁻ ω, cost (π ω) s ∂μ) ∧
    (∀ s, (∀ᵐ u : I, ∃ h, Run (oneProbe u) s [] h s.2) ∧
      (∫⁻ u : I, cost (oneProbe u) s) = 1) ∧
    (∀ u : StrongSeed, Correct (threeProbe u.1 (shift u).1 1)) ∧
    (∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ π : Ω → Controller, (∀ ω, Correct (π ω)) →
      ∀ s, (2 : ENNReal) ≤ ∫⁻ ω, cost (π ω) s ∂μ) ∧
    IsProbabilityMeasure (volume : Measure StrongSeed) ∧
    (∀ s, (∫⁻ u : StrongSeed, cost (threeProbe u.1 (shift u).1 1) s) = 2) ∧
    MeasurableStrategy oneProbe ∧
    MeasurableStrategy (fun u : StrongSeed => threeProbe u.1 (shift u).1 1) ∧
    randomizedValue false = 1 ∧ randomizedValue true = 2 ∧
    (∀ s, {u : I | ∃ h b, Run (oneProbe u) s [] h b ∧ b ≠ s.2} = {s.1}) ∧
    (∀ u : I, ¬ Correct (oneProbe u)) ∧
    (∀ u : StrongSeed, (⨆ s : Source, cost (threeProbe u.1 (shift u).1 1) s) = 3) ∧
    ControlsMeasurably (fun _ : Unit => threeProbe 0 midpoint 1) ∧
    Measurable (fun z : I × Source => response z.1 z.2) := by
  classical
  have mem_parameters (h : History) (p : Sigma (fun _ : I => Bool)) (hp : p ∈ h) :
      p.1 ∈ parameters h := by
    simp only [parameters, AdaptiveReadOnlyExecution.queries, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, rfl⟩
  have zero_ne_one : (0 : I) ≠ 1 := by
    intro he
    have := congrArg (fun a : I => (a : ℝ)) he
    norm_num at this
  have middle_ne_zero : midpoint ≠ (0 : I) := by
    intro he
    have := congrArg (fun a : I => (a : ℝ)) he
    norm_num [midpoint] at this
  have middle_ne_one : midpoint ≠ (1 : I) := by
    intro he
    have := congrArg (fun a : I => (a : ℝ)) he
    norm_num [midpoint] at this
  have singleton_obstruction (h : History) (s : Source) (hc : Consistent h s)
      (hs : Sound h s.2) : 2 ≤ queryCount h := by
    by_contra hn
    have hcard : (parameters h).card ≤ 1 := by change ¬ 2 ≤ (parameters h).card at hn; omega
    obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
    let r := response a s
    let z : I := if a = 0 then 1 else 0
    have hza : z ≠ a := by
      dsimp [z]
      split_ifs with hzero
      · subst a; exact zero_ne_one.symm
      · exact Ne.symm hzero
    have compat_flip : Consistent h (a, !r) := by
      intro p hp
      have hpa : p.1 = a := Finset.mem_singleton.mp (ha (mem_parameters h p hp))
      have hpr := hc p hp
      rw [hpa] at hpr ⊢
      simpa [response, r] using hpr
    have compat_plain : Consistent h (z, r) := by
      intro p hp
      have hpa : p.1 = a := Finset.mem_singleton.mp (ha (mem_parameters h p hp))
      have hpr := hc p hp
      rw [hpa] at hpr ⊢
      simpa [response, hza.symm, r] using hpr
    have hflip := hs (a, !r) compat_flip
    have hplain := hs (z, r) compat_plain
    have absurd : (!r) = r := hflip.trans hplain.symm
    cases r <;> simp at absurd
  have pair_certificate (s : Source) (a c : I) (hac : a ≠ c)
      (hax : a ≠ s.1) (hcx : c ≠ s.1) :
      ∃ h, Consistent h s ∧ Sound h s.2 ∧ queryCount h = 2 := by
    refine ⟨[⟨a, s.2⟩, ⟨c, s.2⟩], ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [response, hax, hcx]
    · intro t ht
      have hta := ht ⟨a, s.2⟩ (by simp)
      have htc := ht ⟨c, s.2⟩ (by simp)
      by_cases hat : a = t.1
      · have hct : c ≠ t.1 := by intro he; exact hac (hat.trans he.symm)
        simpa [response, hct] using htc
      · simpa [response, hat] using hta
    · simp [queryCount, AdaptiveReadOnlyExecution.queryCount,
        AdaptiveReadOnlyExecution.queries, hac]
  have certificates : ∀ s : Source,
      (∀ h, Consistent h s → Sound h s.2 → 2 ≤ queryCount h) ∧
      ∃ h, Consistent h s ∧ Sound h s.2 ∧ queryCount h = 2 := by
    intro s
    refine ⟨fun h hc hs => singleton_obstruction h s hc hs, ?_⟩
    by_cases hx0 : s.1 = 0
    · exact pair_certificate s midpoint 1 middle_ne_one
        (by simpa [hx0] using middle_ne_zero) (by simpa [hx0] using zero_ne_one.symm)
    by_cases hx1 : s.1 = 1
    · exact pair_certificate s 0 midpoint middle_ne_zero.symm
        (by simpa [hx1] using zero_ne_one) (by simpa [hx1] using middle_ne_one)
    · exact pair_certificate s 0 1 zero_ne_one (Ne.symm hx0) (Ne.symm hx1)
  have run_unique (π : Controller) (s : Source) (pre t₁ t₂ : History)
      (b₁ b₂ : Bool) (h₁ : Run π s pre t₁ b₁) (h₂ : Run π s pre t₂ b₂) :
      t₁ = t₂ ∧ b₁ = b₂ := by
    induction h₁ generalizing t₂ b₂ with
    | stop pre b hd =>
      cases h₂ with
      | stop _ b' hd' =>
        have hb : b = b₂ := by simpa [hd] using hd'
        exact ⟨rfl, hb⟩
      | query _ a' t' b' hd' next' => simp [hd] at hd'
    | query pre a t b hd next ih =>
      cases h₂ with
      | stop _ b' hd' => simp [hd] at hd'
      | query _ a' t' b' hd' next' =>
        have haa : a = a' := by simpa [hd] using hd'
        subst a'
        obtain ⟨ht, hb⟩ := ih t' b₂ next'
        exact ⟨congrArg (List.cons ⟨a, response a s⟩) ht, hb⟩
  have run_consistent (π : Controller) (s : Source) (pre t : History) (b : Bool)
      (hr : Run π s pre t b) : Consistent t s := by
    induction hr with
    | stop => simp [Consistent, AdaptiveReadOnlyExecution.Consistent]
    | query pre a t b hd next ih =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact ih p hp
  have replay (π : Controller) (s s' : Source) (pre t : History) (b : Bool)
      (hr : Run π s pre t b) (hc : Consistent t s') : Run π s' pre t b := by
    induction hr with
    | stop pre b hd => exact AdaptiveReadOnlyExecution.Run.stop (read := response) pre b hd
    | query pre a t b hd next ih =>
      have he : response a s' = response a s := hc ⟨a, response a s⟩ (by simp)
      have ht : Consistent t s' := fun p hp => hc p (by simp [hp])
      have hn := ih ht
      rw [← he] at hn ⊢
      exact AdaptiveReadOnlyExecution.Run.query (read := response) pre a t b hd hn
  have terminal_sound (π : Controller) (correct : Correct π) (s : Source)
      (t : History) (b : Bool) (hr : Run π s [] t b) : Sound t b := by
    intro s' hc
    obtain ⟨t', hr'⟩ := correct s'
    exact (run_unique π s' [] t t' b s'.2 (replay π s s' [] t b hr hc) hr').2.symm
  have deterministic_lower (π : Controller) (correct : Correct π) :
      ∃ s h, Run π s [] h s.2 ∧ 3 ≤ queryCount h := by
    obtain ⟨t₀, hr₀⟩ := correct (0, false)
    cases hr₀ with
    | stop _ _ hd =>
      obtain ⟨t', hr'⟩ := correct (0, true)
      have bad := (run_unique π (0, true) [] [] t' false true
        (AdaptiveReadOnlyExecution.Run.stop (read := response) [] false hd) hr').2
      cases bad
    | query _ a t₀ _ hd next =>
      obtain ⟨t, hr⟩ := correct (a, true)
      have hc := run_consistent π (a, true) [] t true hr
      have hs := terminal_sound π correct (a, true) t true hr
      refine ⟨(a, true), t, hr, ?_⟩
      have ha : a ∈ parameters t := by
        cases hr with
        | stop _ _ hd' => simp [hd] at hd'
        | query _ a' t' _ hd' next' =>
          have haa : a' = a := by simpa [hd] using hd'.symm
          subst a'
          exact mem_parameters _ ⟨a, response a (a, true)⟩ (by simp)
      have htwo := singleton_obstruction t (a, true) hc hs
      by_contra hn
      have hsmall : (parameters t).card ≤ 2 := by change ¬ 3 ≤ (parameters t).card at hn; omega
      have hbig : 1 < (parameters t).card := by change 2 ≤ (parameters t).card at htwo; omega
      obtain ⟨c, hcS, hca⟩ := Finset.exists_mem_ne hbig a
      have hac : a ≠ c := Ne.symm hca
      have hpairs : ({a, c} : Finset I).card = 2 := by simp [hac]
      have hsubset : ({a, c} : Finset I) ⊆ parameters t := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> assumption
      have heq : ({a, c} : Finset I) = parameters t :=
        Finset.eq_of_subset_of_card_le hsubset (by omega)
      have hc' : Consistent t (c, false) := by
        intro p hp
        have hpa := mem_parameters t p hp
        rw [← heq] at hpa
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpa
        have hpr := hc p hp
        rcases hpa with he | he
        · simpa [response, he, hac] using hpr
        · simpa [response, he, hca] using hpr
      have bad := hs (c, false) hc'
      cases bad
  have cost_of_run (π : Controller) (s : Source) (h : History) (b : Bool)
      (hr : Run π s [] h b) : cost π s = (queryCount h : ENNReal) := by
    apply le_antisymm
    · exact iInf_le_of_le h (iInf_le_of_le b (iInf_le_of_le hr le_rfl))
    · refine le_iInf fun t => le_iInf fun r => le_iInf fun ht => ?_
      rw [(run_unique π s [] h t b r hr ht).1]
  have three_upper (s : Source) (a c d : I) (hac : a ≠ c)
      (had : a ≠ d) (hcd : c ≠ d) :
      ∃ h, Run (threeProbe a c d) s [] h s.2 ∧
        queryCount h = if a = s.1 ∨ c = s.1 then 3 else 2 := by
    let r := response a s
    let v := response c s
    by_cases he : r = v
    · have hbit : r = s.2 := by
        by_cases hax : a = s.1
        · have hcx : c ≠ s.1 := by intro hx; exact hac (hax.trans hx.symm)
          simpa [v, response, hcx] using he
        · simp [r, response, hax]
      refine ⟨[⟨a, r⟩, ⟨c, v⟩], ?_, ?_⟩
      · apply AdaptiveReadOnlyExecution.Run.query (read := response) [] a [⟨c, v⟩] s.2 rfl
        apply AdaptiveReadOnlyExecution.Run.query (read := response) [⟨a, r⟩] c [] s.2 rfl
        apply AdaptiveReadOnlyExecution.Run.stop (read := response)
        change ((if r = v then some (Sum.inr r) else some (Sum.inl d)) :
          Option (Sum I Bool)) = some (Sum.inr s.2)
        rw [if_pos he, hbit]
      · have hax : a ≠ s.1 := by
          intro hax
          have hcx : c ≠ s.1 := fun hcx => hac (hax.trans hcx.symm)
          have bad : (!s.2) = s.2 := by simpa [r, v, response, hax, hcx] using he
          cases s.2 <;> simp at bad
        have hcx : c ≠ s.1 := by
          intro hcx
          have bad : s.2 = (!s.2) := by simpa [r, v, response, hax, hcx] using he
          cases s.2 <;> simp at bad
        simp [queryCount, AdaptiveReadOnlyExecution.queryCount,
          AdaptiveReadOnlyExecution.queries, hac, hax, hcx]
    · have hdx : d ≠ s.1 := by
        intro hdx
        have hax : a ≠ s.1 := fun hax => had (hax.trans hdx.symm)
        have hcx : c ≠ s.1 := fun hcx => hcd (hcx.trans hdx.symm)
        exact he (by simp [r, v, response, hax, hcx])
      have hbit : response d s = s.2 := by simp [response, hdx]
      refine ⟨[⟨a, r⟩, ⟨c, v⟩, ⟨d, response d s⟩], ?_, ?_⟩
      · apply AdaptiveReadOnlyExecution.Run.query (read := response)
          [] a [⟨c, v⟩, ⟨d, response d s⟩] s.2 rfl
        apply AdaptiveReadOnlyExecution.Run.query (read := response)
          [⟨a, r⟩] c [⟨d, response d s⟩] s.2 rfl
        apply AdaptiveReadOnlyExecution.Run.query (read := response) [⟨a, r⟩, ⟨c, v⟩] d [] s.2
        · change ((if r = v then some (Sum.inr r) else some (Sum.inl d)) :
            Option (Sum I Bool)) = some (Sum.inl d)
          simp [he]
        · apply AdaptiveReadOnlyExecution.Run.stop (read := response)
          change (some (Sum.inr (response d s)) : Option (Sum I Bool)) = some (Sum.inr s.2)
          rw [hbit]
      · have hx : a = s.1 ∨ c = s.1 := by
          by_contra hx
          push_neg at hx
          exact he (by simp [r, v, response, hx.1, hx.2])
        simp [queryCount, AdaptiveReadOnlyExecution.queryCount,
          AdaptiveReadOnlyExecution.queries, hac, had, hcd, hx]
  have upper (s : Source) :
      ∃ h, Run (threeProbe 0 midpoint 1) s [] h s.2 ∧ queryCount h ≤ 3 := by
    obtain ⟨h, hr, hc⟩ := three_upper s 0 midpoint 1
      middle_ne_zero.symm zero_ne_one middle_ne_one
    refine ⟨h, hr, ?_⟩
    rw [hc]
    split_ifs <;> omega
  have worst_lower (π : Controller) (hπ : Correct π) :
      (3 : ENNReal) ≤ ⨆ s : Source, cost π s := by
    obtain ⟨s, h, hr, hc⟩ := deterministic_lower π hπ
    apply le_trans _ (le_iSup (fun s : Source => cost π s) s)
    rw [cost_of_run π s h s.2 hr]
    exact_mod_cast hc
  have worst_upper : (⨆ s : Source, cost (threeProbe 0 midpoint 1) s) ≤ 3 := by
    refine iSup_le fun s => ?_
    obtain ⟨h, hr, hc⟩ := upper s
    rw [cost_of_run _ s h s.2 hr]
    exact_mod_cast hc
  have correct_upper : Correct (threeProbe 0 midpoint 1) :=
    fun s => (upper s).imp fun _ h => h.1
  have weak_lower (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω)
      (hμ : IsProbabilityMeasure μ) (π : Ω → Controller)
      (hπ : ∀ s, ∀ᵐ ω ∂μ, ∃ h, Run (π ω) s [] h s.2) (s : Source) :
      (1 : ENNReal) ≤ ∫⁻ ω, cost (π ω) s ∂μ := by
    letI := hμ
    have hcost : ∀ᵐ ω ∂μ, (1 : ENNReal) ≤ cost (π ω) s := by
      filter_upwards [hπ s, hπ (0, false), hπ (0, true)] with ω hs hf ht
      obtain ⟨h, hr⟩ := hs
      rw [cost_of_run (π ω) s h s.2 hr]
      have hcount : 1 ≤ queryCount h := by
        by_contra hn
        have hempty : parameters h = ∅ := Finset.card_eq_zero.mp (by
          change ¬ 1 ≤ (parameters h).card at hn; omega)
        have hnil : h = [] := List.eq_nil_iff_forall_not_mem.mpr (by
          intro p hp
          have hm := mem_parameters h p hp
          rw [hempty] at hm
          simpa using hm)
        subst h
        cases hr with
        | stop _ _ hd =>
          obtain ⟨tf, hrf⟩ := hf
          obtain ⟨tt, hrt⟩ := ht
          have hbf := (run_unique (π ω) (0, false) [] [] tf s.2 false
            (AdaptiveReadOnlyExecution.Run.stop (read := response) [] s.2 hd) hrf).2
          have hbt := (run_unique (π ω) (0, true) [] [] tt s.2 true
            (AdaptiveReadOnlyExecution.Run.stop (read := response) [] s.2 hd) hrt).2
          have bad : false = true := hbf.symm.trans hbt
          cases bad
      exact_mod_cast hcount
    simpa using lintegral_mono_ae hcost
  have one_run (u : I) (s : Source) :
      Run (oneProbe u) s [] [⟨u, response u s⟩] (response u s) := by
    apply AdaptiveReadOnlyExecution.Run.query (read := response) [] u [] (response u s) rfl
    exact AdaptiveReadOnlyExecution.Run.stop (read := response) _ _ rfl
  have one_cost (u : I) (s : Source) : cost (oneProbe u) s = 1 := by
    rw [cost_of_run _ _ _ _ (one_run u s)]
    simp [queryCount, AdaptiveReadOnlyExecution.queryCount, AdaptiveReadOnlyExecution.queries]
  have weak_upper (s : Source) :
      (∀ᵐ u : I, ∃ h, Run (oneProbe u) s [] h s.2) ∧
      (∫⁻ u : I, cost (oneProbe u) s) = 1 := by
    constructor
    · filter_upwards [Measure.ae_ne (volume : Measure I) s.1] with u hu
      refine ⟨[⟨u, response u s⟩], ?_⟩
      have hb : response u s = s.2 := by simp [response, hu]
      simpa only [hb] using one_run u s
    · simp_rw [one_cost]
      simp
  have shift_distinct (u : StrongSeed) : u.1 ≠ (shift u).1 ∧
      u.1 ≠ (1 : I) ∧ (shift u).1 ≠ (1 : I) := by
    have hu : (u.1 : ℝ) < 1 := u.2
    have hun : u.1 ≠ (1 : I) := ne_of_lt u.2
    refine ⟨?_, hun, ?_⟩ <;>
      intro he <;> have he' := congrArg (fun a : I => (a : ℝ)) he <;>
      dsimp [shift] at he' <;> split_ifs at he' <;> dsimp at he' <;> linarith
  have strong_correct (u : StrongSeed) : Correct (threeProbe u.1 (shift u).1 1) := by
    obtain ⟨hac, had, hcd⟩ := shift_distinct u
    intro s
    obtain ⟨h, hr, _⟩ := three_upper s u.1 (shift u).1 1 hac had hcd
    exact ⟨h, hr⟩
  have strong_lower (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω)
      (hμ : IsProbabilityMeasure μ) (π : Ω → Controller)
      (hπ : ∀ ω, Correct (π ω)) (s : Source) :
      (2 : ENNReal) ≤ ∫⁻ ω, cost (π ω) s ∂μ := by
    letI := hμ
    have hc : ∀ ω, (2 : ENNReal) ≤ cost (π ω) s := by
      intro ω
      obtain ⟨h, hr⟩ := hπ ω s
      have hn := singleton_obstruction h s (run_consistent _ _ _ _ _ hr)
        (terminal_sound _ (hπ ω) _ _ _ hr)
      rw [cost_of_run _ _ _ _ hr]
      exact_mod_cast hn
    simpa using lintegral_mono (μ := μ) hc
  have strong_probability : IsProbabilityMeasure (volume : Measure StrongSeed) := by
    constructor
    rw [Measure.Subtype.volume_univ measurableSet_Iio.nullMeasurableSet,
      unitInterval.volume_Iio]
    simp
  have shift_invol : Function.Involutive shift := by
    intro u
    apply Subtype.ext
    apply Subtype.ext
    have hu : (u.1 : ℝ) < 1 := u.2
    have h0 := u.1.2.1
    dsimp [shift]
    split_ifs <;> dsimp at * <;> linarith
  have shift_injective : Function.Injective shift := shift_invol.injective
  have strong_null : NullSingletonClass (volume : Measure StrongSeed) := by
    constructor
    intro u
    apply le_antisymm _ zero_le
    calc
      volume {u} ≤ (volume : Measure I) ((Subtype.val : StrongSeed → I) '' {u}) :=
        Measure.comap_apply_le _ _ (measurableSet_singleton u).nullMeasurableSet
      _ = 0 := by simp
  letI := strong_null
  have strong_mean (s : Source) :
      (∫⁻ u : StrongSeed, cost (threeProbe u.1 (shift u).1 1) s) = 2 := by
    have fin₁ : {u : StrongSeed | u.1 = s.1}.Finite :=
      (Set.finite_singleton s.1).preimage Subtype.val_injective.injOn
    have fin₂ : {u : StrongSeed | (shift u).1 = s.1}.Finite :=
      fin₁.preimage shift_injective.injOn
    have he₁ : ∀ᵐ u : StrongSeed, u.1 ≠ s.1 := fin₁.countable.ae_notMem volume
    have he₂ : ∀ᵐ u : StrongSeed, (shift u).1 ≠ s.1 := fin₂.countable.ae_notMem volume
    have hcost : (fun u : StrongSeed => cost (threeProbe u.1 (shift u).1 1) s) =ᵐ[volume]
        (fun _ => (2 : ENNReal)) := by
      filter_upwards [he₁, he₂] with u hux hsx
      obtain ⟨hac, had, hcd⟩ := shift_distinct u
      obtain ⟨h, hr, hc⟩ := three_upper s u.1 (shift u).1 1 hac had hcd
      rw [cost_of_run _ _ _ _ hr, hc]
      simp [hux, hsx]
    rw [lintegral_congr_ae hcost, lintegral_const]
    rw [strong_probability.measure_univ]
    simp
  have three_control_measurable {Ω : Type} [MeasurableSpace Ω]
      (a c d : Ω → I) (ha : Measurable a) (hc : Measurable c) (hd : Measurable d) :
      ControlsMeasurably (fun ω => threeProbe (a ω) (c ω) (d ω)) := by
    intro n
    rcases n with _ | n
    · change Measurable (fun z : Ω × (Fin 0 → I × Bool) =>
        (Sum.inl (Sum.inl (a z.1)) : CodedAction))
      exact measurable_inl.comp (measurable_inl.comp (ha.comp measurable_fst))
    rcases n with _ | n
    · simp only [List.ofFn_succ, List.ofFn_zero, threeProbe, actionCode]
      exact measurable_inl.comp (measurable_inl.comp (hc.comp measurable_fst))
    rcases n with _ | n
    · simp only [List.ofFn_succ, List.ofFn_zero, threeProbe, actionCode]
      have h₀ : Measurable (fun z : Ω × (Fin 2 → I × Bool) => (z.2 0).2) := by fun_prop
      have h₁ : Measurable (fun z : Ω × (Fin 2 → I × Bool) => (z.2 1).2) := by fun_prop
      have hq : Measurable (fun z : Ω × (Fin 2 → I × Bool) =>
          (Sum.inl (d z.1) : I ⊕ Bool)) :=
        measurable_inl.comp (hd.comp measurable_fst)
      have hr : Measurable (fun z : Ω × (Fin 2 → I × Bool) =>
          (Sum.inr (z.2 0).2 : I ⊕ Bool)) := measurable_inr.comp h₀
      have hm : Measurable (fun z : Ω × (Fin 2 → I × Bool) =>
          if (z.2 0).2 = (z.2 1).2 then (Sum.inr (z.2 0).2 : I ⊕ Bool)
          else Sum.inl (d z.1)) := hr.ite (measurableSet_eq_fun h₀ h₁) hq
      have houter : Measurable (fun z : Ω × (Fin 2 → I × Bool) =>
          (Sum.inl (if (z.2 0).2 = (z.2 1).2 then (Sum.inr (z.2 0).2 : I ⊕ Bool)
            else Sum.inl (d z.1)) : CodedAction)) := measurable_inl.comp hm
      convert houter using 1
      funext z
      have hi : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
      simp only [hi]
      split_ifs <;> rfl
    · simp only [List.ofFn_succ, threeProbe, actionCode]
      have h₂ : Measurable (fun z : Ω × (Fin (n + 3) → I × Bool) =>
          (z.2 ⟨2, by omega⟩).2) := by fun_prop
      exact measurable_inl.comp (measurable_inr.comp h₂)
  have one_control_measurable : ControlsMeasurably oneProbe := by
    intro n
    rcases n with _ | n
    · change Measurable (fun z : I × (Fin 0 → I × Bool) =>
        (Sum.inl (Sum.inl z.1) : CodedAction))
      fun_prop
    · simp only [List.ofFn_succ, oneProbe, actionCode]
      have h₀ : Measurable (fun z : I × (Fin (n + 1) → I × Bool) =>
          (z.2 0).2) := by fun_prop
      exact measurable_inl.comp (measurable_inr.comp h₀)
  have one_error (s : Source) :
      {u : I | ∃ h b, Run (oneProbe u) s [] h b ∧ b ≠ s.2} = {s.1} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, b, hr, hb⟩
      have hsame := (run_unique _ _ _ _ _ _ _ hr (one_run u s)).2
      by_contra hx
      apply hb
      rw [hsame]
      simp [response, hx]
    · intro hx
      refine ⟨[⟨u, response u s⟩], response u s, one_run u s, ?_⟩
      rw [response, if_pos hx]
      cases s.2 <;> decide
  have one_measurable : MeasurableStrategy oneProbe := by
    refine ⟨one_control_measurable, ?_, ?_, ?_⟩
    · intro s
      simpa only [one_cost] using (measurable_const : Measurable (fun _ : I => (1 : ENNReal)))
    · intro s
      have he : {u : I | ∃ h b, Run (oneProbe u) s [] h b} = Set.univ := by
        ext u; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact ⟨_, _, one_run u s⟩
      rw [he]
      exact MeasurableSet.univ
    · intro s
      rw [one_error]
      exact measurableSet_singleton _
  have shift_measurable : Measurable shift := by
    apply Measurable.subtype_mk
    apply Measurable.subtype_mk
    have hu : Measurable (fun u : StrongSeed => (u.1 : ℝ)) := by fun_prop
    have hm : Measurable (fun u : StrongSeed =>
        if (u.1 : ℝ) < (1 / 2 : ℝ) then (u.1 : ℝ) + 1 / 2 else (u.1 : ℝ) - 1 / 2) :=
      (hu.add_const (1 / 2)).ite (measurableSet_lt hu measurable_const)
        (hu.sub_const (1 / 2))
    convert hm using 1
    funext u
    change ((shift u).1 : ℝ) = _
    by_cases h : (u.1 : ℝ) < 1 / 2
    · rw [shift, dif_pos h, if_pos h]
    · rw [shift, dif_neg h, if_neg h]
  have strong_cost (u : StrongSeed) (s : Source) :
      cost (threeProbe u.1 (shift u).1 1) s =
        if u.1 = s.1 ∨ (shift u).1 = s.1 then 3 else 2 := by
    obtain ⟨hac, had, hcd⟩ := shift_distinct u
    obtain ⟨h, hr, hc⟩ := three_upper s u.1 (shift u).1 1 hac had hcd
    rw [cost_of_run _ _ _ _ hr, hc]
    split_ifs <;> rfl
  have strong_measurable :
      MeasurableStrategy (fun u : StrongSeed => threeProbe u.1 (shift u).1 1) := by
    refine ⟨three_control_measurable Subtype.val (fun u => (shift u).1) (fun _ => 1)
      measurable_subtype_coe shift_measurable.subtype_coe measurable_const, ?_, ?_, ?_⟩
    · intro s
      simp_rw [strong_cost]
      exact measurable_const.ite
        ((measurableSet_eq_fun measurable_subtype_coe measurable_const).union
          (measurableSet_eq_fun shift_measurable.subtype_coe measurable_const)) measurable_const
    · intro s
      have he : {u : StrongSeed | ∃ h b, Run (threeProbe u.1 (shift u).1 1) s [] h b} =
          Set.univ := by
        ext u; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        obtain ⟨h, hr⟩ := strong_correct u s
        exact ⟨h, s.2, hr⟩
      rw [he]
      exact MeasurableSet.univ
    · intro s
      have he : {u : StrongSeed | ∃ h b,
          Run (threeProbe u.1 (shift u).1 1) s [] h b ∧ b ≠ s.2} = ∅ := by
        ext u; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h, b, hr, hb⟩
        obtain ⟨h', hr'⟩ := strong_correct u s
        exact hb (run_unique _ _ _ _ _ _ _ hr hr').2
      rw [he]
      exact MeasurableSet.empty
  have weak_value : randomizedValue false = 1 := by
    apply le_antisymm
    · refine iInf_le_of_le I (iInf_le_of_le inferInstance ?_)
      unfold randomizedValueOn
      refine iInf_le_of_le volume (iInf_le_of_le inferInstance
        (iInf_le_of_le oneProbe (iInf_le_of_le one_measurable
          (iInf_le_of_le (fun s => (weak_upper s).1) ?_))))
      exact iSup_le fun s => le_of_eq (weak_upper s).2
    · refine le_iInf fun Ω => le_iInf fun m => ?_
      unfold randomizedValueOn
      refine le_iInf fun μ => le_iInf fun hμ => le_iInf fun π =>
        le_iInf fun _ => le_iInf fun hπ => ?_
      exact le_trans (weak_lower Ω m μ hμ π hπ (0, false))
        (le_iSup (fun s : Source => ∫⁻ ω, cost (π ω) s ∂μ) (0, false))
  have strong_value : randomizedValue true = 2 := by
    apply le_antisymm
    · refine iInf_le_of_le StrongSeed (iInf_le_of_le inferInstance ?_)
      unfold randomizedValueOn
      refine iInf_le_of_le volume (iInf_le_of_le strong_probability
        (iInf_le_of_le (fun u : StrongSeed => threeProbe u.1 (shift u).1 1)
          (iInf_le_of_le strong_measurable (iInf_le_of_le strong_correct ?_))))
      exact iSup_le fun s => le_of_eq (strong_mean s)
    · refine le_iInf fun Ω => le_iInf fun m => ?_
      unfold randomizedValueOn
      refine le_iInf fun μ => le_iInf fun hμ => le_iInf fun π =>
        le_iInf fun _ => le_iInf fun hπ => ?_
      exact le_trans (strong_lower Ω m μ hμ π hπ (0, false))
        (le_iSup (fun s : Source => ∫⁻ ω, cost (π ω) s ∂μ) (0, false))
  have one_not_correct (u : I) : ¬ Correct (oneProbe u) := by
    intro hu
    obtain ⟨h, hr⟩ := hu (u, false)
    have bad := (run_unique _ _ _ _ _ _ _ hr (one_run u (u, false))).2
    simp [response] at bad
  have strong_worst (u : StrongSeed) :
      (⨆ s : Source, cost (threeProbe u.1 (shift u).1 1) s) = 3 := by
    apply le_antisymm
    · refine iSup_le fun s => ?_
      rw [strong_cost]
      split_ifs <;> norm_num
    · exact worst_lower _ (strong_correct u)
  have response_measurable : Measurable (fun z : I × Source => response z.1 z.2) := by
    have hm : Measurable (fun z : I × Source => z.2.2) := by fun_prop
    have hn : Measurable (fun b : Bool => !b) := measurable_of_countable _
    exact (hn.comp hm).ite (measurableSet_eq_fun measurable_fst
      (measurable_fst.comp measurable_snd)) hm
  have deterministic_control : ControlsMeasurably (fun _ : Unit => threeProbe 0 midpoint 1) :=
    three_control_measurable (fun _ : Unit => 0) (fun _ => midpoint) (fun _ => 1)
      measurable_const measurable_const measurable_const
  have hvalue : deterministicValue = 3 := by
    apply le_antisymm
    · exact iInf_le_of_le (threeProbe 0 midpoint 1) (iInf_le_of_le correct_upper
        (iInf_le_of_le deterministic_control worst_upper))
    · exact le_iInf fun π => le_iInf fun hπ => le_iInf fun _ => worst_lower π hπ
  exact ⟨certificates, deterministic_lower, correct_upper, upper, hvalue,
    le_antisymm worst_upper (worst_lower _ correct_upper), weak_lower, weak_upper,
    strong_correct, strong_lower, strong_probability, strong_mean,
    one_measurable, strong_measurable, weak_value, strong_value, one_error,
    one_not_correct, strong_worst, deterministic_control, response_measurable⟩

end

end D5.S3.ConceptDynamics.Decision.ExactRealProbeCosts

/- GID: D5/S3/Estimation/SequentialDecisionRisk/EffectiveFactoryProgramTransfer
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/EffectiveFactoryProgramTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Effective internal programs and their seeded-controller transfer. -/

import D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliFactoryExecution

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.EffectiveFactoryProgramTransfer

local notation "Action" => Bool ⊕ (Bool × Bool)
local notation "History" => List (Bool × Bool)

/- The internal state is private to a program.  A state is advanced for free
   until the program exposes one visible action.  The history is part of the
   input to `initial`: after an answer is acquired, the next finite internal
   computation starts from the new history. -/
structure InternalProgram (Seed : Type) where
  Memory : Type
  initial : Seed → Bool → History → Memory
  step : Memory → Memory
  visible : Memory → Option Action
  visible_unique : ∀ {m n a b}, visible m = some a → visible n = some b → a = b

namespace InternalProgram

variable {Seed : Type}

def stateAt (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) : ℕ → P.Memory
  | 0 => P.initial seed S h
  | n + 1 => P.step (stateAt P seed S h n)

def visibleAt (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) (n : ℕ) : Option Action :=
  P.visible (P.stateAt seed S h n)

def hasVisible (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) : Prop := ∃ a n, P.visibleAt seed S h n = some a

def stalls (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) : Prop := ∀ n, P.visibleAt seed S h n = none

theorem visible_or_stalls (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) : P.hasVisible seed S h ∨ P.stalls seed S h := by
  by_cases hv : P.hasVisible seed S h
  · exact Or.inl hv
  · right
    intro n
    cases he : P.visibleAt seed S h n with
    | none => rfl
    | some a =>
      exfalso
      exact hv ⟨a, n, he⟩

theorem visible_value_unique (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) {m n : ℕ} {a b : Action}
    (hm : P.visibleAt seed S h m = some a)
    (hn : P.visibleAt seed S h n = some b) : a = b := by
  exact P.visible_unique (by simpa [visibleAt] using hm) (by simpa [visibleAt] using hn)

noncomputable def firstAction (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) : Option Action :=
  by
    classical
    exact if hv : P.hasVisible seed S h then some (Classical.choose hv) else none

theorem firstAction_eq_some (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) {a : Action} (ha : ∃ n, P.visibleAt seed S h n = some a) :
    P.firstAction seed S h = some a := by
  rcases ha with ⟨n, hn⟩
  have hv : P.hasVisible seed S h := ⟨a, n, hn⟩
  rw [firstAction, dif_pos hv]
  congr 1
  rcases Classical.choose_spec hv with ⟨m, hm⟩
  exact P.visible_unique (by simpa [visibleAt] using hm)
    (by simpa [visibleAt] using hn)

theorem firstAction_eq_none (P : InternalProgram Seed) (seed : Seed) (S : Bool)
    (h : History) (hs : P.stalls seed S h) : P.firstAction seed S h = none := by
  rw [firstAction]
  apply dif_neg
  intro hv
  obtain ⟨a, n, hn⟩ := hv
  rw [hs n] at hn
  cases hn

end InternalProgram

/- A total controller is needed by the existing seeded execution.  On a
   permanent internal stall it uses a fixed fallback action.  The admissibility
   hypothesis below makes this fallback a null-set modification, so it cannot
   alter any law or cost integral. -/
def effectivePolicy {Seed : Type} (P : InternalProgram Seed)
    (seed : Seed) (S : Bool) (h : History) : Action :=
  (P.firstAction seed S h).getD (.inl S)

def effectiveStalls {Seed : Type} (P : InternalProgram Seed)
    (seed : Seed) (S : Bool) (h : History) : Prop := P.stalls seed S h

theorem effectivePolicy_eq_of_visible {Seed : Type} (P : InternalProgram Seed)
    (seed : Seed) (S : Bool) (h : History) {a : Action}
    (ha : ∃ n, P.visibleAt seed S h n = some a) :
    effectivePolicy P seed S h = a := by
  rw [effectivePolicy, P.firstAction_eq_some seed S h ha]
  rfl

theorem effectivePolicy_eq_fallback_of_stall {Seed : Type} (P : InternalProgram Seed)
    (seed : Seed) (S : Bool) (h : History) (hs : P.stalls seed S h) :
    effectivePolicy P seed S h = .inl S := by
  rw [effectivePolicy, P.firstAction_eq_none seed S h hs]
  rfl

theorem effective_program_dichotomy {Seed : Type} (P : InternalProgram Seed)
    (seed : Seed) (S : Bool) (h : History) :
    (∃ a n, P.visibleAt seed S h n = some a) ∨ effectiveStalls P seed S h := by
  exact P.visible_or_stalls seed S h

def finiteInternalExecution {Seed : Type} (P : InternalProgram Seed)
    (seed : Seed) (S : Bool) (h : History) : Prop :=
  ∃ a n, P.visibleAt seed S h n = some a

theorem finiteInternalExecution_iff_not_stalls {Seed : Type} (P : InternalProgram Seed)
    (seed : Seed) (S : Bool) (h : History) :
    finiteInternalExecution P seed S h ↔ ¬ effectiveStalls P seed S h := by
  constructor
  · rintro ⟨a, n, hn⟩ hs
    rw [hs n] at hn
    cases hn
  · intro hn
    rcases P.visible_or_stalls seed S h with hv | hs
    · exact hv
    · exact False.elim (hn hs)

theorem effectivePolicy_agrees_ae {Seed : Type} [MeasurableSpace Seed]
    (P : InternalProgram Seed) (ν : Measure Seed)
    (hfinite : ∀ (S : Bool) (h : History), ∀ᵐ seed ∂ν,
      finiteInternalExecution P seed S h) :
    ∀ (S : Bool) (h : History), ∀ᵐ seed ∂ν,
      ∃ a : Action, effectivePolicy P seed S h = a ∧
        ∃ n, P.visibleAt seed S h n = some a := by
  intro S h
  filter_upwards [hfinite S h] with seed hseed
  rcases hseed with ⟨a, n, hn⟩
  exact ⟨a, effectivePolicy_eq_of_visible P seed S h ⟨n, hn⟩, n, hn⟩

def EffectiveCalls {Seed : Type} (P : InternalProgram Seed)
    (S : Bool) : (Seed × (ℕ → Bool)) → WithTop ℕ :=
  fun ω =>
    hittingAfter
      (fun n ω => (fun seed S h => effectivePolicy P seed S h) ω.1 S
        (SeededBernoulliFactoryExecution.acquiredHistory
          (fun seed S h => effectivePolicy P seed S h) S
          (fun _ i bits => bits i) n ω))
      (Set.range (fun cell : Bool × Bool => (.inr cell : Action))) 0 ω

def EffectiveCellAt {Seed : Type} (P : InternalProgram Seed)
    (S : Bool) (n : ℕ) (ω : Seed × (ℕ → Bool)) : Bool × Bool :=
  match
    (fun seed S h => effectivePolicy P seed S h) ω.1 S
      (SeededBernoulliFactoryExecution.acquiredHistory
        (fun seed S h => effectivePolicy P seed S h) S
        (fun _ i bits => bits i) n ω)
  with
  | .inr cell => cell
  | _ => (false, false)

def EffectiveCost {Seed : Type} (P : InternalProgram Seed)
    (S : Bool) (a : ℝ) (ω : Seed × (ℕ → Bool)) : ℝ≥0∞ :=
  if EffectiveCalls P S ω = ⊤ then ⊤ else
    ENNReal.ofReal (((SeededBernoulliFactoryExecution.acquiredHistory
      (fun seed S h => effectivePolicy P seed S h) S
      (fun _ i bits => bits i) ((EffectiveCalls P S ω).untopD 0) ω).length : ℝ) ^ a)

theorem effective_cost_is_seeded_record_cost {Seed : Type}
    (P : InternalProgram Seed) (S : Bool) (a : ℝ) (ω : Seed × (ℕ → Bool)) :
    EffectiveCost P S a ω =
      (if EffectiveCalls P S ω = ⊤ then ⊤ else
        ENNReal.ofReal (((SeededBernoulliFactoryExecution.acquiredHistory
          (fun seed S h => effectivePolicy P seed S h) S
          (fun _ i bits => bits i) ((EffectiveCalls P S ω).untopD 0) ω).length : ℝ) ^ a)) := by
  rfl

/- This is the exact transfer statement used by the factory lower bound.  All
   assumptions on the program are explicit: measurability of its finite-step
   controller, almost-sure exclusion of permanent internal stalls, and the
   complete-output TV contract for the induced controller.  The conclusion is
   the existing logarithmic bound, with the record cost expanded as
   `EffectiveCost`; no internal stall is counted as a source call. -/
set_option maxHeartbeats 600000 in
theorem effective_program_logarithmic_total_call_cost
    {Seed : Type} [MeasurableSpace Seed]
    (B C β : ℝ) (hB : B = 2 ∨ B = 4) (hC : 1 ≤ C)
    (hβ : 0 < β) (hβint : ∀ j : ℕ, β ≠ j) (m : ℕ) (hm : β / 2 < (m : ℝ))
    (P : InternalProgram Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hpolicy : ∀ S h, Measurable (fun seed => effectivePolicy P seed S h))
    (hfinite : ∀ (S : Bool) (h : History), ∀ᵐ seed ∂ν,
      finiteInternalExecution P seed S h) :
    ∃ k : ℝ, 0 < k ∧ ∃ δ₀ : ℝ, δ₀ ∈ Set.Ioo 0 1 ∧
      ∀ δ : ℝ, δ ∈ Set.Ioo 0 δ₀ →
      (∀ (S : Bool) (h : ℝ), h ∈ Set.Ioc 0 (1 / 4 : ℝ) →
        D5.S3.TotalVariation.Pinsker.totalVariation
          (fun cell : Bool × Bool =>
            ((ν.prod (Measure.infinitePi
              (fun _ : ℕ => bernoulliMeasure true false
                (Set.projIcc 0 1 zero_le_one ((1 - h / C) / B))))).real)
              ((stoppedValue (fun n ω => EffectiveCellAt P S n ω)
                (EffectiveCalls P S)) ⁻¹' {cell}))
          (fun cell : Bool × Bool =>
            (if cell.1 then (1 - h / C) / B else 1 - (1 - h / C) / B) / 2 +
              (h ^ β / 16) * (if cell.1 = cell.2 then 1 else -1)) ≤ δ) →
      ENNReal.ofReal (k * Real.log δ⁻¹) ≤
        ⨆ S : Bool, ⨆ h : {h : ℝ // h ∈ Set.Ioc 0 (1 / 4 : ℝ)},
          ∫⁻ ω, EffectiveCost P S (β / 2) ω
            ∂(ν.prod (Measure.infinitePi
              (fun _ : ℕ => bernoulliMeasure true false
                (Set.projIcc 0 1 zero_le_one ((1 - h.1 / C) / B))))) := by
  obtain ⟨k, hk, δ₀, hδ₀, hbound⟩ :=
    SeededBernoulliFactoryExecution.seeded_policy_logarithmic_total_call_cost
      (Seed := Seed) B C β hB hC hβ hβint m hm
  refine ⟨k, hk, δ₀, hδ₀, ?_⟩
  have h_agreement := effectivePolicy_agrees_ae P ν hfinite
  intro δ hδ htv
  have hb := hbound ν inferInstance (fun seed S h => effectivePolicy P seed S h)
    hpolicy δ hδ htv
  convert hb using 1 <;> rfl

end D5.S3.Estimation.SequentialDecisionRisk.EffectiveFactoryProgramTransfer

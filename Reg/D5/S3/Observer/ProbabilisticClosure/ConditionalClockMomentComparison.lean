import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
open _root_.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SharpChallengeInstrument
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal BigOperators
noncomputable section

namespace Laplace
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {A Y : Type} [Fintype A] [Fintype Y]
    (κ : ∀ n, Record A Y n → A → PMF Y) (π : Policy A Y)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (_hμ : 0 < μ) (_hμC : μ ≤ C)
    (_hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (_hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y)
    (n : ℕ),
    ∑ h, (historyLaw κ π n h).toReal * R.readout () () (-clock c n h / C) ≤ rate μ C ^ n

theorem actual_law : arena.Law actual := @adaptive_laplace_decay

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law (A := Unit) (Y := Unit)
    (fun _ _ _ => PMF.pure ()) (fun _ _ => PMF.pure ())
    (fun _ _ _ _ => 1) (μ := 1) (C := 1) (by norm_num) (by norm_num)
    (by intros; norm_num) (by intros; simp [PMF.pure_apply]) 0
  norm_num [rejected, realize, historyLaw, PMF.pure_apply] at h

def record : Registration arena (type_of% (@adaptive_laplace_decay)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change Real.exp (0 : ℝ) ≠ Real.exp 1
    intro h
    have hh := Real.exp_injective h
    norm_num at hh

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@adaptive_laplace_decay) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison.Laplace.registration
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison.Laplace.record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg"],
        stateBinder := 14, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Laplace

namespace Tail
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ mass => mass.toReal) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {A Y : Type} [Fintype A] [Fintype Y]
    (κ : ∀ n, Record A Y n → A → PMF Y) (π : Policy A Y)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (_hμ : 0 < μ) (_hμC : μ ≤ C)
    (_hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (_hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y),
    0 < rate μ C ∧ rate μ C < 1 ∧ 0 < slope μ C ∧
      0 < tailRate μ C ∧ tailRate μ C < 1 ∧
      ∀ n : ℕ, R.readout () () ((historyLaw κ π n).toOuterMeasure
        {h | clock c n h ≤ slope μ C * n}) ≤ tailRate μ C ^ n

theorem actual_law : arena.Law actual := @adaptive_clock_tail

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law (A := Unit) (Y := Unit)
    (fun _ _ _ => PMF.pure ()) (fun _ _ => PMF.pure ())
    (fun _ _ _ _ => 1) (μ := 1) (C := 1) (by norm_num) (by norm_num)
    (by intros; norm_num) (by intros; simp [PMF.pure_apply])).2.2.2.2.2 0
  change (2 : ℝ) ≤ 1 at h
  norm_num at h

def record : Registration arena (type_of% (@adaptive_clock_tail)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ≥0∞), (1 : ℝ≥0∞), ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@adaptive_clock_tail) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison.Tail.registration
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison.Tail.record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ mass => mass.toReal) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "body", "fn", "arg"],
        stateBinder := 13, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Tail

namespace Stopping
abbrev signature : Signature where
  Params := ℝ × ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => tailRate p.1 p.2 ^ n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {A Y : Type} [Fintype A] [Fintype Y]
    (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) (_a₀ : A)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (_hμ : 0 < μ) (_hμC : μ ≤ C)
    (_hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (_hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y)
    (n : ℕ),
    (∑ h, if clock c n h ≤ slope μ C * n then acquiredMass κ σ n h else 0) ≤
        R.readout () (μ, C) n ∧
    (∑ h, acquiredMass κ σ n h) ≤
      (∑ h, if slope μ C * n ≤ clock c n h then acquiredMass κ σ n h else 0) +
        R.readout () (μ, C) n

theorem actual_law : arena.Law actual := @stopping_prefix_clock_tail

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law (A := Unit) (Y := Unit)
    (fun _ _ _ => PMF.pure ()) (fun _ _ => PMF.pure none) ()
    (fun _ _ _ _ => 1) (μ := 1) (C := 1) (by norm_num) (by norm_num)
    (by intros; norm_num) (by intros; simp [PMF.pure_apply]) 0).1
  norm_num [rejected, realize, clock, acquiredMass] at h

def record : Registration arena (type_of% (@stopping_prefix_clock_tail)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1, 1), (0 : ℕ), (1 : ℕ), ?_⟩
    have h := (adaptive_clock_tail (A := Unit) (Y := Unit)
    (fun _ _ _ => PMF.pure ()) (fun _ _ => PMF.pure ())
    (fun _ _ _ _ => 1) (μ := 1) (C := 1) (by norm_num) (by norm_num)
    (by intros; norm_num) (by intros; simp [PMF.pure_apply])).2.2.2.2.1
    change (tailRate 1 1 ^ 0 : ℝ) ≠ tailRate 1 1 ^ 1
    simpa only [pow_zero, pow_one] using (ne_of_lt h).symm

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@stopping_prefix_clock_tail) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison.Stopping.registration
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison.Stopping.record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => tailRate p.1 p.2 ^ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
    definition := none
    coordinates := #[8, 9]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"],
        stateBinder := 14, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"],
        stateBinder := 14, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Stopping

namespace Moments
universe u v
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ s ρ => momentError s ρ) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {A Y : Type} [Fintype A] [Fintype Y]
    {I : Type u} {Ω : I → Type v} [∀ i, MeasurableSpace (Ω i)]
    (κ : ∀ i : I, ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ i : I, ∀ n, Record A Y n → PMF (Option A)) (a₀ : A)
    (c : ∀ i : I, ∀ n, Record A Y n → A → Y → ℝ)
    {μ C s : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C) (hs : 0 < s)
    (hc : ∀ i n h a y, 0 ≤ c i n h a y ∧ c i n h a y ≤ C)
    (hd : ∀ i n h a, μ ≤ ∑ y, (κ i n h a y).toReal * c i n h a y)
    (E : ∀ i, StoppedExecution (κ i) (σ i) (Ω i)),
    R.readout () s (tailRate μ C) < ⊤ ∧
    (∀ i,
      (∫⁻ ω, totalClock (c i) ((E i).path ω) ^ s ∂(E i).law) ≤
        ENNReal.ofReal C ^ s * ∫⁻ ω, totalCalls ((E i).path ω) ^ s ∂(E i).law ∧
      (∫⁻ ω, totalCalls ((E i).path ω) ^ s ∂(E i).law) ≤
        ENNReal.ofReal (slope μ C) ^ (-s) *
          (∫⁻ ω, totalClock (c i) ((E i).path ω) ^ s ∂(E i).law) + momentError s (tailRate μ C)) ∧
    ((⨆ i, ∫⁻ ω, totalClock (c i) ((E i).path ω) ^ s ∂(E i).law) < ⊤ ↔
      (⨆ i, ∫⁻ ω, totalCalls ((E i).path ω) ^ s ∂(E i).law) < ⊤)

theorem actual_law : arena.Law actual := @stopped_clock_moment_comparison

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  letI : ∀ i : PEmpty.{u+1}, MeasurableSpace (PEmpty.{v+1}) := fun i => nomatch i
  have h := law (A := Unit) (Y := Unit) (I := PEmpty.{u+1})
    (Ω := fun _ => PEmpty.{v+1})
    (fun i => nomatch i) (fun i => nomatch i) () (fun i => nomatch i)
    (μ := 1) (C := 1) (s := 1) (by norm_num) (by norm_num) (by norm_num)
    (fun i => nomatch i) (fun i => nomatch i) (fun i => nomatch i)
  exact (lt_irrefl (⊤ : ℝ≥0∞)) h.1

def record : Registration arena (type_of% (@stopped_clock_moment_comparison)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change momentError 1 0 ≠ momentError 1 1
    simp [momentError, momentWeight, ENNReal.rpow_one, ENNReal.tsum_const_eq_top_of_ne_zero]

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@stopped_clock_moment_comparison) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison.Moments.registration
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison.Moments.record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s ρ => momentError s ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
    definition := none
    coordinates := #[13]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
        stateBinder := 12, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Moments

end
end Reg.D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison

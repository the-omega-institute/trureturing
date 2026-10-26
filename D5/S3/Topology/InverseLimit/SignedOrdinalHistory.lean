/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistory
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistory
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: A single coherent run over strict well-founded ordinal pasts. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryTask
import D5.S3.Topology.InverseLimit.SignedOrdinalHistorySuccessor
import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryLimit

/-! Strict-past recursion selects one run before any global semantic readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistory

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent
open SignedOrdinalHistoryBirth SignedOrdinalHistoryState SignedOrdinalHistoryTask
open SignedOrdinalHistorySuccessor
open D5.S3.Topology.Measures

section StrictPastRecursion

universe u v
variable {ι : Type u} [LT ι] (wf : WellFounded ((· < ·) : ι → ι → Prop))
  {Cell : ι → Type v}
  (compatible : ∀ (b a : ι), b < a → Cell b → Cell a → Prop)

private def GoodPast (a : ι) (past : ∀ b, b < a → Option (Cell b)) : Prop :=
  ∃ f : ∀ b, b < a → Cell b,
    (∀ b hb, past b hb = some (f b hb)) ∧
    ∀ b c (hb : b < a) (hc : c < a) (hbc : b < c),
      compatible b c hbc (f b hb) (f c hc)

variable (advance : ∀ a (f : ∀ b, b < a → Cell b),
    (∀ b c (hb : b < a) (hc : c < a) (hbc : b < c),
      compatible b c hbc (f b hb) (f c hc)) →
    {x : Cell a // ∀ b hb, compatible b a hb (f b hb) x})

private noncomputable def guardedStep (a : ι)
    (past : ∀ b, b < a → Option (Cell b)) : Option (Cell a) := by
  classical
  exact if h : GoodPast compatible a past then
    some (advance a (Classical.choose h) (Classical.choose_spec h).2).1
  else none

private noncomputable def guardedRun : ∀ a, Option (Cell a) :=
  wf.fix (guardedStep compatible advance)

private theorem guardedStep_spec (a : ι) (past : ∀ b, b < a → Option (Cell b))
    (h : GoodPast compatible a past) :
    ∃ x, guardedStep compatible advance a past = some x ∧
      ∀ b hb, ∃ y, past b hb = some y ∧ compatible b a hb y x := by
  classical
  let f := Classical.choose h
  have hf := Classical.choose_spec h
  let x := advance a f hf.2
  refine ⟨x.1, ?_, ?_⟩
  · simp only [guardedStep, dite_eq_left h]
    rfl
  · intro b hb
    exact ⟨f b hb, hf.1 b hb, x.2 b hb⟩

private theorem guardedRun_total (a : ι) :
    ∃ x, guardedRun wf compatible advance a = some x ∧
      ∀ b hb, ∃ y, guardedRun wf compatible advance b = some y ∧
        compatible b a hb y x := by
  classical
  induction a using wf.induction with
  | h a ih =>
    let f : ∀ b, b < a → Cell b := fun b hb => Classical.choose (ih b hb)
    have hf (b : ι) (hb : b < a) := Classical.choose_spec (ih b hb)
    have good : GoodPast compatible a (fun b _ => guardedRun wf compatible advance b) := by
      refine ⟨f, fun b hb => (hf b hb).1, ?_⟩
      intro b c hb hc hbc
      obtain ⟨y, hy, hcoh⟩ := (hf c hc).2 b hbc
      have he : y = f b hb := Option.some.inj (hy.symm.trans (hf b hb).1)
      exact he ▸ hcoh
    obtain ⟨x, hx, hrel⟩ := guardedStep_spec compatible advance a
      (fun b _ => guardedRun wf compatible advance b) good
    refine ⟨x, ?_, hrel⟩
    rw [guardedRun, WellFounded.fix_eq]
    exact hx

private noncomputable def realizedRun (a : ι) : Cell a :=
  Classical.choose (guardedRun_total wf compatible advance a)

private theorem realizedRun_some (a : ι) :
    guardedRun wf compatible advance a = some (realizedRun wf compatible advance a) :=
  (Classical.choose_spec (guardedRun_total wf compatible advance a)).1

private theorem realizedRun_coherent (b a : ι) (h : b < a) :
    compatible b a h (realizedRun wf compatible advance b)
      (realizedRun wf compatible advance a) := by
  obtain ⟨y, hy, hc⟩ :=
    (Classical.choose_spec (guardedRun_total wf compatible advance a)).2 b h
  have he : y = realizedRun wf compatible advance b :=
    Option.some.inj (hy.symm.trans (realizedRun_some wf compatible advance b))
  exact he ▸ hc

private theorem advance_val_congr (a : ι) (f g : ∀ b, b < a → Cell b)
    (hf : ∀ b c hb hc hbc, compatible b c hbc (f b hb) (f c hc))
    (hg : ∀ b c hb hc hbc, compatible b c hbc (g b hb) (g c hc))
    (he : f = g) : (advance a f hf).1 = (advance a g hg).1 := by
  subst g
  rfl

private theorem realizedRun_eq (a : ι) :
    realizedRun wf compatible advance a =
      (advance a (fun b _ => realizedRun wf compatible advance b)
        (fun b c _ _ hbc => realizedRun_coherent wf compatible advance b c hbc)).1 := by
  classical
  have good : GoodPast compatible a (fun b _ => guardedRun wf compatible advance b) :=
    ⟨fun b _ => realizedRun wf compatible advance b,
      fun b _ => realizedRun_some wf compatible advance b,
      fun b c _ _ hbc => realizedRun_coherent wf compatible advance b c hbc⟩
  have hf : Classical.choose good = (fun b (_ : b < a) => realizedRun wf compatible advance b) := by
    funext b hb
    exact Option.some.inj (((Classical.choose_spec good).1 b hb).symm.trans
      (realizedRun_some wf compatible advance b))
  have hfix : guardedRun wf compatible advance a =
      some (advance a (Classical.choose good) (Classical.choose_spec good).2).1 := by
    have he := WellFounded.fix_eq wf (guardedStep compatible advance) a
    change guardedRun wf compatible advance a =
      guardedStep compatible advance a (fun b _ => guardedRun wf compatible advance b) at he
    simpa only [guardedStep, dite_eq_left good] using he
  have hx := Option.some.inj ((realizedRun_some wf compatible advance a).symm.trans hfix)
  exact hx.trans (advance_val_congr compatible advance a _ _ _ _ hf)

end StrictPastRecursion

private theorem stageWF : WellFounded ((· < ·) : Stage → Stage → Prop) :=
  InvImage.wf ord Ordinal.lt_wf

private noncomputable def initial_advance (hCH : Cardinal.continuum.{0} = ℵ₁)
    (past : ∀ c : Stage, c < initialStage → State c) :
    {X : State initialStage // ∀ c hc, Coherent hc (past c hc) X} := by
  refine ⟨initialState hCH, ?_⟩
  intro c hc
  exact ((not_lt_of_ge c.2) (show ord c < ω from hc)).elim

private noncomputable def successor_advance (hCH : Cardinal.continuum.{0} = ℵ₁) (b : Stage)
    (past : ∀ c : Stage, c < nextStage b → State c)
    (coherent : ∀ c d hc hd hcd, Coherent hcd (past c hc) (past d hd)) :
    {X : State (nextStage b) // ∀ c hc, Coherent hc (past c hc) X} := by
  let hb : b < nextStage b := Order.lt_succ (ord b)
  refine ⟨nextState (past b hb) hCH, ?_⟩
  intro c hc
  have hcb : c ≤ b := (show ord c ≤ ord b from
    Order.le_of_lt_succ (show ord c < Order.succ (ord b) from hc))
  rcases lt_or_eq_of_le hcb with h | he
  · exact next_coherent_earlier (past b hb) h (past c hc) (coherent c b hc hb h) hCH
  · subst c
    exact next_coherent (past b hb) hCH

private noncomputable def successor_at (hCH : Cardinal.continuum.{0} = ℵ₁)
    (a b : Stage) (he : nextStage b = a)
    (past : ∀ c : Stage, c < a → State c)
    (hc : ∀ c d hc hd hcd, Coherent hcd (past c hc) (past d hd)) :
    {X : State a // ∀ c hc, Coherent hc (past c hc) X} := by
  subst a
  exact successor_advance hCH b past hc

/-- One concrete advancement from this exact strict past. The initial,
successor and proper-limit branches execute their actual constructors. -/
noncomputable def advance (hCH : Cardinal.continuum.{0} = ℵ₁) (a : Stage)
    (past : ∀ b : Stage, b < a → State b)
    (coherent : ∀ b c hb hc hbc, Coherent hbc (past b hb) (past c hc)) :
    {X : State a // ∀ b hb, Coherent hb (past b hb) X} := by
  classical
  by_cases h0 : a = initialStage
  · subst a
    exact initial_advance hCH past
  by_cases hs : ∃ b : Stage, nextStage b = a
  · exact successor_at hCH a (Classical.choose hs) (Classical.choose_spec hs) past coherent
  have hw : ω < ord a := lt_of_le_of_ne a.2
    (fun he => h0 (Subtype.ext (Subtype.ext he.symm)))
  have hl : Order.IsSuccLimit (ord a) := by
    refine ⟨not_isMin_of_lt hw, Order.isSuccPrelimit_of_succ_ne ?_⟩
    intro b he
    have hbω : ω ≤ b := by
      by_contra hn
      have hlt := Ordinal.isSuccLimit_omega0.succ_lt (lt_of_not_ge hn)
      apply (not_lt_of_ge a.2)
      change ord a < ω
      rw [← he]
      exact hlt
    have hba : b < ord a := (Order.lt_succ b).trans_eq he
    let B : Stage := ⟨⟨b, hba.trans a.1.2⟩, hbω⟩
    exact hs ⟨B, Subtype.ext (Subtype.ext he)⟩
  let R := SignedOrdinalHistoryLimit.result a past coherent hw hl
  exact ⟨SignedOrdinalHistoryLimit.limitState R hCH,
    SignedOrdinalHistoryLimit.limit_coherent R hCH⟩

/-- The one actual well-founded run, with no history or step supplier premise. -/
noncomputable def run (hCH : Cardinal.continuum.{0} = ℵ₁) : ∀ a : Stage, State a :=
  realizedRun stageWF (fun _ _ h => Coherent h) (advance hCH)

theorem coherent (hCH : Cardinal.continuum.{0} = ℵ₁) (b a : Stage) (h : b < a) :
    Coherent h (run hCH b) (run hCH a) :=
  realizedRun_coherent stageWF (fun _ _ h => Coherent h) (advance hCH) b a h

/-- Every state is the actual advancement of this same run's own strict past. -/
theorem execution (hCH : Cardinal.continuum.{0} = ℵ₁) (a : Stage) :
    run hCH a = (advance hCH a (fun b _ => run hCH b)
      (fun b c _ _ hbc => coherent hCH b c hbc)).1 :=
  realizedRun_eq stageWF (fun _ _ h => Coherent h) (advance hCH) a

/-- CH alone constructs one coherent run realizing all its own actual steps. -/
theorem exists_history (hCH : Cardinal.continuum.{0} = ℵ₁) :
    ∃ f : ∀ a : Stage, State a,
      ∃ hc : ∀ (b a : Stage) (h : b < a), Coherent h (f b) (f a),
        ∀ a, f a = (advance hCH a (fun b _ => f b)
          (fun b c _ _ hbc => hc b c hbc)).1 :=
  ⟨run hCH, coherent hCH, execution hCH⟩

private theorem nextStage_injective : Injective nextStage := by
  intro b c he
  exact Subtype.ext (Subtype.ext (Order.succ_injective (congrArg ord he)))

private theorem successor_at_readback (hCH : Cardinal.continuum.{0} = ℵ₁)
    (b c : Stage) (he : nextStage c = nextStage b)
    (past : ∀ d : Stage, d < nextStage b → State d)
    (hc : ∀ d e hd he hde, Coherent hde (past d hd) (past e he)) :
    (successor_at hCH (nextStage b) c he past hc).1 =
      nextState (past b (show b < nextStage b from Order.lt_succ (ord b))) hCH := by
  have hcb : c = b := nextStage_injective he
  subst c
  rfl

private theorem advance_successor (hCH : Cardinal.continuum.{0} = ℵ₁) (b : Stage)
    (past : ∀ c : Stage, c < nextStage b → State c)
    (hc : ∀ c d hc hd hcd, Coherent hcd (past c hc) (past d hd)) :
    (advance hCH (nextStage b) past hc).1 =
      nextState (past b (show b < nextStage b from Order.lt_succ (ord b))) hCH := by
  classical
  have hn : nextStage b ≠ initialStage := by
    intro he
    exact (ne_of_gt (b.2.trans_lt (Order.lt_succ (ord b)))) (congrArg ord he)
  have hs : ∃ c : Stage, nextStage c = nextStage b := ⟨b, rfl⟩
  simp only [advance, dite_eq_right hn, dite_eq_left hs]
  exact successor_at_readback hCH b (Classical.choose hs) (Classical.choose_spec hs) past hc

/-- The first state is the actual executed initial prefix. -/
theorem initial_execution (hCH : Cardinal.continuum.{0} = ℵ₁) :
    run hCH initialStage = initialState hCH := by
  rw [execution]
  simp [advance, initial_advance]

/-- The next carrier and incoming event are those of this same selected R. -/
theorem successor_execution (hCH : Cardinal.continuum.{0} = ℵ₁) (b : Stage) :
    run hCH (nextStage b) = nextState (run hCH b) hCH := by
  rw [execution]
  exact advance_successor hCH b _ _

/-- A proper limit uses exactly the constructed run's strict Archive and its
actual once-selected Extension, with no replacement witness. -/
theorem limit_execution (hCH : Cardinal.continuum.{0} = ℵ₁) (a : Stage)
    (hw : ω < ord a) (hl : Order.IsSuccLimit (ord a)) :
    run hCH a = SignedOrdinalHistoryLimit.limitState
      (SignedOrdinalHistoryLimit.result a (fun b _ => run hCH b)
        (fun b c _ _ hbc => coherent hCH b c hbc) hw hl) hCH := by
  classical
  have hn : a ≠ initialStage := by
    intro he
    exact (ne_of_gt hw) (congrArg ord he)
  have hs : ¬ ∃ b : Stage, nextStage b = a := by
    rintro ⟨b, he⟩
    exact hl.succ_ne (ord b) (congrArg ord he)
  rw [execution]
  simp only [advance, dite_eq_right hn, dite_eq_right hs]

/-- Proper F is read from the actual incoming event, retaining regularity
and the norm bound, and evaluated separately at every continuous test. -/
theorem proper_f (hCH : Cardinal.continuum.{0} = ℵ₁) (a : Stage)
    (r : Rows (ord a)) (hr : r ≠ newRow (ord a) a.2) (d : Coord (ord a))
    (s : ℕ → SignedMeasure (K (run hCH a).H))
    (hm : ∀ n, (s n).map (projection (run hCH a).H r) =
      (((run hCH a).P.nu r hr ⟨d.1, (show d.1 < ord a from d.2).trans
        (show ord a < ω₁ from a.1.2)⟩).1 n).1)
    (hn : ∀ n, (s n).totalVariation univ = 1) :
    ∃ mu : SignedMeasure (K (run hCH a).H), mu.totalVariation.Regular ∧
      mu.totalVariation univ ≤ 1 ∧ ∀ g : C(K (run hCH a).H, ℝ),
        Tendsto (fun n => NormPreservingLifts.signedFunctional (s n) g)
          (cofinite ⊓ 𝓟 ((run hCH a).P.J r hr d))
          (𝓝 (NormPreservingLifts.signedFunctional mu g)) := by
  letI : Countable (Coord (ord a)) :=
    (Cardinal.countable_Iio_of_lt_omega_one (show ord a < ω₁ from a.1.2)).to_subtype
  letI : MetricSpace (K (run hCH a).H) :=
    TopologicalSpace.metrizableSpaceMetric (K (run hCH a).H)
  let seq : ℕ → RegularSigned (K (run hCH a).H) :=
    fun n => ⟨s n, inferInstance, inferInstance⟩
  obtain ⟨mu, hb, hc⟩ := (run hCH a).regular r hr d seq hm hn
  letI : mu.1.toJordanDecomposition.posPart.Regular := mu.2.1
  letI : mu.1.toJordanDecomposition.negPart.Regular := mu.2.2
  refine ⟨mu.1, ?_, ?_, ?_⟩
  · change (mu.1.toJordanDecomposition.posPart + mu.1.toJordanDecomposition.negPart).Regular
    infer_instance
  · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)).mp
      (by simpa only [Measure.real, ENNReal.toReal_one] using hb)
  · intro g
    have hg := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hc) g
    change Tendsto (fun n => NormPreservingLifts.signedFunctional (s n) g)
      (along ((run hCH a).P.J r hr d))
      (𝓝 (NormPreservingLifts.signedFunctional mu.1 g)) at hg
    simpa only [along, Nat.cofinite_eq_atTop] using hg

section ExecutedReadback

variable (run : ∀ a : Stage, State a)
  (coherent : ∀ (b a : Stage) (h : b < a), Coherent h (run b) (run a))

private theorem prepared_measure_congr {a : Ordinal.{0}} {H : Prefix (Order.succ a)}
    {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
    (Q : Prepared H ha P launch) (r r' : Rows a) (d d' : Cols a)
    (hr : r = r') (hd : d = d') (n : ℕ) :
    HEq (Q.measure r d n) (Q.measure r' d' n) := by
  subst r'
  subst d'
  rfl

private theorem prepared_launch_readback {a : Ordinal.{0}} {H : Prefix (Order.succ a)}
    {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
    (Q : Prepared H ha P launch) (r : Rows a) (i : Label)
    (hr : r ≠ newRow a ha) (hl : launch = ⟨r, i⟩) (n : ℕ) :
    ((Q.V (newRow a ha)).clopen n : Set (K H)) =
      (projection H r) ⁻¹' ((P.U r hr i).clopen n : Set (Base H r)) := by
  subst launch
  have h := congrArg (fun f : ℕ → Clopens (K H) => (f n : Set (K H))) Q.launch_eq
  simpa only [dite_eq_right hr, Clopens.coe_mk] using h

include coherent in
private theorem ordinary_cofinal_readback (θ : Stage) (d base : Label) :
    ∃ a : Stage, base < a.1 ∧ θ < a ∧ d.1 < ord a ∧
      (CofinalTaskSchedule.reservation a.1).1 = .inl (θ.1, d) ∧
      ∃ (t : Treatment (ord a))
        (R : Result (run a).H a.2 (run a).P
          (scheduledLaunch (run a).H a.2 (run a).P) (run a).event.Q t),
        (run a).event.selected = .ordinary t R ∧
        t.row.1 = ord θ ∧ t.label.1 = d.1 ∧
        ∀ n, HEq ((run a).event.Q.measure t.row t.label n) ((run θ).birth.measure d n) := by
  classical
  obtain ⟨a, ha, hv, he, _⟩ := CofinalTaskSchedule.ordinary_cofinal θ.1 d
    (max base (max θ.1 d)) θ.2 (fun _ _ _ _ => False)
  let A : Stage := ⟨a, θ.2.trans hv.2.1⟩
  have hθ : θ < A := (le_max_left θ.1 d |>.trans (le_max_right base _)).trans_lt ha
  have hd : d.1 < ord A :=
    (le_max_right θ.1 d |>.trans (le_max_right base _)).trans_lt ha
  have hb : base < A.1 := (le_max_left base _).trans_lt ha
  have hex : CofinalTaskSchedule.execute a
      (LocalDelayed (run A).event.Q (run A).event.oldB) = (θ.1, d) := by
    simp only [CofinalTaskSchedule.execute, he, ite_eq_left hv]
  obtain ⟨t, R, hselected⟩ := (run A).event.ordinary_run θ.1 d he
  have ht := (run A).event.target
  rw [hselected, hex] at ht
  have htrow := (Prod.mk.inj ht).1
  have htlabel := (Prod.mk.inj ht).2
  refine ⟨A, hb, hθ, hd, he, t, R, hselected, htrow, htlabel, ?_⟩
  intro n
  let r := oldRow hθ (newRow (ord θ) θ.2)
  let hr := oldRow_ne hθ (newRow (ord θ) θ.2)
  have hrow : t.row = r := Subtype.ext htrow
  have hpack : HEq (preparedOldPack (run A).event.Q
      (run A).event.oldB (run A).oldBonto r hr) (run θ).birth :=
    (heq_of_eq (prepared_old_readback _ _ _ r hr)).trans
      ((heq_of_eq (coherent θ A hθ).birth).trans (BirthPack.cast_heq _ _))
  have hmeasure := BirthPack.heq_measure ((coherent θ A hθ).carrier (top (ord θ)))
    _ _ hpack d n
  have hcol : t.label = ⟨d.1, hd.le⟩ := Subtype.ext htlabel
  apply (prepared_measure_congr (run A).event.Q _ _ _ _ hrow hcol n).trans
  simpa only [preparedOldPack, BirthPack.measure, Prepared.measure] using hmeasure

private def runSemantic (θ s t : Label) (k : ℕ) : Prop :=
  ∃ hθ : ω ≤ θ.1, Intrinsic (run ⟨θ, hθ⟩).birth s t k

private theorem oldB_eval_congr {a : Ordinal.{0}} {H : Prefix (Order.succ a)}
    {ha : ω ≤ a} (B : OldClopens H ha) (r r' : Rows a)
    (hr : r ≠ newRow a ha) (hr' : r' ≠ newRow a ha) (he : r = r') (n : ℕ) :
    HEq (B r hr n) (B r' hr' n) := by
  subst r'
  rfl

theorem cast_B_eval {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (W : BirthPack C) (n : ℕ) :
    HEq ((BirthPack.cast h W).B n) (W.B n) := by
  subst D
  rfl

include coherent in
private theorem delayed_cofinal_readback (θ : Stage) (s t base : Label) (k : ℕ)
    (valid : Intrinsic (run θ).birth s t k) :
    ∃ a : Stage, base < a.1 ∧ θ < a ∧ s.1 < ord a ∧ t.1 < ord a ∧
      (CofinalTaskSchedule.reservation a.1).1 = .inr (θ.1, s, t, k) ∧
      ∃ (D : DelayedTask (run a).event.Q)
        (R : Result (run a).H a.2 (run a).P
          (scheduledLaunch (run a).H a.2 (run a).P) (run a).event.Q ⟨D.row, oldCol D.target⟩)
        (hc : DelayedCertificate (run a).event.Q D R),
        (run a).event.selected = .delayed D R hc ∧
          Matches (run a).event.Q (run a).event.oldB θ.1 s t k D ∧
          HEq D.sourceSupport ((run θ).birth.B (decode k).1) ∧
          HEq D.targetSupport ((run θ).birth.B (decode k).2) := by
  classical
  have hv0 : runSemantic run θ.1 s t k := ⟨θ.2, valid⟩
  obtain ⟨a, ha, hv, he, _⟩ := CofinalTaskSchedule.delayed_cofinal θ.1 s t base k θ.2
    (runSemantic run) hv0
  let A : Stage := ⟨a, θ.2.trans hv.2.1.le⟩
  have hθ : θ < A := hv.2.1
  have hlocal : LocalDelayed (run A).event.Q (run A).event.oldB θ.1 s t k :=
    (stable_local hθ (run θ) (run A) (coherent θ A hθ)
      s t hv.2.2.1 hv.2.2.2 k).mpr valid
  obtain ⟨D, R, hc, hselected, hm⟩ := (run A).event.delayed_run θ.1 s t k he hlocal
  let r := oldRow hθ (newRow (ord θ) θ.2)
  let hr := oldRow_ne hθ (newRow (ord θ) θ.2)
  have hrow : D.row = r := Subtype.ext hm.1
  have hB (n : ℕ) : HEq (((run A).oldBirth r hr).B n) ((run θ).birth.B n) := by
    rw [(coherent θ A hθ).birth]
    exact cast_B_eval _ _ n
  refine ⟨A, ha, hθ, hv.2.2.1, hv.2.2.2, he, D, R, hc, hselected, hm, ?_, ?_⟩
  · exact (heq_of_eq hm.2.2.2.1).trans
      ((oldB_eval_congr (run A).event.oldB _ _ _ _ hrow (decode k).1).trans (hB _))
  · exact (heq_of_eq hm.2.2.2.2).trans
      ((oldB_eval_congr (run A).event.oldB _ _ _ _ hrow (decode k).2).trans (hB _))

private theorem cast_support_mem {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (W : BirthPack C) (i : Label) (n : ℕ) (x : D) :
    x ∈ ((BirthPack.cast h W).U i).clopen n ↔
      Homeomorph.setCongr h.symm x ∈ (W.U i).clopen n := by
  subst D
  rfl

private theorem launch_cofinal_readback (θ : Stage) (i base : Label) :
    ∃ (a : Stage) (hθ : θ < a), base < a.1 ∧
      (CofinalTaskSchedule.reservation a.1).1 = .inl (θ.1, i) ∧
      ∀ n, (((run a).birth.V.clopen n : Clopens (K (run a).H)) : Set _) =
        {x | Homeomorph.setCongr ((coherent θ a hθ).carrier (top (ord θ)))
          (projection (run a).H (oldRow hθ (newRow (ord θ) θ.2)) x) ∈
            ((run θ).birth.U i).clopen n} := by
  classical
  obtain ⟨a, hb, hθ, hi, he, _, _, _, _, _, _⟩ :=
    ordinary_cofinal_readback run coherent θ i base
  let r := oldRow hθ (newRow (ord θ) θ.2)
  let hr := oldRow_ne hθ (newRow (ord θ) θ.2)
  have hv : CofinalTaskSchedule.OrdinaryValid a.1 θ.1 i := ⟨θ.2, hθ.le, hi.le⟩
  have hex : CofinalTaskSchedule.execute a.1 (fun _ _ _ _ => False) = (θ.1, i) := by
    simp only [CofinalTaskSchedule.execute, he, ite_eq_left hv]
  have hrow : (scheduledLaunch (run a).H a.2 (run a).P).row = r := by
    simp only [scheduledLaunch, hex, r, oldRow]
  have hindex : (scheduledLaunch (run a).H a.2 (run a).P).supportIndex = i := by
    simp only [scheduledLaunch, hex]
  have hlaunch : scheduledLaunch (run a).H a.2 (run a).P = ⟨r, i⟩ :=
    congrArg₂ (fun r i => (⟨r, i⟩ : Launch (ord a))) hrow hindex
  have hs := prepared_launch_readback (run a).event.Q r i hr hlaunch
  refine ⟨a, hθ, hb, he, ?_⟩
  intro n
  change (((run a).event.Q.V (newRow (ord a) a.2)).clopen n : Set (K (run a).H)) = _
  rw [hs n]
  ext x
  change projection (run a).H r x ∈ (((run a).oldBirth r hr).U i).clopen n ↔ _
  rw [(coherent θ a hθ).birth]
  exact cast_support_mem _ _ i n _

end ExecutedReadback

/-- Arbitrarily late actual ordinary events act on the original whole measure. -/
theorem ordinary_cofinal (hCH : Cardinal.continuum.{0} = ℵ₁) (θ : Stage) (d base : Label) :
    let f := run hCH
    ∃ a : Stage, base < a.1 ∧ θ < a ∧ d.1 < ord a ∧
      (CofinalTaskSchedule.reservation a.1).1 = .inl (θ.1, d) ∧
      ∃ (t : Treatment (ord a))
        (R : Result (f a).H a.2 (f a).P
          (scheduledLaunch (f a).H a.2 (f a).P) (f a).event.Q t),
        (f a).event.selected = .ordinary t R ∧
        t.row.1 = ord θ ∧ t.label.1 = d.1 ∧
        ∀ n, HEq ((f a).event.Q.measure t.row t.label n) ((f θ).birth.measure d n) :=
  ordinary_cofinal_readback (run hCH) (coherent hCH) θ d base

/-- Intrinsic original-birth validity leads to genuine later local execution
on this constructed run and to the same selected delayed certificate. -/
theorem delayed_cofinal (hCH : Cardinal.continuum.{0} = ℵ₁)
    (θ : Stage) (s t base : Label) (k : ℕ)
    (valid : Intrinsic (run hCH θ).birth s t k) :
    let f := run hCH
    ∃ a : Stage, base < a.1 ∧ θ < a ∧ s.1 < ord a ∧ t.1 < ord a ∧
      (CofinalTaskSchedule.reservation a.1).1 = .inr (θ.1, s, t, k) ∧
      ∃ (D : DelayedTask (f a).event.Q)
        (R : Result (f a).H a.2 (f a).P
          (scheduledLaunch (f a).H a.2 (f a).P) (f a).event.Q ⟨D.row, oldCol D.target⟩)
        (hc : DelayedCertificate (f a).event.Q D R),
        (f a).event.selected = .delayed D R hc ∧
          Matches (f a).event.Q (f a).event.oldB θ.1 s t k D ∧
          HEq D.sourceSupport ((f θ).birth.B (decode k).1) ∧
          HEq D.targetSupport ((f θ).birth.B (decode k).2) :=
  delayed_cofinal_readback (run hCH) (coherent hCH) θ s t base k valid

/-- Support launch and measure labels remain distinct; the new support row
is born at the outgoing stage a, with its original support index i. -/
theorem launch_cofinal (hCH : Cardinal.continuum.{0} = ℵ₁) (θ : Stage) (i base : Label) :
    let f := run hCH
    ∃ (a : Stage) (hθ : θ < a), base < a.1 ∧
      (CofinalTaskSchedule.reservation a.1).1 = .inl (θ.1, i) ∧
      ∀ n, (((f a).birth.V.clopen n : Clopens (K (f a).H)) : Set _) =
        {x | Homeomorph.setCongr ((coherent hCH θ a hθ).carrier (top (ord θ)))
          (projection (f a).H (oldRow hθ (newRow (ord θ) θ.2)) x) ∈
            ((f θ).birth.U i).clopen n} :=
  launch_cofinal_readback (run hCH) (coherent hCH) θ i base

end D5.S3.Topology.InverseLimit.SignedOrdinalHistory

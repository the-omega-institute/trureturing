/- GID: D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual readout, source acquisition, randomized contracts, and original-domain costs. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
import Mathlib.Data.List.Shortlex
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.NullMeasurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition

universe u

open MeasureTheory
open scoped ENNReal
open GenealogicalFiberTransport (Source substitution)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- False means left and true means right, with left preceding right. -/
abbrev Address := List Bool

/-- The two labelled leaves, a branch, and an absent address. -/
inductive Reply
  | alpha | beta | branch | absent
  deriving DecidableEq

instance : Fintype Reply := ⟨{.alpha, .beta, .branch, .absent}, by
  intro r
  cases r <;> simp⟩

/-- Every finite address is a legal query, including the empty root address. -/
def readout : Address → Source → Reply
  | [], .of true => .alpha
  | [], .of false => .beta
  | [], .mul _ _ => .branch
  | _ :: _, .of _ => .absent
  | false :: u, .mul s _ => readout u s
  | true :: u, .mul _ t => readout u t

/-- All actual leaf addresses, in left-to-right order. -/
def leaves : Source → List Address
  | .of _ => [[]]
  | .mul s t => (leaves s).map (false :: ·) ++ (leaves t).map (true :: ·)

/-- All actual node addresses, in preorder. -/
def nodes : Source → List Address
  | .of _ => [[]]
  | .mul s t => [] :: ((nodes s).map (false :: ·) ++ (nodes t).map (true :: ·))

/-- Flip one addressed leaf label, preserving the entire ordered shape. -/
def flip : Source → Address → Source
  | .of b, [] => .of (!b)
  | .of b, _ :: _ => .of b
  | .mul s t, [] => .mul s t
  | .mul s t, false :: u => .mul (flip s u) t
  | .mul s t, true :: u => .mul s (flip t u)

/-- Literal membership in the third actual substitution image. -/
def Positive (t : Source) : Prop := ∃ s : Source, substitution^[3] s = t

/-- A selector receives only its own chronological query-response history. -/
abbrev Policy := Hist (fun _ : Address => Reply) → Sum Address Bool

/-- Pointwise total, globally correct original-domain deterministic strategies.
The same selector and empty initial history are used for every finite tree. -/
structure Strategy where
  policy : Policy
  correct : ∀ U : Source, ∃ (fuel : Nat) (hb : Hist (fun _ : Address => Reply) × Bool),
    execute readout policy fuel [] U = some hb ∧ (hb.2 = true ↔ Positive U)

/-- Distinct actual addresses requested in a chronological history.
Repeated truthful reports contribute no additional paid address. -/
def paid (h : Hist (fun _ : Address => Reply)) : Finset Address :=
  (h.map Sigma.fst).toFinset

/-- The selected finite terminal run, obtained only after pointwise totality. -/
noncomputable def terminal (p : Strategy) (U : Source) :
    Hist (fun _ : Address => Reply) × Bool :=
  Classical.choose (Classical.choose_spec (p.correct U))

/-- A finite correct original run pays once per actual address. -/
noncomputable def cost (p : Strategy) (U : Source) : Nat := (paid (terminal p U).1).card

/-- Response-dependent excess after the compulsory complete-leaf baseline. -/
def chi : Reply → Nat
  | .alpha | .beta => 0
  | .branch | .absent => 1

/-- Extended cost of a history-only policy: nontermination is +∞. -/
noncomputable def extendedCost (policy : Policy) (U : Source) : ℝ≥0∞ := by
  classical
  exact if h : ∃ fuel hb, execute readout policy fuel [] U = some hb then
    ((paid (Classical.choose (Classical.choose_spec h)).1).card : ℝ≥0∞)
  else ∞

/-- Finite wrong returns are distinct from failure to terminate. -/
def wrongReturn (policy : Policy) (U : Source) : Prop :=
  ∃ fuel hb, execute readout policy fuel [] U = some hb ∧
    ¬ (hb.2 = true ↔ Positive U)

/-- Nontermination means that no finite execution returns. -/
def diverges (policy : Policy) (U : Source) : Prop :=
  ¬ ∃ fuel hb, execute readout policy fuel [] U = some hb

/-- The original per-input randomized contract allows measurable null seed exceptions.
No completeness, measurable transcript, or common good-seed set is assumed. -/
structure RandomContract {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) where
  policy : Ω → Policy
  wrongMeasurable : ∀ U, MeasurableSet {s | wrongReturn (policy s) U}
  divergenceMeasurable : ∀ U, MeasurableSet {s | diverges (policy s) U}
  wrongNull : ∀ U, μ {s | wrongReturn (policy s) U} = 0
  divergenceNull : ∀ U, μ {s | diverges (policy s) U} = 0
  measurableCost : ∀ U, Measurable (fun s => extendedCost (policy s) U)

/-- Each random strategy carries its own input-independent probability space. -/
structure RandomStrategy where
  Ω : Type u
  measurableSpace : MeasurableSpace Ω
  seedMeasure : @Measure Ω measurableSpace
  probability : @IsProbabilityMeasure Ω measurableSpace seedMeasure
  controller : @RandomContract Ω measurableSpace seedMeasure

/-- The literal unit interval with its Lebesgue sigma algebra. -/
abbrev Seed := NullMeasurableSpace unitInterval (volume : Measure unitInterval)

/-- Completed Lebesgue probability measure on [0,1], including both endpoints. -/
noncomputable def unitSeedMeasure : Measure Seed :=
  (volume : Measure unitInterval).completion

/-- Uniform random strategies obey the same per-input exceptional-seed contract. -/
abbrev UniformRandomStrategy := RandomContract unitSeedMeasure

/-- Maximum of a finite family, with the nonempty index witness explicit. -/
noncomputable def maxOn {m : Nat} (hm : 0 < m) (f : Fin m → ℝ≥0∞) : ℝ≥0∞ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ f

/-- Expected extended cost under a strategy's own seed law. -/
noncomputable def randomExpected (r : RandomStrategy.{u}) (U : Source) : ℝ≥0∞ :=
  letI := r.measurableSpace
  ∫⁻ s, extendedCost (r.controller.policy s) U ∂r.seedMeasure

/-- Deterministic worst prototype cost, with no source prior. -/
noncomputable def D (m : Nat) (hm : 0 < m) (F : Fin m → Source) : ℝ≥0∞ :=
  sInf {z | ∃ p : Strategy, z = maxOn hm (fun i => (cost p (F i) : ℝ≥0∞))}

/-- Worst fixed-source expectation over arbitrary input-independent seed laws. -/
noncomputable def R (m : Nat) (hm : 0 < m) (F : Fin m → Source) : ℝ≥0∞ :=
  sInf {z | ∃ r : RandomStrategy.{u}, z = maxOn hm (fun i => randomExpected r (F i))}

/-- Worst fixed-source expectation under the fixed uniform seed law. -/
noncomputable def Ru (m : Nat) (hm : 0 < m) (F : Fin m → Source) : ℝ≥0∞ :=
  sInf {z | ∃ r : UniformRandomStrategy,
    z = maxOn hm (fun i => ∫⁻ s, extendedCost (r.policy s) (F i) ∂unitSeedMeasure)}

/-- One common seed is used in every coordinate before the maximum is integrated. -/
noncomputable def W (m : Nat) (hm : 0 < m) (F : Fin m → Source) : ℝ≥0∞ :=
  sInf {z | ∃ r : RandomStrategy.{u}, z =
    letI := r.measurableSpace
    ∫⁻ s, maxOn hm (fun i => extendedCost (r.controller.policy s) (F i)) ∂r.seedMeasure}

/-- Shared-seed maximum under completed Lebesgue measure on the unit interval. -/
noncomputable def Wu (m : Nat) (hm : 0 < m) (F : Fin m → Source) : ℝ≥0∞ :=
  sInf {z | ∃ r : UniformRandomStrategy,
    z = ∫⁻ s, maxOn hm (fun i => extendedCost (r.policy s) (F i)) ∂unitSeedMeasure}

/-- Full joint vectors retain every prototype coordinate. -/
def vector {m : Nat} (F : Fin m → Source) (u : Address) : Fin m → Reply :=
  fun i => readout u (F i)

/-- Only vectors realized at actual addresses belong to the joint-response range. -/
def actualVectors {m : Nat} (F : Fin m → Source) : Set (Fin m → Reply) :=
  Set.range (vector F)

/-- Alpha leaves occur only at the right of the terminal pair (beta,alpha). -/
def alphaValid : Source → Bool
  | .of b => !b
  | .mul s (.of true) => s == .of false
  | .mul s (.of false) => alphaValid s
  | .mul s (.mul l r) => alphaValid s && alphaValid (.mul l r)

/-- Every terminal cherry has the ordered labels (beta,alpha). -/
def cherryValid : Source → Bool
  | .of _ => true
  | .mul (.of b) (.of c) => (!b) && c
  | .mul (.of _) (.mul l r) => cherryValid (.mul l r)
  | .mul (.mul l r) (.of _) => cherryValid (.mul l r)
  | .mul (.mul l r) (.mul s t) => cherryValid (.mul l r) && cherryValid (.mul s t)

/-- A decidable local obstruction shared by all third-step positives. -/
def sourceLaw (t : Source) : Bool := alphaValid t && cherryValid t

theorem source_foundation :
    (∀ t : Source, sourceLaw (substitution^[3] t) = true) ∧
    (∀ t : Source, ∀ u ∈ leaves (substitution^[3] t),
      ¬ Positive (flip (substitution^[3] t) u)) ∧
    (∀ V U : Source, (∀ u ∈ leaves V, readout u U = readout u V) → U = V) ∧
    (∀ V : Source, ∀ u ∈ leaves V, ∀ v : Address, v ≠ u →
      readout v (flip V u) = readout v V) ∧
    (∀ p : Strategy, ∀ U : Source, Positive U →
      (leaves U).toFinset ⊆ paid (terminal p U).1) ∧
    (∀ t : Source, alphaValid (substitution t) = true) ∧
    (∀ t : Source, cherryValid (substitution^[2] t) = true) ∧
    (∀ (policy : Policy) (n m : Nat) (h : Hist (fun _ : Address => Reply))
      (U : Source) (x y : Hist (fun _ : Address => Reply) × Bool),
      execute readout policy n h U = some x →
      execute readout policy m h U = some y → x = y) := by
  have rho3_pair (s t : Source) :
      substitution^[3] (.mul s t) = .mul (substitution^[3] s) (substitution^[3] t) := by
    exact Function.Semiconj₂.iterate
      (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
        fun s t => substitution.map_mul s t) 3 s t
  have rho3_branch (t : Source) : ∃ s r, substitution^[3] t = .mul s r := by
    cases t with
    | of b => cases b <;> exact ⟨_, _, rfl⟩
    | mul s t => rw [rho3_pair]; exact ⟨_, _, rfl⟩
  have flip_branch (s t : Source) (u : Address) : ∃ l r, flip (.mul s t) u = .mul l r := by
    cases u with
    | nil => exact ⟨_, _, rfl⟩
    | cons b u => cases b <;> exact ⟨_, _, rfl⟩
  have law_pair (a b c d : Source) :
      sourceLaw (.mul (.mul a b) (.mul c d)) =
        (sourceLaw (.mul a b) && sourceLaw (.mul c d)) := by
    simp only [sourceLaw, alphaValid, cherryValid]
    cases alphaValid (.mul a b) <;> cases alphaValid (.mul c d) <;>
      cases cherryValid (.mul a b) <;> cases cherryValid (.mul c d) <;> rfl
  have law : ∀ t : Source, sourceLaw (substitution^[3] t) = true := by
    intro t
    induction t with
    | of b => cases b <;> rfl
    | mul s t hs ht =>
      obtain ⟨a,b,ha⟩ := rho3_branch s
      obtain ⟨c,d,hb⟩ := rho3_branch t
      rw [rho3_pair, ha, hb, law_pair]
      rw [ha] at hs
      rw [hb] at ht
      rw [hs, ht]
      rfl
  have obstruct : ∀ t : Source, ∀ u ∈ leaves (substitution^[3] t),
      sourceLaw (flip (substitution^[3] t) u) = false := by
    intro t
    induction t with
    | of b =>
      cases b with
      | false =>
        intro u hu
        change u ∈ [[false,false,false], [false,false,true], [false,true],
          [true,false], [true,true]] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl <;> rfl
      | true =>
        intro u hu
        change u ∈ [[false,false], [false,true], [true]] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl <;> rfl
    | mul s t hs ht =>
      intro u hu
      rw [rho3_pair] at hu ⊢
      simp only [leaves, List.mem_append, List.mem_map] at hu
      rcases hu with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
      · change sourceLaw (.mul (flip (substitution^[3] s) v) (substitution^[3] t)) = false
        obtain ⟨a,b,ha⟩ := rho3_branch s
        obtain ⟨c,d,hb⟩ := rho3_branch t
        obtain ⟨l,r,he⟩ := flip_branch a b v
        have hx := hs v hv
        rw [ha, he] at hx
        rw [ha, he, hb, law_pair, hx]
        rfl
      · change sourceLaw (.mul (substitution^[3] s) (flip (substitution^[3] t) v)) = false
        obtain ⟨a,b,ha⟩ := rho3_branch s
        obtain ⟨c,d,hb⟩ := rho3_branch t
        obtain ⟨l,r,he⟩ := flip_branch c d v
        have hx := ht v hv
        rw [hb, he] at hx
        rw [ha, hb, he, law_pair, hx]
        simp
  have negative : ∀ t : Source, ∀ u ∈ leaves (substitution^[3] t),
      ¬ Positive (flip (substitution^[3] t) u) := by
    intro t u hu hp
    obtain ⟨s,hs⟩ := hp
    have hn := obstruct t u hu
    rw [← hs, law] at hn
    contradiction
  have rigid : ∀ V U : Source,
      (∀ u ∈ leaves V, readout u U = readout u V) → U = V := by
    intro V
    induction V with
    | of b =>
      intro U h
      have hr := h [] (by simp [leaves])
      cases U with
      | of c => cases b <;> cases c <;> simp_all [readout]
      | mul s t => cases b <;> simp [readout] at hr
    | mul s t hs ht =>
      intro U h
      have nonempty : ∀ V : Source, ∃ u, u ∈ leaves V := by
        intro V
        induction V with
        | of _ => exact ⟨[], by simp [leaves]⟩
        | mul s t hs _ =>
          obtain ⟨u,hu⟩ := hs
          exact ⟨false :: u, by simp [leaves, hu]⟩
      have leaf_read : ∀ V : Source, ∀ u ∈ leaves V,
          readout u V = .alpha ∨ readout u V = .beta := by
        intro V
        induction V with
        | of b =>
          intro u hu
          have he : u = [] := by simpa [leaves] using hu
          subst u
          cases b <;> simp [readout]
        | mul s t hs ht =>
          intro u hu
          simp only [leaves, List.mem_append, List.mem_map] at hu
          rcases hu with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
          · exact hs v hv
          · exact ht v hv
      cases U with
      | of b =>
        obtain ⟨u,hu⟩ := nonempty s
        have hh := h (false :: u) (by simp [leaves, hu])
        have hl := leaf_read s u hu
        simp only [readout] at hh
        rcases hl with hl | hl <;> rw [hl] at hh <;> contradiction
      | mul a b =>
        have ha : a = s := hs a (by
          intro u hu
          exact h (false :: u) (by simp [leaves, hu]))
        have hb : b = t := ht b (by
          intro u hu
          exact h (true :: u) (by simp [leaves, hu]))
        rw [ha, hb]
  have unchanged : ∀ V : Source, ∀ u ∈ leaves V, ∀ v : Address, v ≠ u →
      readout v (flip V u) = readout v V := by
    intro V
    induction V with
    | of b =>
      intro u hu v hv
      have he : u = [] := by simpa [leaves] using hu
      subst u
      cases v with
      | nil => exact False.elim (hv rfl)
      | cons c v => rfl
    | mul s t hs ht =>
      intro u hu v hv
      simp only [leaves, List.mem_append, List.mem_map] at hu
      rcases hu with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
      · cases v with
        | nil => rfl
        | cons c v =>
          cases c with
          | false => exact hs u hu v (fun he => hv (congrArg (false :: ·) he))
          | true => rfl
      · cases v with
        | nil => rfl
        | cons c v =>
          cases c with
          | false => rfl
          | true => exact ht u hu v (fun he => hv (congrArg (true :: ·) he))
  have unique (policy : Policy) : ∀ n m h U x y,
      execute readout policy n h U = some x →
      execute readout policy m h U = some y → x = y := by
    intro n
    induction n with
    | zero => intro m h U x y hx; simp [execute] at hx
    | succ n ih =>
      intro m h U x y hx hy
      cases m with
      | zero => simp [execute] at hy
      | succ m =>
        cases hp : policy h with
        | inr b =>
          simp only [execute, hp, Option.some.injEq] at hx hy
          exact hx.symm.trans hy
        | inl q =>
          simp only [execute, hp, Option.map_eq_some_iff] at hx hy
          obtain ⟨a,ha,hax⟩ := hx
          obtain ⟨b,hb,hby⟩ := hy
          have hab := ih m (h ++ [⟨q, readout q U⟩]) U a b ha hb
          subst b
          exact hax.symm.trans hby
  have replay (policy : Policy) : ∀ n h V W t b,
      execute readout policy n h V = some (t,b) →
      (∀ q ∈ paid t, readout q W = readout q V) →
      execute readout policy n h W = some (t,b) := by
    intro n
    induction n with
    | zero => intro h V W t b he; simp [execute] at he
    | succ n ih =>
      intro h V W t b he hagree
      cases hp : policy h with
      | inr c => simpa [execute, hp] using he
      | inl q =>
        simp only [execute, hp, Option.map_eq_some_iff] at he
        obtain ⟨⟨s,c⟩,hs,he⟩ := he
        have ht : (⟨q,readout q V⟩ :: s) = t := congrArg Prod.fst he
        have hc : c = b := congrArg Prod.snd he
        subst t
        subst b
        have hq : readout q W = readout q V := hagree q (by simp [paid])
        have hsagree : ∀ a ∈ paid s, readout a W = readout a V := by
          intro a ha
          apply hagree a
          simpa [paid] using Or.inr ha
        have hr := ih (h ++ [⟨q,readout q V⟩]) V W s c hs hsagree
        simp only [execute, hp, hq, hr, Option.map_some]
  refine ⟨law, negative, rigid, unchanged, ?_, ?_, ?_, unique⟩
  · intro p U hpos u hu
    have hu' : u ∈ leaves U := List.mem_toFinset.mp hu
    by_contra hmissing
    obtain ⟨V,rfl⟩ := hpos
    let W := flip (substitution^[3] V) u
    have ht := Classical.choose_spec (Classical.choose_spec (p.correct (substitution^[3] V)))
    change execute readout p.policy (Classical.choose (p.correct (substitution^[3] V))) []
      (substitution^[3] V) = some (terminal p (substitution^[3] V)) ∧
      ((terminal p (substitution^[3] V)).2 = true ↔ Positive (substitution^[3] V)) at ht
    have ha := replay p.policy _ [] (substitution^[3] V) W
      (terminal p (substitution^[3] V)).1 (terminal p (substitution^[3] V)).2 ht.1 (by
        intro q hq
        exact unchanged (substitution^[3] V) u hu' q (fun he => hmissing (he ▸ hq)))
    have hw := Classical.choose_spec (Classical.choose_spec (p.correct W))
    change execute readout p.policy (Classical.choose (p.correct W)) [] W = some (terminal p W) ∧
      ((terminal p W).2 = true ↔ Positive W) at hw
    have heq := unique p.policy _ _ [] W _ _ ha hw.1
    have htrue : (terminal p (substitution^[3] V)).2 = true := ht.2.mpr ⟨V,rfl⟩
    have hWpos : Positive W := hw.2.mp (by rw [← heq]; exact htrue)
    exact negative V u hu' hWpos
  · intro t
    induction t with
    | of b => cases b <;> rfl
    | mul s t hs ht =>
      cases t with
      | of b =>
        cases b with
        | true => exact hs
        | false =>
          change (alphaValid (substitution s) && true) = true
          rw [hs]
          rfl
      | mul l r =>
        change (alphaValid (substitution s) && alphaValid (substitution (.mul l r))) = true
        rw [hs, ht]
        rfl
  · have pair2 (s t : Source) :
        substitution^[2] (.mul s t) = .mul (substitution^[2] s) (substitution^[2] t) :=
      Function.Semiconj₂.iterate
        (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
          fun s t => substitution.map_mul s t) 2 s t
    have branch2 (t : Source) : ∃ s r, substitution^[2] t = .mul s r := by
      cases t with
      | of b => cases b <;> exact ⟨_,_,rfl⟩
      | mul s t => rw [pair2]; exact ⟨_,_,rfl⟩
    intro t
    induction t with
    | of b => cases b <;> rfl
    | mul s t hs ht =>
      obtain ⟨a,b,ha⟩ := branch2 s
      obtain ⟨c,d,hb⟩ := branch2 t
      rw [pair2, ha, hb, cherryValid]
      rw [ha] at hs
      rw [hb] at ht
      rw [hs, ht]
      rfl

/-- The pending root/frontier work is recomputed solely from this phase's history. -/
def acquisitionStep (todo : List Address) (a : Sigma (fun _ : Address => Reply)) :
    List Address :=
  match todo with
  | [] => []
  | u :: rest => if a.1 = u then
      if a.2 = .branch then (u ++ [false]) :: (u ++ [true]) :: rest else rest
    else todo

def frontier (h : Hist (fun _ : Address => Reply)) : List Address :=
  h.foldl acquisitionStep [[]]

/-- The actual finite preorder reports, used only to verify acquisition executions. -/
def acquisitionTrace (u : Address) : Source → Hist (fun _ : Address => Reply)
  | .of b => [⟨u, if b then .alpha else .beta⟩]
  | .mul s t => ⟨u, .branch⟩ ::
      (acquisitionTrace (u ++ [false]) s ++ acquisitionTrace (u ++ [true]) t)

/-- A finite certificate of the literal frontier transitions. -/
inductive AcquisitionRun : List Address → Hist (fun _ : Address => Reply) →
    List Address → Prop
  | nil (todo) : AcquisitionRun todo [] todo
  | cons (u : Address) (todo : List Address) (y : Reply) (h) (rest)
      (_next : AcquisitionRun (acquisitionStep (u :: todo) ⟨u,y⟩) h rest) :
      AcquisitionRun (u :: todo) (⟨u,y⟩ :: h) rest

/-- Reconstruct a description only from reports that have actually been acquired. -/
def restore : Nat → Hist (fun _ : Address => Reply) → Address → Option Source
  | 0, _, _ => none
  | n+1, h, u => match h.find? (fun a => a.1 == u) with
    | none => none
    | some a => match a.2 with
      | .alpha => some (.of true)
      | .beta => some (.of false)
      | .absent => none
      | .branch => do
          let s ← restore n h (u ++ [false])
          let t ← restore n h (u ++ [true])
          pure (.mul s t)

/-- Finite actual preimage descriptions with no more than the measured number of leaves. -/
noncomputable def boundedSources (ell : Nat) : Finset Source := by
  classical
  exact (Finset.range (ell+1)).biUnion fun a =>
    (Finset.range (ell+1-a)).biUnion fun b =>
      (Finset.univ : Finset (GenealogicalFiberTransport.Fiber (a,b))).image Subtype.val

/-- Finite forward comparison on an acquired description, using the native substitution. -/
noncomputable def finiteDecision (U : Source) : Bool := by
  classical
  exact decide (∃ T ∈ boundedSources U.length, substitution^[3] T = U)

/-- The all-input acquisition selector receives neither a hidden description nor a size.
It requests the actual root and expands only a reported branch. -/
noncomputable def acquisitionPolicy (h : Hist (fun _ : Address => Reply)) : Sum Address Bool :=
  match frontier h with
  | u :: _ => .inl u
  | [] => match restore (h.length+1) h [] with
    | some U => .inr (finiteDecision U)
    | none => .inr false

theorem acquisition_foundation :
    (∀ U : Source, finiteDecision U = true ↔ Positive U) ∧
    (∀ U : Source, execute readout acquisitionPolicy
      ((acquisitionTrace [] U).length + 1) [] U =
        some (acquisitionTrace [] U, finiteDecision U)) := by
  classical
  have composition_length (t : Source) :
      (GenealogicalFiberTransport.composition t).1 +
        (GenealogicalFiberTransport.composition t).2 = t.length := by
    induction t with
    | of b => cases b <;> rfl
    | mul s t hs ht =>
      simp only [GenealogicalFiberTransport.composition, Prod.fst_add, Prod.snd_add,
        FreeMagma.length]
      omega
  have grows (t : Source) : t.length ≤ (substitution t).length := by
    induction t with
    | of b => cases b <;> decide
    | mul s t hs ht =>
      change s.length + t.length ≤ (substitution s).length + (substitution t).length
      omega
  have grows3 (t : Source) : t.length ≤ (substitution^[3] t).length := by
    exact le_trans (grows t) (le_trans (grows (substitution t))
      (grows (substitution (substitution t))))
  have contains (T : Source) (ell : Nat) (hle : T.length ≤ ell) :
      T ∈ boundedSources ell := by
    let a := (GenealogicalFiberTransport.composition T).1
    let b := (GenealogicalFiberTransport.composition T).2
    have hab : a + b ≤ ell := by simpa [a,b, ← composition_length] using hle
    let : Fintype {t : Source // GenealogicalFiberTransport.composition t = (a,b)} :=
      GenealogicalFiberTransport.fiberFintype (a,b)
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_range.mpr (by omega), ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_image.mpr ⟨⟨T,rfl⟩, Finset.mem_univ _, rfl⟩
  have decision (U : Source) : finiteDecision U = true ↔ Positive U := by
    simp only [finiteDecision, decide_eq_true_eq]
    constructor
    · rintro ⟨T,_,hT⟩
      exact ⟨T,hT⟩
    · rintro ⟨T,hT⟩
      exact ⟨T,contains T U.length (by rw [← hT]; exact grows3 T),hT⟩
  have join {a b c : List Address} {h k : Hist (fun _ : Address => Reply)}
      (hr : AcquisitionRun a h b) (hs : AcquisitionRun b k c) :
      AcquisitionRun a (h ++ k) c := by
    induction hr with
    | nil _ => exact hs
    | cons u todo y h rest hn ih => exact .cons u todo y _ c (ih hs)
  have traversal (T : Source) (u : Address) (rest : List Address) :
      AcquisitionRun (u :: rest) (acquisitionTrace u T) rest := by
    induction T generalizing u rest with
    | of b =>
      cases b <;> apply AcquisitionRun.cons <;>
        simpa [acquisitionStep] using AcquisitionRun.nil rest
    | mul s t hs ht =>
      apply AcquisitionRun.cons
      simpa [acquisitionStep] using
        join (hs (u ++ [false]) ((u ++ [true]) :: rest)) (ht (u ++ [true]) rest)
  have folded {todo rest : List Address} {h : Hist (fun _ : Address => Reply)}
      (hr : AcquisitionRun todo h rest) : h.foldl acquisitionStep todo = rest := by
    induction hr with
    | nil _ => rfl
    | cons _ _ _ _ _ _ ih => exact ih
  have child_location (U T : Source) (u : Address)
      (hloc : ∀ v, readout (u ++ v) U = readout v T) (s t : Source)
      (he : T = .mul s t) :
      (∀ v, readout ((u ++ [false]) ++ v) U = readout v s) ∧
      (∀ v, readout ((u ++ [true]) ++ v) U = readout v t) := by
    subst T
    constructor <;> intro v
    · simpa only [List.append_assoc, List.singleton_append, readout] using hloc (false :: v)
    · simpa only [List.append_assoc, List.singleton_append, readout] using hloc (true :: v)
  have truthful (U T : Source) (u : Address)
      (hloc : ∀ v, readout (u ++ v) U = readout v T) :
      ∀ a ∈ acquisitionTrace u T, a.2 = readout a.1 U := by
    induction T generalizing u with
    | of b =>
      intro a ha
      have he : a = ⟨u, if b then .alpha else .beta⟩ := by simpa [acquisitionTrace] using ha
      subst a
      cases b <;> simpa [readout] using (hloc []).symm
    | mul s t hs ht =>
      intro a ha
      simp only [acquisitionTrace, List.mem_cons, List.mem_append] at ha
      rcases ha with rfl | ha | ha
      · simpa only [List.append_nil, readout] using (hloc []).symm
      · exact hs _ (child_location U (.mul s t) u hloc s t rfl).1 a ha
      · exact ht _ (child_location U (.mul s t) u hloc s t rfl).2 a ha
  have reconstruct (U T : Source) (u : Address) (h : Hist (fun _ : Address => Reply))
      (hloc : ∀ v, readout (u ++ v) U = readout v T)
      (htrue : ∀ a ∈ h, a.2 = readout a.1 U)
      (hcontains : ∀ a ∈ acquisitionTrace u T, a ∈ h) :
      ∀ n, (acquisitionTrace u T).length ≤ n → restore n h u = some T := by
    induction T generalizing u with
    | of b =>
      intro n hn
      cases n with
      | zero => simp [acquisitionTrace] at hn
      | succ n =>
        have hm : (⟨u, if b then .alpha else .beta⟩ : Sigma (fun _ : Address => Reply)) ∈ h :=
          hcontains _ (by simp [acquisitionTrace])
        have hf : (h.find? (fun a => a.1 == u)).isSome :=
          List.find?_isSome.mpr ⟨_,hm,by simp⟩
        cases he : h.find? (fun a => a.1 == u) with
        | none => simp [he] at hf
        | some a =>
          have hau : a.1 = u := by simpa using List.find?_some he
          have hay := htrue a (List.mem_of_find?_eq_some he)
          rw [hau] at hay
          have hl := hloc []
          simp only [List.append_nil] at hl
          rw [hl] at hay
          cases b <;> simp [restore, he, hay, readout]
    | mul s t hs ht =>
      intro n hn
      cases n with
      | zero => simp [acquisitionTrace] at hn
      | succ n =>
        have hm : (⟨u, .branch⟩ : Sigma (fun _ : Address => Reply)) ∈ h :=
          hcontains _ (by simp [acquisitionTrace])
        have hf : (h.find? (fun a => a.1 == u)).isSome :=
          List.find?_isSome.mpr ⟨_,hm,by simp⟩
        cases he : h.find? (fun a => a.1 == u) with
        | none => simp [he] at hf
        | some a =>
          have hau : a.1 = u := by simpa using List.find?_some he
          have hay := htrue a (List.mem_of_find?_eq_some he)
          rw [hau] at hay
          have hl := hloc []
          simp only [List.append_nil, readout] at hl
          rw [hl] at hay
          have hn' : (acquisitionTrace (u ++ [false]) s).length +
              (acquisitionTrace (u ++ [true]) t).length + 1 ≤ n+1 := by
            simpa [acquisitionTrace, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
          have hcs : ∀ a ∈ acquisitionTrace (u ++ [false]) s, a ∈ h := by
            intro a ha; exact hcontains a (by simp [acquisitionTrace, ha])
          have hct : ∀ a ∈ acquisitionTrace (u ++ [true]) t, a ∈ h := by
            intro a ha; exact hcontains a (by simp [acquisitionTrace, ha])
          have rs := hs _ (child_location U (.mul s t) u hloc s t rfl).1 hcs n (by omega)
          have rt := ht _ (child_location U (.mul s t) u hloc s t rfl).2 hct n (by omega)
          simp [restore, he, hay, rs, rt]
  have execution {todo rest : List Address} {tr : Hist (fun _ : Address => Reply)}
      (hr : AcquisitionRun todo tr rest) (U : Source)
      (htrue : ∀ a ∈ tr, a.2 = readout a.1 U) :
      ∀ h b, frontier h = todo → acquisitionPolicy (h ++ tr) = .inr b →
        execute readout acquisitionPolicy (tr.length+1) h U = some (tr,b) := by
    induction hr with
    | nil todo =>
      intro h b _ hp
      simp only [List.append_nil] at hp
      simp only [execute, hp]
    | cons u todo y tr rest hn ih =>
      intro h b hh hp
      have hy : y = readout u U := htrue ⟨u,y⟩ (List.mem_cons_self)
      have htail : ∀ a ∈ tr, a.2 = readout a.1 U := by
        intro a ha; exact htrue a (by simp [ha])
      have hfront : frontier (h ++ [⟨u,y⟩]) = acquisitionStep (u::todo) ⟨u,y⟩ := by
        simp only [frontier, List.foldl_append, List.foldl_cons, List.foldl_nil]
        change acquisitionStep (frontier h) ⟨u,y⟩ = _
        rw [hh]
      have hp' : acquisitionPolicy ((h ++ [⟨u,y⟩]) ++ tr) = .inr b := by
        simpa only [List.append_assoc, List.singleton_append] using hp
      have hi := ih htail (h ++ [⟨u,y⟩]) b hfront hp'
      have hquery : acquisitionPolicy h = .inl u := by simp [acquisitionPolicy, hh]
      simp only [List.length_cons, execute, hquery, ← hy, hi,
        Option.map_some]
  refine ⟨decision, ?_⟩
  intro U
  let tr := acquisitionTrace [] U
  have htrue : ∀ a ∈ tr, a.2 = readout a.1 U := truthful U U [] (by intro v; rfl)
  have hrestore : restore (tr.length+1) tr [] = some U :=
    reconstruct U U [] tr (by intro v; rfl) htrue (by intro a ha; exact ha) _ (by
      change (acquisitionTrace [] U).length ≤ (acquisitionTrace [] U).length+1
      omega)
  have hr : AcquisitionRun [[]] tr [] := traversal U [] []
  have hf : frontier tr = [] := folded hr
  have hp : acquisitionPolicy tr = .inr (finiteDecision U) := by
    simp only [acquisitionPolicy, hf, hrestore]
  exact execution hr U htrue [] (finiteDecision U) rfl (by simpa using hp)

/-- The actual total fallback starts with its own empty history on every finite input. -/
noncomputable def fallback : Strategy where
  policy := acquisitionPolicy
  correct U := ⟨(acquisitionTrace [] U).length+1,
    (acquisitionTrace [] U, finiteDecision U), acquisition_foundation.2 U,
    acquisition_foundation.1 U⟩



end D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition

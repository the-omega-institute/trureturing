/- GID: D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite marker tests and finite-atom joint mass coordinates. -/

import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.FiniteAtomLinearRealization

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open AdaptiveMarkerStoppingTails

inductive Task where
  | retained | emitted | raw
  deriving DecidableEq

inductive Output where
  | zero | mark (root : Bool) | rawMark | reject
  deriving DecidableEq, Fintype

inductive Mode where
  | active | stopped | root (value : Bool)
  deriving DecidableEq, Fintype

/-- The root recovered from the acquired marker edge, using its arm parity. -/
def recoveredRoot (h : State) : Bool :=
  match h.actions with
  | [] => false
  | j :: actions => decide (sideCount actions j % 2 = 1)

def currentMode (task : Task) (h : State) : Mode :=
  if h.stopped then
    if task = .retained then .root (recoveredRoot h) else .stopped
  else .active

/-- A native query reads precisely the next unobserved edge of the chosen arm. -/
def nativeStep (task : Task) (source : Source) (h : State) (j : Side) : Output × State :=
  if h.stopped then (.reject, h) else
    let marked := markerResponse source j (sideCount h.actions j)
    let next : State := ⟨j :: h.actions, marked :: h.replies, marked⟩
    (if marked then
      if task = .raw then .rawMark else .mark (recoveredRoot next)
    else .zero, next)

/-- Finite residual tests have access only to new outputs and the current mode. -/
inductive Test where
  | read (accept : Mode → Bool)
  | query (side : Side) (next : Output → Test)
  | inspect (next : Mode → Test)

def nativeAccept (task : Task) (source : Source) (h : State) : Test → Bool
  | .read accept => accept (currentMode task h)
  | .query j next =>
      let step := nativeStep task source h j
      nativeAccept task source step.2 (next step.1)
  | .inspect next => nativeAccept task source h (next (currentMode task h))

/-- Each mixture component generates both complete arms at one shared parameter. -/
def sourceMixture {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval)
    (w : Fin m → ℝ) : Measure Source :=
  ∑ i, ENNReal.ofReal (w i) • sourceLaw alpha (q i)

def exceptionalCount {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => (alpha : ℝ) = (1 - (alpha : ℝ)) * (q i : ℝ)).card

def desiredCard {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) : ℕ :=
  match task with
  | .retained => 4 * m + 2
  | .emitted => 4 * m + 1
  | .raw => 4 * m - 2 * exceptionalCount alpha q + 1

/-- Joint output-successor matrices are independent of old histories and seeds. -/
structure MassModel {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) where
  Carrier : Type
  finite : Fintype Carrier
  mode : Carrier → Mode
  matrix : Side → Output → Carrier → Carrier → ℝ

/-- Backward evaluation of a test gives its fixed linear readout row. -/
def testRow {m : ℕ} {task : Task} {alpha : unitInterval} {q : Fin m → unitInterval}
    (R : MassModel task alpha q) : Test → R.Carrier → ℝ
  | .read accept => fun c => if accept (R.mode c) then 1 else 0
  | .query j next => fun c =>
      letI := R.finite
      ∑ o, ∑ d, R.matrix j o d c * testRow R (next o) d
  | .inspect next => fun c => testRow R (next (R.mode c)) c

/-- The event is defined by execution on the original source, independently of matrices. -/
def nativeEvent {Seed : Type} [MeasurableSpace Seed] (policy : Policy Seed)
    (n : ℕ) (h : State) (B : Set Seed) : Set (Seed × Source) :=
  {p | p.1 ∈ B ∧ actualRun policy p.1 p.2 n = h}

/-- A candidate feature map must explain all positive-probability original histories. -/
def FullNativeBridge {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} (w : Fin m → ℝ) (R : MassModel task alpha q)
    (feature : State → R.Carrier → ℝ) : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (policy : Policy Seed)
    (nu : Measure Seed) [IsProbabilityMeasure nu] (n : ℕ) (h : State) (B : Set Seed),
    MeasurableSet B →
    let law := nu.prod (sourceMixture alpha q w)
    let E := nativeEvent policy n h B
    0 < law.real E →
    (letI := R.finite
     (∑ c, feature h c) = 1 ∧ (∀ c, 0 ≤ feature h c) ∧
       ∀ T : Test, law.real (E ∩ {p | nativeAccept task p.2 h T = true}) =
         law.real E * ∑ c, feature h c * testRow R T c)

/-- The complete finite-atom upper bound includes normalized columns and native tests. -/
def Proposition278 : Prop :=
  ∀ (m : ℕ) (alpha : unitInterval) (q : Fin m → unitInterval) (w : Fin m → ℝ),
    0 < (alpha : ℝ) → (alpha : ℝ) < 1 →
    (∀ i, 0 < (q i : ℝ) ∧ (q i : ℝ) < 1) → Function.Injective q →
    (∀ i, 0 < w i) → (∑ i, w i) = 1 →
    exceptionalCount alpha q ≤ 1 ∧
      ∀ task : Task, ∃ (R : MassModel task alpha q) (feature : State → R.Carrier → ℝ),
        (letI := R.finite
         Fintype.card R.Carrier = desiredCard task alpha q ∧
           (∀ j c, ∑ o, ∑ d, R.matrix j o d c = 1) ∧
           (∀ j o d c, 0 ≤ R.matrix j o d c)) ∧ FullNativeBridge w R feature

end D5.S3.Observer.ProbabilisticClosure.FiniteAtomLinearRealization

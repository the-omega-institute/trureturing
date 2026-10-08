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

/-- Execution in an already terminal interface is independent of the source. -/
def terminalAccept (mode : Mode) : Test → Bool
  | .read accept => accept mode
  | .query _ next => terminalAccept mode (next .reject)
  | .inspect next => terminalAccept mode (next mode)

private theorem native_accept_stopped (task : Task) (source : Source) (h : State)
    (hs : h.stopped = true) (T : Test) :
    nativeAccept task source h T = terminalAccept (currentMode task h) T := by
  induction T with
  | read accept => rfl
  | query j next ih => simpa [nativeAccept, nativeStep, hs, terminalAccept] using ih .reject
  | inspect next ih => exact ih (currentMode task h)

/-- Ordered current arm parities, with no old clock in the residual test. -/
def parity (actions : List Side) : Bool × Bool :=
  (decide (sideCount actions false % 2 = 1), decide (sideCount actions true % 2 = 1))

def selectedParity (eta : Bool × Bool) (j : Side) : Bool := if j then eta.2 else eta.1

def flipParity (eta : Bool × Bool) (j : Side) : Bool × Bool :=
  if j then (eta.1, !eta.2) else (!eta.1, eta.2)

def terminalMode (task : Task) (root : Bool) : Mode :=
  if task = .retained then .root root else .stopped

def markerOutput (task : Task) (root : Bool) : Output :=
  if task = .raw then .rawMark else .mark root

/-- Root-conditioned zero probability, before averaging the hidden root. -/
def rootZero (q : unitInterval) (root : Bool) (eta : Bool × Bool) (j : Side) : ℝ :=
  if root = selectedParity eta j then (q : ℝ) else 1

/-- A finite native-test row at fixed hidden root; this is a kernel recursion. -/
def rootRow (task : Task) (q : unitInterval) (root : Bool) (eta : Bool × Bool) : Test → ℝ
  | .read accept => if accept .active then 1 else 0
  | .query j next =>
      rootZero q root eta j * rootRow task q root (flipParity eta j) (next .zero) +
      (1 - rootZero q root eta j) *
        (if terminalAccept (terminalMode task (selectedParity eta j))
          (next (markerOutput task (selectedParity eta j))) then 1 else 0)
  | .inspect next => rootRow task q root eta (next .active)

def rootCylinderWeight (q : unitInterval) (root : Bool) (actions : List Side) : ℝ :=
  (q : ℝ) ^ (if root then sideCount actions false / 2 + sideCount actions true / 2
    else (sideCount actions false + 1) / 2 + (sideCount actions true + 1) / 2)

private theorem parity_cons (actions : List Side) (j : Side) :
    parity (j :: actions) = flipParity (parity actions) j := by
  have hf := Nat.mod_two_eq_zero_or_one (sideCount actions false)
  have ht := Nat.mod_two_eq_zero_or_one (sideCount actions true)
  simp only [sideCount] at hf ht
  cases j <;> rcases hf with hf | hf <;> rcases ht with ht | ht <;>
    simp [parity, flipParity, sideCount, List.count_cons, Nat.add_mod, hf, ht]

private theorem selected_parity (actions : List Side) (j : Side) :
    selectedParity (parity actions) j = decide (sideCount actions j % 2 = 1) := by
  cases j <;> rfl

private theorem root_cylinder_extension (q : unitInterval) (root : Bool)
    (actions : List Side) (j : Side) :
    rootCylinderWeight q root (j :: actions) =
      rootCylinderWeight q root actions * rootZero q root (parity actions) j := by
  have hp := Nat.mod_two_eq_zero_or_one (sideCount actions j)
  have hexp :
      (if root then sideCount (j :: actions) false / 2 + sideCount (j :: actions) true / 2
       else (sideCount (j :: actions) false + 1) / 2 + (sideCount (j :: actions) true + 1) / 2) =
      (if root then sideCount actions false / 2 + sideCount actions true / 2
       else (sideCount actions false + 1) / 2 + (sideCount actions true + 1) / 2) +
        (if root = selectedParity (parity actions) j then 1 else 0) := by
    simp only [sideCount] at hp
    cases j <;> cases root <;> rcases hp with hp | hp <;>
      simp [sideCount, List.count_cons, selectedParity, parity, hp] <;> omega
  unfold rootCylinderWeight
  rw [hexp, pow_add]
  by_cases he : root = selectedParity (parity actions) j <;> simp [rootZero, he]

private theorem conditional_prefix_mass (q : unitInterval) (root : Bool)
    (actions : List Side) :
    (conditionalSourceLaw q root).real {s | prefixNoMarker s actions} =
      rootCylinderWeight q root actions := by
  have he : {s | prefixNoMarker s actions} =
      noMarkerCylinder (sideCount actions false) (sideCount actions true) := by
    ext s
    simp [prefixNoMarker, noMarkerCylinder, Bool.forall_bool]
  rw [measureReal_def, he, hconditional]
  cases root <;> simp [rootCylinderWeight, ENNReal.toReal_pow]

private theorem measurable_native_accept (task : Task) (T : Test) (h : State) :
    Measurable (fun source => nativeAccept task source h T) := by
  induction T generalizing h with
  | read accept => exact measurable_const
  | inspect next ih => exact ih (currentMode task h) h
  | query j next ih =>
      by_cases hs : h.stopped = true
      · simpa [nativeAccept, nativeStep, hs] using ih .reject h
      · have hs' : h.stopped = false := by cases he : h.stopped <;> simp_all
        have hm : Measurable (fun source => markerResponse source j (sideCount h.actions j)) := by
          unfold markerResponse
          cases hn : sideCount h.actions j <;> cases j <;> simp [endpoint, arm] <;> measurability
        let hzero : State := ⟨j :: h.actions, false :: h.replies, false⟩
        let hmark : State := ⟨j :: h.actions, true :: h.replies, true⟩
        have hzmeas := ih .zero hzero
        have hmmeas := ih (markerOutput task (recoveredRoot hmark)) hmark
        have he : (fun source => nativeAccept task source h (.query j next)) =
            fun source => if markerResponse source j (sideCount h.actions j) = true then
              nativeAccept task source hmark (next (markerOutput task (recoveredRoot hmark)))
            else nativeAccept task source hzero (next .zero) := by
          funext source
          cases hr : markerResponse source j (sideCount h.actions j) <;>
            simp [nativeAccept, nativeStep, hs', hr, hzero, hmark, markerOutput]
        rw [he]
        exact Measurable.ite (hm (measurableSet_singleton true)) hmmeas hzmeas

/-- Original-source cylinder mass for every finite, output-adaptive residual test. -/
private theorem native_root_test_mass (task : Task) (q : unitInterval) (root : Bool)
    (actions : List Side) (replies : List Bool) (T : Test) :
    (conditionalSourceLaw q root).real
      ({source | prefixNoMarker source actions} ∩
        {source | nativeAccept task source ⟨actions, replies, false⟩ T = true}) =
      rootCylinderWeight q root actions * rootRow task q root (parity actions) T := by
  induction T generalizing actions replies with
  | read accept =>
      cases he : accept .active <;>
        simp [nativeAccept, currentMode, rootRow, he, conditional_prefix_mass]
  | inspect next ih =>
      simpa [nativeAccept, currentMode, rootRow] using ih .active actions replies
  | query j next ih =>
      let C : Set Source := {source | prefixNoMarker source actions}
      let Z : Set Source := {source | prefixNoMarker source (j :: actions)}
      let hz : State := ⟨j :: actions, false :: replies, false⟩
      let hm : State := ⟨j :: actions, true :: replies, true⟩
      let e : Bool := terminalAccept (terminalMode task (selectedParity (parity actions) j))
        (next (markerOutput task (selectedParity (parity actions) j)))
      have hr : recoveredRoot hm = selectedParity (parity actions) j := by
        simp [hm, recoveredRoot, selected_parity]
      have hmode : currentMode task hm = terminalMode task (selectedParity (parity actions) j) := by
        simp [currentMode, hm, terminalMode, hr]
      have hterm (source : Source) :
          nativeAccept task source hm (next (markerOutput task (recoveredRoot hm))) = e := by
        rw [native_accept_stopped task source hm rfl, hmode, hr]
      have hsub : Z ⊆ C := fun source h => (hstep source actions j).mp h |>.1
      have hmz : MeasurableSet Z := by
        simpa only [C, Z, noMarkerCylinder, prefixNoMarker, Bool.forall_bool,
          Bool.false_eq_true, ↓reduceIte] using
          hmeas (sideCount (j :: actions) false) (sideCount (j :: actions) true)
      have hmc : MeasurableSet C := by
        simpa only [C, Z, noMarkerCylinder, prefixNoMarker, Bool.forall_bool,
          Bool.false_eq_true, ↓reduceIte] using
          hmeas (sideCount actions false) (sideCount actions true)
      have hev : C ∩ {source | nativeAccept task source ⟨actions, replies, false⟩
            (.query j next) = true} =
          (Z ∩ {source | nativeAccept task source hz (next .zero) = true}) ∪
            (if e then C \ Z else ∅) := by
        ext source
        have hze := hstep source actions j
        cases ho : markerResponse source j (sideCount actions j)
        · simp only [nativeAccept, nativeStep, Bool.false_eq_true, ↓reduceIte, ho]
          simp [C, Z, hz, hm, hze, ho]
        · have hacc : nativeAccept task source ⟨actions, replies, false⟩ (.query j next) =
              nativeAccept task source hm (next (markerOutput task (recoveredRoot hm))) := by
            simp [nativeAccept, nativeStep, ho, hm, markerOutput]
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          rw [hacc, hterm source]
          simp [C, Z, hze, ho, and_comm]

      change (conditionalSourceLaw q root).real
        (C ∩ {source | nativeAccept task source ⟨actions, replies, false⟩
          (.query j next) = true}) = _
      rw [hev]
      cases he : e with
      | false =>
          simp only [he, Bool.false_eq_true, ↓reduceIte, Set.union_empty]
          rw [ih .zero (j :: actions) (false :: replies)]
          rw [root_cylinder_extension, parity_cons]
          simp only [rootRow]
          change _ = rootCylinderWeight q root actions *
            (rootZero q root (parity actions) j *
              rootRow task q root (flipParity (parity actions) j) (next .zero) +
              (1 - rootZero q root (parity actions) j) * (if e then 1 else 0))
          simp [he, mul_assoc]
      | true =>
          simp only [he, ite_true, ↓reduceIte]
          have hd : Disjoint
              (Z ∩ {source | nativeAccept task source hz (next .zero) = true}) (C \ Z) :=
            Set.disjoint_left.mpr fun source h₁ h₂ => h₂.2 h₁.1
          rw [measureReal_union hd (hmc.diff hmz),
            ih .zero (j :: actions) (false :: replies),
            measureReal_sdiff hsub hmz]
          change rootCylinderWeight q root (j :: actions) *
              rootRow task q root (parity (j :: actions)) (next .zero) +
            ((conditionalSourceLaw q root).real {source | prefixNoMarker source actions} -
              (conditionalSourceLaw q root).real {source | prefixNoMarker source (j :: actions)}) = _
          rw [conditional_prefix_mass, conditional_prefix_mass,
            root_cylinder_extension, parity_cons]
          simp only [rootRow]
          change _ = rootCylinderWeight q root actions *
            (rootZero q root (parity actions) j *
              rootRow task q root (flipParity (parity actions) j) (next .zero) +
              (1 - rootZero q root (parity actions) j) * (if e then 1 else 0))
          simp only [he, ite_true, ↓reduceIte]
          ring

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

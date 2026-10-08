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

inductive Output where
  | zero | mark (root : Bool) | rawMark | reject

inductive Mode where
  | active | stopped | root (value : Bool)

/-- The root recovered from the acquired marker edge, using its arm parity. -/
def recoveredRoot (h : State) : Bool :=
  match h.actions with
  | [] => false
  | j :: actions => decide (sideCount actions j % 2 = 1)

def currentMode (task : Task) (h : State) : Mode := by
  classical
  exact
    if h.stopped then
      if task = .retained then .root (recoveredRoot h) else .stopped
    else .active

/-- A native query reads precisely the next unobserved edge of the chosen arm. -/
def nativeStep (task : Task) (source : Source) (h : State) (j : Side) : Output × State := by
  classical
  exact
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

def terminalMode (task : Task) (root : Bool) : Mode := by
  classical
  exact
    if task = .retained then .root root else .stopped

def markerOutput (task : Task) (root : Bool) : Output := by
  classical
  exact
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
  ∑ i, Real.toNNReal (w i) • sourceLaw alpha (q i)

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
  finiteOutputs : Fintype Output
  mode : Carrier → Mode
  matrix : Side → Output → Carrier → Carrier → ℝ

/-- Backward evaluation of a test gives its fixed linear readout row. -/
def testRow {m : ℕ} {task : Task} {alpha : unitInterval} {q : Fin m → unitInterval}
    (R : MassModel task alpha q) : Test → R.Carrier → ℝ
  | .read accept => fun c => if accept (R.mode c) then 1 else 0
  | .query j next => fun c =>
      letI := R.finite
      letI := R.finiteOutputs
      ∑ o, ∑ d, R.matrix j o d c * testRow R (next o) d
  | .inspect next => fun c => testRow R (next (R.mode c)) c

def denominator (alpha q : unitInterval) (eta : Bool × Bool) : ℝ :=
  (alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ) ^ (eta.1.toNat + eta.2.toNat)

def rootMass (alpha q : unitInterval) (eta : Bool × Bool) (root : Bool) : ℝ :=
  (if root then (alpha : ℝ)
   else (1 - (alpha : ℝ)) * (q : ℝ) ^ (eta.1.toNat + eta.2.toNat)) / denominator alpha q eta

def markerRate (alpha q : unitInterval) (eta : Bool × Bool) (j : Side) : ℝ :=
  (1 - (q : ℝ)) * rootMass alpha q eta (selectedParity eta j)

private theorem denominator_pos (alpha q : unitInterval) (ha : 0 < (alpha : ℝ))
    (eta : Bool × Bool) : 0 < denominator alpha q eta := by
  have ha' : 0 ≤ 1 - (alpha : ℝ) := sub_nonneg.mpr alpha.property.2
  have hq : 0 ≤ (q : ℝ) := q.property.1
  dsimp [denominator]
  positivity

private theorem root_mass_sum (alpha q : unitInterval) (ha : 0 < (alpha : ℝ))
    (eta : Bool × Bool) : rootMass alpha q eta false + rootMass alpha q eta true = 1 := by
  simp only [rootMass, Bool.false_eq_true, ↓reduceIte]
  rw [← add_div, add_comm]
  exact div_self (denominator_pos alpha q ha eta).ne'

private theorem root_lift_zero (alpha q : unitInterval) (ha : 0 < (alpha : ℝ))
    (eta : Bool × Bool) (j root : Bool) :
    rootMass alpha q eta root * rootZero q root eta j =
      (1 - markerRate alpha q eta j) * rootMass alpha q (flipParity eta j) root := by
  have hd := (denominator_pos alpha q ha eta).ne'
  have hd' := (denominator_pos alpha q ha (flipParity eta j)).ne'
  rcases eta with ⟨l, r⟩
  cases l <;> cases r <;> cases j <;> cases root <;>
    simp [rootMass, rootZero, markerRate, denominator, selectedParity, flipParity] at hd hd' ⊢ <;>
    field_simp [hd, hd'] <;> ring
  all_goals
    have hn : (q : ℝ) - (q : ℝ) * (alpha : ℝ) + (alpha : ℝ) ≠ 0 := by
      convert hd' using 1 <;> ring
    calc
      (1 : ℝ) = ((q : ℝ) - (q : ℝ) * (alpha : ℝ) + (alpha : ℝ)) *
          ((q : ℝ) - (q : ℝ) * (alpha : ℝ) + (alpha : ℝ))⁻¹ := (mul_inv_cancel₀ hn).symm
      _ = _ := by ring

def terminalCount : Task → ℕ
  | .retained => 2
  | .emitted | .raw => 1

def terminalIndex (task : Task) (root : Bool) : Fin (terminalCount task) := by
  classical
  exact ⟨if task = .retained ∧ root = true then 1 else 0, by
    cases task <;> cases root <;> simp [terminalCount]⟩

@[reducible] def fullModel {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) : MassModel task alpha q := by
  classical
  exact {
    Carrier := (Fin m × (Bool × Bool)) ⊕ Fin (terminalCount task)
    finite := inferInstance
    finiteOutputs := ⟨{.zero, .mark false, .mark true, .rawMark, .reject}, by
      intro o
      cases o with
      | zero => simp
      | mark root => cases root <;> simp
      | rawMark => simp
      | reject => simp⟩
    mode := fun c => match c with
      | .inl _ => .active
      | .inr t => if task = .retained then .root (decide (t.val = 1)) else .stopped
    matrix := fun j o d c => match c with
      | .inl ⟨i, eta⟩ =>
          (if o = .zero then
            if d = .inl (i, flipParity eta j) then 1 - markerRate alpha (q i) eta j else 0
           else 0) +
          (if o = markerOutput task (selectedParity eta j) then
            if d = .inr (terminalIndex task (selectedParity eta j)) then
              markerRate alpha (q i) eta j else 0
           else 0)
      | .inr t => if o = .reject then if d = .inr t then 1 else 0 else 0 }

private theorem full_terminal_row {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (t : Fin (terminalCount task)) (T : Test) :
    testRow (fullModel task alpha q) T (.inr t) =
      if terminalAccept ((fullModel task alpha q).mode (.inr t)) T then 1 else 0 := by
  classical
  letI := (fullModel task alpha q).finite
  letI := (fullModel task alpha q).finiteOutputs
  induction T with
  | read accept => rfl
  | inspect next ih => exact ih ((fullModel task alpha q).mode (.inr t))
  | query j next ih =>
      simp [testRow, fullModel, Finset.univ, terminalAccept, ih .reject]

private theorem full_active_row {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (i : Fin m) (eta : Bool × Bool) (j : Side) (next : Output → Test) :
    testRow (fullModel task alpha q) (.query j next) (.inl (i, eta)) =
      (1 - markerRate alpha (q i) eta j) *
        testRow (fullModel task alpha q) (next .zero) (.inl (i, flipParity eta j)) +
      markerRate alpha (q i) eta j *
        (if terminalAccept (terminalMode task (selectedParity eta j))
          (next (markerOutput task (selectedParity eta j))) then 1 else 0) := by
  classical
  letI := (fullModel task alpha q).finite
  letI := (fullModel task alpha q).finiteOutputs
  have ht : (fullModel task alpha q).mode (.inr (terminalIndex task (selectedParity eta j))) =
      terminalMode task (selectedParity eta j) := by
    cases task <;> cases h : selectedParity eta j <;> simp [fullModel, terminalIndex, terminalMode, terminalCount]
  simp [testRow, fullModel, Finset.univ, Finset.sum_add_distrib, add_mul]
  rw [full_terminal_row, ht]

private theorem full_row_lift {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (ha : 0 < (alpha : ℝ))
    (i : Fin m) (eta : Bool × Bool) (T : Test) :
    testRow (fullModel task alpha q) T (.inl (i, eta)) =
      rootMass alpha (q i) eta false * rootRow task (q i) false eta T +
      rootMass alpha (q i) eta true * rootRow task (q i) true eta T := by
  induction T generalizing eta with
  | read accept =>
      cases he : accept .active <;> simp [testRow, fullModel, rootRow, he, root_mass_sum alpha (q i) ha]
  | inspect next ih => simpa [testRow, fullModel, rootRow] using ih .active eta
  | query j next ih =>
      rw [full_active_row, ih .zero (flipParity eta j)]
      simp only [rootRow]
      have hf := root_lift_zero alpha (q i) ha eta j false
      have ht := root_lift_zero alpha (q i) ha eta j true
      have hm :
          rootMass alpha (q i) eta false * (1 - rootZero (q i) false eta j) +
            rootMass alpha (q i) eta true * (1 - rootZero (q i) true eta j) =
          markerRate alpha (q i) eta j := by
        cases he : selectedParity eta j <;> simp [rootZero, markerRate, he] <;> ring
      linear_combination
        -(rootRow task (q i) false (flipParity eta j) (next .zero)) * hf -
        (rootRow task (q i) true (flipParity eta j) (next .zero)) * ht -
        (if terminalAccept (terminalMode task (selectedParity eta j))
          (next (markerOutput task (selectedParity eta j))) then (1 : ℝ) else 0) * hm

/-- The event is defined by execution on the original source, independently of matrices. -/
def nativeEvent {Seed : Type} [MeasurableSpace Seed] (policy : Policy Seed)
    (n : ℕ) (h : State) (B : Set Seed) : Set (Seed × Source) :=
  {p | p.1 ∈ B ∧ actualRun policy p.1 p.2 n = h}

private theorem native_active_history_fiber {Seed : Type} [MeasurableSpace Seed]
    (policy : Policy Seed) (n : ℕ) (actions : List Side) (B : Set Seed) :
    nativeEvent policy n ⟨actions, List.replicate n false, false⟩ B =
      {u | u ∈ B ∧ zeroReplay policy u n = actions} ×ˢ
        {source | prefixNoMarker source actions} := by
  ext p
  simp only [nativeEvent, Set.mem_ofPred_eq, Set.mem_prod]
  have hb := stopped_execution_replay_bridge policy p.1 p.2 n
  constructor
  · rintro ⟨hB, hrun⟩
    have hs : (actualRun policy p.1 p.2 n).stopped = false := by rw [hrun]
    obtain ⟨ha, hr, hc⟩ := hb.2.2.1 hs
    have hactions : zeroReplay policy p.1 n = actions := by simpa [hrun] using ha.symm
    exact ⟨⟨hB, hactions⟩, hactions ▸ (hb.2.1.mp hs)⟩
  · rintro ⟨⟨hB, ha⟩, hsource⟩
    have hs : (actualRun policy p.1 p.2 n).stopped = false :=
      hb.2.1.mpr (ha ▸ hsource)
    obtain ⟨har, hrr, hcr⟩ := hb.2.2.1 hs
    refine ⟨hB, ?_⟩
    cases hrun : actualRun policy p.1 p.2 n
    simp only [hrun] at har hrr hs
    simp_all

private theorem source_law_real (alpha q : unitInterval) (S : Set Source) :
    (sourceLaw alpha q).real S =
      (alpha : ℝ) * (conditionalSourceLaw q true).real S +
      (1 - (alpha : ℝ)) * (conditionalSourceLaw q false).real S := by
  rw [sourceLaw, measureReal_add_apply]
  simp [unitInterval.coe_symm_eq]

private theorem source_mixture_real {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (S : Set Source) :
    (sourceMixture alpha q w).real S = ∑ i, w i * (sourceLaw alpha (q i)).real S := by
  rw [sourceMixture, measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum (by finiteness)]
  simp [ENNReal.toReal_mul, Real.coe_toNNReal, hw, measureReal_def]

private theorem native_seed_test_mass {m : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (task : Task) (policy : Policy Seed) (nu : Measure Seed) [IsProbabilityMeasure nu]
    (n : ℕ) (actions : List Side) (B : Set Seed) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (T : Test) :
    (nu.prod (sourceMixture alpha q w)).real
      (nativeEvent policy n ⟨actions, List.replicate n false, false⟩ B ∩
        {p | nativeAccept task p.2 ⟨actions, List.replicate n false, false⟩ T = true}) =
      nu.real {u | u ∈ B ∧ zeroReplay policy u n = actions} *
        ∑ i, w i *
          ((alpha : ℝ) * rootCylinderWeight (q i) true actions *
            rootRow task (q i) true (parity actions) T +
          (1 - (alpha : ℝ)) * rootCylinderWeight (q i) false actions *
            rootRow task (q i) false (parity actions) T) := by
  letI : IsFiniteMeasure (sourceMixture alpha q w) := by
    unfold sourceMixture
    infer_instance
  rw [native_active_history_fiber]
  have he :
      ({u | u ∈ B ∧ zeroReplay policy u n = actions} ×ˢ
        {source | prefixNoMarker source actions}) ∩
          {p | nativeAccept task p.2 ⟨actions, List.replicate n false, false⟩ T = true} =
      {u | u ∈ B ∧ zeroReplay policy u n = actions} ×ˢ
        ({source | prefixNoMarker source actions} ∩
          {source | nativeAccept task source ⟨actions, List.replicate n false, false⟩ T = true}) := by
    ext p
    simp [and_assoc]
  rw [he, measureReal_prod_prod, source_mixture_real alpha q w hw]
  simp only [source_law_real, native_root_test_mass]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

def atomEvidence (alpha q : unitInterval) (actions : List Side) : ℝ :=
  (alpha : ℝ) * rootCylinderWeight q true actions +
    (1 - (alpha : ℝ)) * rootCylinderWeight q false actions

def totalEvidence {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval)
    (w : Fin m → ℝ) (actions : List Side) : ℝ :=
  ∑ i, w i * atomEvidence alpha (q i) actions

def fullFeature {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (h : State) :
    (fullModel task alpha q).Carrier → ℝ := by
  classical
  exact fun c => match c with
    | .inl ⟨i, eta⟩ => if h.stopped = false ∧ eta = parity h.actions then
        w i * atomEvidence alpha (q i) h.actions / totalEvidence alpha q w h.actions else 0
    | .inr t => if h.stopped = true ∧ t = terminalIndex task (recoveredRoot h) then 1 else 0

private theorem root_cylinder_decomposition (q : unitInterval) (actions : List Side) :
    rootCylinderWeight q false actions = rootCylinderWeight q true actions *
      (q : ℝ) ^ ((parity actions).1.toNat + (parity actions).2.toNat) := by
  have hf := Nat.mod_two_eq_zero_or_one (sideCount actions false)
  have ht := Nat.mod_two_eq_zero_or_one (sideCount actions true)
  have he :
      (sideCount actions false + 1) / 2 + (sideCount actions true + 1) / 2 =
      sideCount actions false / 2 + sideCount actions true / 2 +
        ((parity actions).1.toNat + (parity actions).2.toNat) := by
    rcases hf with hf | hf <;> rcases ht with ht | ht <;>
      simp [parity, hf, ht] <;> omega
  simp only [rootCylinderWeight, Bool.false_eq_true, ↓reduceIte]
  rw [he, pow_add]

private theorem evidence_root_mass (alpha q : unitInterval) (ha : 0 < (alpha : ℝ))
    (actions : List Side) (root : Bool) :
    atomEvidence alpha q actions * rootMass alpha q (parity actions) root =
      (if root then (alpha : ℝ) else 1 - (alpha : ℝ)) * rootCylinderWeight q root actions := by
  have hd := (denominator_pos alpha q ha (parity actions)).ne'
  have hfactor : atomEvidence alpha q actions =
      rootCylinderWeight q true actions * denominator alpha q (parity actions) := by
    rw [atomEvidence, root_cylinder_decomposition]
    dsimp [denominator]
    ring
  rw [hfactor]
  unfold rootMass
  cases root <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    rw [mul_assoc, mul_comm (denominator alpha q (parity actions)) _, div_mul_cancel₀ _ hd]
  · rw [root_cylinder_decomposition]
    ring
  · ring

private theorem evidence_pos (alpha q : unitInterval) (ha : 0 < (alpha : ℝ))
    (hq : 0 < (q : ℝ)) (actions : List Side) : 0 < atomEvidence alpha q actions := by
  have ha' : 0 ≤ 1 - (alpha : ℝ) := sub_nonneg.mpr alpha.property.2
  dsimp [atomEvidence, rootCylinderWeight]
  positivity

private theorem total_evidence_pos {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (hq : ∀ i, 0 < (q i : ℝ)) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1)
    (actions : List Side) : 0 < totalEvidence alpha q w actions := by
  have hm : 0 < m := by
    by_contra hm
    have hm' : m = 0 := by omega
    subst m
    simp at hsum
  apply Finset.sum_pos'
  · intro i hi
    exact le_of_lt (mul_pos (hw i) (evidence_pos alpha (q i) ha (hq i) actions))
  · exact ⟨⟨0, hm⟩, Finset.mem_univ _,
      mul_pos (hw ⟨0, hm⟩) (evidence_pos alpha (q ⟨0, hm⟩) ha (hq ⟨0, hm⟩) actions)⟩

private theorem full_feature_readout {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (actions : List Side) (replies : List Bool) (T : Test)
    (hZ : totalEvidence alpha q w actions ≠ 0) :
    (letI := (fullModel task alpha q).finite
     totalEvidence alpha q w actions *
       ∑ c, fullFeature task alpha q w ⟨actions, replies, false⟩ c *
         testRow (fullModel task alpha q) T c) =
      ∑ i, w i *
        ((alpha : ℝ) * rootCylinderWeight (q i) true actions *
          rootRow task (q i) true (parity actions) T +
        (1 - (alpha : ℝ)) * rootCylinderWeight (q i) false actions *
          rootRow task (q i) false (parity actions) T) := by
  classical
  letI := (fullModel task alpha q).finite
  letI := (fullModel task alpha q).finiteOutputs
  simp only [fullFeature, Bool.false_eq_true, ↓reduceIte, false_and, true_and, and_true,
    Fintype.sum_sum_type, zero_mul, Finset.sum_const_zero, add_zero,
    ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  simp only [ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i hi
  rw [full_row_lift task alpha q ha]
  have hf := evidence_root_mass alpha (q i) ha actions false
  have ht := evidence_root_mass alpha (q i) ha actions true
  simp only [Bool.false_eq_true, ↓reduceIte] at hf ht
  field_simp [hZ]
  linear_combination
    w i * rootRow task (q i) false (parity actions) T * hf +
    w i * rootRow task (q i) true (parity actions) T * ht

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
         letI := R.finiteOutputs
         Fintype.card R.Carrier = desiredCard task alpha q ∧
           (∀ j c, ∑ o, ∑ d, R.matrix j o d c = 1) ∧
           (∀ j o d c, 0 ≤ R.matrix j o d c)) ∧ FullNativeBridge w R feature

end D5.S3.Observer.ProbabilisticClosure.FiniteAtomLinearRealization

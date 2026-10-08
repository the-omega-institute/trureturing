/- GID: D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite marker tests and finite-atom joint mass coordinates. -/

import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Data.Matrix.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.FiniteAtomLinearRealization

universe u

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open AdaptiveMarkerStoppingTails

set_option backward.isDefEq.respectTransparency false in
inductive Task where
  | retained | emitted | raw
  deriving DecidableEq, Fintype

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

def currentMode (task : Task) (h : State) : Mode := by
  exact
    if h.stopped then
      if task = .retained then .root (recoveredRoot h) else .stopped
    else .active

/-- A native query reads precisely the next unobserved edge of the chosen arm. -/
def nativeStep (task : Task) (source : Source) (h : State) (j : Side) : Output × State := by
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
  exact
    if task = .retained then .root root else .stopped

def markerOutput (task : Task) (root : Bool) : Output := by
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
  rw [measureReal_def, he, conditional_no_marker_cylinder_mass]
  cases root <;> simp [rootCylinderWeight, ENNReal.toReal_pow]

theorem measurable_marker_response (side : Side) (count : ℕ) :
    Measurable (fun source => markerResponse source side count) := by
  unfold markerResponse
  cases count <;> cases side <;> simp only [endpoint, arm] <;> measurability

theorem measurable_native_accept (task : Task) (T : Test) (h : State) :
    Measurable (fun source => nativeAccept task source h T) := by
  induction T generalizing h with
  | read accept => exact measurable_const
  | inspect next ih => exact ih (currentMode task h) h
  | query j next ih =>
      by_cases hs : h.stopped = true
      · simpa [nativeAccept, nativeStep, hs] using ih .reject h
      · have hs' : h.stopped = false := by cases he : h.stopped <;> simp_all
        have hm := measurable_marker_response j (sideCount h.actions j)
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
      have hsub : Z ⊆ C := fun source h => (prefix_no_marker_cons source actions j).mp h |>.1
      have hmz : MeasurableSet Z := by
        simpa only [C, Z, noMarkerCylinder, prefixNoMarker, Bool.forall_bool,
          Bool.false_eq_true, ↓reduceIte] using
          measurable_set_no_marker_cylinder (sideCount (j :: actions) false) (sideCount (j :: actions) true)
      have hmc : MeasurableSet C := by
        simpa only [C, Z, noMarkerCylinder, prefixNoMarker, Bool.forall_bool,
          Bool.false_eq_true, ↓reduceIte] using
          measurable_set_no_marker_cylinder (sideCount actions false) (sideCount actions true)
      have hev : C ∩ {source | nativeAccept task source ⟨actions, replies, false⟩
            (.query j next) = true} =
          (Z ∩ {source | nativeAccept task source hz (next .zero) = true}) ∪
            (if e then C \ Z else ∅) := by
        ext source
        have hze := prefix_no_marker_cons source actions j
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
  [finite : Fintype Carrier]
  mode : Carrier → Mode
  matrix : Side → Output → Carrier → Carrier → ℝ

attribute [instance] MassModel.finite

/-- Backward evaluation of a test gives its fixed linear readout row. -/
def testRow {m : ℕ} {task : Task} {alpha : unitInterval} {q : Fin m → unitInterval}
    (R : MassModel task alpha q) : Test → R.Carrier → ℝ
  | .read accept => fun c => if accept (R.mode c) then 1 else 0
  | .query j next => fun c =>

      ∑ o, ∑ d, R.matrix j o d c * testRow R (next o) d
  | .inspect next => fun c => testRow R (next (R.mode c)) c

def denominator (alpha q : unitInterval) (eta : Bool × Bool) : ℝ :=
  (alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ) ^ (eta.1.toNat + eta.2.toNat)

def rootMass (alpha q : unitInterval) (eta : Bool × Bool) (root : Bool) : ℝ :=
  (if root then (alpha : ℝ)
   else (1 - (alpha : ℝ)) * (q : ℝ) ^ (eta.1.toNat + eta.2.toNat)) / denominator alpha q eta

def markerRate (alpha q : unitInterval) (eta : Bool × Bool) (j : Side) : ℝ :=
  (1 - (q : ℝ)) * rootMass alpha q eta (selectedParity eta j)

theorem denominator_pos (alpha q : unitInterval) (ha : 0 < (alpha : ℝ))
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
  exact ⟨if task = .retained ∧ root = true then 1 else 0, by
    cases task <;> cases root <;> simp [terminalCount]⟩

@[reducible] def fullModel {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) : MassModel task alpha q := by
  exact {
    Carrier := (Fin m × (Bool × Bool)) ⊕ Fin (terminalCount task)
    finite := inferInstance
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

theorem full_terminal_row {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (t : Fin (terminalCount task)) (T : Test) :
    testRow (fullModel task alpha q) T (.inr t) =
      if terminalAccept ((fullModel task alpha q).mode (.inr t)) T then 1 else 0 := by
  classical
  induction T with
  | read accept => rfl
  | inspect next ih => exact ih ((fullModel task alpha q).mode (.inr t))
  | query j next ih =>
      simp [testRow, fullModel, Finset.univ, Fintype.complete, terminalAccept, ih .reject]
      split_ifs <;> simp_all

theorem full_active_row {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (i : Fin m) (eta : Bool × Bool) (j : Side) (next : Output → Test) :
    testRow (fullModel task alpha q) (.query j next) (.inl (i, eta)) =
      (1 - markerRate alpha (q i) eta j) *
        testRow (fullModel task alpha q) (next .zero) (.inl (i, flipParity eta j)) +
      markerRate alpha (q i) eta j *
        (if terminalAccept (terminalMode task (selectedParity eta j))
          (next (markerOutput task (selectedParity eta j))) then 1 else 0) := by
  classical
  have ht : (fullModel task alpha q).mode (.inr (terminalIndex task (selectedParity eta j))) =
      terminalMode task (selectedParity eta j) := by
    cases task <;> cases h : selectedParity eta j <;> simp [fullModel, terminalIndex, terminalMode, terminalCount]
  simp [testRow, fullModel, Finset.univ, Fintype.complete, Finset.sum_add_distrib, add_mul]
  rw [full_terminal_row, ht]
  split_ifs <;> ring

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
def nativeEvent {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (n : ℕ) (h : State) (B : Set Seed) : Set (Seed × Source) :=
  {p | p.1 ∈ B ∧ actualRun policy p.1 p.2 n = h}

private theorem native_active_history_fiber {Seed : Type*} [MeasurableSpace Seed]
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

private theorem native_seed_test_mass {m : ℕ} {Seed : Type*} [MeasurableSpace Seed]
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

private theorem full_feature_pairing {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (h : State)
    (f : (fullModel task alpha q).Carrier → ℝ) :
    (∑ c, fullFeature task alpha q w h c * f c) =
    if h.stopped then f (.inr (terminalIndex task (recoveredRoot h))) else
      ∑ i, (w i * atomEvidence alpha (q i) h.actions / totalEvidence alpha q w h.actions) *
        f (.inl (i,parity h.actions)) := by
  classical
  cases hs : h.stopped
  · simp only [fullFeature, hs, Bool.false_eq_true, ↓reduceIte, true_and, false_and,
      Fintype.sum_sum_type, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_prod_type]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · simp only [fullFeature, hs, Bool.true_eq_false, ↓reduceIte, true_and, false_and,
      Fintype.sum_sum_type, zero_mul, one_mul, Finset.sum_const_zero, zero_add,
      ite_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem full_feature_readout {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (actions : List Side) (replies : List Bool) (T : Test)
    (hZ : totalEvidence alpha q w actions ≠ 0) :
    (totalEvidence alpha q w actions *
       ∑ c, fullFeature task alpha q w ⟨actions, replies, false⟩ c *
         testRow (fullModel task alpha q) T c) =
      ∑ i, w i *
        ((alpha : ℝ) * rootCylinderWeight (q i) true actions *
          rootRow task (q i) true (parity actions) T +
        (1 - (alpha : ℝ)) * rootCylinderWeight (q i) false actions *
          rootRow task (q i) false (parity actions) T) := by
  classical
  rw [full_feature_pairing]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Finset.mul_sum]
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
  ∀ (Seed : Type u) [MeasurableSpace Seed] (policy : Policy Seed)
    (nu : Measure Seed) [IsProbabilityMeasure nu] (n : ℕ) (h : State) (B : Set Seed),
    MeasurableSet B →
    let law := nu.prod (sourceMixture alpha q w)
    let E := nativeEvent policy n h B
    0 < law.real E →
    ((∑ c, feature h c) = 1 ∧ (∀ c, 0 ≤ feature h c) ∧
       (∀ T : Test, Measurable (fun source => nativeAccept task source h T)) ∧
       ∀ T : Test, law.real (E ∩ {p | nativeAccept task p.2 h T = true}) =
         law.real E * ∑ c, feature h c * testRow R T c)

private theorem full_feature_probability {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (hq : ∀ i, 0 < (q i : ℝ)) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1)
    (h : State) :
    ((∑ c, fullFeature task alpha q w h c) = 1 ∧
       ∀ c, 0 ≤ fullFeature task alpha q w h c) := by
  classical
  have hZ := total_evidence_pos alpha q w ha hq hw hsum h.actions
  constructor
  · have hpair := full_feature_pairing task alpha q w h (fun _ => 1)
    simp only [mul_one] at hpair
    rw [hpair]
    cases hs : h.stopped
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      rw [← Finset.sum_div]
      exact div_self hZ.ne'
    · simp [hs]
  · intro c
    cases c with
    | inl p =>
        dsimp [fullFeature]
        split_ifs
        · exact div_nonneg
            (mul_nonneg (hw p.1).le (evidence_pos alpha (q p.1) ha (hq p.1) h.actions).le) hZ.le
        · exact le_rfl
    | inr t => dsimp [fullFeature]; split_ifs <;> norm_num

private theorem full_stopped_readout {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (h : State) (hs : h.stopped = true) (T : Test) :
    (∑ c, fullFeature task alpha q w h c * testRow (fullModel task alpha q) T c) =
      if terminalAccept (currentMode task h) T then 1 else 0 := by
  classical
  have ht : (fullModel task alpha q).mode (.inr (terminalIndex task (recoveredRoot h))) =
      currentMode task h := by
    cases task <;> cases hr : recoveredRoot h <;>
      simp [currentMode, hs, terminalIndex, terminalCount, hr]
  simp only [fullFeature, hs, Bool.true_eq_false, ↓reduceIte, true_and, false_and,
    Fintype.sum_sum_type, ite_mul, zero_mul, one_mul, Finset.sum_const_zero, zero_add,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [full_terminal_row, ht]

theorem full_model_probability {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (ha : 0 < (alpha : ℝ)) :
    (Fintype.card (fullModel task alpha q).Carrier = 4 * m + terminalCount task ∧
       (∀ j c, ∑ o, ∑ d, (fullModel task alpha q).matrix j o d c = 1) ∧
       ∀ j o d c, 0 ≤ (fullModel task alpha q).matrix j o d c) := by
  classical
  have hrate (i : Fin m) (eta : Bool × Bool) (j : Side) :
      0 ≤ markerRate alpha (q i) eta j ∧ markerRate alpha (q i) eta j ≤ 1 := by
    have hroot (root : Bool) : 0 ≤ rootMass alpha (q i) eta root := by
      have ha' : 0 ≤ 1 - (alpha : ℝ) := sub_nonneg.mpr alpha.property.2
      have hq' : 0 ≤ (q i : ℝ) := (q i).property.1
      have hden := (denominator_pos alpha (q i) ha eta).le
      cases root <;> dsimp [rootMass] <;> positivity
    have hsum := root_mass_sum alpha (q i) ha eta
    have hle : rootMass alpha (q i) eta (selectedParity eta j) ≤ 1 := by
      cases selectedParity eta j <;> linarith [hroot false, hroot true]
    have hqn := (q i).property.1
    have hql := (q i).property.2
    dsimp [markerRate]
    constructor
    · exact mul_nonneg (sub_nonneg.mpr hql) (hroot _)
    · nlinarith [hroot (selectedParity eta j)]
  refine ⟨?_, ?_, ?_⟩
  · change Fintype.card ((Fin m × (Bool × Bool)) ⊕ Fin (terminalCount task)) = _
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  · intro j c
    cases c with
    | inl p =>
        simp [fullModel, Finset.univ, Fintype.complete, Finset.sum_add_distrib]
    | inr t => simp [fullModel, Finset.univ, Fintype.complete]
  · intro j o d c
    cases c with
    | inl p =>
        have hr := hrate p.1 p.2 j
        dsimp [fullModel]
        split_ifs <;> linarith
    | inr t => dsimp [fullModel]; split_ifs <;> norm_num

/-- All positive-probability original histories have fixed linear finite-test readouts. -/
theorem native_finite_test_realization {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (hq : ∀ i, 0 < (q i : ℝ)) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1) :
    (Fintype.card (fullModel task alpha q).Carrier = 4 * m + terminalCount task ∧
       (∀ j c, ∑ o, ∑ d, (fullModel task alpha q).matrix j o d c = 1) ∧
       (∀ j o d c, 0 ≤ (fullModel task alpha q).matrix j o d c) ∧
       FullNativeBridge.{u} w (fullModel task alpha q) (fullFeature task alpha q w)) := by
  classical
  obtain ⟨hcard, hcol, hpos⟩ := full_model_probability task alpha q ha
  refine ⟨hcard, hcol, hpos, ?_⟩
  intro Seed inst policy nu prob n h B hB
  dsimp only
  intro hE
  obtain ⟨hsumFeature, hposFeature⟩ := full_feature_probability task alpha q w ha hq hw hsum h
  refine ⟨hsumFeature, hposFeature, fun T => measurable_native_accept task T h, ?_⟩
  intro T
  cases h with
  | mk actions replies stopped =>
      cases stopped with
      | true =>
          rw [full_stopped_readout task alpha q w _ rfl T]
          cases he : terminalAccept (currentMode task ⟨actions, replies, true⟩) T
          · have hev :
                nativeEvent policy n ⟨actions, replies, true⟩ B ∩
                  {p | nativeAccept task p.2 ⟨actions, replies, true⟩ T = true} = ∅ := by
              ext p
              simp [native_accept_stopped task p.2 ⟨actions, replies, true⟩ rfl T, he]
            rw [hev]
            simp [he]
          · have hev :
                nativeEvent policy n ⟨actions, replies, true⟩ B ∩
                  {p | nativeAccept task p.2 ⟨actions, replies, true⟩ T = true} =
                nativeEvent policy n ⟨actions, replies, true⟩ B := by
              ext p
              simp [native_accept_stopped task p.2 ⟨actions, replies, true⟩ rfl T, he]
            rw [hev]
            simp [he]
      | false =>
          obtain ⟨p, hp⟩ := nonempty_of_measureReal_ne_zero hE.ne'
          have hrun : actualRun policy p.1 p.2 n = ⟨actions, replies, false⟩ := hp.2
          have hs : (actualRun policy p.1 p.2 n).stopped = false := by rw [hrun]
          have hr := (stopped_execution_replay_bridge policy p.1 p.2 n).2.2.1 hs
          have hreplies : replies = List.replicate n false := by simpa [hrun] using hr.2.1
          subst replies
          have hZ := total_evidence_pos alpha q w ha hq hw hsum actions
          have hmass := native_seed_test_mass task policy nu n actions B alpha q w
            (fun i => (hw i).le) (.read fun _ => true)
          simp only [nativeAccept, currentMode, Bool.false_eq_true, ↓reduceIte, rootRow,
            Set.setOf_true, Set.inter_univ, mul_one] at hmass
          change (nu.prod (sourceMixture alpha q w)).real
              (nativeEvent policy n ⟨actions, List.replicate n false, false⟩ B) =
            nu.real {u | u ∈ B ∧ zeroReplay policy u n = actions} *
              totalEvidence alpha q w actions at hmass
          rw [native_seed_test_mass task policy nu n actions B alpha q w (fun i => (hw i).le) T,
            hmass, mul_assoc, full_feature_readout task alpha q w ha actions _ T hZ.ne']

/-- Updating the source history agrees with normalized joint matrix transport. -/
def FeatureUpdates {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} (R : MassModel task alpha q)
    (feature : State → R.Carrier → ℝ) : Prop :=

  ∀ (h : State) (j : Side) (source : Source),
    let step := nativeStep task source h j
    let v := Matrix.mulVec (R.matrix j step.1) (feature h)
    0 < (∑ d, v d) → ∀ d, feature step.2 d = v d / (∑ e, v e)

private theorem atom_evidence_extension (alpha q : unitInterval) (ha : 0 < (alpha : ℝ))
    (actions : List Side) (j : Side) :
    atomEvidence alpha q (j :: actions) =
      atomEvidence alpha q actions * (1 - markerRate alpha q (parity actions) j) := by
  have hf := evidence_root_mass alpha q ha actions false
  have ht := evidence_root_mass alpha q ha actions true
  rw [atomEvidence, root_cylinder_extension, root_cylinder_extension]
  cases he : selectedParity (parity actions) j
  · simp only [rootZero, he, markerRate, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hf ht ⊢
    simp only [atomEvidence] at hf ⊢
    linear_combination (1 - (q : ℝ)) * hf
  · simp only [rootZero, he, markerRate, ↓reduceIte]
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hf ht ⊢
    simp only [atomEvidence] at ht ⊢
    linear_combination (1 - (q : ℝ)) * ht

private theorem full_zero_transport {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (h : State) (hs : h.stopped = false) (j : Side) :
    (Matrix.mulVec ((fullModel task alpha q).matrix j .zero) (fullFeature task alpha q w h)) =
      fun d => match d with
      | .inl (i,eta) => if eta = parity (j :: h.actions) then
          w i * atomEvidence alpha (q i) (j :: h.actions) / totalEvidence alpha q w h.actions
        else 0
      | .inr _ => 0 := by
  classical
  funext d
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [mul_comm _ (fullFeature task alpha q w h _)]
  rw [full_feature_pairing]
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  cases task <;> cases d with
  | inl p =>
      rcases p with ⟨i,eta⟩
      simp [fullModel, markerOutput, parity_cons, ite_and, mul_ite, eq_comm]
      split_ifs <;> simp_all [atom_evidence_extension alpha (q i) ha h.actions j] <;> ring
  | inr t => simp [fullModel, markerOutput]

private theorem full_marker_transport {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (h : State) (hs : h.stopped = false) (j : Side) :
    (Matrix.mulVec ((fullModel task alpha q).matrix j (markerOutput task (selectedParity (parity h.actions) j)))
       (fullFeature task alpha q w h)) =
      fun d => if d = .inr (terminalIndex task (selectedParity (parity h.actions) j)) then
        ∑ i, (w i * atomEvidence alpha (q i) h.actions / totalEvidence alpha q w h.actions) *
          markerRate alpha (q i) (parity h.actions) j else 0 := by
  classical
  funext d
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [mul_comm _ (fullFeature task alpha q w h _)]
  rw [full_feature_pairing]
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  cases task <;> simp [fullModel, markerOutput, mul_ite, Finset.sum_ite_irrel]

private theorem full_reject_transport {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (h : State) (hs : h.stopped = true) (j : Side) :
    (Matrix.mulVec ((fullModel task alpha q).matrix j .reject) (fullFeature task alpha q w h)) =
      fullFeature task alpha q w h := by
  classical
  funext d
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [mul_comm _ (fullFeature task alpha q w h _)]
  rw [full_feature_pairing]
  simp only [hs, ↓reduceIte]
  cases d <;> simp [fullFeature,fullModel,hs,eq_comm]

theorem full_feature_updates {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (hq : ∀ i, 0 < (q i : ℝ)) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1) :
    FeatureUpdates (fullModel task alpha q) (fullFeature task alpha q w) := by
  classical
  intro h j source
  change (0 < ∑ d, Matrix.mulVec ((fullModel task alpha q).matrix j (nativeStep task source h j).1)
    (fullFeature task alpha q w h) d) → ∀ d,
      fullFeature task alpha q w (nativeStep task source h j).2 d =
        Matrix.mulVec ((fullModel task alpha q).matrix j (nativeStep task source h j).1)
          (fullFeature task alpha q w h) d /
        (∑ e, Matrix.mulVec ((fullModel task alpha q).matrix j (nativeStep task source h j).1)
          (fullFeature task alpha q w h) e)
  cases hs : h.stopped with
  | true =>
      rw [show nativeStep task source h j = (.reject,h) from by simp [nativeStep,hs]]
      change 0 < _ → ∀ d, fullFeature task alpha q w h d = _
      rw [full_reject_transport task alpha q w h hs j,
        (full_feature_probability task alpha q w ha hq hw hsum h).1]
      simp
  | false =>
      cases hm : markerResponse source j (sideCount h.actions j) with
      | false =>
          rw [show nativeStep task source h j =
            (.zero, ⟨j :: h.actions, false :: h.replies, false⟩) from by simp [nativeStep,hs,hm]]
          change (0 < ∑ d, Matrix.mulVec ((fullModel task alpha q).matrix j .zero)
              (fullFeature task alpha q w h) d) → ∀ d,
            fullFeature task alpha q w ⟨j :: h.actions, false :: h.replies, false⟩ d =
              Matrix.mulVec ((fullModel task alpha q).matrix j .zero) (fullFeature task alpha q w h) d / _
          rw [full_zero_transport task alpha q w ha h hs j]
          have hZ := total_evidence_pos alpha q w ha hq hw hsum h.actions
          have hZ' := total_evidence_pos alpha q w ha hq hw hsum (j :: h.actions)
          have hmass :
              (∑ d : (fullModel task alpha q).Carrier,
                match d with
                | .inl (i,eta) => if eta = parity (j :: h.actions) then
                    w i * atomEvidence alpha (q i) (j :: h.actions) / totalEvidence alpha q w h.actions
                  else 0
                | .inr _ => 0) =
              totalEvidence alpha q w (j :: h.actions) / totalEvidence alpha q w h.actions := by
            rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
            simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]
            rw [← Finset.sum_div]
            rfl
          rw [hmass]
          intro hv d
          cases d with
          | inl p =>
              simp only [fullFeature, Bool.false_eq_true, ↓reduceIte, true_and]
              split_ifs <;> simp_all
              field_simp [hZ.ne',hZ'.ne']
          | inr t => simp [fullFeature]
      | true =>
          have hr : recoveredRoot ⟨j :: h.actions, true :: h.replies, true⟩ =
              selectedParity (parity h.actions) j := by simp [recoveredRoot,selected_parity]
          rw [show nativeStep task source h j =
            (markerOutput task (selectedParity (parity h.actions) j),
              ⟨j :: h.actions, true :: h.replies, true⟩) from by simp [nativeStep,hs,hm,markerOutput,← hr]]
          change 0 < _ → ∀ d, fullFeature task alpha q w ⟨j :: h.actions, true :: h.replies, true⟩ d = _
          rw [full_marker_transport task alpha q w h hs j]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          intro hv d
          cases d <;> simp [fullFeature,hr,ite_div,div_self hv.ne']

/-- Full finite carriers preserve native tests and normalized output successors. -/
theorem result {m : ℕ} (task : Task) (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (hq : ∀ i, 0 < (q i : ℝ)) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1) :
    (Fintype.card (fullModel task alpha q).Carrier = 4 * m + terminalCount task ∧
       (∀ j c, ∑ o, ∑ d, (fullModel task alpha q).matrix j o d c = 1) ∧
       (∀ j o d c, 0 ≤ (fullModel task alpha q).matrix j o d c) ∧
       FullNativeBridge.{u} w (fullModel task alpha q) (fullFeature task alpha q w)) ∧
      FeatureUpdates (fullModel task alpha q) (fullFeature task alpha q w) :=
  ⟨native_finite_test_realization task alpha q w ha hq hw hsum,
    full_feature_updates task alpha q w ha hq hw hsum⟩

end D5.S3.Observer.ProbabilisticClosure.FiniteAtomLinearRealization

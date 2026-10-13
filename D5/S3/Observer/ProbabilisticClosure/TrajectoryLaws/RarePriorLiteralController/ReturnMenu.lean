/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/ReturnMenu
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/ReturnMenu
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paid scratch erasure and native menu re-entry preserve committed-bank transactions. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.CurrentAcquisition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open RarePriorFiniteMonitor RarePriorResidentCode RarePriorSerialExecution
namespace LiveProducer.Return

set_option maxRecDepth 10000

def scratchWidth : ℕ := (runtimeSize) + ((runtimeSize+1) + ((runtimeSize) + ((runtimeSize*4) + ((runtimeSize+1) + ((runtimeSize+1) + ((runtimeSize+2) + ((793800) + ((793801) + ((793800) + ((12) + ((13) + ((frameKeyWidth) + ((frameWidth) + ((programWidth) + ((programWidth+1) + ((14) + ((15))))))))))))))))))

def controlCount : ℕ := 50

/-- A successor controller around the retained native segment. Only its current
core is cleared; the saved service and outer installation context are retained. -/

@[ext] structure State where
  current : Current.State
  menu : Motor 14
  pc : Fin 9
  cursor : Fin (scratchWidth+1)
  control : Fin (controlCount+1)
  deriving DecidableEq

abbrev Cell := Fin (runtimeSize) ⊕ Fin (runtimeSize+1) ⊕ Fin (runtimeSize) ⊕ Fin (runtimeSize*4) ⊕ Fin (runtimeSize+1) ⊕ Fin (runtimeSize+1) ⊕ Fin (runtimeSize+2) ⊕ Fin (793800) ⊕ Fin (793801) ⊕ Fin (793800) ⊕ Fin (12) ⊕ Fin (13) ⊕ Fin (frameKeyWidth) ⊕ Fin (frameWidth) ⊕ Fin (programWidth) ⊕ Fin (programWidth+1) ⊕ Fin (14) ⊕ Fin (15)


def cellCodec : Cell ≃ Fin scratchWidth := (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (Equiv.refl _))))))))))))))))))

def readCell (s : State) : Cell → Bool
  | (.inl i) => s.current.current.pre.tape i
  | (.inr (.inl i)) => s.current.current.pre.headBits i
  | (.inr (.inr (.inl i))) => s.current.current.key.tape i
  | (.inr (.inr (.inr (.inl i)))) => s.current.current.query i
  | (.inr (.inr (.inr (.inr (.inl i))))) => s.current.current.payload i
  | (.inr (.inr (.inr (.inr (.inr (.inl i)))))) => s.current.current.result.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))) => s.current.current.result.headBits i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))) => s.current.current.fields.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))) => s.current.current.fields.headBits i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))) => s.current.current.row.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))) => s.current.current.opcodes.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))) => s.current.current.opcodes.headBits i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))) => s.current.current.addressed.key i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))) => s.current.current.addressed.offset i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))) => s.current.current.addressed.head.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))))) => s.current.current.addressed.head.headBits i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))))) => s.menu.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))))))))))))) => s.menu.headBits i

/-- One physical scratch cell is written. No Runtime is decoded or assigned. -/

def clearCell (s : State) : Cell → State
  | (.inl i) => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with tape := Function.update s.current.current.pre.tape i false}}}}
  | (.inr (.inl i)) => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with headBits := Function.update s.current.current.pre.headBits i false}}}}
  | (.inr (.inr (.inl i))) => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with tape := Function.update s.current.current.key.tape i false}}}}
  | (.inr (.inr (.inr (.inl i)))) => {s with current := {s.current with current := {s.current.current with query := Function.update s.current.current.query i false}}}
  | (.inr (.inr (.inr (.inr (.inl i))))) => {s with current := {s.current with current := {s.current.current with payload := Function.update s.current.current.payload i false}}}
  | (.inr (.inr (.inr (.inr (.inr (.inl i)))))) => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with tape := Function.update s.current.current.result.tape i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))) => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with headBits := Function.update s.current.current.result.headBits i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))) => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with tape := Function.update s.current.current.fields.tape i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))) => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with headBits := Function.update s.current.current.fields.headBits i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))) => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with tape := Function.update s.current.current.row.tape i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))) => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with tape := Function.update s.current.current.opcodes.tape i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))) => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with headBits := Function.update s.current.current.opcodes.headBits i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))) => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with key := Function.update s.current.current.addressed.key i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))) => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with offset := Function.update s.current.current.addressed.offset i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))) => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with tape := Function.update s.current.current.addressed.head.tape i false}}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))))) => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with headBits := Function.update s.current.current.addressed.head.headBits i false}}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))))) => {s with menu := {s.menu with tape := Function.update s.menu.tape i false}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))))))))))))) => {s with menu := {s.menu with headBits := Function.update s.menu.headBits i false}}

private def zeroOffset : Fin frameWidth := ⟨0,by unfold frameWidth; omega⟩

/-- Every case is a paid finite rail-control set. These are still macro rail
instructions, separate from the single-bit scratch writes. -/

def setControl (s : State) (tag : Fin controlCount) : State :=
  match tag.val with
  | 0 => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with probe := 0}}}}
  | 1 => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with pc := .seek}}}}
  | 2 => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with latch := false}}}}
  | 3 => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with probe := 0}}}}
  | 4 => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with pc := .seek}}}}
  | 5 => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with latch := false}}}}
  | 6 => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with probe := 0}}}}
  | 7 => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with pc := .seek}}}}
  | 8 => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with latch := false}}}}
  | 9 => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with probe := 0}}}}
  | 10 => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with pc := .seek}}}}
  | 11 => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with latch := false}}}}
  | 12 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with probe := 0}}}}}
  | 13 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with pc := .seek}}}}}
  | 14 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with latch := false}}}}}
  | 15 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with tail := 0}}}}
  | 16 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with probe := 0}}}}
  | 17 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with carry := 0}}}}
  | 18 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with query := 0}}}}
  | 19 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with pc := 0}}}}
  | 20 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with tail := 0}}}}
  | 21 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with probe := 0}}}}
  | 22 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with carry := 0}}}}
  | 23 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with query := 0}}}}
  | 24 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with pc := 0}}}}
  | 25 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with query := ⟨0,by unfold runtimeSize; omega⟩}}}}
  | 26 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with row := 0}}}}
  | 27 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with cursor := 0}}}}
  | 28 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with accumulator := 0}}}}
  | 29 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with equalFlag := true}}}}
  | 30 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with pc := 0}}}}
  | 31 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with baseProbe := 0}}}}}
  | 32 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with keyProbe := 0}}}}}
  | 33 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with strideProbe := 0}}}}}
  | 34 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with offsetProbe := 0}}}}}
  | 35 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with pc := .baseTest}}}}}
  | 36 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with returnBase := true}}}}}
  | 37 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with returnStride := false}}}}}
  | 38 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with latch := false}}}}}
  | 39 => {s with current := {s.current with current := {s.current.current with role := false}}}
  | 40 => {s with current := {s.current with current := {s.current.current with operation := 0}}}
  | 41 => {s with current := {s.current with current := {s.current.current with slot := 0}}}
  | 42 => {s with current := {s.current with current := {s.current.current with offset := zeroOffset}}}
  | 43 => {s with current := {s.current with current := {s.current.current with bankProbe := 0}}}
  | 44 => {s with current := {s.current with current := {s.current.current with bankLatch := false}}}
  | 45 => {s with current := {s.current with current := {s.current.current with phase := 0}}}
  | 46 => {s with current := {s.current with acquiring := false}}
  | 47 => {s with menu := {s.menu with probe := 0}}
  | 48 => {s with menu := {s.menu with pc := .seek}}
  | 49 => {s with menu := {s.menu with latch := false}}
  | _ => s

/-- The menu taps the last bit of each control block in the committed bank.
The arithmetic tap map is a macro, and the fourteen copied bits are paid. -/
def menuROM (s : State) (i : Fin 14) : Bool :=
  s.current.current.actual ⟨(i.val+1)*(56700*(6023*4))-1,by
    have := i.isLt
    unfold runtimeSize
    omega⟩

def menuClass (tape : Fin 14 → Bool) : Fin 4 :=
  if tape 12 then 3 else if tape 11 then 2 else if tape 10 then 1 else 0

def actualRequest (s : State) : Bool :=
  if s.pc = 0 then Current.actualRequest s.current else decide (s.pc = 7)
def freshRequest (_ : State) : Bool := false

/-- Zero executes the unchanged Current segment; one acknowledges its return;
two erases scratch; three sets rail controls; four is core-ready; five copies
committed control; six dispatches that copied menu; seven acquires; eight stops. -/

def step (s : State) (source fresh : Letter) : State :=
  match s.pc.val with
  | 0 => if s.current.current.phase = 11 then {s with pc := 1}
    else {s with current := Current.step s.current source fresh}
  | 1 => {s with pc := 2,cursor := 0}
  | 2 => if h : s.cursor.val < scratchWidth then
      {(clearCell s (cellCodec.symm ⟨s.cursor.val,h⟩)) with
        cursor := ⟨s.cursor.val+1,by omega⟩}
    else {s with pc := 3,control := 0}
  | 3 => if h : s.control.val < controlCount then
      {(setControl s ⟨s.control.val,h⟩) with control := ⟨s.control.val+1,by omega⟩}
    else {s with pc := 4,cursor := 0,control := 0}
  | 4 => {s with pc := 5}
  | 5 => if s.menu.pc = .halt then {s with pc := 6}
    else {s with menu := motorStep (menuROM s) s.menu}
  | 6 => match (menuClass s.menu.tape).val with
      | 0 => {s with pc := 7}
      | 1 => {s with pc := 0,current := {s.current with current := {s.current.current with operation := 2}}}
      | 2 => {s with pc := 0,current := {s.current with current := {s.current.current with operation := 3}}}
      | _ => {s with pc := 8}
  | 7 => {s with pc := 0, current := {s.current with
      current := {s.current.current with operation := Fin.castAdd 2 source}}}
  | _ => s


private theorem current_ports (s : Current.State) (a b c d : Letter)
    (h : Current.actualRequest s = false) : Current.step s a b = Current.step s c d := by
  cases ha : s.acquiring <;> cases hr : s.current.role <;>
    simp [Current.actualRequest,Current.step,ha,hr] at h ⊢

private theorem ports (s : State) (a b c d : Letter)
    (h : actualRequest s = false) : step s a b = step s c d := by
  have hlt := s.pc.isLt
  interval_cases hp : s.pc.val
  · have hpc : s.pc = 0 := Fin.ext hp
    have hh : Current.actualRequest s.current = false := by
      simpa only [actualRequest,hpc,↓reduceIte] using h
    simp only [step,hp]
    split
    · simp only [step,hp] <;> rfl
    · rw [current_ports s.current a b c d hh]
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · have hpc : s.pc = 7 := Fin.ext hp
    simp [actualRequest,hpc] at h
  · simp only [step,hp] <;> rfl

@[irreducible] def run (s : State) (source fresh : Letter) (n : ℕ) : State :=
  (fun q => step q source fresh)^[n] s

def entry (s : Current.State) : State := ⟨s,motorEntry 14,0,0,0⟩

def coreReady (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) : State :=
  ⟨Current.entry saved image a c false 0,motorEntry 14,4,0,0⟩

private noncomputable def cellDecidableEq : DecidableEq Cell := Classical.decEq Cell
attribute [local instance] cellDecidableEq


private theorem read_clear (s : State) (c d : Cell) :
    readCell (clearCell s c) d = if d = c then false else readCell s d := by
  rcases c with i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i <;> rcases d with j | j | j | j | j | j | j | j | j | j | j | j | j | j | j | j | j | j <;>
    simp [readCell,clearCell,Function.update_apply]

private theorem clear_frame (s : State) (c : Cell) :
    (clearCell s c).current.saved = s.current.saved ∧
    (clearCell s c).current.current.actual = s.current.current.actual ∧
    (clearCell s c).current.current.synthetic = s.current.current.synthetic ∧
    (clearCell s c).current.current.addressed.outer = s.current.current.addressed.outer ∧
    (clearCell s c).pc = s.pc ∧ (clearCell s c).cursor = s.cursor ∧
    (clearCell s c).control = s.control := by
  rcases c with i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem run_zero (s : State) (a b : Letter) : run s a b 0 = s := by
  simp only [run,Function.iterate_zero,id_eq]

private theorem run_one (s : State) (a b : Letter) : run s a b 1 = step s a b := by
  simp only [run,Function.iterate_one]

private theorem run_succ (s : State) (a b : Letter) (n : ℕ) :
    run s a b (n+1) = step (run s a b n) a b := by
  simp only [run,Function.iterate_succ_apply']

private theorem run_cons (s : State) (a b : Letter) (n : ℕ) :
    run s a b (n+1) = run (step s a b) a b n := by
  simp only [run,Function.iterate_succ_apply]

private theorem run_add (s : State) (a b : Letter) (m n : ℕ) :
    run s a b (m+n) = run (run s a b m) a b n := by
  simp only [run,Nat.add_comm m n,Function.iterate_add_apply]


def output (s : State) : Option Bool :=
  if s.pc = 0 then Current.output s.current else none

def trace (s : State) (a b : Letter) : ℕ → List Bool
  | 0 => []
  | n+1 => (output s).toList ++ trace (step s a b) a b n


/-- A pointwise prefix-erasure invariant for the actual single-cell loop. -/

private theorem erased_prefix (s : State) (hpc : s.pc = 2) (hc : s.cursor = 0)
    (n : ℕ) (hn : n ≤ scratchWidth) :
    let q := run s 0 0 n
    q.pc = 2 ∧ q.cursor.val = n ∧
    q.current.saved = s.current.saved ∧
    q.current.current.actual = s.current.current.actual ∧
    q.current.current.synthetic = s.current.current.synthetic ∧
    q.current.current.addressed.outer = s.current.current.addressed.outer ∧
    (∀ i : Fin scratchWidth, readCell q (cellCodec.symm i) =
      if i.val < n then false else readCell s (cellCodec.symm i)) := by
  induction n with
  | zero =>
      simp only [run,Function.iterate_zero,id_eq,hpc,hc,Fin.val_zero,
        not_lt_zero',↓reduceIte,true_and]
      exact fun _ => trivial
  | succ n ih =>
      have hh := ih (by omega)
      let p := run s 0 0 n
      have hbound : p.cursor.val < scratchWidth := by rw [hh.2.1]; omega
      let cell : Fin scratchWidth := ⟨p.cursor.val,hbound⟩
      have hs : step p 0 0 =
          {(clearCell p (cellCodec.symm cell)) with cursor := ⟨p.cursor.val+1,by omega⟩} := by
        have hpp : p.pc = 2 := hh.1
        simp [step,hpp,hbound,cell,clear_frame]
      have hf := clear_frame p (cellCodec.symm cell)
      have hrun : run s 0 0 (n+1) =
          {(clearCell p (cellCodec.symm cell)) with cursor := ⟨p.cursor.val+1,by omega⟩} := by
        rw [run_succ]
        exact hs
      rw [hrun]
      dsimp only
      refine ⟨hf.2.2.2.2.1.trans hh.1,?_,hf.1.trans hh.2.2.1,
        hf.2.1.trans hh.2.2.2.1,hf.2.2.1.trans hh.2.2.2.2.1,
        hf.2.2.2.1.trans hh.2.2.2.2.2.1,?_⟩
      · change p.cursor.val+1 = n+1
        rw [hh.2.1]
      · intro i
        change readCell (clearCell p (cellCodec.symm cell)) (cellCodec.symm i) = _
        rw [read_clear,hh.2.2.2.2.2.2 i]
        have he : (cellCodec.symm i = cellCodec.symm cell) ↔ i.val = n := by
          rw [cellCodec.symm.injective.eq_iff,Fin.ext_iff]
          change i.val = p.cursor.val ↔ i.val = n
          rw [hh.2.1]
        simp only [he]
        by_cases h : i.val = n
        · simp [h]
        · have hh : (i.val < n) ↔ (i.val < n+1) := by omega
          simp only [h,↓reduceIte,hh]

private def controlCheckpoint (s : State) (n : ℕ) (hn : n ≤ controlCount) : State :=
  {s with
    current := {s.current with
      current := {s.current.current with
        pre := {s.current.current.pre with
          probe := (if 0 < n then 0 else s.current.current.pre.probe),
          pc := (if 1 < n then .seek else s.current.current.pre.pc),
          latch := (if 2 < n then false else s.current.current.pre.latch)
        },
        result := {s.current.current.result with
          probe := (if 3 < n then 0 else s.current.current.result.probe),
          pc := (if 4 < n then .seek else s.current.current.result.pc),
          latch := (if 5 < n then false else s.current.current.result.latch)
        },
        fields := {s.current.current.fields with
          probe := (if 6 < n then 0 else s.current.current.fields.probe),
          pc := (if 7 < n then .seek else s.current.current.fields.pc),
          latch := (if 8 < n then false else s.current.current.fields.latch)
        },
        opcodes := {s.current.current.opcodes with
          probe := (if 9 < n then 0 else s.current.current.opcodes.probe),
          pc := (if 10 < n then .seek else s.current.current.opcodes.pc),
          latch := (if 11 < n then false else s.current.current.opcodes.latch)
        },
        addressed := {s.current.current.addressed with
          head := {s.current.current.addressed.head with
            probe := (if 12 < n then 0 else s.current.current.addressed.head.probe),
            pc := (if 13 < n then .seek else s.current.current.addressed.head.pc),
            latch := (if 14 < n then false else s.current.current.addressed.head.latch)
          },
          control := {s.current.current.addressed.control with
            baseProbe := (if 31 < n then 0 else s.current.current.addressed.control.baseProbe),
            keyProbe := (if 32 < n then 0 else s.current.current.addressed.control.keyProbe),
            strideProbe := (if 33 < n then 0 else s.current.current.addressed.control.strideProbe),
            offsetProbe := (if 34 < n then 0 else s.current.current.addressed.control.offsetProbe),
            pc := (if 35 < n then .baseTest else s.current.current.addressed.control.pc),
            returnBase := (if 36 < n then true else s.current.current.addressed.control.returnBase),
            returnStride := (if 37 < n then false else s.current.current.addressed.control.returnStride),
            latch := (if 38 < n then false else s.current.current.addressed.control.latch)
          }
        },
        key := {s.current.current.key with
          tail := (if 15 < n then 0 else s.current.current.key.tail),
          probe := (if 16 < n then 0 else s.current.current.key.probe),
          carry := (if 17 < n then 0 else s.current.current.key.carry),
          query := (if 18 < n then 0 else s.current.current.key.query),
          pc := (if 19 < n then 0 else s.current.current.key.pc)
        },
        row := {s.current.current.row with
          tail := (if 20 < n then 0 else s.current.current.row.tail),
          probe := (if 21 < n then 0 else s.current.current.row.probe),
          carry := (if 22 < n then 0 else s.current.current.row.carry),
          query := (if 23 < n then 0 else s.current.current.row.query),
          pc := (if 24 < n then 0 else s.current.current.row.pc)
        },
        native := {s.current.current.native with
          query := (if 25 < n then ⟨0,by unfold runtimeSize; omega⟩ else s.current.current.native.query),
          row := (if 26 < n then 0 else s.current.current.native.row),
          cursor := (if 27 < n then 0 else s.current.current.native.cursor),
          accumulator := (if 28 < n then 0 else s.current.current.native.accumulator),
          equalFlag := (if 29 < n then true else s.current.current.native.equalFlag),
          pc := (if 30 < n then 0 else s.current.current.native.pc)
        },
        role := (if 39 < n then false else s.current.current.role),
        operation := (if 40 < n then 0 else s.current.current.operation),
        slot := (if 41 < n then 0 else s.current.current.slot),
        offset := (if 42 < n then zeroOffset else s.current.current.offset),
        bankProbe := (if 43 < n then 0 else s.current.current.bankProbe),
        bankLatch := (if 44 < n then false else s.current.current.bankLatch),
        phase := (if 45 < n then 0 else s.current.current.phase)
      },
      acquiring := if 46 < n then false else s.current.acquiring},
    menu := {s.menu with
      probe := if 47 < n then 0 else s.menu.probe,
      pc := if 48 < n then .seek else s.menu.pc,
      latch := if 49 < n then false else s.menu.latch},
    pc := 3,control := ⟨n,by omega⟩}




private theorem control_cycle (s : State) (n : ℕ) (hn : n < controlCount) :
    step (controlCheckpoint s n (by omega)) 0 0 = controlCheckpoint s (n+1) (by omega) := by
  have h : n < 50 := hn
  interval_cases n <;> rfl



private theorem control_prefix (s : State) (n : ℕ) (hn : n ≤ controlCount) :
    run {s with pc := 3,control := 0} 0 0 n = controlCheckpoint s n hn := by
  induction n with
  | zero => rw [run_zero]; rfl
  | succ n ih =>
      rw [run_succ]
      change step (run {s with pc := 3,control := 0} 0 0 n) 0 0 = _
      rw [ih (by omega)]
      exact control_cycle s n (by omega)


private def normalized (s : State) : State :=
  {controlCheckpoint s controlCount le_rfl with pc := 4,cursor := 0,control := 0}



private theorem controls_execute (s : State) :
    run {s with pc := 3,control := 0} 0 0 (controlCount+1) = normalized s := by
  rw [run_succ]
  change step (run {s with pc := 3,control := 0} 0 0 controlCount) 0 0 = _
  rw [control_prefix s controlCount le_rfl]
  rfl



private theorem normalized_ready (s : State) (hz : ∀ c, readCell s c = false) :
    normalized s = coreReady s.current.saved s.current.current.addressed.outer
      s.current.current.actual s.current.current.synthetic := by
  apply State.ext
  · apply Current.State.ext
    · rfl
    · apply CurrentBank.State.ext
      · apply AddressState.ext
        · rfl
        · rfl
        · funext i
          exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))
        · funext i
          exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))
        · apply Motor.ext
          · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))))
          · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))))
          · rfl
          · rfl
          · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · apply Motor.ext
        · funext i; exact hz (.inl i)
        · funext i; exact hz (.inr (.inl i))
        · rfl
        · rfl
        · rfl
      · apply Key.ext
        · funext i; exact hz (.inr (.inr (.inl i)))
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      · funext i; exact hz (.inr (.inr (.inr (.inl i))))
      · rfl
      · funext i; exact hz (.inr (.inr (.inr (.inr (.inl i)))))
      · apply Motor.ext
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inl i))))))
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))
        · rfl
        · rfl
        · rfl
      · apply Motor.ext
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))
        · rfl
        · rfl
        · rfl
      · apply Key.ext
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · apply Motor.ext
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))
        · rfl
        · rfl
        · rfl
    · rfl
  · apply Motor.ext
    · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))))))
    · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))))))))))))))
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl



private theorem retired_ready (s : State) (hp : s.pc = 0)
    (hr : s.current.current.phase = 11) :
    run s 0 0 (2+scratchWidth+1+(controlCount+1)) =
      coreReady s.current.saved s.current.current.addressed.outer
        s.current.current.actual s.current.current.synthetic := by
  let start : State := {s with pc := 2,cursor := 0}
  have hs : run s 0 0 2 = start := by simp [run,step,hp,hr,start]
  have he := erased_prefix start rfl rfl scratchWidth le_rfl
  generalize heq : run start 0 0 scratchWidth = erased at he
  have hz : ∀ c, readCell erased c = false := by
    intro c
    have h := he.2.2.2.2.2.2 (cellCodec c)
    simpa only [cellCodec.symm_apply_apply,Fin.isLt,↓reduceIte] using h
  have hc : step erased 0 0 = {erased with pc := 3,control := 0} := by
    have hn : ¬ erased.cursor.val < scratchWidth := by rw [he.2.1]; omega
    have hep : erased.pc = 2 := he.1
    simp [step,hep,hn]
  rw [run_add s 0 0 (2+scratchWidth+1) (controlCount+1),
    run_add s 0 0 (2+scratchWidth) 1,run_add s 0 0 2 scratchWidth,hs,heq,run_one]
  change run (step erased 0 0) 0 0 (controlCount+1) = _
  rw [hc,controls_execute,normalized_ready erased hz]
  exact by rw [he.2.2.1,he.2.2.2.2.2.1,he.2.2.2.1,he.2.2.2.2.1]




private theorem menu_rom (s : State) (z : Runtime)
    (ha : s.current.current.actual = word (runtimeCodec z)) :
    menuROM s = word (RarePriorResidentCode.controlCodec z.fields.control) := by
  funext i
  simp only [menuROM,ha,word]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hv : (runtimeCodec z).val =
      (RarePriorResidentCode.controlCodec z.fields.control).val*(56700*(6023*4))+
      (registersCodec z.fields.registers).val*(6023*4)+
      (monitorCodec z.monitor).val*4+(modeCodec z.mode).val := by
    change (finProdFinEquiv (finProdFinEquiv
      (RarePriorResidentCode.controlCodec z.fields.control,registersCodec z.fields.registers),
      finProdFinEquiv (monitorCodec z.monitor,modeCodec z.mode))).val = _
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [hv]
  have := (registersCodec z.fields.registers).isLt
  have := (monitorCodec z.monitor).isLt
  have := (modeCodec z.mode).isLt
  omega


private theorem menu_exit (s : State) (n : ℕ) (hp : s.pc = 5)
    (he : (motorRun (menuROM s) s.menu n).pc = .halt) :
    ∃ t ≤ n+1, run s 0 0 t =
      {s with menu := motorRun (menuROM s) s.menu n,pc := 6} := by
  induction n generalizing s with
  | zero =>
      have hh : s.menu.pc = .halt := he
      exact ⟨1,by omega,by simp [run,step,hp,hh,motorRun]⟩
  | succ n ih =>
      by_cases hh : s.menu.pc = .halt
      · have hf : motorStep (menuROM s) s.menu = s.menu := by simp [motorStep,hh]
        exact ⟨1,by omega,by simp [run,step,hp,hh,motorRun,Function.iterate_fixed hf]⟩
      · let q : State := {s with menu := motorStep (menuROM s) s.menu}
        have hq : step s 0 0 = q := by simp [step,hp,hh,q]
        have hqe : (motorRun (menuROM q) q.menu n).pc = .halt := by
          rw [motorRun,Function.iterate_succ_apply] at he
          exact he
        obtain ⟨t,ht,heq⟩ := ih q hp hqe
        refine ⟨t+1,by omega,?_⟩
        rw [run_cons,hq,heq]
        have hrom : menuROM q = menuROM s := rfl
        rw [hrom]
        simp only [q,motorRun,Function.iterate_succ_apply]



private theorem ready_menu (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (z : Runtime) (ha : a = word (runtimeCodec z)) :
    ∃ t, ∃ q : State, run (coreReady saved image a c) 0 0 t = q ∧ q.pc = 6 ∧
      q.current = (coreReady saved image a c).current ∧
      q.menu.tape = word (RarePriorResidentCode.controlCodec z.fields.control) := by
  let s : State := {coreReady saved image a c with pc := 5}
  have hrom := menu_rom s z ha
  have he := motor_return (word (RarePriorResidentCode.controlCodec z.fields.control))
  have hp : (motorRun (menuROM s) s.menu (copyTime 14)).pc = .halt := by
    rw [hrom]
    exact he.1
  obtain ⟨t,_,ht⟩ := menu_exit s (copyTime 14) rfl hp
  refine ⟨1+t,{s with menu := motorRun (menuROM s) s.menu (copyTime 14),pc := 6},?_,rfl,rfl,?_⟩
  · rw [run_add]
    have hh : run (coreReady saved image a c) 0 0 1 = s := by rw [run_one]; rfl
    rw [hh,ht]
  · change (motorRun (menuROM s) s.menu (copyTime 14)).tape = _
    rw [hrom]
    exact he.2

private theorem current_add (s : Current.State) (m n : ℕ) :
    Current.run s 0 0 (m+n) = Current.run (Current.run s 0 0 m) 0 0 n := by
  simp only [Current.run,Nat.add_comm m n,Function.iterate_add_apply]



private theorem native_prefix (s : State) (hp : s.pc = 0) (n : ℕ)
    (hbefore : ∀ k, k < n → (Current.run s.current 0 0 k).current.phase ≠ 11) :
    run s 0 0 n = {s with current := Current.run s.current 0 0 n} := by
  induction n with
  | zero => simp only [run_zero,Current.run,Function.iterate_zero,id_eq]
  | succ n ih =>
      have hi := ih (fun k hk => hbefore k (by omega))
      rw [run_succ]
      change step (run s 0 0 n) 0 0 = _
      rw [hi]
      have hn := hbefore n (by omega)
      simp only [step,hp,Fin.val_zero,hn,↓reduceIte]
      simp only [Current.run,Function.iterate_succ_apply']




private theorem current_fixed (s : Current.State) (ha : s.acquiring = false)
    (hp : s.current.phase = 11) : Current.step s 0 0 = s := by
  simp only [Current.step,ha,Bool.false_eq_true,↓reduceIte]
  have hf : CurrentBank.step s.current = s.current := by simp [CurrentBank.step,hp]
  rw [hf]
  apply Current.State.ext <;> first | rfl | exact ha.symm

/-- First-return time is proof-side only. The successor executes the retained
segment unchanged through that cut, without storing a clock. -/

private theorem native_join (p q : Current.State) (n : ℕ) (hp : p.acquiring = false)
    (he : Current.run p 0 0 n = q) (hq : q.current.phase = 11) :
    ∃ t, t ≤ n ∧ run (entry p) 0 0 t = entry q ∧
      Current.run p 0 0 t = q ∧
      (∀ k, k < t → (Current.run p 0 0 k).current.phase ≠ 11) := by
  have hex : ∃ t, (Current.run p 0 0 t).current.phase = 11 := ⟨n,by rw [he]; exact hq⟩
  let t := Nat.find hex
  have ht : (Current.run p 0 0 t).current.phase = 11 := Nat.find_spec hex
  have hle : t ≤ n := Nat.find_min' hex (by rw [he]; exact hq)
  have hbefore : ∀ k, k < t → (Current.run p 0 0 k).current.phase ≠ 11 := by
    intro k hk
    exact Nat.find_min hex hk
  have hj := native_prefix (entry p) rfl t hbefore
  have hacq : (Current.run p 0 0 t).acquiring = false := by
    rw [Current.passive_run p hp]; exact hp
  have hf : Current.step (Current.run p 0 0 t) 0 0 = Current.run p 0 0 t := by
    exact current_fixed _ hacq ht
  have heq : Current.run p 0 0 t = q := by
    rw [show n = t+(n-t) by omega,current_add] at he
    rw [Current.run,Function.iterate_fixed hf] at he
    exact he
  refine ⟨t,hle,?_,heq,hbefore⟩
  simpa only [heq,entry] using hj

/-- External original-menu semantics, absent from all transition inputs. -/
def gate (z : Runtime) (source : Letter) : Option Operation :=
  match z.fields.control with
  | .fourth (.pending b) => some (.stop b)
  | .fourth .delivered => none
  | _ => some (.read source)

private def menuRole (c : NativeControl) : Fin 4 :=
  match c with
  | .fourth (.pending b) => if b = 0 then 1 else 2
  | .fourth .delivered => 3
  | _ => 0

private theorem menu_class (c : NativeControl) :
    menuClass (word (RarePriorResidentCode.controlCodec c)) = menuRole c := by
  cases c with
  | seed a => cases a with
      | none => rfl
      | some b => fin_cases b <;> rfl
  | early t phase => fin_cases t <;> cases phase <;> rfl
  | fourth c => cases c with
      | active phase => cases phase <;> rfl
      | pending b => fin_cases b <;> rfl
      | delivered => rfl



private theorem copied_gate (s : State) (z : Runtime) (hp : s.pc = 6)
    (hc : s.menu.tape = word (RarePriorResidentCode.controlCodec z.fields.control))
    (x y : Letter) :
    (gate z x = none → (step s x y).pc = 8 ∧ actualRequest (step s x y) = false) ∧
    (∀ op, gate z x = some op →
      ∃ t : ℕ, (t = 1 ∨ t = 2) ∧
        ∃ q : State, run s x y t = q ∧ q.pc = 0 ∧
          q.current = {s.current with current := {s.current.current with operation := operationCodec op}}) := by
  have hm : menuClass s.menu.tape = menuRole z.fields.control := by rw [hc,menu_class]
  have active (hr : menuRole z.fields.control = 0) (hg : gate z x = some (.read x)) :
      (gate z x = none → (step s x y).pc = 8 ∧ actualRequest (step s x y) = false) ∧
      (∀ op, gate z x = some op → ∃ t : ℕ, (t = 1 ∨ t = 2) ∧
        ∃ q : State, run s x y t = q ∧ q.pc = 0 ∧
          q.current = {s.current with current := {s.current.current with operation := operationCodec op}}) := by
    have hs : step s x y = {s with pc := 7} := by simp only [step,hp,Fin.val_ofNat,hm,hr]; rfl
    constructor
    · intro h; rw [hg] at h; cases h
    · intro op h
      rw [hg] at h
      have ho : op = .read x := (Option.some.inj h).symm
      subst op
      refine ⟨2,Or.inr rfl,
        {s with pc := 0,current := {s.current with current := {s.current.current with operation := Fin.castAdd 2 x}}},
        ?_,rfl,rfl⟩
      rw [run_succ s x y 1,run_one]
      rw [hs]
      rfl
  cases hz : z.fields.control with
  | seed a => exact active (by simp only [hz,menuRole]) (by simp [gate,hz])
  | early t phase => exact active (by simp only [hz,menuRole]) (by simp [gate,hz])
  | fourth c => cases c with
      | active phase => exact active (by simp only [hz,menuRole]) (by simp [gate,hz])
      | pending b =>
          constructor
          · intro h; simp [gate,hz] at h
          · intro op h
            have ho : op = .stop b := (Option.some.inj (by simpa [gate,hz] using h)).symm
            subst op
            refine ⟨1,Or.inl rfl,
              {s with pc := 0,current := {s.current with current := {s.current.current with operation := operationCodec (.stop b)}}},
              ?_,rfl,rfl⟩
            rw [run_one]
            fin_cases b <;> simp only [step,hp,Fin.val_ofNat,hm,hz,menuRole] <;> rfl
      | delivered =>
          constructor
          · intro _
            have hs : step s x y = {s with pc := 8} := by
              simp only [step,hp,Fin.val_ofNat,hm,hz,menuRole]; rfl
            rw [hs]
            exact ⟨rfl,rfl⟩
          · intro op h; simp [gate,hz] at h

/-- The paid menu round retains the whole core-ready bank and launches only
its actual original menu operation. No supplied ready-role selector is used. -/
def MenuRound (r : State) (z : Runtime) : Prop :=
  ∃ t, ∃ m : State, run r 0 0 t = m ∧ m.pc = 6 ∧ m.current = r.current ∧
    m.menu.tape = word (RarePriorResidentCode.controlCodec z.fields.control) ∧
    (∀ x y : Letter,
      (gate z x = none → (step m x y).pc = 8 ∧ actualRequest (step m x y) = false) ∧
      (∀ op, gate z x = some op → ∃ u : ℕ, (u = 1 ∨ u = 2) ∧
        ∃ q : State, run m x y u = q ∧ q.pc = 0 ∧
          q.current = {r.current with current := {r.current.current with operation := operationCodec op}}))

private theorem menu_round (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (z : Runtime) (ha : a = word (runtimeCodec z)) :
    MenuRound (coreReady saved image a c) z := by
  obtain ⟨t,m,hm,hp,hcurrent,hmenu⟩ := ready_menu saved image a c z ha
  refine ⟨t,m,hm,hp,hcurrent,hmenu,?_⟩
  intro x y
  have h := copied_gate m z hp hmenu x y
  rw [hcurrent] at h
  exact h

@[irreducible] def code (s : State) : List Bool :=
  Current.code s.current ++ motorCode s.menu ++ bitCode s.pc ++
    bitCode s.cursor ++ bitCode s.control

def width : ℕ := Current.width+motorWidth 14+9+(scratchWidth+1)+(controlCount+1)

@[irreducible] def staticImage : List Bool := Current.staticImage ++
  (List.ofFn (fun i : Fin 9 => bitCode i)).flatten ++
  (List.ofFn (fun i : Fin 50 => bitCode i)).flatten

def staticWidth : ℕ := Current.staticWidth+81+2500

private theorem static_length : staticImage.length = staticWidth := by
  simp only [staticImage,staticWidth,List.length_append,Current.static_length,
    LiveProducer.opcode_length]

def bound : ℕ := programWidth+staticWidth+width+1

private theorem code_length (s : State) : (code s).length = width := by
  simp only [code,width,List.length_append,Current.code_length,motor_code_length,bit_code_length]



private theorem code_injective : Function.Injective code := by
  intro s t h
  simp only [code,List.append_assoc] at h
  obtain ⟨hc,h⟩ := split_block (Current.code s.current) (Current.code t.current) _ _
    Current.width (Current.code_length _) (Current.code_length _) h
  obtain ⟨hm,h⟩ := split_block (motorCode s.menu) (motorCode t.menu) _ _
    (motorWidth 14) (motor_code_length _) (motor_code_length _) h
  obtain ⟨hp,h⟩ := split_block (bitCode s.pc) (bitCode t.pc) _ _
    9 (bit_code_length _) (bit_code_length _) h
  obtain ⟨hi,hk⟩ := split_block (bitCode s.cursor) (bitCode t.cursor) _ _
    (scratchWidth+1) (bit_code_length _) (bit_code_length _) h
  apply State.ext
  · exact Current.code_injective hc
  · exact motor_encoding hm
  · exact bit_code_injective hp
  · exact bit_code_injective hi
  · exact bit_code_injective hk


set_option maxHeartbeats 2000000 in
private theorem charged (s : State) :
    programImage.length+staticImage.length+(code s).length < bound := by
  simp only [programImage,List.length_ofFn,static_length,code_length,bound]
  omega

private theorem native_nonretired (s : State) (hp : s.pc = 0)
    (ha : s.current.acquiring = false) (n : ℕ)
    (hn : (Current.run s.current 0 0 n).current.phase ≠ 11) :
    run s 0 0 n = {s with current := Current.run s.current 0 0 n} := by
  apply native_prefix s hp n
  intro k hk hr
  let p := Current.run s.current 0 0 k
  have hpa : p.acquiring = false := by
    change (Current.run s.current 0 0 k).acquiring = false
    rw [Current.passive_run s.current ha]; exact ha
  have hf : Current.step p 0 0 = p := by
    exact current_fixed p hpa hr
  have he : Current.run s.current 0 0 n = p := by
    rw [show n = k+(n-k) by omega,current_add]
    exact Function.iterate_fixed hf (n-k)
  exact hn (by rw [he]; exact hr)



private theorem next_query (s : State) (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (z : Runtime) (op : Operation)
    (hp : s.pc = 0) (hs : s.current = Current.entry saved image a c false (operationCodec op))
    (ha : a = word (runtimeCodec z)) :
    ∃ t, ∃ q : State, run s 0 0 t = q ∧ q.pc = 0 ∧ q.current.current.phase = 13 ∧
      q.current.current.query = word (nativeKeyCodec (z,op)) ∧
      q.current.current.actual = a ∧ q.current.current.synthetic = c ∧
      q.current.current.operation = operationCodec op := by
  obtain ⟨t,p,ht,hphase,hquery,_,hactual,hsynthetic,hop,_⟩ :=
    CurrentBank.bank_query image a c false z op (by simpa only [Bool.false_eq_true,↓reduceIte] using ha)
  have he : Current.run s.current 0 0 t = {s.current with current := p} := by
    rw [hs,Current.passive_run _ rfl]
    change {Current.entry saved image a c false (operationCodec op) with current := CurrentBank.run (CurrentBank.entry image a c false (operationCodec op)) t} = _
    rw [ht]
  have hacq : s.current.acquiring = false := by rw [hs]; rfl
  have hn : (Current.run s.current 0 0 t).current.phase ≠ 11 := by rw [he]; simp [hphase]
  have hrun := native_nonretired s hp hacq t hn
  refine ⟨t,{s with current := {s.current with current := p}},?_,hp,hphase,hquery,hactual,hsynthetic,hop⟩
  simpa only [he] using hrun

/-- The committed menu and its next bank query are executed on the same core.
The saved service and outer image context are not cleared by this relation. -/
def NextRound (r : State) (z : Runtime) : Prop :=
  ∃ t, ∃ m : State, run r 0 0 t = m ∧ m.pc = 6 ∧ m.current = r.current ∧
    m.menu.tape = word (RarePriorResidentCode.controlCodec z.fields.control) ∧
    (∀ x y : Letter,
      (gate z x = none → (step m x y).pc = 8 ∧ actualRequest (step m x y) = false) ∧
      (∀ op, gate z x = some op → ∃ u : ℕ, (u = 1 ∨ u = 2) ∧
        ∃ q : State, run m x y u = q ∧ q.pc = 0 ∧
          q.current = {r.current with current := {r.current.current with operation := operationCodec op}} ∧
          ∃ v, ∃ f : State, run q 0 0 v = f ∧ f.pc = 0 ∧ f.current.current.phase = 13 ∧
            f.current.current.query = word (nativeKeyCodec (z,op)) ∧
            f.current.current.actual = r.current.current.actual ∧
            f.current.current.synthetic = r.current.current.synthetic ∧
            f.current.current.operation = operationCodec op))




private theorem next_round (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (z : Runtime) (ha : a = word (runtimeCodec z)) :
    NextRound (coreReady saved image a c) z := by
  obtain ⟨t,m,hm,hp,hcurrent,hmenu,hgate⟩ := menu_round saved image a c z ha
  refine ⟨t,m,hm,hp,hcurrent,hmenu,?_⟩
  intro x y
  constructor
  · exact (hgate x y).1
  · intro op hop
    obtain ⟨u,hu,q,hq,hqp,hqc⟩ := (hgate x y).2 op hop
    refine ⟨u,hu,q,hq,hqp,hqc,?_⟩
    have hentry : q.current = Current.entry saved image a c false (operationCodec op) := by
      rw [hqc]; rfl
    exact next_query q saved image a c z op hqp hentry ha

end LiveProducer.Return

/-- The successor-local return handshake erases every current-core scratch cell
and sets its rail controls before reading the committed bank's original menu.
Saved service and outer image scratch are retained, so this is core-ready only. -/

theorem current_bank_paid_core_return (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (role : Bool) (z d : Runtime) (op : Operation)
    (himage : image.installation.tape = programTape)
    (hbank : (if role then c else a) = LiveProducer.word (runtimeCodec z))
    (hd : runtimeStep z op = some d) :
    Function.Injective LiveProducer.Return.code ∧
    (∀ s : LiveProducer.Return.State, programImage.length+LiveProducer.Return.staticImage.length+
      (LiveProducer.Return.code s).length < LiveProducer.Return.bound) ∧
    (∀ (s : LiveProducer.Return.State) (x y u v : Letter),
      LiveProducer.Return.actualRequest s = false →
        LiveProducer.Return.step s x y = LiveProducer.Return.step s u v) ∧
    ∃ t, ∃ r : LiveProducer.Return.State,
      LiveProducer.Return.run (LiveProducer.Return.entry
        (LiveProducer.Current.entry saved image a c role (operationCodec op))) 0 0 t = r ∧
      r = LiveProducer.Return.coreReady saved r.current.current.addressed.outer
        (if role then a else LiveProducer.word (runtimeCodec d))
        (if role then LiveProducer.word (runtimeCodec d) else c) ∧
      r.current.current.addressed.outer.installation.tape = programTape ∧
      (∀ w : Runtime, r.current.current.actual = LiveProducer.word (runtimeCodec w) →
        LiveProducer.Return.NextRound r w) := by
  obtain ⟨tp,p,tr,q,hp,hacq,hphase,hq,hret,ha,hc,_,_,hi,_⟩ :=
    current_bank_original_frames saved image a c role z d op himage hbank hd
  have hwhole : LiveProducer.Current.run
      (LiveProducer.Current.entry saved image a c role (operationCodec op)) 0 0 (tp+tr) = q := by
    rw [LiveProducer.Current.run,Nat.add_comm tp tr,Function.iterate_add_apply]
    change LiveProducer.Current.run
      (LiveProducer.Current.run
        (LiveProducer.Current.entry saved image a c role (operationCodec op)) 0 0 tp) 0 0 tr = q
    rw [hp,hq]
  obtain ⟨tn,_,hn,_,_⟩ := LiveProducer.Return.native_join _ q (tp+tr) rfl hwhole hret
  have hsaved : q.saved = saved := by
    have h := congrArg LiveProducer.Current.State.saved hwhole
    rw [LiveProducer.Current.passive_run _ rfl] at h
    exact h.symm
  let ready := LiveProducer.Return.coreReady saved q.current.addressed.outer
    (if role then a else LiveProducer.word (runtimeCodec d))
    (if role then LiveProducer.word (runtimeCodec d) else c)
  have hready : LiveProducer.Return.run (LiveProducer.Return.entry q) 0 0
      (2+LiveProducer.Return.scratchWidth+1+(LiveProducer.Return.controlCount+1)) = ready := by
    rw [LiveProducer.Return.retired_ready _ rfl hret]
    change LiveProducer.Return.coreReady q.saved q.current.addressed.outer q.current.actual q.current.synthetic = ready
    rw [hsaved,ha,hc]
  refine ⟨LiveProducer.Return.code_injective,LiveProducer.Return.charged,LiveProducer.Return.ports,
    tn+(2+LiveProducer.Return.scratchWidth+1+(LiveProducer.Return.controlCount+1)),ready,?_,rfl,hi,?_⟩
  · rw [LiveProducer.Return.run_add,hn,hready]
  · intro w hw
    exact LiveProducer.Return.next_round saved q.current.addressed.outer _ _ w hw


/-- The actual finite tagged producer consumes the unary key, native scanner,
encoded return-word copier and address subroutine on its active commit path.
This is a rail-model source transaction, not original COMPLETE membership:
header/slot scheduling, resident opcode fetch, live renderer-row preparation,
canonical ready reset and the full synthetic service refinement remain open. -/
theorem tagged_source_commit (s : TransferSnapshot) (op : Operation) (slot : Fin 6) (i : Fin frameWidth) :
    Function.Injective LiveProducer.code ∧
    (∀ q : LiveProducer.State, programImage.length+LiveProducer.staticImage.length+
      (LiveProducer.code q).length < LiveProducer.bound) ∧
    (∀ (q : LiveProducer.State) (a b c d : Letter),
      LiveProducer.actualRequest q = false → LiveProducer.freshRequest q = false →
      LiveProducer.step q a b = LiveProducer.step q c d) ∧
    (∀ (q : LiveProducer.State) (a b : Letter) (t : ℕ),
      (LiveProducer.run q a b t).addressed.outer.base.retained = q.addressed.outer.base.retained) ∧
    (∀ d : Runtime, runtimeStep s.base.retained.actual op = some d →
      (∃ t, ∃ q : LiveProducer.State,
        LiveProducer.run (LiveProducer.prepared s op slot i) 0 0 t = q ∧ q.stage = .returned ∧
        LiveProducer.returnedRuntime q = some d ∧ LiveProducer.returnedOperation q = some op ∧
        ∃ u ≤ t, LiveProducer.emitted (LiveProducer.run (LiveProducer.prepared s op slot i) 0 0 u) =
          some (frameTape (eventROM s.base.retained.actual.fields op slot) i)) ∧
      (∀ n : ℕ, let q := LiveProducer.run (LiveProducer.prepared s op slot i) 0 0 n
        q.stage ≠ .fault ∧ (q.stage ≠ .returned →
          LiveProducer.rank (LiveProducer.step q 0 0) < LiveProducer.rank q))) ∧
    (∀ (x : Letter) (d : Runtime), runtimeStep s.base.retained.actual (.read x) = some d →
      ∃ t, ∃ q : LiveProducer.State,
        LiveProducer.run (LiveProducer.step (LiveProducer.sourceEntry s slot i) x 0) 0 0 t = q ∧
        q.stage = .returned ∧ LiveProducer.returnedRuntime q = some d ∧
        LiveProducer.returnedOperation q = some (.read x)) := by
  refine ⟨LiveProducer.code_encoding,LiveProducer.charged,LiveProducer.ports,
    LiveProducer.saved_cuts,?_,
    (fun x d hd => LiveProducer.acquisition_commit s x slot i d hd)⟩
  intro d hd
  have he := LiveProducer.native_commit s op slot i d hd
  refine ⟨he,?_⟩
  obtain ⟨t,q,hq,hqs,_⟩ := he
  have hr : LiveProducer.Returns (LiveProducer.prepared s op slot i) := ⟨t,by rw [hq]; exact hqs⟩
  intro n
  have hn := LiveProducer.returns_after _ hr n
  exact ⟨LiveProducer.no_fault _ hn,LiveProducer.rank_step _ hn⟩



end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController

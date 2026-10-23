/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Source-blind native stack execution with exact output and paid reads. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
import D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout acquisitionTrace nodes)
open NativeSerialMachine

/-- A pending right address, or an already acquired left subtree. -/
inductive Frame where
  | left : Address → Frame
  | right : Source → Frame

/-- Source values in control are built only from acquired replies. -/
inductive Control where
  | visit : Address → List Frame → Control
  | deliver : Source → List Frame → Control

/-- One fixed program: the register, epoch and unknown input are not arguments.
The absent case is total but is never reached from the initial control. -/
def sourceControl : Control → Op Control Source
  | .visit u k => .read u (fun y => match y with
      | .alpha => .deliver (.of true) k
      | .beta => .deliver (.of false) k
      | .branch => .visit (u ++ [false]) (.left (u ++ [true]) :: k)
      | .absent => .deliver (.of true) k)
  | .deliver T [] => .stop T
  | .deliver T (.left v :: k) => .localStep (.visit v (.right T :: k))
  | .deliver T (.right s :: k) => .localStep (.deliver (.mul s T) k)

def initialControl : Control := .visit [] []

/-- Complete native chronology, including both local actions at each branch. -/
def productionTrace (u : Address) : Source → Trace
  | .of b => [.read 0 u (if b then .alpha else .beta)]
  | .mul s t => .read 0 u .branch ::
      (productionTrace (u ++ [false]) s ++ .localStep ::
        (productionTrace (u ++ [true]) t ++ [.localStep]))

/-- The continuation accepts the acquired subtree. It is not a runtime oracle:
all subtree and location parameters in this invariant are proof parameters. -/
private theorem traverse (U T : Source) (u : Address)
    (location : ∀ v, readout (u ++ v) U = readout v T)
    (k : List Frame) (tail : Trace) (out : Source)
    (next : Run sourceControl (.deliver T k) 0 U tail out) :
    Run sourceControl (.visit u k) 0 U (productionTrace u T ++ tail) out := by
  induction T generalizing u k tail with
  | of b =>
      have root := location []
      simp only [List.append_nil] at root
      cases b
      · simpa only [productionTrace, Bool.false_eq_true, if_false, List.singleton_append] using
          (Run.read rfl root next : Run sourceControl (.visit u k) 0 U
            (.read 0 u .beta :: tail) out)
      · simpa only [productionTrace, if_true, List.singleton_append] using
          (Run.read rfl root next : Run sourceControl (.visit u k) 0 U
            (.read 0 u .alpha :: tail) out)
  | mul s t left right =>
      have locl : ∀ v, readout ((u ++ [false]) ++ v) U = readout v s := by
        intro v
        simpa only [List.append_assoc, List.singleton_append, readout] using location (false :: v)
      have locr : ∀ v, readout ((u ++ [true]) ++ v) U = readout v t := by
        intro v
        simpa only [List.append_assoc, List.singleton_append, readout] using location (true :: v)
      have combine : Run sourceControl (.deliver t (.right s :: k)) 0 U
          (.localStep :: tail) out := Run.localStep rfl next
      have rt := right (u ++ [true]) locr (.right s :: k) (.localStep :: tail) combine
      have switch : Run sourceControl (.deliver s (.left (u ++ [true]) :: k)) 0 U
          (.localStep :: (productionTrace (u ++ [true]) t ++ .localStep :: tail)) out :=
        Run.localStep rfl rt
      have lt := left (u ++ [false]) locl (.left (u ++ [true]) :: k) _ switch
      have root : readout u U = .branch := by simpa [readout] using location []
      simpa only [productionTrace, List.cons_append, List.append_assoc,
        List.singleton_append] using (Run.read rfl root lt)

private theorem production_reads (T : Source) (u : Address) :
    reads (productionTrace u T) =
      (acquisitionTrace u T).map (fun a => (0, a.1, a.2)) := by
  have append (a b : Trace) : reads (a ++ b) = reads a ++ reads b := by
    induction a with
    | nil => rfl
    | cons e a ih => cases e <;> simp [reads, ih]
  induction T generalizing u with
  | of b => rfl
  | mul s t ihs iht =>
      simp only [productionTrace, reads, append, ihs, iht, List.append_nil,
        acquisitionTrace, List.map_cons, List.map_append]

private theorem stationary {x y : Config Control}
    (reach : StateTransition.Reaches (nativeStep sourceControl) x y) :
    y.2.1 = x.2.1 ∧ y.2.2.1 = x.2.2.1 := by
  have step {a b : Config Control} (h : b ∈ nativeStep sourceControl a) :
      b.2.1 = a.2.1 ∧ b.2.2.1 = a.2.2.1 := by
    rcases a with ⟨c,e,r,old⟩
    cases c with
    | visit u k =>
        simp only [nativeStep, sourceControl, Option.mem_def] at h
        cases Option.some.inj h
        exact ⟨rfl,rfl⟩
    | deliver T k =>
        cases k with
        | nil => simp [nativeStep,sourceControl] at h
        | cons f k =>
            cases f <;>
              simp only [nativeStep, sourceControl, Option.mem_def] at h <;>
              cases Option.some.inj h <;> exact ⟨rfl,rfl⟩
  induction reach with
  | refl => exact ⟨rfl,rfl⟩
  | tail reach h ih =>
      obtain ⟨he,hr⟩ := step h
      exact ⟨he.trans ih.1,hr.trans ih.2⟩

/-- Every finite input terminates under the same initial control. The full native
log is retained, the actual register never changes, and paid reads are exactly
one visit per real node in the existing acquisition order. -/
theorem native_source_producer (U : Source) :
    Run sourceControl initialControl 0 U (productionTrace [] U) U ∧
    (∀ old : Trace, ∃ c : Control,
      StateTransition.Reaches (nativeStep sourceControl) (initialControl,0,U,old)
        (c,0,U,old ++ productionTrace [] U) ∧ sourceControl c = .stop U) ∧
    (∀ (old : Trace) (x : Config Control),
      StateTransition.Reaches (nativeStep sourceControl) (initialControl,0,U,old) x →
        x.2.1 = 0 ∧ x.2.2.1 = U) ∧
    reads (productionTrace [] U) =
      (acquisitionTrace [] U).map (fun a => (0,a.1,a.2)) ∧
    (reads (productionTrace [] U)).map (fun a => a.2.1) = nodes U ∧
    ((reads (productionTrace [] U)).map (fun a => a.2.1)).Nodup ∧
    (reads (productionTrace [] U)).length = (nodes U).length := by
  have run : Run sourceControl initialControl 0 U (productionTrace [] U) U := by
    simpa only [List.append_nil, initialControl] using
      traverse U U [] (by intro v; rfl) [] [] U (Run.stop rfl)
  have exactReads := production_reads U []
  have addresses : (reads (productionTrace [] U)).map (fun a => a.2.1) = nodes U := by
    rw [exactReads, List.map_map]
    simpa [Function.comp_def] using
      ActualPureAcquisitionCompiler.trace_addresses U []
  refine ⟨run, ?_, fun _ _ h => stationary h, exactReads, addresses, ?_, ?_⟩
  · intro old
    obtain ⟨c,e,_,reach,stop,_⟩ := actual_register_execution sourceControl run U rfl old
    have fixed := stationary reach
    simp only at fixed
    rcases fixed with ⟨rfl,_⟩
    exact ⟨c,reach,stop⟩
  · rw [addresses]
    exact ActualPureAcquisitionCompiler.nodes_nodup U
  · simpa only [List.length_map] using congrArg List.length addresses

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer

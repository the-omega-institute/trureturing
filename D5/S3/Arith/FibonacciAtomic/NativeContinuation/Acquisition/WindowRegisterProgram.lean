/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterProgram
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterProgram
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: A fixed local program composes packed acquisition and register transfer. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.WindowRegisterComposition

namespace PhysicalWindowContinuation.CanonicalAcquisition

abbrev State := PhysicalWindowContinuation.Control ⊕ RegisterHandoff.PortControl

inductive Action where
  | read (t : Track) (next : Symbol → State)
  | write (t : Track) (s : Symbol) (next : State)
  | move (t : Track) (right : Bool) (next : State)
  | halt

def baseAction : Instruction → Action
  | .read t f => .read t (Sum.inl ∘ f)
  | .write t b k => .write t b (.inl k)
  | .move t d k => .move t d (.inl k)
  | .halt => .halt

def portAction : RegisterHandoff.PortInstruction → Action
  | .read t f => .read t (Sum.inr ∘ f)
  | .write t b k => .write t b (.inr k)
  | .move t d k => .move t d (.inr k)
  | .halt => .halt

def program : State → Action
  | .inl .done => .read workTrack (fun _=>.inr (.home 0))
  | .inl k => baseAction (PhysicalWindowContinuation.program k)
  | .inr k => portAction (RegisterHandoff.program k)

structure Config where
  control : State
  head : Track → ℤ
  cell : Track → ℤ → Symbol

def step (c : Config) : Config :=
  match program c.control with
  | .read t f => { c with control := f (c.cell t (c.head t)) }
  | .write t b k => { c with
      control := k
      cell := Function.update c.cell t (Function.update (c.cell t) (c.head t) b) }
  | .move t d k => { c with
      control := k
      head := Function.update c.head t (c.head t + (if d then 1 else -1)) }
  | .halt => c

def run (c : Config) (n : ℕ) : Config := step^[n] c

def base (c : Configuration) : Config := ⟨.inl c.control,c.head,c.cell⟩
def port (c : RegisterHandoff.PortConfig) : Config := ⟨.inr c.control,c.head,c.cell⟩
def initial (w : List Window) (e : Bool) : Config := base (PhysicalWindowContinuation.initial w e)

theorem program_base (k : PhysicalWindowContinuation.Control) (hk : k≠.done) :
    program (.inl k)=baseAction (PhysicalWindowContinuation.program k) := by
  cases k <;> simp_all [program]

theorem step_base (c : Configuration) (hc : c.control≠.done) :
    step (base c)=base (PhysicalWindowContinuation.step c) := by
  simp only [step,base,program_base _ hc]
  cases h : PhysicalWindowContinuation.program c.control <;>
    simp [baseAction,PhysicalWindowContinuation.step,h,base,Function.comp_def]

theorem step_port (c : RegisterHandoff.PortConfig) :
    step (port c)=port (RegisterHandoff.step c) := by
  simp only [step,port,program]
  cases h : RegisterHandoff.program c.control <;>
    simp [portAction,RegisterHandoff.step,h,port,Function.comp_def]

theorem run_port (c : RegisterHandoff.PortConfig) (n : ℕ) :
    run (port c) n=port (RegisterHandoff.run c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    change step (run (port c) n)=_
    rw [ih,step_port]
    simp only [RegisterHandoff.run,Function.iterate_succ_apply']

theorem base_prefix (c : Configuration) (t : ℕ)
    (hp : ∀ n<t,(PhysicalWindowContinuation.run c n).control≠.done) :
    ∀ n≤t,run (base c) n=base (PhysicalWindowContinuation.run c n) := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (by omega)
    rw [run,Function.iterate_succ_apply']
    change step (run (base c) n)=_
    rw [he,step_base _ (hp n (by omega))]
    simp only [PhysicalWindowContinuation.run,Function.iterate_succ_apply']

theorem base_done_stutter (c : Configuration) (hc : c.control=.done) (n : ℕ) :
    PhysicalWindowContinuation.run c n=c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PhysicalWindowContinuation.run,Function.iterate_succ_apply']
    change PhysicalWindowContinuation.step (PhysicalWindowContinuation.run c n)=_
    rw [ih]
    simp [PhysicalWindowContinuation.step,PhysicalWindowContinuation.program,hc]

/-- The paid extension starts at the first actual packed completion. -/
theorem first_done_lift (c : Configuration) (T : ℕ)
    (hc : (PhysicalWindowContinuation.run c T).control=.done) :
    ∃ s≤T,run (base c) s=base (PhysicalWindowContinuation.run c T) ∧
      ∀ n ≤ s, run (base c) n=base (PhysicalWindowContinuation.run c n) := by
  let hex : ∃ n,(PhysicalWindowContinuation.run c n).control=.done := ⟨T,hc⟩
  let s := Nat.find hex
  have hs : s≤T := Nat.find_min' hex hc
  have hp : ∀ n<s,(PhysicalWindowContinuation.run c n).control≠.done := by
    intro n hn
    exact Nat.find_min hex hn
  have hsame : PhysicalWindowContinuation.run c T=PhysicalWindowContinuation.run c s := by
    rw [show T=(T-s)+s by omega,PhysicalWindowContinuation.run,Function.iterate_add_apply]
    change PhysicalWindowContinuation.run (PhysicalWindowContinuation.run c s) (T-s)=_
    exact base_done_stutter _ (Nat.find_spec hex) _
  refine ⟨s,hs,?_,base_prefix c s hp⟩
  exact (base_prefix c s hp s (by rfl)).trans (congrArg base hsame.symm)

end PhysicalWindowContinuation.CanonicalAcquisition

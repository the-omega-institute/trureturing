import Reg.Support.DependentFamily
import D5.S0.Computability.BinaryMachine.StackProgram
import D5.S0.Computability.BinaryMachine.PolynomialBound

set_option autoImplicit false
namespace Reg.Support.BinaryMachineAudit
open _root_.Complexity _root_.Complexity.StackProgram

/-- A counted stack execution contains at least one instruction. -/
theorem no_zero_exec {k : Nat} {L : Type} {p : Program k L} {q r result} :
    ¬ Exec p q r 0 result := by
  intro h
  have hh := h.run
  change (none : Option _) = some result at hh
  cases hh

/-- An always-jumping finite machine never halts, even with arbitrary finite fuel. -/
def spinning : Machine where
  states := 0
  start := 0
  code := fun _ _ => .step Symbol.blank Move.stay 0

theorem spinning_run (fuel : Nat) (c : Config spinning) : run spinning fuel c = none := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih => exact ih _

theorem spinning_not_polynomial : ¬ PolynomialTimeMachine spinning := by
  rintro ⟨c,e,h⟩
  obtain ⟨t,b,out,_,hr⟩ := h []
  have hh := spinning_run t ⟨spinning.start,Tape.ofInput []⟩
  change run spinning t _ = _ at hr
  rw [spinning_run] at hr
  cases hr

end Reg.Support.BinaryMachineAudit

namespace Reg.ContractPrototype.Inputs.ValidatedImplementedOld
unsafe def hiddenImpl (_ : Nat) : Bool := false
@[implemented_by hiddenImpl] def hiddenBit (_ : Nat) : Bool := false
def Carrier := Bool
def route (b : Carrier) : Bool := if hiddenBit 1 then b else b
end Reg.ContractPrototype.Inputs.ValidatedImplementedOld

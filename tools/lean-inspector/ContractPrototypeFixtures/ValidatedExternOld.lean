namespace Reg.ContractPrototype.Inputs.ValidatedExternOld
@[extern c inline "((uint8_t)0)"] def hiddenBit (_ : Nat) : Bool := false
def Carrier := Bool
def route (b : Carrier) : Bool := if hiddenBit 1 then b else b
end Reg.ContractPrototype.Inputs.ValidatedExternOld

namespace Reg.ContractPrototype.Inputs.ValidatedOpaqueOld
opaque hiddenBit : Bool := false
def Carrier := Bool
def route (b : Carrier) : Bool := if hiddenBit then b else b
end Reg.ContractPrototype.Inputs.ValidatedOpaqueOld

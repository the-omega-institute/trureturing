namespace Reg.ContractPrototype.Inputs.ValidatedPartialOld
partial def hiddenBit (n : Nat) : Bool := if n == 0 then false else hiddenBit (n-1)
def Carrier := Bool
def route (b : Carrier) : Bool := if hiddenBit 1 then b else b
end Reg.ContractPrototype.Inputs.ValidatedPartialOld

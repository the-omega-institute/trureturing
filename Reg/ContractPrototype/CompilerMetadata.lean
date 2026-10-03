namespace Reg.ContractPrototype.CompilerMetadata

def leaf (_ : Nat) : Bool := false
unsafe def targetA (_ : Nat) : Bool := false
unsafe def targetB (_ : Nat) : Bool := false
def replacement (_ : Nat) : Bool := false
theorem replacement_eq : leaf = replacement := rfl
def initializer : IO (Nat → Bool) := pure (fun _ => false)

end Reg.ContractPrototype.CompilerMetadata

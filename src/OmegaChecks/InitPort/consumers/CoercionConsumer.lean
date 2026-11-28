import OmegaInit.Coe

private structure Input where value : Nat
private structure Intermediate where value : Nat
private structure Output where value : Nat

private instance : Omega.Coe Input Intermediate := ⟨fun x => ⟨x.value + 1⟩⟩
private instance : Omega.Coe Intermediate Output := ⟨fun x => ⟨x.value * 2⟩⟩
private instance : Omega.CoeFun Input (fun _ => Nat → Nat) := ⟨fun x n => x.value + n⟩
private instance : Omega.CoeDep Nat 11 Output := ⟨⟨37⟩⟩

#guard (↑(Input.mk 5) : Output).value == 12
#guard (↑(11 : Nat) : Output).value == 37
#guard (⇑(Input.mk 5)) 4 == 9

private structure Carrier where val : Type
private instance : Omega.CoeSort Carrier Type := ⟨Carrier.val⟩
private abbrev naturals : Carrier := ⟨Nat⟩
example : (4 : ↥naturals) = 4 := rfl

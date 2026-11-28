import OmegaInit.Data.Fin.Basic

example (i : Omega.Fin 0) : False := Omega.Fin.elim0 i
example (i : Omega.Fin 97) : (↑i : Nat) = Omega.Fin.val i := rfl
example : Omega.Fin.val (100 : Omega.Fin 97) = 3 := rfl
example : Omega.Fin.val (25 : Omega.Fin 1) = 0 := rfl
example : Omega.Fin.val (340282366920938463463374607431768211460 :
    Omega.Fin 340282366920938463463374607431768211457) = 3 := rfl

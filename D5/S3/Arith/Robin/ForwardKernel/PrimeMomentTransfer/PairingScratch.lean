import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectAlgebra
open scoped BigOperators
open D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
example : Fintype.card {P : Finset (Finset (Fin 6)) //
    IsPerfectPairing (Finset.univ : Finset (Fin 6)) P} = 15 := by
  native_decide
end

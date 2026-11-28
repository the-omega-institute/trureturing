import OmegaInit.Data.List.Scan.Basic

private def inputs : Omega.List Nat := .cons 1 (.cons 2 (.cons 3 .nil))
private def digits (a b : Nat) := a * 10 + b
private def values : Omega.List Nat → List Nat
  | .nil => []
  | .cons a xs => a :: values xs

#guard values (Omega.List.scanl digits 0 inputs) == [0, 1, 12, 123]
#guard values (Omega.List.scanr digits 0 inputs) == [60, 50, 30, 0]
#guard values (@Omega.List.scanlM Omega.Id _ _ Omega.Id.instMonad digits 8 .nil) == [8]
#guard values (@Omega.List.scanrM Omega.Id _ _ Omega.Id.instMonad digits 8 .nil) == [8]

private abbrev Trace (α : Type) := Nat → α × Nat

@[instance_reducible] private def traceMonad : Omega.Monad Trace where
  pure a s := (a, s)
  bind action next s :=
    let (a, t) := action s
    next a t

private def leftStep (acc digit s : Nat) : Nat × Nat := (digits acc digit, digits s digit)
private def rightStep (digit acc s : Nat) : Nat × Nat := (digits acc digit, digits s digit)

#guard (let (xs, trace) := @Omega.List.scanlM Trace _ _ traceMonad leftStep 0 inputs 0
        (values xs, trace)) == ([0, 1, 12, 123], 123)
#guard (let (xs, trace) := @Omega.List.scanrM Trace _ _ traceMonad rightStep 0 inputs 0
        (values xs, trace)) == ([321, 32, 3, 0], 321)

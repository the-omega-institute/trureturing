import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalCanonicalClassification
/-! Transient exact checker boundary certificates. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalBoundaryProbe
open OriginalCanonicalClassification OriginalFunctionalNormalization OriginalNativeConstruction
open ActualTreeReadoutAcquisition (Reply)

def modeTT : Fin 2 → Bool := fun _ => true
def modeFT : Fin 2 → Bool := fun j => j = 1
def modeFF : Fin 2 → Bool := fun _ => false
def modeTF : Fin 2 → Bool := fun j => j = 0
def e0 : Expr 2 4 := .var 0 0
def e1 : Expr 2 4 := .var 0 1
def e01 : Expr 2 4 := .pair e0 e1
def e2 : Expr 2 4 := .var 0 2
def e3 : Expr 2 4 := .var 0 3

-- These are transient equation bridges, after an explicit well-founded unfolding.
private theorem edge_system :
    (OriginalFunctionalNormalization.normalize edgeSystem).system = edgeSystem := by
  rw [OriginalFunctionalNormalization.normalize.eq_def]
  split
  · rfl
  · rename_i h
    exact (h (by decide)).elim

private theorem edge_reconstruction :
    (OriginalFunctionalNormalization.normalize edgeSystem).reconstruction =
      fun i => Expr.var 0 i := by
  rw [OriginalFunctionalNormalization.normalize.eq_def]
  split
  · rfl
  · rename_i h
    exact (h (by decide)).elim

private theorem empty_system {k : Nat} (E : Definitions k 0) :
    (OriginalFunctionalNormalization.normalize E).system = E := by
  rw [OriginalFunctionalNormalization.normalize.eq_def]
  split
  · rfl
  · rename_i h
    exact (h (of_decide_eq_true rfl)).elim

private theorem empty_reconstruction {k : Nat} (E : Definitions k 0) :
    (OriginalFunctionalNormalization.normalize E).reconstruction =
      fun i => Expr.var 0 i := by
  rw [OriginalFunctionalNormalization.normalize.eq_def]
  split
  · rfl
  · rename_i h
    exact (h (of_decide_eq_true rfl)).elim

-- C01: both true, exact ordered finite symbolic output, retaining zero powers.
example : canonicalCompile edgeSystem modeTT e01 =
    some (.pair (.power 0 (.token 0 0)) (.power 0 (.token 1 0))) := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C02: mixed false/true, pair fails because its first component is infinite.
example : canonicalCompile edgeSystem modeFT e01 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C03: both false.
example : canonicalCompile edgeSystem modeFF e01 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C04: the opposite mixed mode.
example : canonicalCompile edgeSystem modeTF e01 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C05: first finite original state.
example : canonicalCompile edgeSystem modeTT e0 = some (.power 0 (.token 0 0)) := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C06: first state becomes infinite in mixed mode.
example : canonicalCompile edgeSystem modeFT e0 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C07: second state stays finite in mixed mode.
example : canonicalCompile edgeSystem modeFT e1 = some (.power 0 (.token 1 0)) := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C08: second state is infinite in all-false mode.
example : canonicalCompile edgeSystem modeFF e1 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C09: guarded recurrent state, true mode.
example : canonicalCompile edgeSystem modeTT e2 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C10: guarded recurrent state, mixed mode.
example : canonicalCompile edgeSystem modeFT e2 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C11: guarded recurrent state, false mode.
example : canonicalCompile edgeSystem modeFF e2 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C12: genuinely free state, true mode.
example : canonicalCompile edgeSystem modeTT e3 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C13: genuinely free state, false mode.
example : canonicalCompile edgeSystem modeFF e3 = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C14: a disabled parameter token.
example : canonicalCompile edgeSystem modeFT (.token 0 0) = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C15: an enabled parameter token.
example : canonicalCompile edgeSystem modeFT (.token 1 0) = some (.token 1 0) := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C16: literal Omega.
example : canonicalCompile edgeSystem modeTT .omega = none := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C17: ground leaf is independent of parameter modes.
example : canonicalCompile edgeSystem modeFF (.ground (.of true)) = some (.ground (.of true)) := by
  simp only [canonicalCompile, edge_system, edge_reconstruction]
  decide
-- C18: both parameter and state counts empty, finite ground.
example : canonicalCompile (k := 0) (m := 0) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (.ground (.of true)) = some (.ground (.of true)) := by
  simp only [canonicalCompile, empty_system, empty_reconstruction]
  decide
-- C19: both counts empty, literal Omega still rejected.
example : canonicalCompile (k := 0) (m := 0) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) .omega = none := by
  simp only [canonicalCompile, empty_system, empty_reconstruction]
  decide
-- C20: no states, mixed parameter token.
example : canonicalCompile (m := 0) (fun i => Fin.elim0 i)
    modeFT (.token 1 0) = some (.token 1 0) := by
  simp only [canonicalCompile, empty_system, empty_reconstruction]
  decide
-- C21: inclusive h=0 includes the root alpha.
example : prefixReply edgeSystem modeTT (fun _ => 0) 0 (.token 0 0) [] = .alpha := by
  simp only [prefixReply, prefixTree, edge_system, edge_reconstruction]
  decide
-- C22: absence beneath a finite leaf, including the boundary depth.
example : prefixReply edgeSystem modeTT (fun _ => 0) 1 (.token 0 0) [false] = .absent := by
  simp only [prefixReply, prefixTree, edge_system, edge_reconstruction]
  decide
-- C23: root of a finite pair.
example : prefixReply edgeSystem modeTT (fun _ => 0) 0 e01 [] = .branch := by
  simp only [prefixReply, prefixTree, edge_system, edge_reconstruction]
  decide
-- C24: inclusive h=1 retains a finite child.
example : prefixReply edgeSystem modeTT (fun _ => 0) 1 e01 [false] = .alpha := by
  simp only [prefixReply, prefixTree, edge_system, edge_reconstruction]
  decide
-- C25: recurrent state retains its right branch at the inclusive boundary.
example : prefixReply edgeSystem modeTT (fun _ => 0) 1 e2 [true] = .branch := by
  simp only [prefixReply, prefixTree, edge_system, edge_reconstruction]
  decide
-- C26: free state's canonical Omega filling has a branch at the boundary.
example : prefixReply edgeSystem modeFF (fun _ => 0) 1 e3 [false] = .branch := by
  simp only [prefixReply, prefixTree, edge_system, edge_reconstruction]
  decide

#print axioms edge_system
#print axioms edge_reconstruction
#print axioms empty_system
#print axioms empty_reconstruction
end D5.S3.Arith.FibonacciAtomic.Observer.OriginalBoundaryProbe

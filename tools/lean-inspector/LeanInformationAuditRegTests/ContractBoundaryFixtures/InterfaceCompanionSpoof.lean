import Lean
namespace Boundary.InterfaceCompanionSpoof
structure Box where
  value : Nat
run_meta Lean.addAndCompile <| Lean.Declaration.defnDecl {
  name := `Boundary.InterfaceCompanionSpoof.Box.ctorElim
  levelParams := []
  type := Lean.mkConst `Nat
  value := Lean.mkNatLit 17
  hints := .opaque
  safety := .safe }
end Boundary.InterfaceCompanionSpoof

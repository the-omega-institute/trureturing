import LeanInformationAuditInterface.Contract.Catalog
open Lean
namespace ArchitectureFixtures.InterfaceRunMeta
run_meta Lean.addAndCompile <| Lean.Declaration.defnDecl { name := `ArchitectureFixtures.InterfaceRunMeta.generatedValue, levelParams := [], type := Lean.mkConst `Nat, value := Lean.mkNatLit 17, hints := .opaque, safety := .safe }
end ArchitectureFixtures.InterfaceRunMeta

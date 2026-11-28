module
public import Lean

open Lean
namespace OmegaChecks.InitPort.PublicTypeClient

/-- Render complete kernel applications and binders without typeclass search or implementation imports. -/
private partial def levelText : Level → String
  | .zero => "0"
  | .succ l => "(" ++ levelText l ++ " + 1)"
  | .max a b => "(max " ++ levelText a ++ " " ++ levelText b ++ ")"
  | .imax a b => "(imax " ++ levelText a ++ " " ++ levelText b ++ ")"
  | .param n => n.toString
  | _ => panic! "unexpected level"

private partial def source (e : Expr) (xs : List String := []) : String := Id.run do
  let var := "x" ++ toString xs.length
  let bind := fun (info : BinderInfo) (dom : Expr) =>
    let (l,r) := match info with
      | .implicit => ("{","}") | .strictImplicit => ("⦃","⦄")
      | .instImplicit => ("[","]") | _ => ("(",")")
    l ++ var ++ " : " ++ source dom xs ++ r
  match e with
  | .bvar i => return xs[i]!
  | .sort l => return "(Sort " ++ levelText l ++ ")"
  | .const n us =>
    return "@" ++ n.toString ++ (if us.isEmpty then "" else ".{" ++ String.intercalate ", " (us.map levelText) ++ "}")
  | .app _ _ => return "(" ++ String.intercalate " " ((source e.getAppFn xs) :: (e.getAppArgs.toList.map (source · xs))) ++ ")"
  | .forallE _ dom body bi => return "(∀ " ++ bind bi dom ++ ", " ++ source body (var::xs) ++ ")"
  | .lam _ dom body bi => return "(fun " ++ bind bi dom ++ " => " ++ source body (var::xs) ++ ")"
  | .letE _ dom value body _ => return "(let " ++ var ++ " : " ++ source dom xs ++ " := " ++ source value xs ++ "; " ++ source body (var::xs) ++ ")"
  | .mdata _ x => return source x xs
  | .proj _ i x => return "(" ++ source x xs ++ ")." ++ toString (i+1)
  | .lit (.natVal n) => return toString n
  | _ => panic! "unhandled kernel expression"

public def client (typ : Expr) (n : Name) (universes : List Name) (compile : Bool := true) : String := Id.run do
  let decl := if universes.isEmpty then "" else "universe " ++ String.intercalate " " (universes.map Name.toString) ++ "\n"
  let modifier := if compile then "" else "noncomputable "
  return "section\n" ++ decl ++ modifier ++ "example : " ++ source typ ++ " :=\n  " ++
    source (mkConst n (universes.map Level.param)) ++ "\nend\n"

end OmegaChecks.InitPort.PublicTypeClient

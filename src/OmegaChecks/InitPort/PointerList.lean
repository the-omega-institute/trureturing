module

public import OmegaChecks.InitPort.Translation
import all OmegaChecks.InitPort.ReferencePut

open Lean
namespace OmegaChecks.InitPort.PointerList

private def lam (name : Name) (domain : Expr) (body : Expr → Expr) (bi := BinderInfo.default) : Expr :=
  let var := mkFVar ⟨name⟩
  .lam name domain ((body var).abstract #[var]) bi

private def arr (a b : Expr) := Expr.forallE .anonymous a (b.liftLooseBVars 0 1) .default

private def guardHead (u : Level) (α a b yes : Expr) : Expr :=
  let cmp := mkApp3 (mkConst `ptrEq [u]) α a b
  let bl := mkConst `Bool
  let t := mkConst `Bool.true
  mkApp5 (mkConst `ite [1]) bl (mkApp3 (mkConst `Eq [1]) bl cmp t)
    (mkApp2 (mkConst `instDecidableEqBool) cmp t) yes (mkConst `Bool.false)

/-- The pinned recursive occurrence appears only on the two tails of the cons/cons branch. -/
private def equation (u : Level) : Expr :=
  lam `α (.sort u.succ) (bi := .implicit) fun α =>
    let list := mkApp (mkConst `List [u]) α
    lam `xs list fun xs => lam `ys list fun ys =>
      let matcher := mkPrivateNameCore `Init.Util `ptrEqList.match_1
      let motive := lam `xl list fun _ => lam `yl list fun _ => mkConst `Bool
      let bothNil := lam `unit (mkConst `Unit) fun _ => mkConst `Bool.true
      let bothCons := lam `a α fun a => lam `as list fun as => lam `b α fun b => lam `bs list fun bs =>
        guardHead u α a b (mkApp3 (mkConst `ptrEqList [u]) α as bs)
      let other := lam `left list fun _ => lam `right list fun _ => mkConst `Bool.false
      mkAppN (mkConst matcher [u, 1]) #[α, motive, xs, ys, bothNil, bothCons, other]

private def interface (u : Level) : Expr :=
  let list := mkApp (mkConst `List [u]) (.bvar 0)
  .forallE `α (.sort u.succ) (arr list (arr list (mkConst `Bool))) .implicit

public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let .defnInfo d := ci | return false
  let rename := if strict then InitKernelPort.portName else id
  let [level] := d.levelParams | return false
  unless d.name == rename `ptrEqList && d.all == [d.name] && d.safety == .unsafe do return false
  let tr := InitKernelPort.translate rename
  let u := Level.param level
  return ReferencePut.sameTerm d.type (tr (interface u)) && ReferencePut.sameTerm d.value (tr (equation u))

/-- Total double-list traversal, structural on the first list. An element comparison
has the same unsafe boundary as `ptrEq` in the installed term. -/
private def model (u : Level) : Expr :=
  lam `α (.sort u.succ) (bi := .implicit) fun α =>
    let list := mkApp (mkConst `List [u]) α
    let bl := mkConst `Bool
    let result := arr list bl
    let cases (xs nil cons : Expr) :=
      mkApp5 (mkConst `List.casesOn [1, u]) α (lam `q list fun _ => bl) xs nil cons
    let nil := lam `ys list fun ys =>
      cases ys (mkConst `Bool.true) (lam `b α fun _ => lam `bs list fun _ => mkConst `Bool.false)
    let cons := lam `a α fun a => lam `as list fun _ => lam `ih result fun ih => lam `ys list fun ys =>
      cases ys (mkConst `Bool.false) (lam `b α fun b => lam `bs list fun bs => guardHead u α a b (mkApp ih bs))
    lam `xs list fun xs => mkApp5 (mkConst `List.rec [u.succ, u]) α (lam `q list fun _ => result) nil cons xs

/-- Kernel-check a total model and the pinned one-step term, then compare their
reductions on all four constructor pairs at arbitrary elements and tails. -/
public def check (env : Kernel.Environment) (d : DefinitionVal) : IO Unit := do
  let [level] := d.levelParams | throw <| IO.userError "unexpected ptrEqList universes"
  let u := Level.param level
  let tr := InitKernelPort.translate InitKernelPort.portName
  let value := tr (model u)
  let checked ← match env.addDeclCore 0 1000 (.defnDecl {d with safety := .safe, value}) none with
    | .ok checked => pure checked
    | .error e => throw <| IO.userError s!"invalid structural list pointer comparison: {← e.toMessageData {} |>.toString}"
  let checked := Environment.ofKernelEnv checked
  unless (Kernel.check checked {} d.value).toOption.any (Kernel.isDefEqGuarded checked {} d.type) do
    throw <| IO.userError "invalid recursive list pointer comparison"
  let atPair (f : Expr) (left right : Bool) : Expr :=
    tr <| lam `α (.sort u.succ) (bi := .implicit) fun α =>
      let list := mkApp (mkConst `List [u]) α
      lam `a α fun a => lam `as list fun as => lam `b α fun b => lam `bs list fun bs =>
        let ctor (cons : Bool) (head tail : Expr) := if cons then mkApp3 (mkConst `List.cons [u]) α head tail
          else mkApp (mkConst `List.nil [u]) α
        mkApp3 f α (ctor left a as) (ctor right b bs)
  for left in [false, true] do
    for right in [false, true] do
      let folded := atPair (mkConst `ptrEqList [u]) left right
      let step := atPair (equation u) left right
      unless Kernel.isDefEqGuarded checked {} folded step do
        throw <| IO.userError s!"list pointer comparison equation mismatch at {left}, {right}"

end OmegaChecks.InitPort.PointerList

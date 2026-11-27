module
public import Lean
public import OmegaChecks.InitPort.Alternatives.BorrowedIndex
import all OmegaChecks.InitPort.Alternatives.BorrowedIndex

open Lean

namespace OmegaChecks.InitPort.BorrowedIndex

private def lookup {α : Type u} [Inhabited α] (xs : Array α) (i : Nat) : α :=
  if i < USize.size / 2 then (if h : i < xs.size then xs.getInternal i h else default) else default

private theorem values {α : Type u} [Inhabited α] (xs : Array α) (i : Nat) :
    Alternatives.Array.get!InternalBorrowed xs i = lookup xs i := by
  unfold Alternatives.Array.get!InternalBorrowed lookup
  split <;> rfl

/-- Extract a pinned inline function by its complete signature. Block comments have
no computational content. The comparison retains the order of every return and check. -/
private def hasFunction (header signature body : String) : Bool := Id.run do
  let [_, suffix] := header.splitOn (signature ++ " {") | return false
  let first :: _ :: _ := suffix.splitOn "\n}" | return false
  let code := match first.splitOn "/*" with
    | [] => ""
    | start :: pieces => start ++ String.join (pieces.map fun (part : String) => (part.splitOn "*/").getLast!)
  return code.toList.filter (fun c => !c.isWhitespace) == body.toList.filter (fun c => !c.isWhitespace)

private def checkHeader : IO Unit := do
  let header ← IO.FS.readFile ((← findSysroot) / "include" / "lean" / "lean.h")
  let branch (read : String) :=
    "if (lean_is_scalar(i)) { size_t idx = lean_unbox(i); if (idx < lean_array_size(a)) { return " ++
    read ++ "(a, idx); } } lean_inc(def_val); return lean_array_get_panic(def_val);"
  let signature (name : String) :=
    "static inline lean_object * " ++ name ++ "(b_lean_obj_arg def_val, b_lean_obj_arg a, b_lean_obj_arg i)"
  unless hasFunction header (signature "lean_array_get_borrowed") (branch "lean_array_get_core") &&
      hasFunction header (signature "lean_array_get") (branch "lean_array_uget") &&
      hasFunction header "static inline lean_object * lean_array_uget(b_lean_obj_arg a, size_t i)"
        "lean_object * r = lean_array_get_core(a, i); lean_inc(r); return r;" &&
      hasFunction header "static inline b_lean_obj_res lean_array_get_core(b_lean_obj_arg o, size_t i)"
        "assert(i < lean_array_size(o)); return lean_to_array(o)->m_data[i];" &&
      header.contains "#define LEAN_MAX_SMALL_NAT (SIZE_MAX >> 1)" &&
      header.contains "lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }" &&
      header.contains "lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }" &&
      header.contains "lean_array_size(b_lean_obj_arg o) { return lean_to_array(o)->m_size; }" &&
      header.contains "static inline size_t lean_unbox(lean_object * o) { return (size_t)(o) >> 1; }" &&
      hasFunction header "static inline lean_obj_res lean_usize_to_nat(size_t n)"
        "if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT)) return lean_box(n); else return lean_big_usize_to_nat(n);" do
    throw <| IO.userError "native array read or small Nat representation differs from the certified implementation"

public def check (env : Environment) (native : OpaqueVal) (candidate : Expr) : IO Unit := do
  let owner := env.getModuleIdx? `Init.Prelude
  let some (.defnInfo owned) := env.find? `Array.get!Internal | throw <| IO.userError "missing checked array read"
  unless native.name == `Array.get!InternalBorrowed && native.isUnsafe && owner.isSome &&
      [native.name, owned.name].all (fun n => env.getModuleIdxFor? n == owner) && owned.safety == .safe &&
      getExternNameFor env `c native.name == some "lean_array_get_borrowed" &&
      getExternNameFor env `c owned.name == some "lean_array_get" do
    throw <| IO.userError "mismatched native array read declarations"
  checkHeader
  let levels := native.levelParams.map Level.param
  let verify : MetaM Unit := Meta.forallTelescope native.type fun args _ => do
    let #[α, inhabited, _, _] := args | throwError "unexpected input to borrowed array read"
    let original ← Meta.mkLambdaFVars args (mkApp2 (mkConst `Inhabited.default levels) α inhabited)
    unless Kernel.isDefEqGuarded env {} original native.value do throwError "unexpected upstream hidden fallback"
    let model := mkConst ``Alternatives.Array.get!InternalBorrowed levels
    unless Kernel.isDefEqGuarded env {} candidate model do throwError "borrowed read does not retain the failure path"
    let statement ← Meta.mkForallFVars args (← Meta.mkEq (mkAppN candidate args) (mkAppN (mkConst ``lookup levels) args))
    let .ok inferred := Kernel.check env {} (mkConst ``values levels) | throwError "invalid array read proof"
    unless Kernel.isDefEqGuarded env {} inferred statement do throwError "incomplete borrowed array lookup proof"
  verify.run' |>.toIO' {fileName := "<borrowed array lookup>", fileMap := default} {env}

end OmegaChecks.InitPort.BorrowedIndex

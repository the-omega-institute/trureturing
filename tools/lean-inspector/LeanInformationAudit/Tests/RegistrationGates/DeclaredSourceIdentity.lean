import LeanInformationAudit.Registry.Evidence

open Lean Meta LeanInformationAudit.TemplateAudit

private def report (label : String) (ok : Bool) : MetaM Unit :=
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

private def encoding (e : Expr) (params : List Name := []) : MetaM ByteArray := do
  let .ok (bytes, _) := compactRawEncoding params e
    | throwError "[FAIL] compact_source_encoding_setup"
  return bytes

-- Mixing a changed subtree with an earlier equal-looking subtree exercises the
-- interning hit, which encoding the two roots separately does not exercise.
private def pair (p q : Expr) : Expr := mkApp2 (mkConst ``And) p q

private def distinct (label : String) (p q : Expr) : MetaM Unit := do
  report ("compact_source_" ++ label ++ "_distinct")
    ((← encoding (pair p q)) != (← encoding (pair p p)))

run_meta do
  let nat := mkConst ``Nat
  let body := mkApp3 (mkConst ``Eq [.succ .zero]) nat (.bvar 0) (.bvar 0)
  for (kind, binder) in #[("forall", Expr.forallE), ("lambda", Expr.lam)] do
    let p := binder `x nat body .default
    for (mode, bi) in #[("implicit", BinderInfo.implicit),
        ("strictImplicit", BinderInfo.strictImplicit), ("instImplicit", BinderInfo.instImplicit)] do
      distinct (kind ++ "_" ++ mode) p (binder `x nat body bi)
    let renamed := binder `renamed nat body .default
    report ("compact_source_" ++ kind ++ "_renaming_invariant")
      ((← encoding (pair p renamed)) == (← encoding (pair p p)))
  let letX := Expr.letE `x nat (mkNatLit 0) (.bvar 0) false
  let letY := Expr.letE `y nat (mkNatLit 0) (.bvar 0) false
  report "compact_source_let_renaming_invariant"
    ((← encoding (pair letX letY)) == (← encoding (pair letX letX)))
  distinct "let_nondep" letX (.letE `x nat (mkNatLit 0) (.bvar 0) true)
  let metadata (data : MData) := Expr.mdata data nat
  distinct "metadata_value" (metadata ⟨[(`tag, .ofNat 0)]⟩)
    (metadata ⟨[(`tag, .ofNat 1)]⟩)
  distinct "metadata_order" (metadata ⟨[(`a, .ofNat 0), (`b, .ofNat 1)]⟩)
    (metadata ⟨[(`b, .ofNat 1), (`a, .ofNat 0)]⟩)
  let withSyntax (s : Syntax) := metadata ⟨[(`syntax, .ofSyntax s)]⟩
  distinct "metadata_source_info" (withSyntax (.atom .none "x"))
    (withSyntax (.atom (.synthetic ⟨0⟩ ⟨1⟩ true) "x"))
  distinct "metadata_raw_substring"
    (withSyntax (.ident .none ⟨"ax", ⟨1⟩, ⟨2⟩⟩ `x []))
    (withSyntax (.ident .none ⟨"bx", ⟨1⟩, ⟨2⟩⟩ `x []))
  let universes (u v : Name) := pair (.sort (.param u)) (.sort (.param v))
  report "compact_source_universe_renaming_invariant"
    ((← encoding (universes `u `v) [`u, `v]) == (← encoding (universes `a `b) [`a, `b]))
  report "compact_source_universe_order_distinct"
    ((← encoding (universes `u `v) [`u, `v]) != (← encoding (universes `v `u) [`u, `v]))
  distinct "raw_level" (.sort (.param `u)) (.sort (.max (.param `u) .zero))
  distinct "raw_proof_subterm" (mkConst ``True.intro)
    (mkApp (.lam `h (mkConst ``True) (.bvar 0) .default) (mkConst ``True.intro))

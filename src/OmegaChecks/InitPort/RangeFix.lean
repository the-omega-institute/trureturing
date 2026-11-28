module
public import OmegaChecks.InitPort.CertifiedFunction
public import Init.Data.Range.Polymorphic.RangeIterator
import all OmegaChecks.InitPort.Alternatives.RangeLoop
import all Init.WFExtrinsicFix

/-! An inclusive bounded range supplies termination for the official recursive step. -/

open Lean Std Std.Iterators Std.PRange OmegaChecks.InitPort.Alternatives
namespace OmegaChecks.InitPort.RangeFix

@[expose] public noncomputable def reference.{u,v,w,x,r}
    {A : Sort u} {B : A → Sort v} {C : ∀ a, B a → Sort w} {D : ∀ a b, C a b → Sort x}
    [∀ a b c, Nonempty (D a b c)]
    {α γ : Type r} [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    (pl : α → γ → ForInStep γ → Prop)
    (key : ((a : A) ×' (b : B a) ×' C a b) → IterM (α := Rxc.Iterator α) Id α × γ)
    (F : ∀ a b c, (∀ a' b' c', InvImage (IteratorLoop.rel (Rxc.Iterator α) Id pl) key
      ⟨a', b', c'⟩ ⟨a, b, c⟩ → D a' b' c') → D a b c) (a b c) : D a b c :=
  WellFounded.extrinsicFix₃ (C₃ := D) _ F a b c

public noncomputable def implementation.{u,v,w,x,r} : type_of% @reference.{u,v,w,x,r} := by
  intro A B C D nonempty α γ enum le dec law compat pl key F a b c
  letI := closedFinite (α := α)
  exact finiteFix₃ (C₃ := D) (InvImage.wf key (IteratorLoop.wellFounded_of_finite (P := pl))) F a b c

public theorem agreement.{u,v,w,x,r} : @reference.{u,v,w,x,r} = @implementation.{u,v,w,x,r} := by
  funext A B C D nonempty α γ enum le dec law compat pl key F a b c
  letI := closedFinite (α := α)
  exact WellFounded.extrinsicFix₃_eq_fix (InvImage.wf key (IteratorLoop.wellFounded_of_finite (P := pl)))

public def owner := `Init.Data.Range.Polymorphic.RangeIterator
public def helper := mkPrivateNameCore owner `Std.Rxc.Iterator.fixWithUpperBound

public def specialize? (sub : Expr) : MetaM (Option Expr) := do
  unless sub.getAppFn.isConstOf ``WellFounded.extrinsicFix₃ do return none
  let #[A, B, C, D, ne, rel, step, a, b, c] := sub.getAppArgs | return none
  unless rel.getAppFn.isConstOf ``InvImage do return none
  let #[_, _, base, key] := rel.getAppArgs | return none
  unless base.getAppFn.isConstOf ``IteratorLoop.rel do return none
  let #[it, m, α, _, γ, pl] := base.getAppArgs | return none
  unless it.getAppFn.isConstOf ``Rxc.Iterator && m.isConstOf ``Id do return none
  try
    return some (← Meta.mkAppOptM helper
      #[A, B, C, D, ne, α, γ, none, none, none, none, none, pl, key, step, a, b, c])
  catch _ => return none

end OmegaChecks.InitPort.RangeFix

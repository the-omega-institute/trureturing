module
prelude
public import OmegaInit.Prelude

/-! Omega original.

Cancellation bounds a separation when two points have a common quotient
base. The ordered addition is supplied by its laws, so the estimate is
independent of a particular natural-number implementation.
-/

@[expose] public section

namespace Omega.Arithmetic.CompactFloor

/-- Move the lower point's base to the upper bound and cancel the common
lower point. In a quotient band, `gap` is a multiple of the step and
`cap` bounds the upper residue. -/
theorem band_span {A : Sort u} (add : A → A → A) (le : A → A → Prop)
    (trans : ∀ {a b c}, le a b → le b c → le a c)
    (mono : ∀ a {b c}, le b c → le (add a b) (add a c))
    (cancel : ∀ {a b c}, le (add a c) (add b c) → le a b)
    {gap lower base cap : A}
    (hgap : le (add gap lower) (add cap base)) (hbase : le base lower) :
    le gap cap :=
  cancel (trans hgap (mono cap hbase))

end Omega.Arithmetic.CompactFloor

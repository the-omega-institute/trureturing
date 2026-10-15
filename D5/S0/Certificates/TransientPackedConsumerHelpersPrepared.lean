/- Prepared transient helpers for the actual finite EJM packed consumer;
uncompiled. The original FinitePackedLaneGuard source is preserved unchanged.
Mathlib's ofDigits addition is unconditional, including arithmetic carries;
the guard consumer still requires bounds on both full resulting lane operands.
Native packing, broadcast alignment and source-coordinate coverage remain
separate proof obligations. No actual guard or bucket acceptance is asserted.
These requested integration helpers are not canonical wrapper deliveries.
Compiled source-owned evidence and binding remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/16309. -/

import D5.S0.Certificates.FinitePackedLaneGuard
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PackedConsumerHelpersPrepared
open D5.S0.Certificates.FinitePackedLaneGuard (pack mask guard_le)

/-- Pointwise function addition has exactly the arithmetic sum of its packs.
No range premise is needed for this identity; guard bounds are separate. -/
theorem pack_ofFn_add (width : ℕ) {n : ℕ} (f g : Fin n → ℕ) :
    pack width (List.ofFn (fun i => f i + g i)) =
      pack width (List.ofFn f) + pack width (List.ofFn g) := by
  have zipped : (List.ofFn f).zipWith (· + ·) (List.ofFn g) =
      List.ofFn (fun i => f i + g i) := by
    apply List.ext_getElem
    · simp only [List.length_zipWith, List.length_ofFn, Nat.min_self]
    · intro i leftInside rightInside
      simp only [List.getElem_zipWith, List.getElem_ofFn]
  have lengths : (List.ofFn f).length = (List.ofFn g).length := by
    simp only [List.length_ofFn]
  have addition := Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq
    (b := 2 ^ width) lengths
  simpa only [pack, zipped] using addition.symm

/-- Consume the packed guard on the exact ofFn lists and recover every Fin n
comparison. Both bounds concern the full values f i and g i, including sums
and offsets, rather than only their component summands. -/
theorem guard_ofFn_le (width : ℕ) (positive : 0 < width) {n : ℕ}
    (f g : Fin n → ℕ)
    (fBound : ∀ i, f i < 2 ^ (width - 1))
    (gBound : ∀ i, g i < 2 ^ (width - 1))
    (guard : Nat.land
      (mask width n + pack width (List.ofFn g) - pack width (List.ofFn f))
      (mask width n) = mask width n) :
    ∀ i, f i ≤ g i := by
  have boundsOfFn : ∀ h : Fin n → ℕ, (∀ i, h i < 2 ^ (width - 1)) →
      ∀ x ∈ List.ofFn h, x < 2 ^ (width - 1) := by
    intro h bounded x member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact bounded i
  have lengths : (List.ofFn f).length = (List.ofFn g).length := by
    simp only [List.length_ofFn]
  have pointwise := guard_le width positive (List.ofFn f) (List.ofFn g) lengths
    (boundsOfFn f fBound) (boundsOfFn g gBound)
    (by simpa only [List.length_ofFn] using guard)
  intro i
  have atIndex := pointwise.get (i := i.val)
    (by simpa only [List.length_ofFn] using i.isLt)
    (by simpa only [List.length_ofFn] using i.isLt)
  simpa only [List.get_eq_getElem, List.getElem_ofFn, Fin.eta] using atIndex

#print axioms pack_ofFn_add
#print axioms guard_ofFn_le
end PackedConsumerHelpersPrepared

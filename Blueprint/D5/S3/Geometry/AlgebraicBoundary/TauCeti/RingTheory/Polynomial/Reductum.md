# Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Reductum.

## Abstract

Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Reductum.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/Polynomial/Reductum.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For every semiring R, reductum p k is the coefficient cutoff below k: its i-th coefficient is p.coeff i if i<k and zero otherwise. This is pinned PowerSeries.coeff_trunc applied to p.toPowerSeries. In particular cutoff zero is zero, cutoffs above natDegree p equal p, and cutoff at natDegree p equals p.eraseLead. These conclusions include zero and trivial semirings. The finite set reducta p is the image of the cutoffs k<natDegree p+2, so it contains every distinct reductum, including p and zero.

The same set is the image of (eraseLead^[k]) p over k<support.card p+1. For nonzero p, coefficient comparison gives reducta p = insert p (reducta p.eraseLead): a cutoff below the degree is unchanged by erasing the leading coefficient; a cutoff between the two successive degrees is p.eraseLead; the only cutoff above the original degree is p itself. The bounded orbit has the identical recurrence by splitting its iterate index into zero and a successor and using pinned card_support_eraseLead_add_one. At p=0 both sets are {0}. Strong induction on support.card therefore proves equality of the two finite sets in both directions.

Pinned card_support_eraseLead and Function.Semiconj.iterate_right give support.card((eraseLead^[k]) p)=support.card p-k. Hence every iterate at or beyond support.card p is zero; no nonzero/positive-degree premise is needed. The actual Collins proof uses reductum_map, map_reductum_natDegree_map_add_one, natDegree_reductum_natDegree_map_add_one and reductum_mem_reducta to select cutoffs at the mapped degrees. This preserves its original coefficient-ring and HasUniqueDiv conditions, independently of the orbit description.

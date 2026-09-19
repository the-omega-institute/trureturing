[Index](../marked_head_profile.md) · [Full-tail mean](360-mean-partial-matching-without-tail-loss.md) · [Shallow source bound](366-shallow-tail-truncation-on-the-actual-source.md) · [Maximum-selection obstruction](369-whole-maximum-matchings-can-have-no-common-slots.md)

# Integrated source budgets survive a one-edge rank loss

The whole-cover example of 369 has no unit-slot-compatible family that
maximizes every local rank. Nevertheless, its actual shallow graphs admit
a compatible partial family retaining all forced edges and every prime's
integrated source lower bound from 366. Its total size is 862, exactly one
below the sum 863 of the independent maximum ranks.

Thus that obstruction does not exclude the weaker requirement consumed by
the integrated target budgets. The family uses all 595 original private
sources and keeps every selected edge below its actual cofactor cutoff.
Only one source loses rank. This is an exact result for the same even-cover
control, not a universal selection theorem, an odd covering system, or a
legal replacement of the original arithmetic progressions.

## 1. The quota required by the integrated bound

Retain the literal cover, period Q, original prime-private sets and full
CRT coordinates of 369. For prime q let H_q be its complete original
height, R_q its actual cofactor region, and ell_q(x) the cutoff of 366.
There are q^(H_q-1) private tails at each x in R_q. The strengthened
integrated source lower bound, expressed in integer counts, is

    B_q = sum_(x in R_q) q^(H_q-1)
              [q-2+q^(1-ell_q(x))].

Each summand equals
`(q-2)q^(H_q-1)+q^(H_q-ell_q(x))`, an integer. Under the original Haar
law every selected edge carries source mass 1/Q, so `B_q/Q` is exactly
366's b_q. No independent source normalization is introduced.

For comparison, the earlier 360 lower bound is

    B_q^base = (q-2)|Priv_q|+|R_q| <= B_q.

The present construction satisfies the stronger B_q. A selection needs
only `sum_(y in Priv_q)|M_(q,y)| >= B_q` for this integrated requirement;
it need not maximize every source or satisfy the cutoff-dependent mean
separately on every cofactor.

## 2. Exact compatible optimum for the whole example

Use the 24 original classes of 369, unchanged. Their actual cutoff counts
and the resulting quotas are:

| q | Private sources | Sources with cutoff 1 | Sources with cutoff 2 | B_q | Independent maximum total | Compatible total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 397 | 397 | 0 | 397 | 397 | 397 |
| 3 | 165 | 147 | 18 | 318 | 324 | 323 |
| 5 | 25 | 15 | 10 | 92 | 94 | 94 |
| 7 | 8 | 8 | 0 | 48 | 48 | 48 |

There is a joint choice with

    M_(3,351) = {6},

while all other 594 sources retain maximum rank. All original globally
forced edges remain selected. Every residual slot (z,d) has load at most
one, and every selected height is at most ell_q(cofactor(y)).

At the critical point z=1, this choice removes the first source's use of
525. The q=5 source uses 315 and the q=7 source can use 525. These are
the same two original slots that forced the three-source collision in
369. Choices at the remaining sources must still be made jointly;
repairing this point alone is not a whole-family certificate.

The checker constructs the complete family from the actual shallow
maximum menus, allowing the stated one-source deletion. It separates
components only when their complete candidate footprints share no
residual slot, searches their finite joint choices, and then validates
the assembled family at every source and every original residual slot.
It does not require an optimizer, an external witness file, or a new law.

The total is

    397+323+94+48 = 862.

No compatible partial family can have size 863: every local size is
bounded by its local maximum, so equality with their sum would force
every source to be maximum, contradicting 369. Thus 862 is the exact
maximum, including among arbitrary partial families. The restricted
construction is used only for attainment of this upper bound.

## 3. Where the source surplus is spent

For q=3, the cofactor x=1 modulo 350 has cutoff one and three complete
tails. Their selected sizes sum to five, below the local strengthened
quota six. At each of the six cofactors

    x in {23,71,93,163,233,303} modulo 350,

the cutoff is two and those three tails have total selected size five,
above their local quota four. Every other ternary cofactor attains its
local quota exactly. The net ternary surplus is therefore `6-1=5`.

For q=5, the cofactors 37 and 85 modulo 126 each have cutoff two and
five complete tails. Each contributes 17 selections against quota 16;
all other quinary cofactors attain their local quota. The surplus is two.
The binary and septenary quotas are attained exactly.

This is a comparison of actual counts on the original cofactor sets.
No point is moved to another cofactor, and no tail is discarded. Surplus
from different cofactors is combined only in the stated sum for one
prime. The construction fails the stronger demand that every cofactor
retain its separate cutoff-dependent mean.

Indeed, that stronger joint demand is impossible for this example.
All three critical cofactors of 369 have cutoff one, whose demanded
mean is q-1. Since no source exceeds q-1, every tail at each such
cofactor would have to saturate every root. In particular the three
critical sources would again demand three uses of two slots.

## 4. A precise criterion for repairing a fixed family by deletion

The following criterion applies to any fixed family of actual local
matchings and any integer prime quotas B_q that it already attains.
It is a direct application of finite Hall matching, not a new abstract
matching theorem or a claim that the required inequalities always hold.

Let N_q be the selected count at prime q and put `Delta_q=N_q-B_q`.
For each residual slot e=(z,d), let U_e be the set of primes whose
fixed selections use it. For a fixed prime a slot is used at most once,
because the original reset recovers its unique source. Retain all edges
whose targets are nonresidual.

There is a subfamily obtained only by deleting edges, satisfying every
quota and every residual unit capacity, if and only if for every prime
subset S,

    sum_e (|U_e intersect S|-1)_+ <= sum_(q in S) Delta_q.
                                                        (DB1)

Necessity counts the removals required from the uses belonging to S:
each slot can retain at most one of them, and prime q can lose at most
Delta_q selections.

For sufficiency, let O_q be the number of residual uses by q. It needs
to retain at least `t_q=max(0,O_q-Delta_q)` of them. Form a bipartite
graph with t_q copies of prime q, all adjacent to the actual slots it
uses, and unit slot capacity. Hall's condition is

    sum_(q in S) t_q <= |union_(q in S) N(q)|.

Since
`sum_(q in S) O_q-|union_(q in S)N(q)|`
equals the left side of DB1, these conditions are equivalent: to handle
the positive part in t_q, apply DB1 to the members of S with positive
`O_q-Delta_q`. Conversely, discarding negative summands can only
strengthen the Hall requirement. An injective Hall choice specifies
which uses to retain. Deleting the others preserves all local root and
color constraints and any original height cutoff.

If the fixed family includes the globally forced edges of 364, these
survive this deletion procedure. Their lifts are private to their
original child, so they lie outside the residual capacity constraint.

Dividing DB1 by Q yields the same criterion in original Haar masses.
Its left side is the integral, over residual z, of
`sum_(d in E(z))(sum_(q in S)L_(q,d)(z)-1)_+`, with literal selected
incidence indicators L. No separately optimized marginals are combined.

DB1 is necessary and sufficient for deleting from the specified family.
It is only sufficient when exchanges to other original edges are also
allowed. A bad initial family need not decide the unrestricted choice
problem. The construction in section 2 allows joint menu choices before
making its one deletion.

## 5. Verification and remaining arithmetic requirement

The extended [exact checker](../frontier/whole_maximum_slot_obstruction.py)
retains the full cover and all-source verification of 369, then checks
the constructive partial repair independently. Its added checks cover
all source ranks, original labels, complete tails, cutoffs, forced edges,
residual capacities, integral quotas and the cofactor surpluses above.
The original 7,457 checks remain, and 10,069 added checks validate the
repair. Its 305 occupied residual slots all have load one; all 239 forced
incidences lift to private targets. Ordinary execution and execution from
an unrelated directory with `python3 -I -S -O -B` give identical output.

Finite Hall is already available in pinned Mathlib as
`Finset.all_card_le_biUnion_card_iff_existsInjective'`. The repository's
[rational flow/cut certificate module](../../../../D5/S0/Certificates/RationalSTCutCertificate.lean)
provides weak duality and certificate soundness; it is not an integer
flow existence theorem. Neither is wrapped in a new Lean declaration.
The present argument and finite checker are not Lean verified.

The unrestricted odd-cover task still needs an arithmetic proof that
appropriate joint choices meet a sufficient family of such cuts, or
another valid allocation using the actual original labels and law.
Passing this control supplies no universal cut bound and no whole-AP
replacement. It establishes that the integrated source requirement
survives the specific obstruction that defeats pointwise maximality.

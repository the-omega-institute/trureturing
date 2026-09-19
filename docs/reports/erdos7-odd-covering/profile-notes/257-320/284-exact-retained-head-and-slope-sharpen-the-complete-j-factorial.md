[Index](../../marked_head_profile.md) · [Complete retained-pair source](276-actual-retained-tail-pairs-strengthen-original-j-costs-and-square.md)

# Exact retained head and slope sharpen the complete J factorial bound

On both entire actual saturated J faces, the original load A satisfies

    integral Phi5(A) dmu
      <=782845887531143161/992250000000000000
       =0.7889603300893355... .                          (EH1)

Here Phi_k(n)=(n-k)_+*(n-k+1)_+/2. Compared with276's complete
Phi5 bound4552688500270367/5670000000000000, the exact improvement is

    1734325002021383/124031250000000000
      =0.01398296801831299... .                          (EH2)

The source constraints are the unchanged3306-variable model. The gain
comes from evaluating the retained factorial head and its selected
positive-seven slope exactly. Every original residue, all62,500,000
containing choices, the common late interval and all exponent tails
remain. No additional source constraint or actual optimizer is asserted.

## Apply the full-tail inequality after counting retained events

For every nonnegative integer x,T and integer k>=1, set

    h_k(x)=(x-k+1)_+.

The complete inequality is

    Phi_k(x+T)<=Phi_k(x)+h_k(x)*T+binom(T,2).             (EH3)

When x>=k-1, expanding gives equality for every T. Otherwise put
 a=k-1-x>=1. The right side is binom(T,2), while the left side is
binom((T-a)_+,2), which is no larger. This proves the unbounded
integer domain without a finite load cutoff.

Keep the original shallow head B=1+I3+I9+I5+I15+I45. Let R count
exactly the six retained zero-seven labels25,27,75,81,135,125.
Write the complete load as

    A=B+R+T,

where T contains every other zero-seven label and every positive-seven
label. Applying(EH3) at x=B+R keeps the retained contribution exact.
For comparison with276's split, define

    G_B(R)=Phi_k(B)+h_k(B)*R+binom(R,2)-Phi_k(B+R),
    S_B(R)=h_k(B)+R-h_k(B+R).                            (EH4)

Both are nonnegative. With a=(k-1-B)_+,

    S_B(R)=min(R,a),
    G_B(R+1)-G_B(R)=S_B(R).                             (EH5)

If B>=k-1, both vanish. Otherwise
G_B(R)=binom(R,2)-binom((R-a)_+,2). These are exact identities,
not new probabilistic assumptions.

Thus the old expansion can be improved by using Phi_k(B+R) as its
head and h_k(B+R) as its remaining-load slope. The same old slope
h_k(B)+R may still upper-bound any remaining nonnegative term for
which a sharper integral is not available.

## The head uses the actual survivor states

Use276's four-bit mask q=popcount(mask) for25/27/75/81 and its three
nonempty135/125 states with counts n_s=(1,1,2). At each rectangle-mask
coordinate, Y is the total survivor mass and V_s its marked-state
masses. The implicit zero-state complement is already represented
in Y. Exact integration of the new head is

    Phi_k(B+q)*Y
      +sum_s[Phi_k(B+q+n_s)-Phi_k(B+q)]*V_s.             (EH6)

Equivalently, subtract G_B(q) on Y and
G_B(q+n_s)-G_B(q) on V_s from the old retained-head coefficients.
This is an exact integral on the same actual survivor mu. There is
no extra copy of Y for each marked state.

## The selected positive-seven slope uses the actual raw states

Keep precisely276's selected positive-seven blocks: cofactor1 at
every positive depth, cofactors3,5,9,15 at depth1, and cofactors3,5
at depth2. For a fixed set of the six independent projections, write

    W_i=1/5+(6/35)*m1_i+(6/245)*m2_i.                  (EH7)

The coefficient1/5 is the entire geometric sum over cofactor1 depths.
The raw source X and its marked-state restrictions U_s upper-bound
these terms using the usual conditional seven-coordinate caps.
Apply those caps directly to the nonnegative new slope h_k(B+R).
The resulting complete selected-block bound is

    W_i*h_k(B+q)*X
      +W_i*sum_s[h_k(B+q+n_s)-h_k(B+q)]*U_s.           (EH8)

This replaces the old cap expression using W_i*(h_k(B)+R).
Algebraically the coefficient changes are S_B(q)*W_i on X and
[S_B(q+n_s)-S_B(q)]*W_i on U_s. The argument first changes the
nonnegative integrand in the same selected cap summand, then applies
its cap. It does not subtract an upper estimate from an unknown
actual cross integral. In particular, these coefficients use raw
X/U, without an additional survivor density factor.

## Every complementary tail remains

All unselected terms retain the old valid coefficients. Since
h_k(B+R)<=h_k(B)+R, the complete unselected old and positive-seven
cross bounds of276 still dominate their new slopes.
The old-old, old-positive-seven and positive-seven-pair partitions
are unchanged:

    selected POO payment=8857/202500,
    selected POZ payment=5402/91875,
    original full pair bound=4879/7200.

The fifteen retained old-old pairs are absorbed into(EH6). The42
selected old-positive-seven cap blocks combine with the corresponding
shallow-head cross to give(EH8). Every unselected original pair stays
in its assigned complete complement. No further pair payment is
subtracted, and the conditional PZZ term is unchanged.

The five old cross remainders, raw positive-seven mask remainders,
complete conditional first/second-depth tables and later-depth
constant31/1470 remain exactly those of276. Only the coefficients
of the already retained head and selected blocks change. The common
late secant coefficient and full tail constant are unchanged.
This proves the modified objective for every finite original family
with arbitrary exponent heights; the inherited nonnegative geometric
tails cover all omitted heights. The same source relabelling covers
both complete saturated J orientations.

## Full original-domain certificate

The helper independently checks all42 pairs of shallow head
B=1,...,6 and retained count R=0,...,6 in(EH4)--(EH5). For every
objective it also verifies the final coefficients directly against
(EH6) and(EH8), including each marked-state increment. The general
proof(EH3), rather than these finite coefficient checks, justifies
the remaining unbounded tail.

The earlier full-function affine bounds remain valid for Phi5.
They may therefore still prune a complete branch before the stronger
joint objective is evaluated. Sixty original independent seed branches
are rechecked with the changed objective; their optimality is not
assumed. The full scan records

| Bound | Count |
| --- | ---: |
| Whole layouts pruned |12488|
| Remaining conditional projections |60000|
| Conditional projections pruned |59383|
| Remaining exact-dual branches |617|

The exact coverage identity is

    5000*12488+59383+617=62500000.                       (EH9)

The637 distinct rational duals check2,105,922 domination columns.
Every branch decision and the largest retained certificate bound
recompute exactly. The maximizing bound uses layout(1,4,2,1,2,4,2)
and projection(1,4,4,1,4,1,4); this is not an actual attainment claim.

The [helper](../../frontier/j-geometry/j_face_exact_retained_factorial_head.py) and
[certificate](../../certificates/source_norms/j-geometry/j_face_exact_retained_factorial_head.json)
use the existing rational-table/run-length dual codec and logical
split-artifact reader. Canonical replay needs only exact standard-library
arithmetic:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_exact_retained_factorial_head.py --check
```

The result is a complete source bound. A separate consumer is needed
for the full52-cost comparison. Off-face transport, global joining,
Lean verification and unrestricted Erdos7 are not conclusions of
this source certificate.

[Index](../../marked_head_profile.md) · [Column heights](355-column-height-matching-bound.md) · [Mean matching](360-mean-partial-matching-without-tail-loss.md) · [Common source](363-common-source-antichain-capacity.md) · [Forced colors](364-singleton-cofactor-ideal-and-forced-colors.md)

# Complete shallow-tail coverage sharpens the actual mean source bound

At each original prime-private cofactor state, the height statistic of
355 preserves more than one shallow full matching: retaining all labels
up to that height still covers every nonprime root at every tail.
Applying 360 to this complete truncated model improves the mean matching
lower bound on the same source. The shared target allocation of 359 and
the prime-parent bound of 363 then apply to these actual selections.

The gain is adaptive in the cofactor state. In a whole irredundant cover,
the global height statistic equals the original height; replacing it by
a smaller constant gives no improvement. Nor can the target-capacity
denominator be made point-dependent without another allocation proof.
An actual divisor-closed period-60 cover disproves that proposed
columnwise replacement.

These are ordinary finite arguments and exact checks. The mean-rank,
matching, CRT and target-allocation results are reused. No literature
novelty, new Lean verification, new excluded prime-support class, or
resolution of unrestricted Erdős #7 is claimed.

## 1. The order statistic preserves all local coverage

Use 354's original model at a prime q and a fixed cofactor state
`x in R_q`. Keep the full original height H and the uniform tail
`T_q=Z/q^(H-1)Z`. Each compatible original label `d=q^e m` has
one nonprime first-q root, one tail prefix of depth `e-1`, and
its actual numerical cofactor m. Numerical distinctness gives at
most one label for each `(m,e)`. The pure color m=1 has no label
at e=1 on these roots. Every root is covered at every complete tail.

For each compatible nonpure color put

    h_m(x)=max{e : the original q^e m is compatible with x}.

There are at least q-1 such colors by 354. Let `ell_q(x)` be the
(q-1)-st largest value, counting different colors separately. Fix
`ell=ell_q(x)`. The set of colors with `h_m(x)>ell` has size at
most q-2. Retain exactly the compatible original labels with
`e<=ell`.

**Every root is still covered at every tail.** To prove this, take
any root and any tail cylinder J of depth ell-1. A prefix of depth
at most ell-1 either contains J or misses it. If no retained label
at this root contains J, all of J must be covered by later labels.
They use at most q-2 nonpure colors and one pure color. At each
exponent e>ell there are therefore at most q-1 such labels, even
before discarding those at another root or outside J. Each one
meets J with relative mass at most `q^(ell-e)`. The union bound is

    (q-1) sum_(e=ell+1..H) q^(ell-e)
       = 1-q^(ell-H) < 1.

This contradicts complete coverage of J. The same argument applies
to every root and every J, including ell=H when the sum is empty.

The estimate already occurs in 355 for the one node reached by its
matching path. Its application to every node is what establishes
complete shallow coverage here. This does not assert that the
truncated graph has the full graph's maximum rank at every tail,
or that a deep original AP can be removed from the whole cover.
The cutoff depends on x.

The retained labels depend only on the first ell-1 tail digits.
Their quotient has the uniform `Z/q^(ell-1)Z` law; every quotient
point has exactly `q^(H-ell)` preimages under the original tail
Haar law. Thus 360 directly gives, for maximum matchings of this
truncated nonpure graph,

    E_(t in T_q) rank_low(q,x,t)
       >= q-2+q^(1-ell_q(x)).                         (ST1)

The matching witnesses remain original numerical labels of heights
at most ell_q(x), all at the same cofactor and tail. The proof's
quotient does not replace the original carrier or its measure.

## 2. Integrate on the original prime-private source

Write H_X for uniform probability on the complete original cofactor
space, and pi_q for the original prime-private Haar mass. As in 354,

    Priv_q={a_q mod q} x T_q x R_q,
    pi_q=H_X(R_q)/q > 0.

Define the dimensionless mean lower bound and its actual source mass

    rbar_q=q-2+E_(x uniform on R_q) q^(1-ell_q(x)),
    b_q=rbar_q pi_q
       =(1/q) integral_(R_q) [q-2+q^(1-ell_q(x))] dH_X.

Choose a maximum matching of the truncated graph at every source.
Summing ST1 gives, on the original full Haar law H,

    integral_(Priv_q) selected_count dH >= b_q.       (ST2)

No independently optimized cofactor states or resampled tails are
combined. Each finite source has its own actual matching, and all
source masses use the original H. These matchings need not maximize
the rank of the untruncated graphs; the lower bound and the later
capacity argument require only the stated actual selections.

For `r_q=q-2+q^(1-H_q)`, the gain is exactly

    rbar_q-r_q
      =(q-1) sum_(h=1..H_q-1) q^(-h)
                 Pr_(x uniform on R_q)[ell_q(x)<=h]. (ST3)

It is nonnegative, and is positive precisely when a positive part
of the original R_q has ell_q(x)<H_q. There is presently no uniform
positive lower bound on that part under the hypothetical extremal
odd-cover assumptions.

## 3. The same target budget consumes the stronger source lower bound

Retain all the hypotheses and quantities of 363, including divisor
closure where it supplies original parents. In particular,

    alpha_q=q/(q-1)(1-q^(-H_q)),
    U_q=min((s-1)pi_q, u_q+min(epsilon_q,Delta_q^F)).

Here s counts original support primes, u_q is the sum of private
masses of actual prime-cofactor children, and epsilon_q and Delta_q^F
are the same residual source and containing-cylinder excess masses
as in 363. They are not recomputed under a new probability law.

Its prime-parent upper bound holds for the chosen truncated partial
matchings: the lift is still injective for each fixed q, keeps the
same original cofactor and tail, and uses original labels. If C_q
is the original H-integral of their selected composite-parent count,

    C_q >= (b_q-U_q)_+.

Applying the unchanged 359/363 allocation therefore yields

    sum_q (b_q-U_q)_+/alpha_q <= M_comp,              (ST4)

    M_comp=sum_(m composite in D) (1/m)
                 [1-product_(p in Lambda:p not dividing m)(1-1/p)].

The forced singleton columns of 364 all have height one, so they
remain in every truncated graph. Relocating their colors to their
degree-one roots preserves the selected color set and rank and
keeps every witness below the cutoff. If f_q is the number of
these forced composite colors, the same used-height argument gives

    sum_q [f_q pi_q
           + (b_q-f_q pi_q-U_q)_+/alpha_q] <= M_comp. (ST5)

ST4 and ST5 dominate their coarse 363 and 364 lower bounds since
`b_q>=r_q pi_q`. They refine those guaranteed source bounds, not the
exact 359 allocation once the actual selected source sets and used
heights are known. A strict mean improvement may be absorbed by
the prime-parent allowance U_q and need not strictly improve ST5.

## 4. Global irredundancy prevents a smaller constant cutoff

Let z be private to an original `d=q^e m`, d!=q. The reset result
of 357 places its cofactor x in R_q. If `e>ell_q(x)`, complete
shallow coverage would cover z with another original label of
strictly smaller q-height, contradicting privacy. Hence

    z in Priv_d, q^e exactly divides d, d!=q
       ==> ell_q(cofactor(z)) >= e.                 (ST6)

In particular a private point of a class with maximal height H_q
gives ell_q(x)=H_q (for H_q=1 this already holds everywhere).
Thus the global statistic L_* of 355 equals H_q in every whole
irredundant model with the present prime interface.

This equality also follows from the existing Simpson highest-digit
cut recorded in 343: taking its divisor `Q/q` requires at least q
original labels of q-height H_q. At most one is pure, so at least
q-1 distinct nonpure columns reach H_q. Consequently the class-count
consequence `n>=q H_q+q-1` under divisor closure is not a new bound.

ST6 is a support restriction as well: high-label private witnesses
cannot be counted as shallow-cofactor gain in ST3. The global
maximum equaling H_q does not prevent other cofactor states from
having a smaller cutoff.

## 5. Point-dependent capacity denominators fail on an actual cover

Consider these nine original classes of period 60:

    (0 mod 2), (0 mod 3), (3 mod 4), (0 mod 5),
    (5 mod 6), (7 mod 10), (13 mod 15),
    (9 mod 20), (1 mod 30).

The full period is covered, every class has private points, the
modulus set is divisor-closed above one, and comparable classes
are disjoint. This is an even-cover control.

At q=2, the full height is 2 and the actual cofactor region is

    R_2={1,2,4,7,8,11,14} subset Z/15Z.

Its cutoff equals 2 at x=4,14 and equals 1 at the other five points.
For the one nonprime root, choose child 10 on source points
`{2,22,32,52}` and child 20 on `{4,44}`. Each selected child lifts
to its actual original class with no changed tail. Both have parent
m=5, all choices lie below their cutoff, and each is a maximum
matching at its source.

The two source masses are 1/15 and 1/30. Their respective cutoffs
are 1 and 2, so the proposed pointwise normalization gives

    integral_(S_(2,5)) 1/alpha_(ell_2(x)) dH
       = 1/15 + (1/30)/(3/2) = 4/45.

But the actual containing-cylinder bound of 359 for this column is

    rho_(2,5)/(2*5) = (1-1/3)/10 = 1/15.

The excess is 1/45. Using the fixed alpha_2=3/2 instead gives
`(1/15+1/30)/(3/2)=1/15`, exactly the permitted capacity.
The different exponent sources have different cofactor cutoffs;
normalizing each by its own geometric sum counts more than the
one available column budget.

This refutes the unlicensed columnwise denominator replacement.
It does not assert that an aggregated all-prime inequality fails,
or supply an odd-cover counterexample. ST4 and ST5 retain the
original alpha_q and do not use the invalid replacement.

## 6. Verification and remaining arithmetic obligation

The [standalone checker](../../frontier/whole-cover/shallow_tail_truncation.py)
retains original labels and complete tails, tests local sharp
models and actual whole even covers, and compares the cutoff
distribution, mean bounds, and selected-source quantities with
literal AP membership. A cutoff below the sharp threshold loses
coverage; the period-60 control detects the invalid adaptive
denominator. The affine refinement from 364 tests q=5 on its full
original source; missing parents prevent using that fixture as
a complete all-prime target-budget verification.

For a strict improvement within the complete target budget, use the
divisor-closed, irredundant period-450 cover

    (0 mod 2), (0 mod 3), (0 mod 5), (5 mod 6),
    (4 mod 9), (9 mod 10), (7 mod 15), (11 mod 25),
    (13 mod 30), (1 mod 45), (31 mod 50), (46 mod 75),
    (1 mod 150), (16 mod 225).

Comparable original classes are disjoint. Exact enumeration gives:

| q | rbar_q | Original 364 summand | ST5 summand |
| --- | --- | --- | --- |
| 2 | 1 | 2/75 | 2/75 |
| 3 | 76/39 | 0 | 1/50 |
| 5 | 18/5 | 7/270 | 1/30 |

At q=3, twelve of the thirteen cofactor states have cutoff one and
one has cutoff two. At q=5, one of the two cofactor states has each
cutoff. The complete lower bound increases from 71/1350 to 2/25,
a strict gain of 37/1350. For the checker's actual selected original
matchings, used heights and shared target allocation, the full chain is

    2/25 <= 29/300 <= 209/1800 <= 47/300 <= M_comp=11/50.

The affine period-921600 fixture separately has 1512 cutoff-one and
24 cutoff-two q=5 cofactor states. Its rbar_5 is 319/80 instead of
16/5, and its 364 source summand increases from 77/4608 to
511/23040, a gain of 7/1280. This fixture lacks original parents;
the strict source gain is not a complete M_comp claim.

The checker performs 168484 checks: 24 local sharp models, 20 actual
prime sources, 1706 actual cofactor models and 8232 actual source-tail
points. Three divisor-closed fixtures complete the target-budget
chain. Matching ranks are checked independently by all root-subset
Hall deficiencies. A normal run and an isolated optimized run from
a relocated path produce identical output. These checks are finite
experiments, not Lean verification; all whole-cover fixtures contain
even moduli.

The remaining task is to bound the low-cutoff source mass in ST3
from the full arithmetic/extremal hypotheses, or to use these
actual shallow selections in a complete covering-preserving repair.
The truncation and improved source estimate alone do not provide
either condition.

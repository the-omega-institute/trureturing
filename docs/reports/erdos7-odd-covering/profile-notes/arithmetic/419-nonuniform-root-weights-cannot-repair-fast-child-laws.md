[Index](../../marked_head_profile.md) · [Centered-layout lower certificates](391-diagonal-prefix-sources-obstruct-the-finite-height-moment-comparison.md) · [Sharp root classification](403-root-structure-of-sharp-minimum-sources.md) · [Concentrated clean signatures](407-limits-of-stationary-row-mixtures-and-finite-signature-summaries.md) · [Concentrated source](414-same-projection-transport-controls-concentrated-sharp-sources.md) · [Successful laws on that source](418-concentrated-sharp-sources-admit-a-common-law-at-every-height.md)

# Nonuniform root weights cannot repair uniformly fast child laws

There are actual sharp minimum sources in the single-+2/four-clean root
class on which every mixture of normalized five-decaying child laws
fails, regardless of its root weights. At every height K>=6 the original
independent-phase squared-load maximum of every such probability is at
least

    307459328/48828125 = 6 + 14490578/48828125 > 2t_K,
    t_K = 3-(K+2)3^-K.                              (F1)

This is an actual lower bound for the stated class of probabilities.
It does not exclude a different supported probability with slower or
more concentrated conditional tails, and it does not refute the
arbitrary-source comparison or unrestricted Erdős #7. The proof below
is ordinary analysis with exact finite controls, not Lean certification.

The source constructors and their signatures are reused from 407 and
414. The lower certificate uses the centered-layout averaging method
of 391. The additional conclusion is their combination on an explicit family
in the first root class of 403, with quantification over every root-weight
vector and every child probability obeying the stated decay condition.

## Actual sources in the single-+2/four-clean class

For K>=3 put h=K-1. Write F_h for the standard complete five-ary
seven-adic tree, with digits 0,...,4 read lowest first. Define S_K by
these five root children:

| Root column | Actual child source |
|---|---|
| 0 | The concentrated sharp source R_h from 414 |
| i=1,2,3,4 | The clean star-i source C_(i,h) from 407, with dominant row 1 |

The central child is admissible and has 5^h+2 points. Every clean child
has one row above each leaf of F_h. Its good row pairs are precisely
those containing i. Thus the four clean children divide 2:2 in each
complementary pair partition; the central child is good on both sides.
Every global row pair has three good root children, and the full
projection is F_K. The source has exactly 5^K+2 points, so 400's lower
bound makes it sharp minimum. This is the first pattern of 403 with
an actual admissible exceptional child, not merely assigned signatures.

The projected leaves carrying a non-row-1 point are disjoint from
those carrying row 1. In particular, the two duplicated projection
leaves of R_h have row pairs 34 and 24, so neither contains row 1.
The exact numbers of non-row-1 projected leaves are

    N_e(h) = 25*3^(h-2)-7                  in the central child,
    0                                      in clean child 1,
    N_c(h) = 5*3^(h-1)                    in clean children 2,3,4.
                                                     (F2)

The central count is the actual full-five disagreement count of 414
and 417: the only duplicated leaves are already entirely outside row
1, so choosing their smaller row counts the same projection set. The
clean count starts at five at height one and triples at each further
level. For h>=2,

    N_e(h)-N_c(h)=10*3^(h-2)-7>0.

## Every root weight and every conditional five-decay law

Choose any nonnegative w_0,...,w_4 with sum one. In each actual child
choose any normalized probability eta_i satisfying, for every tail
prefix and 1<=j<=h,

    eta_i(Y == u mod 7^j) <= 5^-j.                  (F3)

Put mass w_i on eta_i in root column i and call the resulting supported
probability nu. The weights and child laws may depend on the entire
source and on K; they are chosen before any original-divisor phases.
Zero root weights are allowed. Conditions on unused child laws cause
no restriction on nu, since every child has a uniform five-tree law.

At depth h the child has exactly 5^h projection leaves. Each has mass
at most 5^-h and their masses sum to one, so all these masses equal
5^-h. Splitting a duplicated leaf between its actual rows cannot
change its row-1 mass. Consequently, writing

    delta_h = N_e(h)/5^h,

the row-1 mass beta_1 of nu satisfies the exact identity and bound

    beta_1 = 1-w_0*delta_h-(w_2+w_3+w_4)(3/5)^(h-1)
           >= 1-delta_h.                           (F4)

No balance condition on the root weights has been used. Every law
permitted by F3 has this obstruction, including every available choice
at the central child's duplicated leaves.

## A fixed layout mixture converts concentration into actual cost

For z in F_K choose the original layout lambda_z centered at the CRT
point with row 1 and seven-adic coordinate z. It assigns a phase to
every original divisor 7^j and 5*7^j, including 1 and 5. These are legal
members of the full independent-phase layout family.

For a fixed point (r,y) of S_K define

    T(y,z) = sum_(j=0)^K 1_(y == z mod 7^j).

Its literal load under lambda_z equals (1+1_(r=1))*T(y,z). For z
uniform on F_K, each fixed y in F_K has

    E_z T(y,z)^2 = S_K(1/5),
    S_K(q) = sum_(j=0)^K (2j+1)q^j.                (F5)

Indeed, an ordered pair of prefix conditions with maximal depth j
matches exactly a fraction 5^-j of the centers, and there are 2j+1
ordered depth pairs with this maximum. Averaging over the one actual
probability nu therefore gives

    E_z E_nu ell_(lambda_z)^2 = (1+3*beta_1)S_K(1/5).

At least one legal layout has expectation at least this average. Hence
the original functional, with all phases still independent, obeys

    Gamma_K(nu) >= (1+3*beta_1)S_K(1/5)
                >= (4-3*delta_h)S_K(1/5).          (F6)

The centered layouts supply only a lower certificate; they do not
replace the full adversarial maximum. Their uniform mixture is fixed
before nu. The individual layout attaining at least the average may
depend on nu, as allowed by the original quantifier order.

## Failure at every height at least six

For h>=2,

    delta_h-delta_(h+1)
      = (50*3^(h-2)-28)/5^(h+1) > 0.

The positive factor 4-3*delta_h increases, and S_K(1/5) also increases.
At K=6, h=5, the lower bound in F6 is exactly

    delta_5 = 668/3125,
    (4-3*delta_5)S_6(1/5) = 307459328/48828125.

Its excess above six is 14490578/48828125, proving F1 at every K>=6.
At K=6 its excess above the finite target 4358/729 is

    11344881362/35595703125.

There is also a direct uniform target comparison. Report 407, SO9,
gives S_K(1/5)/t_K>=5/8, so

    Gamma_K(nu)-2t_K
      >= (4/5-3*delta_h)S_K(1/5)
      >= 496/3125                         for K>=6. (F7)

The stronger ceiling-six lower bound is already sufficient. Both
comparisons concern actual squared loads, rather than the failure of
a chosen root or tail upper bound.

## Every fixed decay rate faster than the ternary scale

Fix real constants C>=1 and 1/5<=c<1/3 independently of height and the
selected probabilities. Replace F3 by the conditional bounds

    eta_i(Y == u mod 7^j) <= C*c^j.                 (F8)

This class is nonempty, since uniform projection leaves satisfy F8.
Count the non-row-1 projected leaves at the last level using F2. For
every root weight vector and every collection of child laws in F8,

    1-beta_1 <= (25C/9)(3c)^h.

The same fixed layout mixture gives

    Gamma_K(nu)
      >= [4-(25C/3)(3c)^(K-1)]S_K(1/5).            (F9)

This lower bound tends to 15/2, so it eventually exceeds six. Thus
every sequence of laws satisfying the same C,c bounds fails the target
at all sufficiently large heights. An explicit sufficient condition
for F9 to exceed the finite target is

    (3c)^(K-1) < 12/(125C):

then the bracket in F9 exceeds 16/5, and SO9 applies. No uniformity is
asserted as c approaches 1/3 or as C grows. The ternary endpoint and
height-dependent constants are outside this obstruction.

## What this rules out, and what remains

[Report 401, section 8](401-a-recursive-minimum-source-has-one-law-at-every-height.md)
refutes one fixed equal-private-weight recipe on a pair-balanced
source. Report 407 proves that finite clean signatures cannot enforce
nontrivial fixed row polytopes under uniformly faster-than-ternary
decay. Here those concentration constructions occur inside an actual
sharp source with a single +2 child, and a common layout mixture turns
them into a lower bound on the original squared-load functional for
all root weights and all child probabilities in F3 or F8.

The central R_h itself admits successful probabilities by 418.
There is no contradiction: that theorem does not require its selected
probability to have normalized five-decay prefixes. Nor does success
of a child alone prove that it composes with four other children into
a successful root law. A complete selection theorem for arbitrary
single-+2/four-clean sources must permit other conditional tail laws
or retain additional joint structure. That theorem remains open here.

## Reusable constructors and exact verification

[`five_decay_root_mixture_obstruction.py`](../../frontier/cover-geometry/five_decay_root_mixture_obstruction.py)
provides:

* `source_children(K)` and `source(K)`, reusing 414's concentrated and
  clean-source constructors;
* `uniform_child_laws(K, split_duplicates=False)`, including an option
  to split duplicated projection leaves equally over their actual rows;
* `verify_child_mixture(K, weights, laws, constant=1, ratio=1/5)`, which
  checks actual support, exact normalization, every conditional prefix
  cap, and one common probability before applying the lower bound;
* `five_decay_bounds` and `fast_decay_bounds`, which evaluate F6 and F9
  for arbitrary allowed heights without enumerating leaves;
* `layout_average_lower_bound`, which evaluates F5's exact dual average
  for an actual supplied law on the standard five-tree carrier.

Program probabilities and C,c inputs are exact rational numbers. Its
source controls at K=3,4,5,6 check every actual child capability, every
global pair tree, the full five-tree, both projected-leaf counts and
the absence of row-1/non-row-1 ambiguity in a fibre. Mixture controls
include every pure root-weight vector, nonuniform weights, and split
central fibres. There are 2,604 literal original-layout/point checks of
F5 at heights 0,1,2, and 16 malformed-input controls. All checks use
explicit exceptions and remain active under `-O`.

From the repository root:

    python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/five_decay_root_mixture_obstruction.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/five_decay_root_mixture_obstruction.py

The finite controls establish correspondence with the retained
constructors and the literal phase game. The all-law and all-height
quantifiers come from the counting and averaging proof above.

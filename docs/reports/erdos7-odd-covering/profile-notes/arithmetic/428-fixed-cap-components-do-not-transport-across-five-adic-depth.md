[Index](../../marked_head_profile.md) · [Full-height forest laws](379-root-forest-disintegration-and-residue-costs.md) · [Previous common-law theorem](427-shared-row-cap-mixtures-break-the-six-barrier.md)

# Fixed cap components do not transport across five-adic depth

Report 427 permits arbitrary legal component laws to be fixed before
choosing their common mixture. That guarantee does not extend directly
from 5-height one to greater 5-height, even when the six pair components
retain all the first-root and 5-tail caps supplied by report 379.

At heights `(H,K)=(3,3)`, one complete actual source with a missing
first-5 root admits seven such fixed components for which every convex
mixture has complete original-layout squared load at least

    99992/10455 > t_3^2 = 5776/729,
    99992/10455 - 5776/729 = 4168696/2540565 > 0.             (FT1)

A common distribution on only four legal layouts certifies this lower
bound. The same source has a uniform law with exact complete-layout
moment `3933/1225`, strictly below the target. Thus the failure belongs
to transporting **arbitrary fixed components by changing only their
weights**. It neither refutes the unrestricted source comparison nor
an architecture that may choose its component laws jointly in advance.
An additional exact comparison keeps both complete coordinate marginals
unchanged while changing the joint law: the moment falls from `328/27`
to `5776/729`. Thus even complete separate coordinate distributions do
not determine the layout moment.
These are ordinary proofs and exact rational checks, not Lean results
or a resolution of Erdős #7.

## 1. A complete source satisfying the full-height tree conditions

Use lowest digits first and set

    R = {x mod125 : x mod5 in {1,2,3,4}} times Z/343.         (FT2)

Its size is `4*25*343=34300`. Every complete ternary 5-tree of depth
three meets the four allowed first roots, and all subsequent 5 tails
are present. Its product with any complete five-ary 7-tree of depth
three therefore meets `R`. The full 7-projection contains complete
five-ary trees; every pair-row projection is the full 7 carrier and
contains complete ternary trees. The separate 5-projection condition
also holds. No condition is being inferred for an arbitrary individual
conditional fibre.

For a supported probability `nu`, keep the original independent layout
definition

    Gamma_(3,3)(nu) = max_lambda E_nu L_lambda^2,
    L_lambda = sum_(0<=a,b<=3) 1_(x=u_(a,b) mod5^a,
                                  y=v_(a,b) mod7^b).         (FT3)

Every pair of phase residues is independently allowed. CRT identifies
it with one phase for the original numerical divisor `5^a7^b`; all
sixteen labels, including one, remain present.

## 2. Seven legal fixed components

For each of the six pairs `B subset {1,2,3,4}`, choose `r` uniformly
in `B` and independently choose `d_0,d_1,d_2` uniformly in `{0,1,2}`.
Define the actual forest law `eta_B` by

    x = r+5d_0+25d_1,
    y = d_0+7d_1+49d_2.                                    (FT4)

Every specified 7-prefix of depth `b` has mass either zero or `3^-b`.
A specified first-5 root together with a 5-tail prefix of depth
`a=0,1,2` has mass either zero or `(1/2)3^-a`, hence at most `3^-a`.
Each law is supported in its prescribed actual row pair. These are
all the forest-law constraints in report 379, RF3, at these heights.
The positive 5-tail and 7-prefix caps hold simultaneously, but the
two coordinates are correlated through the shared digits in FT4.

For the full-five component `mu`, take `x=1` and choose all three
7 digits independently and uniformly in `{0,1,2,3,4}`. Its 7-prefix
masses are zero or `5^-b`. It is a legal full-five cap law on the same
actual source. It is concentrated in one complete 5-coordinate, so
it supplies no nontrivial 5-tail cap.

All seven components are now fixed. Only their convex mixture weights
may change in the claim being tested.

## 3. Four original layouts give one common lower certificate

For `r=1,2,3,4`, let `lambda_r` be the complete layout centered at the
CRT point `(r mod125,0 mod343)`. Its phases at every divisor are the
reductions of this one point. These are four legal members of the
larger independent-phase layout set; using them for a lower bound
does not replace that set by centered layouts.

Under a forest law, if its sampled first root differs from the
center root, only the four 5-exponent-zero labels contribute. Their
squared-load expectation is

    S_3(3) = 1+3/3+5/9+7/27 = 76/27.                       (FT5)

If the sampled root matches the center root, let `n` count the
initial zero digits among `d_0,d_1,d_2`, capped at three. The number
of matching 5-prefixes is `2+min(2,n)`, and the number of matching
7-prefixes is `1+n`. The complete load is their product. Thus

| Initial zero run `n` | Probability | Squared complete load |
| --- | --- | --- |
| 0 | `2/3` | `4` |
| 1 | `2/9` | `36` |
| 2 | `2/27` | `144` |
| 3 | `1/27` | `256` |

The matching-root expectation is `832/27`. Averaging the two equally
likely roots of a pair consequently gives

    E_(eta_B) L_(lambda_r)^2 =
        454/27  if r belongs to B,
         76/27  otherwise.                                 (FT6)

For `mu`, the 7-prefix moment is `S_5(3)=232/125`. All four
5-prefixes match at center one; only the exponent-zero prefix matches
at another center. Hence

    E_mu L_(lambda_1)^2 = 3712/125,
    E_mu L_(lambda_r)^2 = 232/125  for r=2,3,4.              (FT7)

Use one distribution on these four layouts:

    theta_1 = 8684/31365,
    theta_2 = theta_3 = theta_4 = 22681/94095.               (FT8)

Its weights are positive and sum to one. By FT6, every pair component
has expected price

    E_theta E_(eta_B) L_lambda^2
        = 76/27 + 14 sum_(r in B) theta_r.                  (FT9)

For the three pairs not containing one, this is `99992/10455`.
For the other pairs it is `947122/94095`, which is larger. By FT7,
the full component has price

    (232/125)(1+15theta_1) = 99992/10455.                    (FT10)

For any convex mixture `nu` of the seven fixed components, linearity
and the fact that a maximum dominates an average now give

    Gamma_(3,3)(nu)
       >= E_theta E_nu L_lambda^2 >= 99992/10455.            (FT11)

This proves FT1 without requiring optimality of the four-layout
certificate or computing the complete minimax value.

## 4. One additional common marginal law need not repair the choice

The particular law

    xi = (eta_{2,3}+eta_{2,4}+eta_{3,4})/3                  (FT12)

has its first-5 root uniform in `{2,3,4}` and the same ternary shared
digits as FT4. It therefore satisfies both families of prefix caps

    xi(x=u mod5^a) <= 3^-a,
    xi(y=v mod7^b) <= 3^-b.                                 (FT13)

These are the simultaneous two-prime marginal caps of report 376.
Adding this fixed component cannot help: it already belongs to the
convex hull of the six forest components, and its price under FT8 is
again `99992/10455`.

This is a statement about that legal fixed choice. It does **not**
show that the whole family of common-cap laws is insufficient, or that
optimizing its member together with the other components must fail.
The same distinction applies to the full forest-law polytopes.

There is a more precise comparison using this `xi`. Its complete
5-coordinate marginal is uniform on the 27 points
`r+5d_0+25d_1`, with `r in {2,3,4}` and `d_0,d_1 in {0,1,2}`.
Its complete 7-coordinate marginal is uniform on the 27 points whose
three digits belong to `{0,1,2}`. Let `xi_ind` be the independent
product of these **same two complete marginals**. It has 729 points
and is supported on the same actual `R`; `xi` has 81 points. This
operation changes their joint relation, not either coordinate's
distribution or any of its prefix readings.

For `0<=a,b<=3`, the maximum joint-prefix masses under these laws are

    M_xi(a,b) = 3^-b                         if a=0,
                3^(-1-max(a-1,b))           if a>=1,
    M_ind(a,b) = 3^(-a-b).                                  (FT13a)

Indeed, a positive 5-prefix under `xi` fixes the first root, of
probability `1/3`, and then `a-1` of the same ternary digits used by
the 7-prefix. Their joint restriction fixes `max(a-1,b)` digits.
Under `xi_ind` the two prefix restrictions are independent.

The ordered-pair LCM expansion bounds every independent original
layout by `sum_(a,b=0)^3 (2a+1)(2b+1) M(a,b)`. The centered layout
at `(2,0)` attains every term for both laws. Consequently,

    Gamma_(3,3)(xi)     = 328/27,
    Gamma_(3,3)(xi_ind) = (76/27)^2 = 5776/729,
    Gamma_(3,3)(xi)-Gamma_(3,3)(xi_ind) = 3080/729 > 0.       (FT13b)

The independent product reaches the target exactly; the correlated
law exceeds it despite having identical complete coordinate marginals.
This identifies joint prefix information absent from separate marginal
caps. It does not authorize replacing a law by its independent product
on an arbitrary source: here the complete source `R` contains all the
required pairs, which is checked explicitly.

## 5. The same source has a good unrestricted law

Give all `34300` points of `R` equal mass. Its 5-prefix masses are
one at depth zero and at most `1/(4*5^(a-1))` at depth `a>=1`.
Its independent 7 coordinate has prefix masses `7^-b`. Expanding
any complete squared load into ordered pairs of original indicators,
each compatible intersection has the corresponding LCM prefix mass;
incompatible phases contribute zero. There are `2a+1` ordered
5-exponent pairs with maximum `a`, and similarly for the 7 exponents.
Thus this one law has

    Gamma_(3,3)
       <= (1+3/4+5/20+7/100)(1+3/7+5/49+7/343)
        = 3933/1225 < 5776/729.                             (FT14)

A layout centered at any actual point attains every bound in this
expansion, so equality holds in the first comparison with `3933/1225`.
The source theorem itself has not failed in this example.

Report 427's first-5-layer estimate omits labels with 5-exponent at
least two. Here those additional labels detect the correlation of
the two 5-tail digits with the 7-prefix in FT4, and the full component
has no 5-tail spreading guarantee to compensate uniformly. Therefore
an extension cannot simply retain arbitrary components and retune
their weights. It must justify enough joint control of the complete
original loads; allowing globally coordinated component selection is
one option left open by this counterexample.

## 6. Exact verification

[`fixed_component_height_obstruction.py`](../../frontier/cover-geometry/fixed_component_height_obstruction.py)
provides reusable routines for actual laws, coordinate and forest caps,
independent original-divisor layouts, and a common lower certificate.
The retained example checks every cap of the eight component laws,
evaluates all sixteen original indicators on their actual points under
all four layouts, and checks the exact rational gap. It also constructs
the independent product, compares both complete marginals, computes
all joint-prefix maxima for both laws, sums all 256 ordered-label LCM
bounds, and verifies attainment at `(2,0)`. Separately it computes the
uniform-source LCM bound and directly verifies attainment on all
`34300` actual source points. No numerical optimizer is used.

```sh
python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_component_height_obstruction.py --compact
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_component_height_obstruction.py --compact
```

Both runs write only their result to stdout. The ordinary proof is the
common four-layout certificate FT5--FT11; the checks do not replace its
quantifiers with a finite sample of mixture weights.

[Index](../../marked_head_profile.md) · [Complete mean and hinge operator](109-the-mean-and-all-hinges-share-one-original-test.md) · [Complete denominator](111-each-ap11-block-shares-its-mean-and-curvature.md) · [Compatible factorial head](112-the-factorial-tail-retains-one-compatible-original-head.md)

# Quadratic hinges and the factorial tail share one head

Keeping one original head across the positive hinge part and the
complete factorial tail improves nine current quadratic cost bounds.
On both entire actual saturated K-control beta faces, the complete
signed numerator satisfies

    N<=34.928308537534440910051265828682... .        (QH1)

With111's unchanged complete denominator,

    d>=50511415637/632754738000,
    C0+N/d<=459.139828574756367119359048904977... .  (QH2)

The comparison decreases111 by2.741357063314553111933075784272....
The improvement concerns five transformed quadratic AP costs and
four of the six raw81 costs. The other two raw81 rows retain their
stronger existing bounds. All52 original cost terms, the negative
mass term, full square complements and infinite tails remain present.

The scope is r=rho=0 and D=53/360 on the two complete actual K faces.
This is an ordinary source theorem and exact rational computation,
with no off-face extension, new global K, Lean verification or
unrestricted Erdos7 resolution. The comparison remains above403.

## 1. Expand the whole quadratic cost with its correct signs

For an original quadratic cost f, let its complete eventual polynomial
be

    f(v)=a*v²+b, v>=v0, a>0.

Set theta=2*a and use the complete factorial-tail function

    Phi5(v)=(v-5)_+*(v-4)/2.

The exact all-load expansion has the form

    f(v)=f(1)+sum_t c_t*(v-t)_++theta*Phi5(v), v>=1. (QH3)

Its coefficients are

    c1=f(2)-f(1),
    c_t=f(t+1)-2*f(t)+f(t-1), 2<=t<=4,
    c_t=f(t+1)-2*f(t)+f(t-1)-theta, t>=5.

They vanish beyond max(5,v0). The checker verifies every finite
transition of(QH3) directly from the pinned original cost function.
For all larger integers, Phi5(v)=v²/2-9*v/2+10. The identities

    sum_t c_t-9*theta/2=0,
    f(1)-sum_t t*c_t+10*theta=b                    (QH4)

match the entire remaining polynomial. Thus the finite transitions
and(QH4) prove(QH3) at every load; no finite truncation replaces a
quadratic tail.

Among the11 original quadratic rows,10 have f(1)>=0, theta>0 and
all c_t>=0, with supported thresholds at most8. The sole exception
is the raw81 row n=1, f(v)=(v²-81)_+. In the chosen Phi5 basis,

    f(v)=2*Phi5(v)-2*sum_(t=5..8)(v-t)_+
                                      +17*(v-9)_+.             (QH5)

Upper bounds on the four negatively weighted hinges cannot be
substituted in(QH5) to obtain an upper bound on f. That row keeps
its existing certified bound. This is a limitation of this positive
expansion and operator, not a claim that another representation
cannot improve the row.

## 2. The positive parts keep the same original head

Fix one complete original357 test A and its independently labelled
six-head layout ell. Let xi=(T,F) be its original21/35 projections.
For the coefficients c_t of one positive expansion(QH3), write
M_c(ell,xi) for109's complete mean/hinge bound at this fixed layout.
It includes all its weighted peeled old and positive-seven tails,
selected original cylinders, and its certified mean-head deletion.

The original test satisfies

    sum_t c_t*integral_mu(A-t)_+ <= M_c(ell,xi).

For that same A and ell,112 gives

    integral_mu Phi5(A) <= J(ell)+P,
    P=2539/3600,                                  (QH6)

where J retains its compatible factorial head, complete old-tail
cross term, and fixed-cell complete positive-seven LCM rows. Its
positive-seven estimates are uniform in xi, so(QH6) is valid for
the actual projections already used in M_c.

Multiply(QH6) by theta and add the positive hinge bound before
maximizing. Equation(QH3) gives

    integral_mu f(A)
      <= f(1)*D+max_(ell,xi)[M_c(ell,xi)+theta*J(ell)]
                                             +theta*2539/3600. (QH7)

The same head ell appears in both terms inside the maximum. No
common maximizing residue is imposed between different AP costs,
or between separate original tail labels of one test. Each source
and cylinder bound is valid for those original labels uniformly.

The mean and factorial bounds can both use known deletion measures:
they integrate different nonnegative functions in(QH3). Their
weighted upper bounds are added once. There is no further independent
deletion credit or separate numerical gain subtracted afterward.
The pair constant P includes every old-old, old-seven and seven-seven
complement from108's nonnegative cap-series partition, unchanged.

The independent scalar maximum of J remains139/900, as in112.
It is not substituted before the common maximum in(QH7). The
improvement retains the incompatibility between head choices that
favor the two portions of the same original cost.

## 3. The finite maxima preserve the complete costs and tails

The10 accepted positive expansions have original inventory indices

    41,42,43,44,45,47,48,49,50,51.

The first five are the original transformed quadratic AP costs;
the last five are raw81 rows n=2,...,6. For each, the checker
combines all c_t and theta into one positive rational scale and
primitive integer coefficients. If109's MeanHead extracts another
factor from the hinge coefficients alone, that factor is explicitly
multiplied back before the factorial head is added.

The factorial head is an integer divided by5400. The existing
mean/hinge scale is divisible by5400, so all combined objective
comparisons use exact integers. For each cost the program checks
all12500 original head layouts and all10 xi choices:1,250,000 new
joint source-LP evaluations. Every head LP has a feasible primal
and a matching dual. The112 factorial components are reconstructed
on the same layouts and their complete digest agrees with112.

Saved maximizing witnesses are re-evaluated through both public
source APIs. All10 costs have a maximizing canonical head

    ell=(0,1,2,0,2,1,2).

The maximizing xi may differ between costs. These are maxima of
upper-bound operators and do not assert actual-family attainment.

The current-row comparisons are:

| Original cost | Bound retained in111 | Joint candidate | Accepted |
| --- | ---: | ---: | --- |
| AP (0,0) | 5.32912382816021 | 5.28358896132804 | New |
| AP (0,1) | 1.47938516714508 | 1.45013887788591 | New |
| AP (0,2) | 0.17511967718414 | 0.17169128951512 | New |
| AP (1,0) | 1.67611155633262 | 1.64299969405578 | New |
| AP (2,0) | 0.23412978976387 | 0.22954559827164 | New |
| Raw81, n=1 | 1.64044206673381 | Negative hinges in(QH5) | Existing |
| Raw81, n=2 | 3.31801660666080 | 3.33231555010515 | Existing |
| Raw81, n=3 | 4.20196712018141 | 3.93532177950545 | New |
| Raw81, n=4 | 4.51836389764013 | 4.29763923982291 | New |
| Raw81, n=5 | 4.66240557264634 | 4.49457446496059 | New |
| Raw81, n=6 | 4.74065043538504 | 4.61455307202246 | New |

Every accepted entry is the minimum of that row's new bound and
its current111 bound. In particular the n=2 candidate is rejected
despite its nonnegative expansion. No improvement is measured
against an earlier, weaker row.

The source LP and both operators retain the entire root1 beta
mass constraint. First-beta cell permutations and the compatible
root0-cell exchange transport(QH7) to both whole actual faces.
All finite-prefix arguments pass to complete tests using109 and112's
finite dominating cap sums and complete geometric tails. These
facts do not extend the result to positive r or rho.

## 4. The complete signed comparison improves once

Keep every linear cost of109 and use the accepted quadratic rows
above in the full52-cost vector. One simultaneous legal substitution
into the existing all-load majorants gives zero further improvement.
The complete numerator is still

    N=r_mass*D+sum_(i=1..52)weight_i*cost_i
                                        +c_square*(374/75),
    r_mass<0, weight_i>0, c_square>0.

Its exact reduction from111 is

    829414479633015302854496767913693428057
      /3790110501206299971744011718750000000000
      =0.2188364902208082985666452259219853... .     (QH8)

The new numerator is

    N=2524547854381128907264555471562966542931
        /72277987686355182340239690559500000000.

The denominator is reconstructed from111's four complete AP11 block
costs, full count remainder and independent AP13 term. Its value
remains50511415637/632754738000. Both numerator and denominator
are positive. With the unchanged offset C0, the final exact bound is

    3253808038485254109147885098089939401708907
      /7086747513465768980547138892364583187500,

which proves(QH1)--(QH2). The retained complete comparison still
does not meet the sufficient threshold403.

## Reproduction

[whole_quadratic_same_head.py](../../frontier/moments-survival/whole_quadratic_same_head.py)
pins111's complete consumer,109's mean/hinge operator and112's
compatible factorial head. Its
[certificate](../../certificates/source_norms/moments-survival/whole_quadratic_same_head.json)
contains every exact expansion, the negative-coefficient obstruction,
primitive scalings, all1,250,000 combined objective checks, saved
witnesses, all52 cost bounds and the complete unchanged denominator.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/moments-survival/whole_quadratic_same_head.py --check
```

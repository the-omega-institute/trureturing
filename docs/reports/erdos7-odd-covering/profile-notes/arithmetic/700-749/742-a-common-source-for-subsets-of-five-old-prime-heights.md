# A common-source invariant for five old prime heights

The actual pure-survivor construction extends from23 to ANY subset of
the five old coordinates11,13,17,19,23. It supplies one full-height
query comparison and one positive supported source after a single actual
mixed restriction. All32 choices of which old heights are unrestricted
have positive certified source mass. The ternary height remains at most2
and the5/7 heights remain at most1.

For old19 AND23 at arbitrary finite heights, the same source satisfies
a complete-query square bound below260. Therefore the existing
two-fresh-direction gate proves actual uncovered Haar density at least

    12493553/7475059800>1/600                             (JH1)

for every distinct-modulus family dividing

    315*11*13*17*19^H*23^K*q1^E*q2^F,

where H,K,E,F are arbitrary nonnegative finite integers and the two
distinct fresh primes are sorted with q1>=29,q2>=31. All original
phases are arbitrary and fixed globally. This is ordinary mathematics
with exact arithmetic; no Lean verification or unrestricted covering
result is claimed.

## 1. One actual source for each set of unrestricted old coordinates

Let B={11,13,17,19,23}, and J subset B. Coordinates in J may have
arbitrary finite original heights. Coordinates in B minus J retain
height at most1. In every original, keep v3<=2,v5<=1,v7<=1.

Use the SAME six-shape pruned315 source mu_i and its genuine auxiliary
comparison law Y_i from the [old23 construction](741-an-actual-full-height23-source-supports-six-fresh-primes.md). Every complete315 query
L satisfies L<=_icx Y_i on mu_i. Write

    c_i=E Y_i-1,
    c=(185/86,178/85,178/85,2,157/77,157/77),
    Nmin=(77,78,78,75,74,74).

The actual315 law is uniform on its own pruned survivors, with density
at most315/Nmin_i. It depends on the originals, not on a later query.

At an unrestricted old prime p, remove its actual pure first root,
or one fixed auxiliary first root if that original is absent. Within
each remaining first root, remove ALL actual pure p-power originals
at their stated finite heights. The surviving Haar mass in that root
is at least

    1/p-sum_(e>=2)p^(-e)=(p-2)/(p(p-1))>0.

Give each live root probability1/(p-1), uniformly relative to Haar
on its actual survivors. The resulting one-coordinate probability rho_p
has density at most p/(p-2), and cylinder caps

    u_p(1)=1/(p-1),
    u_p(e)=p^(1-e)/(p-2), e>=2,
    sum_(e>=1)u_p(e)=1/(p-2).                            (JH2)

At a shallow prime use the uniform law on the p-1 live first roots.
Its density cap is p/(p-1), and its only required positive-exponent
query cap is1/(p-1). Missing coordinates may be refined without adding
actual original classes.

Form the ONE raw source

    sigma_(i,J)=mu_i times product_(p in B)rho_p.

All factors use the actual pure inventory from the same original family.
The carrier includes the old exponents occurring in fresh-bearing classes,
not just old-only classes. The whole-source Haar cap is

    D_(i,J)=(315/Nmin_i)
       product_(p in J)p/(p-2)
       product_(p in B minus J)p/(p-1).                 (JH3)

## 2. The complete query boundary remains a common convex comparison

For each p in J introduce an auxiliary integer N_p with

    Pr(N_p>=1)=1/(p-1),
    Pr(N_p>=e)=p^(1-e)/(p-2), e>=2.

For each shallow p introduce B_p~Bernoulli(1/(p-1)). Take these
comparison variables independent of each other and of Y_i, and define

    Z_(i,J)=Y_i product_(p in J)(1+N_p)
                   product_(p in B minus J)2^B_p.       (JH4)

The actual raw old query law satisfies

    Q<=_icx Z_(i,J)

for EVERY complete full old divisor query Q, uniformly over all its
globally fixed phases and finite old exponent slots.

The proof repeats the event-increment lemma already used for old23.
At one fixed old point, order the query indicators by increasing
height, with their decreasing deterministic caps. Convex increments
bound their sum by nested auxiliary events. For a fixed auxiliary
N_p=n, Jensen bounds the sum of n+1 prior-coordinate query loads by
the average of their separately scaled convex readings. Apply the
previous complete-query comparison to EACH slot before averaging n.
Constant-one padding handles auxiliary layers beyond the actual finite
height. Different exponents may select different queries throughout.

Iterating this procedure over the actual product factors yields(JH4).
The product order does not matter for the auxiliary law. Its independence
belongs to the comparison, not to the eventual actual restricted source.
All its integer moments are finite. The pure geometric auxiliary tails
are analytic upper bounds for finite inventories, not infinitely many
new forbidden originals.

Thus the reusable boundary data are the fixed315 source/comparator,
the actual pure laws with their caps, their joint Haar density product,
and the complete query comparison(JH4). It is not enough to keep just
an uncovered fraction or one maximizing query.

## 3. One restriction pays every actual mixed original

Put

    z_p=1/(p-2) if p in J, and z_p=1/(p-1) otherwise.

Condition sigma_(i,J) ONCE on avoiding the remaining actual old-only
mixed originals. At each fixed outside exponent tuple, distinct numerical
labels allow at most one original per315 cofactor. Singleton outside
supports have no unit cofactor because the pure originals are already
avoided. Their nonunit315 query mean is at most c_i. Larger supports
may use the unit, with complete mean at most c_i+1. Summing the complete
finite height inventories, then using the geometric cap totals, gives

    s_(i,J)>=delta_(i,J)
       =c_i+2+sum_p z_p-(c_i+1)product_p(1+z_p).         (JH5)

This bound retains all simultaneous original phases; it does not combine
separately optimized sources. If delta is positive, the normalized law
mu_(i,J) on this actual remaining event satisfies

    (delta_(i,J)/D_(i,J))mu_(i,J)<=Haar.                 (JH6)

All32 subsets and six shapes have positive delta. In particular all
five old heights can be unrestricted simultaneously. The smallest
paired Haar factor then is

    2719/3194470=0.000851158408124... .                  (JH7)

Its first-shape factors are delta=35347/5065830 and D=5681/693.
Thus every distinct family supported on

    315*11^H11*13^H13*17^H17*19^H19*23^H23

has actual survivor Haar mass at least(JH7), with all five displayed
heights arbitrary finite. Positivity for every subset can also be seen
from the largest z values: delta decreases in every z_p and in c_i,
and the exact worst continuous retention remains positive when all
five coordinates are unrestricted. Paired density factors are checked
separately; a shape's smallest mass is not combined with another
shape's density cap.

This construction normalizes only after the ONE shared mixed-deletion
event. It avoids compounding an independent normalization loss at
every lifted coordinate. It still retains the315 height restrictions.

## 4. The same upper-tail law controls all later costs

Let Z=Z_(i,J) and delta=delta_(i,J). Take its largest delta probability
mass, splitting the quantile atom when needed, and normalize to form
the single upper-tail comparison law Z^top_delta. For every increasing
convex phi and every actual complete query Q,

    E_mu phi(Q)<=E phi(Z^top_delta).                    (JH8)

Indeed, for a quantile cutoff t and a=phi(t),

    E_mu phi(Q)
      <=a+E_sigma(phi(Q)-a)_+/delta
      <=a+E(phi(Z)-a)_+/delta.

The last expression is the expectation under that one upper-tail law.
Flat portions of phi cause no issue. The cutoff is chosen from Z and
delta, not separately for each query or phi. Equation(JH8) also extends
by Jensen to every actual finite geometrically padded field used by
the fresh-prime carving theorem. No independence between those fields
is assumed.

For J={19,23}, exact finite low-atom enumeration gives, in ALL six shapes,

    Pr(Z>8)<=delta<=Pr(Z>=8).                            (JH9)

Consequently the earlier cutoff8 already gives the optimal shared
upper-delta law for this source. Changing that cutoff does not improve
the budget while retaining the same raw comparison and retention.

## 5. The double-height source has a positive two-direction continuation

For J={19,23}, the worst paired source factor is

    hmin=763798/62292165,
    delta_first=54557/701760, D_first=5681/896.           (JH10)

Using(JH8)-(JH9), the exact square cost on every source shape is below260.
Thus every actual fresh-support field C has

    C>=1, E_mu C^2<260,

on the same law. For two fresh primes at least29,31, reuse the existing
all-real gate

    10A^2+10B^2+C^2+20[(28-A)_+(30-B)_+-C]_+>=7750.

Writing the bracket as W gives

    20 E_mu W>7750-21*260=2290.

The actual finite-height carving construction and(JH10) now give

    Haar(full survivors)
      >=hmin*2290/(20*28*30)
       =12493553/7475059800>1/600,

proving(JH1). Larger fresh primes use the established monotonicity of
the normalized fibre response. All original19/23 powers and fresh
powers have been retained in the same numerical-label inventory.

## 6. Exact arithmetic and proof boundaries

The [source consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old_height_subset_source.py)
and [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old_height_subset_source.json)
check all32 subsets and six paired source factors, reconstruct every
head comparison law, and compute the double-height source's shared
quantile8 and complete square moment. The finite enumeration covers
all auxiliary products at most8; the entire raw second moment is
computed by exact geometric sums, so its complement includes every
higher product. No tail is rounded or discarded.

The consumer pins the head-source result and the existing two-direction
scalar gate; it does not rerun their D2 geometry or domain enclosure.
The source construction and common-query transport above are ordinary
proof inputs. Independently implemented source arithmetic agrees on
all192 paired retention/density cases, low-atom probabilities, complete
second moments and the final two-direction density.

The source now covers all five displayed outside old heights. The
embedded3/5/7 restrictions remain. A later continuation must bound its
actual query fees on this supported law; a positive source mass alone
is not sufficient. Neither the source nor the two-fresh application
settles arbitrary odd prime support.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old_height_subset_source.py
```

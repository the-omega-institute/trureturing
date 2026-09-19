[Index](../marked_head_profile.md) · [Source-dependent credits](147-source-dependent-credits-cross-the-old-middle-bottleneck.md) · [Previous full partition](155-the-signed-mass-bound-reaches-the-current-source-credit-ceiling.md) · [Complete residual neighborhood](160-one-actual-residual-closes-a-hundredfold-wider-neighborhood.md)

# The complete local domain removes the zero-escape ceiling

Using160 on its full actual-source domain and155 on its complement
gives the ordinary complete comparison

    K<=509.30613707186495... .                    (LC1)

The exact rational is in the certificate. This improves155 by
0.001427050158270924... . All original fallback branches and both
terminal errors remain. The smaller sufficient gap above403 is
still106.3067120721831... . No unrestricted Erdos7 resolution,
Lean verification or change to the canonical global certificate
is claimed.

The former sigma=rho=0 ceiling no longer controls: that entire
source region is now handled by160. The new limiting region of
this fixed proof is the outer source strip, at the crossing
sigma=0.04184389894246468... of the marked and unmarked reserve
curves. Its actual residual may be zero. Thus further improvements
strictly inside160's current domain do not by themselves improve
the full comparison.

## 1. Partition actual sources before selecting a comparison

Write sigma=1-qK, and retain the actual r and rho of155, including

    r<=5rho.                                    (LC2)

The local domain from160 is

    sigma<=sigma0=1/27,
    rho<=rho0=1/1000,
    r<=r0=1/520.                                (LC3)

On(LC3),160's complete52-cost comparison gives508.9706821709662...
and hence is strictly below(LC1). Its two closed residual shells
cover all rho in(LC3). No individual local cost bound is used at
a different source outside(LC3).

Outside(LC3), at least one of qK<26/27, rho>1/1000 or r>1/520
holds. Use the original slot cutoff r*=3/1000 and the new source
cutoff delta from section3. The concentrated small-r complement
has these three covering branches:

| Branch | Actual source conditions | Retained residual lower bound |
| --- | --- | --- |
|Outer source strip|sigma0<=sigma<=delta, r<=r*|0|
|Residual outside local domain|sigma<=sigma0, r<=r*, rho>=rho0|rho0|
|Slot loss outside local domain|sigma<=sigma0, r0<=r<=r*, rho<=rho0|r0/5=1/2600|

The weak boundaries are included in both adjacent valid bounds.
The third lower bound follows from(LC2), on the same source. A
source with r>r0 and rho<1/2600 is impossible; no independent
choice of those coordinates is introduced.

For sigma<=delta and r>=r*, keep155's complete large-r branch.
For larger sigma keep its early middle, old middle and far branches,
with both sides of each mass-bound switch. The eight original
absent-prime or ineffective-source fallbacks remain unchanged.
Thus every actual source belongs to a complete valid branch.

## 2. Retain the old reserve and one residual outside the local domain

All46 original fixed cost alternatives and all their infinite
tails remain exactly those of147/155. Use their constants

    a=53/360,
    B(sigma)=B0-B1*sigma+B2*sigma^2,
    e(sigma)=gamma2*sigma-(gamma2-gamma1)*sigma^2,
    A=54.27497997750398...,
    P=37.97187303103495...,
    Q=0.515666653007543...,
    L=2.7524858798079705... .

On sigma<=delta and r<=r*, the same source reserve and denominator
give, for decrement h from K0,

    Phi_(K0-h)>=F_h(sigma)+(A-h-P-5L)*rho,
    F_h(sigma)=B(sigma)-Q*sigma+e(sigma)
                                      -h*(a+sigma/10).         (LC4)

This is155 JC4, using154's actual signed mass bound. The r loss
was paid once using(LC2). For a branch with rho>=u, the lower bound
is F_h(sigma)+(A-h-P-5L)u, provided that coefficient is positive.

Its quadratic coefficient is negative. Hence its two source
endpoints suffice on each of the three rows in section1. The
endpoint decrement capacity is

    [B(sigma)-Q*sigma+e(sigma)+(A-P-5L)u]
                          /[a+sigma/10+u].     (LC5)

For large r, discard the marked cost credits and their penalties.
The original unmarked reserve gives capacity

    (A*r*/5)/(a+delta/10+r*/5).                 (LC6)

No P or L remains after its associated marked credit is discarded.
The early middle capacity is e(sigma)/(a+sigma/10), the old middle
uses e(sigma)/(a+5sigma/9), and the far branch uses
e(sigma)/[1/4+11sigma(1-sigma)/36]. Their target polynomials remain
concave for the decrement used below.

## 3. Set the source cutoff where the two outside curves meet

The old source cutoff21/500 remains a valid upper domain for all
marked estimates and their uniform P,L,Q. Taking a smaller cutoff
uses these same conservative coefficients. Between sigma0 and
21/500, the two relevant capacities at the cutoff are

    H_marked(s)=[B(s)-Q*s+e(s)]/(a+s/10),
    H_unmarked(s)=e(s)/(a+s/10).                (LC7)

Their unique crossing solves

    B2*s^2-(B1+Q)*s+B0=0.                      (LC8)

Here the left side decreases strictly throughout the interval.
For a direct derivative check, put
u=gamma2-B1-Q and v=gamma2-gamma1-B2>0. The derivative numerator
of H_marked is

    a*u-B0/10-2a*v*s-v*s^2/10.

It is decreasing and already negative at sigma0. The derivative
numerator of H_unmarked is

    a*gamma2-2a*(gamma2-gamma1)*s
                        -(gamma2-gamma1)*s^2/10.

It is decreasing and still positive at21/500. Thus H_marked
decreases and H_unmarked increases on the entire interval. Their
minimum is maximized at(LC8), for this fixed choice of costs,
penalties and branch forms.

Exact rational substitution isolates that root between

    delta_minus=41843898942/10^12,
    delta_plus =41843898943/10^12.               (LC9)

Use delta=delta_plus. At these two endpoints the left side of(LC8)
is respectively2.502180210389949...*10^-13 and
-2.882588100167293...*10^-13. The actual decrement is

    h=H_marked(delta)=0.15455144381840713... .    (LC10)

The ideal crossing capacity is at most
min(H_marked(delta_minus),H_unmarked(delta_plus)). This upper bound
exceeds(LC10) by only1.128064341850695...*10^-13. This is an exact
bracket for this one cutoff tradeoff, not an optimality statement
about other source comparisons or actual covering families.

Had the original21/500 cutoff been retained after removing the
local domain, the capacity would have been0.1545337514352853...
and K<=509.3061547642481... . The new cutoff therefore improves
that valid comparison by0.0000176923831218... . Both exceed155's
old zero-escape capacity0.1531243936601362... .

## 4. All13 endpoints, eight fallbacks and two terminal errors

The following are the capacities from the complete complement.
Each value is an exact rational in the certificate.

| Branch endpoint | Decrement capacity |
| --- | ---: |
|Outer small-r strip, sigma=1/27|0.1550145564820504...|
|Outer small-r strip, sigma=delta|0.1545514438184071...|
|rho>=1/1000, sigma=0|0.1692323234831657...|
|rho>=1/1000, sigma=1/27|0.1707173601767292...|
|r>=1/520, sigma=0|0.1593455802217810...|
|r>=1/520, sigma=1/27|0.1610786593586812...|
|Concentrated large r|0.2142340226722464...|
|Early middle, sigma=delta|0.1545514438203110...|
|Early middle, sigma=1/3|0.7447028124933494...|
|Old middle, right limit at1/3|0.4045043131927663...|
|Old middle, left limit at1/2|0.3697332370738243...|
|Far, sigma=1/2|0.4814398746578308...|
|Far, sigma=1|0.1878037429972404...|

Exactly the marked outer-strip endpoint has zero signed margin at
(LC10); all other margins are positive. The early-middle margin
at the neighboring cutoff is the exact positive opposite of the
upper-end value in(LC8). Non-strict comparison at the limiting
outer endpoint suffices for(LC1).

The shared residual coefficient in(LC4) is

    A-h-P-5L=2.3861261036107706...>0.

The original positive survival factor and target coefficient
also stay positive, so division uses the same valid direction.
Every one of the eight complete fallback values remains below
(LC1). The two unchanged terminal errors give sufficient gaps
106.3067120721831... and106.5266574800776... above403.

The bottleneck is now the marked/unmarked crossing outside the
local source range. Better local constants at sigma<=1/27 leave
the controlling quantities in(LC7) unchanged. Extending the
applicable local domain to that strip, improving a complete
outer reserve, or changing the complete branch assignment would
address this new obstruction. The far endpoint still imposes the
separate capacity4gamma1=0.1878037429972404... on the unchanged
far branch.

The [helper](../frontier/local_removed_outer_comparison.py) pins
160's complete result and reconstructs155's original outer data,
then checks the full complement, the exact cutoff bracket and
every surviving terminal quantity. Its
[certificate](../certificates/source_norms/local_removed_outer_comparison.json)
does not repeat any unchanged finite head scan or move a local
cost across sources.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/local_removed_outer_comparison.py --check
```

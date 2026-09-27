[Index](../../marked_head_profile.md) · [Complete global comparison](../065-128/118-the-shared-slot-gap-enters-the-complete-global-comparison.md) · [Actual denominator](../065-128/107-carrier-mass-and-the-shared-residual-improve-global-k.md) · [Earlier template ceiling](../065-128/76-exact-capacity-of-the-current-neighborhood-globalization.md)

# A small local comparison leaves the outer escape bottleneck

A complete comparison on the rectangle

    sigma<=delta0=1/10000, rho<=rho0=1/100000,
    r<=r_star=1/520                                  (LG1)

can be joined to118's outside proof only by checking the same global
target on every complementary source region. Even an arbitrarily
strong local comparison leaves an unchanged outside bottleneck at
sigma=1/27. For118's fixed outside inequalities, the exact maximum
total target decrement is

    h_star=14770812110462491761326815853356593185964018503363273
           /119118386954523245186930572658320423396326251100000000
          =0.1240011092166792000107... .             (LG2)

The already used decrement is31/250=0.124, leaving only

    h_star-31/250=0.0000011092166792000107... .       (LG3)

This remaining room already follows from118 without any new local
theorem. It is not a gain attributable to a stronger local quotient.
The capacity target is509.3366874064666935...; this section records
the exact capacity and gluing criterion, without changing118's
canonical target. It does not assert optimality for actual covering
families or rule out stronger outside inequalities.

## 1. Keep the signed reserve and target payment together

Use118's exact constants, with no new choice of original costs:

    delta=1/27, r_star=1/520,
    a=53/360, b=5/9,
    B=0.019760166644524508...,
    P=37.151211450575968...,
    Q=0.515666653007543...,
    A=54.274979977503980... .

Here A is the existing conservative residual coefficient. The exact
fractions, all46 original cost choices and every complete tail are
reconstructed from118 by the helper. Put

    e(sigma)=gamma2*sigma-(gamma2-gamma1)*sigma^2,
    W_h(sigma)=e(sigma)-h*(a+b*sigma).              (LG4)

For sigma<=delta and r<r_star the proved full signed inequality is

    Phi_(K0-h)>=B-Q*sigma+W_h(sigma)
                              +(A-P-h)*rho.       (LG5)

It pays the cost losses P*rho and the target decrement h*rho from
the same actual residual. It requires A-P-h>=0. In particular, a
local credit or a source reserve is not a second copy of this budget.

For delta<=sigma<1/2, the unchanged outside inequality is simply

    Phi_(K0-h)>=W_h(sigma).                        (LG6)

For1/2<=sigma<=1,118 retains its separate complete raw-mass bound

    Phi_(K0-h)>=R_h(sigma),
    R_h(sigma)=e(sigma)-h*[1/4+(11/36)*sigma*(1-sigma)]. (LG7)

The proof does not apply106's strict sigma<1/2 denominator theorem
at1/2. W_h(1/2) is the limiting polynomial value; R_h covers the
actual boundary. Both polynomials are concave at the parameters
considered here, including h_star.

## 2. The exact complement of the small local rectangle

Inside sigma<=delta and r<r_star, the complement of(LG1) is covered
by two regions:

* delta0<=sigma<=delta, with rho>=0;
* 0<=sigma<=delta0, with rho>=rho0.

Their shared boundary can be included in both estimates without
adding their bounds. For the first region drop the nonnegative rho
term in(LG5). For the second replace rho by rho0. Concavity reduces
each to its two sigma endpoints.

For sigma<=delta and r>=r_star, the actual packing implication
rho>=r_star/5 gives the unchanged bound

    Phi_(K0-h)>=(A-h)*r_star/5-h*(a+b*delta).       (LG8)

This region is wholly outside(LG1), since r_star>5rho0. The middle
and far ranges are also wholly outside(LG1). These statements concern
the actual sigma,rho,r, with both K orientations and every feasible
first-beta distribution retained.

Each outside endpoint condition has the form

    R-h*D>=0, R>0, D>0,

and is therefore equivalent to h<=R/D. The exact rational check gives

| Outside condition | Maximum allowed total decrement |
| --- | ---: |
| Small r, source annulus at delta0 |0.134214098608484...|
| Small r, source annulus at delta |0.127942755263314...|
| Small r, rho>=rho0, sigma=0 |0.135373928539302...|
| Small r, rho>=rho0, sigma=delta0 |0.135367592447867...|
| Concentrated large r |0.124120726293864...|
| Middle at delta |0.124001109216679...|
| Middle limiting endpoint1/2 |0.369733237073824...|
| Far at1/2 |0.481439874657830...|
| Far at1 |0.187803742997240...|

The residual condition A-P-h>=0 and the far concavity condition
gamma2-gamma1-11h/36>=0 have respective capacities17.1237685269...
and1.7497460668..., so neither controls. All eight original complete
fallback bounds stay strictly below K0-h_star. The largest fallback
is436.0511214100737..., also unaffected by a conditional local461
comparison.

## 3. Capacity and the precise local-to-global implication

The unique smallest outside ratio in the table is

    h_star=e(delta)/(a+b*delta).                    (LG9)

Every outside branch has nonnegative margin at h_star, and all have
positive margin for h<h_star. Conversely, if h>h_star, then
W_h(delta)<0. By continuity W_h remains negative for some sigma>delta,
so assigning the exact endpoint to the neighboring marked branch
cannot repair the middle interval. This establishes the capacity of
these specified outside inequalities. It is not a negative signed
margin or a covering witness for any actual source: the estimate can
be loose, and other source information can improve it.

Suppose a separate theorem proves, for the same original final
comparison quantity and every actual source in(LG1), a local upper
bound L. Then the gluing conditions are

    L<=K0-h,
    0<=h<=h_star,                                 (LG10)

together with the inherited positive-division and fallback conditions.
For example, the conditional input L=461 satisfies(LG10) at h_star,
with target room48.33668740646669.... The helper treats461 only as
a hypothetical input; it does not verify or assert the local theorem.
The proof is a case distinction on source regions. It does not require
two intermediate denominator estimates to be equal. It does require
both regional theorems to bound the same final comparison quantity.

If that quantity has an actual representation C0+N/E, E>0, a local
ratio bound gives the signed inequality (T-C0)*E-N>=(T-L)*E for
T>=L. This margin belongs to its local source; it cannot be transferred
to a different source in the middle interval. When certifying a local
ratio by N<=Nbar and E>=d>0, the additional sign Nbar>=0 justifies
C0+N/E<=C0+Nbar/d. In118's target-decrement calculation the direction
is different: the negative term -hE requires the upper bound
E<=a+b*sigma+rho. Neither use licenses substituting the opposite
denominator bound or adding two reserves.

For attribution, even the local input in(LG10) is unnecessary at
h_star. The original small-r inequality(LG5) has positive endpoints
on the full interval[0,delta] at this h, including the omitted
sigma=0 endpoint. Thus all of(LG3) is unused numerical room in118.
The large gain between a local461 and the global509-scale bound does
not appear as a global decrement in this template.

## 4. Why shrinking the original neighborhood is not a shortcut

Replacing delta by delta0 in only the escape branch, without retaining
the old marked annulus, would require

    h<=e(delta0)/(a+b*delta0)
      =0.0003948607261650205... .                  (LG11)

Likewise using only the residual reserve at the new cutoff would give

    h<=A*rho0/(a+b*delta0+rho0)
      =0.0036849615627572315... .                  (LG12)

Both are less than the already spent31/250. Therefore the new local
box cannot replace118's larger proved neighborhood and leave only
these two outside estimates. Keeping the original outer branches
avoids that loss, but leaves the bottleneck(LG9).

Both complete terminal errors retain their original nonnegative sign.
Even the capacity target plus either full error remains above403;
the box20/current8 gap remains106.3372624067848354...>0. No terminal
tail or later-prime continuation has been discharged by this gluing
criterion. To obtain a substantial global improvement, one must
strengthen or replace an outside bound, enlarge the region on which
the strong local theorem holds, or use a different complete comparison.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/local_to_global_escape_capacity.py --check
```

The helper reconstructs118, checks every rational endpoint and sign,
all eight fallbacks and both unchanged complete errors. Its capacity
proof is the preceding concavity and affine-target argument, not a
parameter grid. No canonical globalK update, Lean verification or
unrestricted Erdos7 resolution is claimed.

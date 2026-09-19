[Index](../../marked_head_profile.md) · [Previous global bound](../j-source/213-the-affine-j-reserve-enters-the-complete-global-comparison.md) · [Expanded complete K rectangle](215-the-source-bridge-covers-a-larger-complete-residual-strip.md) · [Actual affine J reserve](../j-source/212-a-supporting-affine-margin-sharpens-the-whole-j-reserve.md)

# The expanded residual bridge improves the complete global bound

The full K rectangle from215 removes213's inner-strip obstruction
and permits a larger certified J-source neighborhood. Rechecking the
entire complementary-region decomposition gives

    K<=5395874779870081281884158980542968000758032904442
        /10604409950230783929560784643860990069247109625
      =508.8330991723543... .

The improvement over213 is0.0002975238192743777.... Both original208
local rectangles remain covered, as does the additional full residual
strip certified by215. All four original paired source layers, every
local52-cost comparison, every infinite tail, eight fallback branches
and both unchanged terminal errors remain.

This is an ordinary complete global comparison supported by exact
rational checks. It is not a Lean or frozen-state claim, does not
assert sharpness for actual covering families, and does not reach
the sufficient threshold403. Unrestricted Erdos7 remains unresolved.

## 1. Retain the paired layers and aggregate source constraint

Use213's original constants K0,H,gamma1,gamma2,gamma3 and eK,eJ,eB,eC.
For a decrement h, the four complete paired floors are

    fK=-h*eK, fJ=gamma1-h*eJ,
    fB=gamma2-h*eB, fC=gamma3-h*eC,
    Anew=A-(23/42)*h.

The helper freshly reconstructs all23328 original source/carrier
rows and their allocated survival margins. At h=0 and at the new h,
it checks all23328 lower and23328 upper actual-mass endpoints. The
original conditional, signed-gap and denominator digests agree.
The six exact fourth-layer controllers are unchanged.

At the new target,

    fK<fJ<0<fB<fC, Anew>0.

With x=qK, y=qJ and b=qB, the same genuine source functions are
reweighted before Jensen, giving

    Phi_h>=fK*x+fJ*y+fB*b+fC*(1-x-y-b)+Anew*rho.

The actual factor representation imposes

    sqrt(qK+qB)+sqrt(qJ)<=1.

As proved in200/213, eliminating b and minimizing the resulting
concave function of sqrt(y) leaves two alternatives:

    FB(x)=fK*x+fB*(1-x),
    FJ(t)=fK*t^2+fJ*(1-t)^2+2*fC*t*(1-t), t=sqrt(x).

Each alternative is bounded over its whole interval before either
is selected. No minimum of convex functions is declared convex.

## 2. Cover both complete inner residual strips

Three complete local bounds are checked against the new target:

| Source radius | Residual radius | Complete bound | Provider |
| --- | --- | --- | --- |
| 1/20 | 1/1000 | 482.85065012970296... | 208 |
| 1/12 | 1/3000 | 475.8959674330319... | 208 |
| 1/12 | 1/2300 | 506.97634810178624... | 215 |

The third rectangle contains the second; retaining the second
documents that its stronger numerical comparison and complete tails
still apply on the old domain. The new coverage is supplied by215's
independently proved full rectangle, not by extrapolating208.

The uncovered inner regions are now contained in

    0<=sigma<=1/20, rho>=1/1000;
    1/20<=sigma<=1/12, rho>=1/2300.

Since Anew>0, each residual is reduced to its indicated lower bound.
For each alternative, concavity in sqrt(1-sigma) reduces the entire
closed interval to its two endpoints. The helper checks all eight
endpoint inequalities with integer-certified square-root brackets
of width10^-30 and the correct sign for every substitution.

The smallest inner endpoint margin is

    0.005449100663911518...,

at sigma=1/20, rho=1/2300 in the B alternative. In particular, the
left boundary and every point immediately to its right are covered.
No endpoint is removed merely because another local theorem also
covers the boundary itself.

## 3. Cover the whole outer region with one J rectangle

Use

    d=1/1112, R=317/25000000, t0=d/2=1/2224.

These satisfy d+R<1/1000. Thus212 applies to the entire J rectangle
and retains every197 family error. Define

    rH=-H*eK*t0^2+2*(gamma3-H*eC)*t0*(1-t0),
    pH=eK*t0^2+eJ*(1-t0)^2+2*eC*t0*(1-t0),
    extra=rH/pH, h=H+extra, K=K0-h.

The extra decrement is0.009008073608616168.... The complete far-J
region has x<=11/12 and y<=1-d. Its three concave endpoint bounds are

    FB(11/12)>=0.0013696039574828472...,
    FJ(t0)=0,
    FJ(sqrt(11/12))>=0.018820387824176804... .

The substitution1-sqrt(1-d)>=d/2 enlarges the tested interval; it
does not exclude any actual source. All three checks are exact
rational inequalities after the certified square-root enclosure.

In the near-J region y>=1-d, the aggregate constraint implies
x<=d^2. Put a=fJ-fK>0. For rho>=R, the same actual residual yields

    Phi_h>=fJ-a*d^2+Anew*R
          >=8.962075749923304...*10^-8>0.

For rho<=R, the original direction40 receives212's complete reserve

    reserve=79/1944-6*d-E197(d,R)
           =400274107/46912500000
           =0.008532355065281109...>0.

The helper reconstructs all197 shallow and infinite-axis errors and
checks that none changed. Multiplication by the same original
direction40 weight gives

    Phi_h>=fJ-a*d^2+w40*reserve
          >=8.879847482596199...*10^-7>0.

Only the actual old49 margin is replaced, once. Neither a second
residual nor a favorable correlation independent of the common
source is introduced.

## 4. Complete local comparisons and remaining boundary

The helper reconstructs both208 local numerators and survival
denominators. It additionally reruns215's complete rectangle proof:
all new guards, all26 transported objectives,3120 independent branch
checks, all52 numerator costs and every tail. A second assembly of
the enlarged numerator confirms its signed mass, square, heavy and
independent cost contributions.

At the new global target, each local denominator and each remaining
actual-S coefficient is positive. All eight original fallback bounds
remain below the target. Both complete terminal error corrections
are retained, so the resulting gaps above403 remain positive. This
improvement therefore advances the ordinary comparison without
settling the unrestricted problem.

## 5. Reproduce the exact complete join

From the repository root:

```sh
python3 docs/reports/erdos7-odd-covering/frontier/transport/expanded_bridge_global_comparison.py --check
```

The check reads split certificates through the existing IO interface,
verifies every pinned logical input, reconstructs all paired layers
and the enlarged rectangle, and requires exact equality with the
stored complete global certificate. The predecessor files remain
unchanged.

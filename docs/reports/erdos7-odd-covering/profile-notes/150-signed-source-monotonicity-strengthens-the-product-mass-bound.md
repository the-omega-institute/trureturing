[Index](../marked_head_profile.md) · [Coupled source products](148-coupled-source-products-sharpen-the-actual-mass-bound.md) · [Original source mass](106-the-actual-denominator-shares-the-carrier-mass-residual.md)

# Signed source monotonicity strengthens the product mass bound

The original actual-source mass satisfies the stronger bound

    qK>=1-sigma, 0<=sigma<=6/49
      ==> S0<=53/360+sigma/10,
          0<E<=S=S0+rho<=53/360+sigma/10+rho.      (MP1)

This improves148's slope61/360 and extends its domain3/61. The proof
retains the signed source expression before taking upper bounds. It
uses coordinate monotonicity to discard only source deletions that
can decrease that expression, then optimizes the same two coupled
concentration products. The complete original carrier cap R, source
labels and residual rho=S-S0 are unchanged.

The result applies to both K orientations and the whole actual beta
domain. It gives a denominator upper bound for a later signed target
comparison; it does not prove a lower survival bound or a global K
improvement on its own.

## 1. Use the same six losses and two concentration products

Apply148's orientation argument, valid here because6/49<1/2.
Write ua,uz,ub,ud,ul,up for the alpha,z,beta,deficit,late and actual
carrier factor losses. Put

    A=(1-ua)*(1-uz)*(1-ub),
    A*(1-ud)>=1-sigma,
    A*(1-ul)*(1-up)>=1-sigma.                    (MP2)

All six losses lie in[0,sigma]. The actual distinguished carrier
c*=(0,1,1,1,1) has mass1-up. All carrier scores c.n are nonnegative.
Thus, retaining106's original full cap R,

    S0<=F:=sum_j a_j*n_j-R/5,
    a_0=1, a_j=(4+up)/5 for j>0,
    n_j=w_j*d_j/9-late_j.                        (MP3)

Here a_j are objective coefficients, w_j are widths and d_j are
availabilities. They are distinct from the barycentric factor losses.
The source domain gives

    1/2<=w_j<=1, 1/4<=d_j<=1, 4/5<=a_j<=1,
    R=max d/18+sum w/36+max(root sums of w)/36
                                      +max w/36+1/72. (MP4)

## 2. The signed expression is coordinatewise increasing

Increase one width w_j by t>=0 while keeping all other coordinates
fixed in(MP4). The sum, maximum root sum and maximum entry of w each
increase by at most t. Consequently

    F(new)-F(old)
      >=[(4/5)*(1/4)/9-3/(5*36)]*t=t/180>=0.     (MP5)

Likewise, increasing one availability d_j by t changes max d by at
most t, so

    F(new)-F(old)
      >=[(4/5)*(1/2)/9-1/(5*18)]*t=t/30>=0.      (MP6)

Decreasing any late_j also increases F, since its coefficient is
-a_j<0. These are finite-difference inequalities for maxima; no
differentiability or fixed maximizing cell is assumed.

Keep the selected deficit and late masses, the alpha-root1 mass,
the total root1 beta mass, and z. Remove every other deficit, alpha0,
root0 beta and unselected late mass. These operations increase widths
or availabilities, or decrease late coordinates. Their intermediate
coordinates stay in(MP4), hence(MP5),(MP6) show that they increase F.
This is an upper-bound operation on a finite source relaxation;
the resulting coordinates need not be realizable by an actual family.

The resulting data are

    w0=(1+ud)/2, w1=w2=w3=w4=1,
    z=(3+uz)/4, alpha1=(1-ua)/4,
    beta0=beta1=0, sum_(j>=2)beta_j=(1-ub)/4,
    late0=(1-ul)/72, other late_j=0.              (MP7)

Root0 availabilities are both z; root1 availabilities are at most z.
The largest root width sum is3 and the largest width is1. Therefore

    R=z/18+ud/72+1/4.                            (MP8)

The root1 beta distribution remains arbitrary: all its objective
coefficients and widths are equal, so only its total enters F.

## 3. Expand after the common signed terms cancel

Substitute(MP7),(MP8) directly into(MP3):

    F=(1+ud)*z/18-(1-ul)/72
      +(4+up)/5*[4z/9-(1-ua)/12-(1-ub)/36]-R/5.

The exact expansion is

    360*(F-53/360)
      =24ua+36uz+8ub+14ud+5ul+16up
                         +5ud*uz+8up*uz+6up*ua+2up*ub. (MP9)

Unlike an absolute source-norm bound, this expression preserves the
cancellation between the raw mass and the carrier subtraction, and
the cancellation with the complete cap R. The cross terms are kept.

## 4. Compress the three common factors, then the two separate losses

Set y=1-A and x=(sigma-y)/(1-y). The products(MP2) imply

    0<=y<=sigma,
    ud<=x, 1-(1-ul)*(1-up)<=x.                   (MP10)

Collect the ua,uz,ub terms in(MP9) and put M=36+5ud+8up. They are

    M*uz+(24+6up)*ua+(8+2up)*ub.

On sigma<=6/49 the following uniform inequalities hold:

    24+6up<=36*(1-sigma)<=M*(1-uz),
    8+2up<=36*(1-sigma)<=M*(1-uz)*(1-ua).         (MP11)

For the second one, the remaining product is at least A>=1-sigma.
The first numerical inequality is weakest at sigma=6/49 and follows
from sigma<=2/7; the beta inequality also has positive margin at that
endpoint. Sequential product expansion now gives

    M*uz+(24+6up)*ua+(8+2up)*ub<=M*y.             (MP12)

The remaining expression from(MP9) is consequently at most

    36y+(14+5y)*ud+5ul+(16+8y)*up.

Since5<=(16+8y)*(1-up),

    5ul+(16+8y)*up
      <=(16+8y)*[1-(1-ul)*(1-up)].               (MP13)

Use both separate bounds(MP10) to get

    360*(F-53/360)<=36y+(30+13y)*(sigma-y)/(1-y).

Finally the exact identity

    36sigma-[36y+(30+13y)*(sigma-y)/(1-y)]
       =(sigma-y)*(6-49y)/(1-y)>=0               (MP14)

holds throughout the stated domain. Combining(MP3)--(MP14) proves
S0<=53/360+sigma/10. The original0<E<=S=S0+rho proves(MP1) with
the same residual coefficient1. The exchange of the two root0 cells
transports the entire argument to the other orientation.

## 5. Exact scope and scalar non-extension

The linear36sigma bound in(MP14) is exact for its reduced envelope
at y=sigma. No actual-family attainment is asserted.
Above6/49 the reduced envelope fails to obey that line. One exact
witness is

    sigma=1/8, y=123/1000, x=2/877,
    uz=y, ud=up=x, ua=ub=ul=0.

Both relaxed products in(MP2) equal1-sigma, while the excess over
36sigma in(MP14) is27/438500>0. These two relaxed products alone do
not impose the whole original qK equation. This witness therefore
does not establish failure of(MP1) for actual sources beyond6/49;
it only prevents extending this particular final scalar certificate.

[monotone_product_carrier_mass.py](../frontier/monotone_product_carrier_mass.py)
exports `bound_S0`, `bound_E`, `EARLY_LIMIT=6/49` and `SLOPE=1/10`.
Its symbolic rational expansion derives all ten terms in(MP9) from
the original signed formula; it also checks the monotonicity prices,
product-compression guards and exact non-extension witness.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/monotone_product_carrier_mass.py --check
```

The continuous-source theorem is proved above. The program verifies
its algebra and domain constants, without enumerating covering
families or replacing the ordinary proof by finite samples. No
global comparison, Lean verification or unrestricted Erdos7 result
is asserted here.

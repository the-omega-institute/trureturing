[Index](../marked_head_profile.md) · [Original actual mass](106-the-actual-denominator-shares-the-carrier-mass-residual.md) · [Source-dependent outside credits](147-source-dependent-credits-cross-the-old-middle-bottleneck.md)

# Coupled source products sharpen the actual mass bound

For the original actual-source mass and residual of106,

    qK>=1-sigma, 0<=sigma<=3/61
      ==> S0<=53/360+(61/360)*sigma,
          0<E<=S=S0+rho<=53/360+(61/360)*sigma+rho. (PC1)

The slope61/360 replaces106's5/9 on this stated domain. Both K
orientations, the whole beta face, the actual carrier distribution
and all original source tails remain. The change is to retain two
coupled product inequalities in the concentration proof, instead of
bounding each factor loss separately by sigma. No source variables
are assumed probabilistically independent.

This improves an upper bound for the actual denominator. It is not
a lower bound for survival, and does not by itself give a complete
global comparison. The residual is exactly the existing rho=S-S0.

## 1. Orientation retains two product constraints

Use106's product-barycentric coordinates, with alpha-root1 weight
a2, z=3/4 weight z0, root1 beta weight bB, and deficit, late and
carrier factors d_i,l_i,pi_i for the two K orientations. Put

    A=a2*z0*bB,
    t=d1*l1*pi_(1,1)+d2*l2*pi_(1,0),
    qK=A*t>=1-sigma.                              (PC2)

The two d_i sum to at most1, and the two l_i*pi_i also sum to at
most1. Since t>=qK>1/2,106's orientation lemma selects i such that

    d_i>=t, l_i*pi_i>=t.

Orient this i as selected deficit/late cell0 and carrier(1,1). Define
the six losses in[0,1] by

    a2=1-u_alpha, z0=1-u_z, bB=1-u_beta,
    d_i=1-u_d, l_i=1-u_l, pi_i=1-u_pi.

Then, crucially,

    A*(1-u_d)>=1-sigma,
    A*(1-u_l)*(1-u_pi)>=1-sigma.                  (PC3)

Every loss is at most sigma, but(PC3) contains more information than
those six separate bounds. The sum in(PC2) has not been replaced by
an unjustified single product of all six factors: the two different
constraints in(PC3) are kept separately.

## 2. Price the original source formula by individual factor losses

As in106, let

    w_j=1-deficit_j, d_j=z-alpha_ROOT(j)-beta_j,
    n_j=w_j*d_j/9-late_j, s=sum_j n_j,
    R=max_j d_j/18+sum_j w_j/36
       +max(sum_(j<2)w_j,sum_(j>=2)w_j)/36
       +max_j w_j/36+1/72,
    S0=s-(sum_c pi_c*c.n+R)/5.                    (PC4)

Here d_j is availability, while u_d is the selected deficit-factor
loss. The original full/partial carrier coefficient vectors c are
nonnegative. No term of R is truncated.

Project to the same entire K beta face as106, normalizing its positive
root1 beta mass without choosing a beta vertex. The factorwise norm
bounds are

    ||deficit-deficit*||1<=u_d,
    ||alpha-alpha*||1<=u_alpha/2,
    z-z*=u_z/4>=0,
    ||beta-beta*||1<=u_beta/2,
    ||late-late*||1<=u_l/36.                     (PC5)

The positive root1 beta mass exists by(PC3). Because all widths and
availabilities lie in[0,1], expanding the products in n and noting
that a root contains at most three cells gives

    ||n-n*||1<=(u_d+5u_z/4+3u_alpha/2+u_beta/2)/9
                                                        +u_l/36. (PC6)

The complete face identities are

    s*=1/4, c*.n*=2/9, R*=7/24, S0*=53/360,
    c*=(0,1,1,1,1).                              (PC7)

The opposite root0 cell has availability at least
3/4-(u_alpha+u_beta)/4: z can only increase, while its alpha and
root0 beta masses have those respective caps. Also

    sum w>=9/2,
    sum_(root1)w>=3-u_d/2,
    max w>=w_1>=1-u_d/2.

Substituting these specific lower choices into each maximum in R
proves

    R>=7/24-(u_alpha+u_beta+2u_d)/72.             (PC8)

No maximizing cell needs to stay fixed.

The actual distinguished carrier has mass1-u_pi; all other c.n are
nonnegative. Therefore

    S0<=sum_j[1-(1-u_pi)c*_j/5]*n_j-R/5.

The bracketed coefficients lie in[0,1]. Compare to n* using(PC6),
then use(PC7),(PC8), to obtain

    S0<=53/360
       +(61u_alpha+50u_z+21u_beta+42u_d+10u_l+16u_pi)/360. (PC9)

The numerator coefficients come from three contributions:

| Factor | Source norm | Loss of R/5 | Carrier loss | Total |
| --- | ---: | ---: | ---: | ---: |
|alpha|60|1|0|61|
|z|50|0|0|50|
|beta|20|1|0|21|
|deficit|40|2|0|42|
|late|10|0|0|10|
|carrier|0|0|16|16|

All entries are scaled by360. In particular, the carrier term uses
the face value c*.n*=2/9 after the common source norm is paid. It does
not assert that the actual c*.n equals its face value.

## 3. Optimize the coupled losses exactly

Set y=1-A. By(PC3),0<=y<=sigma. Since sigma<=3/61,

    50<=61*(1-u_alpha),
    21<=61*(1-y2),
    y2=1-(1-u_alpha)*(1-u_z).

Indeed both remaining products are at least1-sigma>=58/61.
Consequently

    61u_alpha+50u_z+21u_beta<=61y.                (PC10)

Likewise10<=16*(1-u_pi), giving

    10u_l+16u_pi<=16*[1-(1-u_l)*(1-u_pi)].        (PC11)

Put x=(sigma-y)/(1-y). The two separate constraints(PC3) give
u_d<=x and1-(1-u_l)*(1-u_pi)<=x. Thus the numerator in(PC9) is at
most61y+58x. The exact identity

    61sigma-[61y+58*(sigma-y)/(1-y)]
      =(sigma-y)*(3-61y)/(1-y)>=0                (PC12)

holds throughout0<=y<=sigma<=3/61. This proves the first inequality
in(PC1). The unchanged identity S=S0+rho and original0<E<=S prove
its second line, using the same residual once.

## 4. Boundary of this scalar envelope

The coefficient61 is sharp for the reduced product-loss optimization:
u_alpha=sigma with all other losses zero satisfies(PC3) and attains
61sigma. This is a statement about the relaxation, without an
actual-source attainment claim.

Beyond sigma=3/61, that linear envelope fails. For example, take

    sigma=1/18, u_alpha=1/20,
    u_d=u_pi=1/171, u_z=u_beta=u_l=0.

Both products in(PC3) equal17/18, but

    61u_alpha+42u_d+16u_pi-61sigma=1/3420>0.

More generally, for3/61<y<sigma<1, take u_alpha=y and
u_d=u_pi=(sigma-y)/(1-y). The excess in(PC12) changes sign. This
does not refute(PC1), which has an explicit restricted domain, nor
does it construct an actual covering family. A later consumer must
use a separately proved bound above3/61, such as106's5/9 bound.

The helper exports `bound_S0(sigma)` and `bound_E(sigma,rho)` with
the proved domain checked, together with exact constants
`EARLY_LIMIT=3/61` and `SLOPE=61/360`.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/product_coupled_carrier_mass.py --check
```

Its exact checks retain all six coefficients, the polynomial identity,
domain margins, unchanged residual coefficient and the explicit
scalar non-extension witness. The continuum proof is(PC2)--(PC12),
not interpolation of the helper's example values. The result is
ordinary mathematics with rational verification; no Lean or global
K improvement is claimed without a complete downstream comparison.

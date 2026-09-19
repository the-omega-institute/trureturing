[Index](../marked_head_profile.md) · [Whole K faces](71-global-j-k-control-faces-and-exact-escape-gaps.md) · [Actual residual](85-a-broad-five-slot-source-deletion-tradeoff.md) · [Complete denominator](94-quadratic-marked-events-and-a-common-residual-improve-global-k.md)

# The actual denominator shares the carrier mass residual

On the effective actual-source branch, let qK be the original
product-barycentric mass of the two K zero boxes, including the actual
carrier factor. If

    qK >= 1-sigma,  0 <= sigma < 1/2,

then the original carrier-averaged lower mass satisfies

    S0 <= 53/360 + 5*sigma/9.                         (M1)

Consequently, with the same actual residual rho=S-S0>=0 used in85,
the original positive complete denominator obeys

    0 < E <= S = S0+rho
              <= 53/360 + 5*sigma/9 + rho.           (M2)

Both full beta triangles and their entire stated neighborhoods are
included. No beta vertex concentration, fixed maximizing carrier,
sigma<=1/18 restriction or zero actual residual is required.

The ordinary proof below establishes the continuum inequality. The
exact arithmetic program
[carrier_mass_residual_bound.py](../frontier/carrier_mass_residual_bound.py)
and its [certificate](../certificates/source_norms/carrier_mass_residual_bound.json)
check the constants, all18 carrier coefficients, both affine triangle
bases and all terms of the complete cap. They are not Lean proofs.
This result supplies a denominator upper bound; it does not by itself
improve a global comparison or resolve unrestricted Erdos7.

## 1. The same actual carrier lower mass

Use the source coordinates of71 and85:

    ROOT=(0,0,1,1,1), w_j=1-deficit_j,
    d_j=z-alpha_ROOT(j)-beta_j,
    n_j=w_j*d_j/9-late_j, s=sum_j n_j.

The nonnegative deficit, alpha, beta and late vectors have total caps
1/2,1/4,1/4 and1/72. Also3/4<=z<=1. In particular,

    w_j>=1/2, d_j>=1/4, late_j<=1/72,
    n_j>=0, w_j<=1, d_j<=1.                         (M3)

The18 original full and partial carriers are

    c=(root,cell) in {-1,0,1} x {-1,0,1,2,3,4}.

For each carrier define the nonnegative coefficients

    c_j = 1_(ROOT(j)=root) + 1_(j=cell).

The value -1 denotes an absent label and contributes zero. Write

    R=max_j d_j/18 + sum_j w_j/36
       +max(sum_(j<2)w_j,sum_(j>=2)w_j)/36
       +max_j w_j/36 + 1/72.                       (M4)

The original mass formula in46, also reconstructed in53, is exactly

    D_c=s-(c.n+R)/5.

For the same normalized actual carrier distribution pi this gives

    S0=sum_c pi_c D_c
      =s-(sum_c pi_c c.n+R)/5.                     (M5)

Thus no nonshallow term is dropped, and no new carrier distribution
is chosen. In85 the identity rho=S-S0 uses precisely this S0. The
original complete survival denominator satisfies0<E<=S, as retained
in94. These are the inputs for the last step of(M2).

## 2. Concentration chooses one whole face

Use71's barycentric notation: d_i for deficit weights, l_i for late
weights, a_2 for the alpha-root1 weight, z_0 for the z=3/4 weight,
and b_B=b_3+b_4+b_5 for the three root1 beta vertices. Then

    qK=a_2*z_0*b_B*(d_1*l_1*pi_(1,1)
                             +d_2*l_2*pi_(1,0)).   (M6)

Every displayed factor lies in[0,1]. The concentration argument of71
therefore gives one orientation for which the supported alpha, z,
beta-face, deficit, late and carrier weights are all at least1-sigma.
For completeness, the only choice issue reduces to

    r=p_1*h_1+p_2*h_2 >= 1-sigma > 1/2,
    p_1+p_2<=1, h_1+h_2<=1.

Choose i with p_i>=r. If h_i<=1/2, then

    r<=p_i*h_i+(1-p_i)*(1-h_i)<=1/2,

a contradiction. If h_i>1/2, the same upper bound is at most h_i,
so h_i>=r. Here h_i=l_i*pi_i; each of its two factors is at least r.

Consider the orientation with selected deficit and late cell0 and
distinguished carrier c*=(1,1). The other orientation exchanges
cells0 and1. Project onto this K face, normalizing the root1 beta
weights without selecting a vertex:

    deficit*=(1/2,0,0,0,0), alpha*=(0,1/4),
    z*=3/4, beta*=(0,0,beta2*,beta3*,beta4*),
    beta2*+beta3*+beta4*=1/4,
    late*=(1/72,0,0,0,0).

The normalization is defined because b_B>=1-sigma>0. As in71,

    ||deficit-deficit*||1 <= sigma,
    ||alpha-alpha*||1 <= sigma/2,
    |z-z*| <= sigma/4,
    ||beta-beta*||1 <= sigma/2,
    ||late-late*||1 <= sigma/36.                   (M7)

Since all widths and availabilities are at most one, expanding each
product difference and using that each root occurs at most three
times yields

    ||n-n*||1
      <= (sigma+5*sigma/4+3*sigma/2+sigma/2)/9
                                                +sigma/36
       = sigma/2.                                (M8)

On the whole projected beta triangle,

    n*=(1/36,1/12,(1/2-beta2*)/9,
                       (1/2-beta3*)/9,(1/2-beta4*)/9),
    s*=1/4, c*=(0,1,1,1,1), c*.n*=2/9,
    R*=7/24, s*-(c*.n*+R*)/5=53/360.              (M9)

These are affine identities in beta*. In(M4), the two root0
availabilities are3/4 while every root1 availability lies in[1/4,1/2];
the widths are fixed. Hence R* is constant throughout the triangle.
The program verifies the affine bases against the existing six K
controls and all18 original carrier mass entries at each basis point.

## 3. A lower bound for the complete cap throughout the neighborhood

The same concentration conditions imply

    alpha0<=sigma/4, beta0+beta1<=sigma/4,
    deficit0>=(1-sigma)/2.

The other deficit coordinates consequently have total at most sigma/2.
Use these facts directly in each term of(M4):

    max d >= d_1 >= 3/4-sigma/2,
    sum w >= 9/2,
    rootmax w >= w_2+w_3+w_4 >= 3-sigma/2,
    max w >= w_1 >= 1-sigma/2.                    (M10)

The constant last term1/72 is unchanged. Therefore

    R >= 7/24-sigma*(1/36+1/72+1/72)
       = 7/24-sigma/18.                          (M11)

These lower bounds use explicit root and cell terms of each maximum.
They do not assert that the corresponding terms remain maximizing.
This is why the argument applies to the entire sigma<1/2 neighborhood.

## 4. Couple the mass loss and carrier loss before estimating

Since pi_c*>=1-sigma and all c.n are nonnegative by(M3),

    sum_c pi_c c.n >= (1-sigma)c*.n.

Set A_j=1-(1-sigma)c*_j/5. The distinguished carrier has only
zero-one coefficients, so0<=A_j<=1. Thus(M5) gives

    S0 <= sum_j A_j*n_j-R/5
       <= sum_j A_j*n_j*+||n-n*||1-R/5
       <= s*-c*.n*/5 + sigma*c*.n*/5
                       +sigma/2-R*/5+sigma/90
        = 53/360 + 2*sigma/45 + sigma/2 + sigma/90
        = 53/360 + 5*sigma/9.

This proves(M1). The cell0/cell1 exchange preserves the source caps,
all18 carriers, the norm estimate and each term of R, so it proves the
same inequality for the other orientation. Finally E<=S=S0+rho gives
(M2), using the same rho once. In particular, a later target decrement
h consumes h*rho from an existing positive residual budget; it must not
treat(M2) as a rho-free denominator bound.

The helper exports boundS0(sigma) and boundE(sigma,rho), with the exact
domain and residual nonnegativity checked explicitly.

[Index](../../marked_head_profile.md) · [Complete original local comparison](145-all-fifty-two-costs-give-a-complete-uniform-k-comparison.md) · [Actual carrier mass](../065-128/106-the-actual-denominator-shares-the-carrier-mass-residual.md) · [Two heavy costs](142-both-heavy-vector-controllers-have-a-uniform-source-radius.md)

# A global mass floor and coupled costs expand the K radius

For the same original52-cost comparison as145, both actual K
orientations and all admissible first-beta distributions satisfy

    sigma<=1/50, rho<=1/100000, r<=1/520
      ==> original comparison <=
        149990748106336357793499557621385857105126585482689492847
        /300345099760267858640221803730168614445757220522864000
        =499.3946903946737... <509.                 (ER1)

The sigma radius is200 times145's1/10000. This is a larger local
rectangle, including all original tails and alternatives, not an
improvement of the complete outside comparison or a measure of
progress towards unrestricted Erdos7. The remaining residual and
source regions still require their own complete bounds.

Two ordinary inequalities make the expansion possible: a global
lower bound for the actual carrier mass, and cancellation of common
source terms before bounding the two heavy costs. The certificate
checks exact rational arithmetic and finite optimization reductions;
no Lean verification or unrestricted resolution is asserted.

## 1. A global lower bound on the effective source product domain

Use106's full original definitions, with ROOT=(0,0,1,1,1):

    w_j=1-deficit_j,
    d_j=z-alpha_ROOT(j)-beta_j,
    n_j=w_j*d_j/9-late_j, s=sum_j n_j,
    R=max_j d_j/18+sum_j w_j/36
      +max(sum_(j<2)w_j,sum_(j>=2)w_j)/36
      +max_j w_j/36+1/72,
    D_c=s-(c.n+R)/5,
    S0=sum_c pi_c D_c, S=S0+rho.                  (ER2)

The18 original full/partial carriers have
c_j=1_(ROOT(j)=root)+1_(j=cell), where each absent label is -1.
The normalized carrier distribution pi is the actual one. The
five source factors are the deficit, alpha, beta and late simplices
with caps1/2,1/4,1/4,1/72, and the interval3/4<=z<=1. Their vertex
counts are6,3,6,6,2. This product is an outer domain containing the
effective packed sources, including the sources with the actual
first-beta and orientation restrictions.

For each fixed c, D_c is concave in each source factor separately:

* With the other factors fixed, every n_j, hence s and c.n, is
  affine in each one of deficit, alpha, beta, late and z. The product
  w_j*d_j is separately affine because its two factors involve
  disjoint source coordinates.
* With one factor varying, each displayed maximum in R is a maximum
  of affine functions. The remaining sum and constant terms are
  affine. Thus R is convex in that factor; it is constant in late.
* Consequently D_c=s-c.n/5-R/5 is separately concave in all five
  factors. This is not an assertion of joint concavity.

Decompose each source factor into its own simplex or interval
vertices, and apply the concavity inequality successively in the
five factors. The result is

    D_c(theta)>=sum_v lambda_v D_c(v),             (ER3)

where lambda_v is the product of the five barycentric weights.
These weights implement a deterministic parameter decomposition;
they do not assert probabilistic independence of actual source data.
The vertices in this containing product need not themselves be
realizable packed sources. Taking the actual pi-average preserves
the inequality, so a lower bound for every vertex/carrier entry is
a lower bound for every actual S0.

All1296*18=23328 entries have an independent integer expression.
At a vertex put a_j=2w_j, b_j=4d_j and ell_j=72late_j. These are
integers, and

    N_j=a_j*b_j-ell_j=72n_j,
    Rnum=max b+sum a+max(sum_(j<2)a_j,sum_(j>=2)a_j)
         +max a+1=72R,
    360D_c=5sum N-c.N-Rnum.                      (ER4)

The minimum integer in(ER4) is53; exactly20 vertex/carrier pairs
attain it. The certificate retains the complete histogram, all20
minimizers and a digest of all23328 entries. Equations(ER2)--(ER4)
therefore prove

    S0>=53/360, S>=53/360+rho.                    (ER5)

This applies throughout the stated effective source product domain,
without a K concentration assumption. It is a carrier-mass lower
bound, not a lower bound of53/360 for the final AP denominator E.
The additional original costs separating S from E must still be paid.

## 2. Cancel the common mass in the two heavy costs

Fix either heavy cost i=0,16 and any of its100 original91 branches.
Write the new margin as

    M_b=C*s+G_b.

The original cost inequality uses C*S-min_b M_b. Thus the common
mass is C*(S-s), before any estimate is made. On the same actual
first-beta projection used in142, let star denote the projected K
face. The unchanged identities and norms are

    s*=1/4, S0*=53/360, c*.n*=2/9, R*=7/24,
    ||n-n*||1<=N=delta/2,
    ||eta-eta*||1<=delta/9,
    ||d-d*||infinity<=3delta/4,
    pi_c*>=1-delta.                              (ER6)

The distinguished c* has only zero-one coefficients, and all
original c.n are nonnegative. Hence

    score.n>= (1-delta)c*.n
            >=c*.n*-N-delta*(2/9).

The second inequality follows by substituting c*.n>=c*.n*-N and
dropping the favorable delta*N. The complete cap estimate106 gives
R>=R*-delta/18. Substituting both into(ER2) yields

    S-s=-(score.n+R)/5+rho
       <=53/360-1/4+(7/45)*delta+rho.             (ER7)

Let L_b be142's complete branch error. Its C*N term pays only the
variation of C*s. After the exact cancellation it is removed, so
the resulting cost error is

    C*((7/45)*delta+rho)+max_b(L_b-C*N).

Relative to142's C*((5/9)*delta+rho)+max_b L_b, the saving is exactly

    C*((5/9-7/45)*delta+N)=(9/10)*C*delta.       (ER8)

Every other score, marker, selected-deep and complete residual term
is retained. In particular, r<=5rho still gives rbar=1/20000 at the
chosen residual cap, so91's required rbar<1/2500 remains valid.
The availability guard3delta/4<=1/18 holds at all reported radii.

## 3. Cancel the identical complete zero-seven block

The common raw expression in each heavy branch is

    raw357(f)-raw35(f_zero),
    f_zero=seven_block(f,0).                     (ER9)

The exact raw357 decomposition used in140 contains raw35(f_zero)
as its first finite seven block. It therefore cancels identically.
All remaining finite blocks and the exact infinite tail keep their
original nonnegative Lipschitz prices. If L_full and L_zero are the
three-coordinate price vectors from140, the price of(ER9) is

    L_remaining=L_full-L_zero.

142 used L_full+L_zero. Thus, independently of the selected branch,
the additional exact saving is

    2*(L_zero,n*N+L_zero,eta*delta/9
                         +L_zero,d*3delta/4).    (ER10)

The helper checks that the original zero tag is exactly the first
finite block, that all three price components agree, and that all
remaining components are nonnegative. This does not subtract
unrelated maxima or assume convexity of a difference of maxima.

At delta=1/27 the weighted heavy error falls from4.710507713989868...
to1.8831990213338072... through(ER8),(ER10). These are transport-error
payments, not changes to the already adopted face bounds.

## 4. Complete local comparisons and the wider-envelope obstruction

In145's denominator formula substitute the valid mass lower bound
53/360 from(ER5):

    d=(1-1/614922)*(53/360)-B_shared-H1/55902.     (ER11)

B_shared is the same jointly maximized five-cost deduction at the
new radius, including complete tails. The numerator retains145's
11 mean costs,28 single-hinge costs,10 quadratic/raw costs, the two
improved heavy costs and the first retained raw81 cost. Their labels
partition exactly the original52 labels. It also retains the complete
square, the original offset, and the negative signed mass term,
which uses the lower bound53/360. Positive mass terms use the
original upper bound53/360+5delta/9+rho.

Exact complete evaluations give:

| sigma radius | Final denominator lower | Complete numerator upper | Complete comparison upper |
| --- | ---: | ---: | ---: |
|1/100|0.07847089504306004...|35.9344392237378...|479.5274705727244...|
|1/50|0.07719421042741008...|36.88343711844352...|499.3946903946737...|

Both use rho<=1/100000 and r<=1/520. Each full reduction evaluates
9750000 original heads, with312 independent rational comparisons.
The corresponding continuum statements follow from the source
inequalities, convex finite reductions and exact infinite-tail
identities already used in134--145, together with(ER3),(ER7),(ER9).
Head enumeration alone would not prove the source-uniform claim.

At delta=1/27, (ER11) still gives d=0.07501960802791048...>0, but
these particular cost envelopes cannot establish the target509.
Keep only the following nonnegative increments over113's face
numerator, dropping the mean11, single-hinge H2 and joint-quadratic9
increments completely:

| Retained envelope payment | Increment |
| --- | ---: |
|Two heavy costs after both cancellations|1.8831990213338072...|
|Single-hinge H1|0.23646916049143943...|
|Single-hinge positive mass|0.001651857964895905...|
|Complete square|0.17719110643053101...|
|First raw81|0.027865045401990262...|
|Second raw81|0.12843163958016185...|

The omitted envelopes have nonnegative increments: their enlarged
feasible programs and complete nonnegative error tails include the
zero-radius programs. Even this optimistic numerator gives

    offset+N_optimistic/d
      =6561231119924799494981826229970575191577141242905187452231
       /12620047998103584862049908394339895972286143963402000000
      =519.9054013828438...>509.                 (ER12)

This is a lower bound on the value of this fixed upper-envelope
calculation. It is not a lower bound on any actual source comparison,
not a counterexample to a covering conjecture and not an obstruction
to a different valid proof. It prevents an unsupported extrapolation
of(ER1) to1/27 using the same estimates.

The remaining heavy payment dominates the retained numerator losses.
A concrete next improvement is to keep the individual source-factor
losses and their product concentration constraints inside the heavy
score and marker estimates, instead of paying independent delta
prices in every term. Another is to use branch-specific face slack
before taking the common maximum. A stronger local rectangle must
still be joined to complete bounds for its residual complement and
other source regions before it improves the global comparison.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/k_neighborhood_radius_study.py --delta 1/50 --check --output docs/reports/erdos7-odd-covering/certificates/source_norms/endpoint-bounds/k_neighborhood_radius_1_50.json
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/k_neighborhood_radius_study.py --delta 1/27 --denominator-only --check --output docs/reports/erdos7-odd-covering/certificates/source_norms/endpoint-bounds/k_neighborhood_radius_obstruction_1_27.json
```

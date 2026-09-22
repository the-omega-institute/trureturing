[Index](../../marked_head_profile.md) · [Original marked bounds](94-quadratic-marked-events-and-a-common-residual-improve-global-k.md) · [Generic retained-deep bridge](99-tied-root-deep-payments-use-one-actual-capacity-budget.md)

# Fractional deep payments improve the global comparison

The original marked bounds and the generic retained-deep bounds can be
combined with fixed convex weights for each original cost. Their losses
use one actual residual and the existing source-escape reserve. This
gives the complete global bound

    K<=108494180838410638605728787506811049584537629
          /212986060315016386011231666281461556328000
      =509.39568851568337270436921899285... .          (FD0)

The target is K0-13/200, improving94 by3/200. It exceeds the old
scalar-template decrement capacity0.05733665963... because the new
retained-deep inequality removes its fixed deep loss. No prior target
decrement is added again. All original test residues, complete exponent
tails, quadratic curvature, eight fallback branches and both terminal
errors are retained. The box20/current8 sufficient gap is still positive
at106.3962635160015146031940... . Unrestricted Erdos7 remains open.
These are ordinary proofs and exact rational checks, not Lean results.

## 1. Two alternatives bound the same cost

Use94's46 original costs, barriers C_i and positive comparison weights
beta_i. For each independently labelled test, let d_i be its actual
barrier margin and m_i its original carrier-averaged lower bound. The
same actual source, forbidden-carrier mixture and residual rho occur
in all these inequalities. In a concentration region sigma=1-qK<=delta,
with best-slot source loss r<r_star, retain the packing gap G>=g>0 and
best-slot mass bound m/5>=b_star. Write

    alpha_i=1 or6/5,
    s_i=13/1215 or40/3645,
    vmin_i=f_i(2)-f_i(1), vmax_i=f_i(4)-f_i(3),

for linear or quadratic costs, respectively. The selected-deep
coefficient s_i is the complete sum over depths3,...,5 or3,...,6,
including the outside complete-seven factor1/5.

The original94 inequality and99's generic bridge give simultaneously

    d_i-m_i>=max(0,a_i-p_i*rho,b_i-t_i*rho-q_i*sigma), (FD1)

where

    a_i=vmin_i*min((alpha_i-(1+delta)/5)*g,b_star)
                                              -(s_i/5)*vmax_i,
    p_i=max(vmax_i,vmin_i/(9*g)),
    b_i=vmin_i*min(((1-delta)/5)*g,b_star),
    t_i=max(C_i,vmin_i/(9*g)), q_i=s_i*C_i/4.          (FD2)

For the last inequality,99 bounds the actual selected-deep loss by
C_i*Edeep+s_i*C_i*chi. Its source imbalance obeys chi<=sigma/4. Its
stronger residual term is rho-r/5; replacing it by rho only weakens
the bound. The actual best-slot mass m<=1/9 gives the fixed penalties
in(FD2). Every alternative still concerns the same cost. No gain is
added to another gain for that cost.

## 2. Fixed fractions share one actual error budget

Choose numbers lambda_i,nu_i>=0 with lambda_i+nu_i<=1, independently
of all source parameters and residues. Since a maximum is at least
any convex combination of its entries, (FD1) implies

    d_i-m_i>=lambda_i*(a_i-p_i*rho)
                      +nu_i*(b_i-t_i*rho-q_i*sigma).

Define

    B=sum_i beta_i*(lambda_i*a_i+nu_i*b_i),
    P=sum_i beta_i*(lambda_i*p_i+nu_i*t_i),
    Q=sum_i beta_i*nu_i*q_i.                          (FD3)

Let Acur be74's conservative positive coefficient of the old actual
mass residual. If P<=Acur, summing the cost comparisons proves

    Acur*rho+sum_i beta_i*(d_i-m_i)
                      >=B-Q*sigma+(Acur-P)*rho
                      >=B-Q*sigma.                  (FD4)

This also explains why summing the penalties of every available new
bound and finding a total larger than Acur is not an obstruction.
One may use a fraction of a valid inequality. Equivalently, for fixed
sigma, the original sum of positive maxima is convex and piecewise
affine in rho; its minimum is attained at zero or at an intersection
of its finitely many affine branches. The certificate below needs
only the fixed fractions, not a claim of optimality.

## 3. One explicit selection satisfies all source guards

Fix

    delta=1/32, r_star=1/600, h=13/200.

The concentration geometry gives

    h1>=1/3-delta/6, eta_min>=1/9-delta/18,
    Delta<=3*delta/4=3/128<1/18.

The four general source packing guards of85 are

    1/10-r_star,
    (1/3-delta/6)/5-r_star,
    (1/9-delta/18)/5-r_star,
    (1/3-delta/6)*(1/10-3*delta/4)-2*r_star.

Their minimum is g=97/4800>0; every first-label and division guard
holds. Also b_star=1/50-r_star/5=59/3000>0. The original unselected
pure3, positive5 and seven tails stay in their complete formulas.

Use lambda_i=1 on the following30 original indices:

    3,4,5,6,9,11,12,13,14,15,19,20,21,22,25,27,
    28,29,30,31,34,35,37,38,39,40,42,43,44,45.

Use nu_i=1 on these nine indices:

    2,8,10,18,24,26,32,33,36.

Use nu_41=1/5 for the quadratic tuple00. Every unspecified fraction
is zero, including lambda_41. The unused4/5 of this cost uses the
zero bound in(FD1). Thus40 costs contribute and six retain only their
old bound. All46 costs remain in the original comparison.

The resulting exact sums are

    B=1931931302049339947737789697
        /117314167779548282132029440000
      =0.01646801352825297128573708...,

    P=10790192748327095388917880693000300293
        /199998816611196407666923838977200000
      =53.95128296835649791865116...,

    Q=14185245333258106709560688348220751
        /115621837676100064384764059170800000
      =0.12268655833854046721060457... .              (FD5)

The unused residual coefficient is strictly positive:

    Acur-P=0.32369700914748258929334488... .           (FD6)

These fixed rational fractions are sufficient. No parameter optimum
or best possible comparison is asserted.

## 4. Pay source imbalance with the existing escape reserve

Let E be the actual positive survival denominator, and B_escape the
old product-interpolated signed gap. Profiles92 and94 prove, using
the same source/carrier product weights,

    B_escape-hE>=R_h(sigma),
    R_h(sigma)=-h/4+(gamma2-11*h/36)*sigma
                     -(gamma2-gamma1-11*h/36)*sigma^2. (FD7)

Here gamma1 and gamma2 are the two exact positive escape layers of92.
The quadratic coefficient being subtracted is positive. Hence R_h is
concave on[0,1]. The source mass estimate used in(FD7) retains both
K and J control masses; it is not an independently optimized mass.

For the concentrated small-r case, combining(FD4) with(FD7) gives

    Phi_(K0-h)>=B-Q*sigma+R_h(sigma).

This is concave in sigma. Its minimum on[0,delta] is at one of the
two endpoints. Outside concentration use R_h directly and check the
endpoints delta,1.

In the concentrated large-r case, the actual cofactor5 defect gives
rho>=r/5>=r_star/5. Discarding the nonnegative old escape reserve and
using E<=1/4+11*delta/36 gives the margin

    Acur*r_star/5-h*(1/4+11*delta/36).                (FD8)

The five strict endpoint comparisons are:

| Case | Signed margin lower bound |
| --- | ---: |
| Small r, sigma=0 | 0.0002180135282529712857... |
| Small r, sigma=delta | 0.0134355420536763112256... |
| Large r | 0.0012210002702791046137... |
| Outside, sigma=delta | 0.0008014834735027295402... |
| Outside, sigma=1 | 0.0307009357493101091336... |

The old comparison is evaluated at K0 first; the full decrement is
-hE. Acur<=A0 is therefore a valid coefficient before subtracting
that entire denominator term. The proof does not additionally
subtract h times the residual or silently change to another mass
coefficient. The checker also verifies positivity of the inherited
target-dependent sign coefficient A0-(23/42)*h.

The same positive survival bound permits division. All eight complete
fallback comparisons stay strictly below K0-h. Both complete terminal
errors are added without alteration. This proves(FD0) throughout the
original source split; it does not extrapolate a face equality into
a neighborhood or assert concavity of a patched table.

## Reproduction and boundary

The [checker](../../frontier/source-budgets/fractional_deep_global.py) pins94's complete
original inventory and99's generic retained-deep theorem. It compares
all46 barriers, weights and derivative bounds, reconstructs both
alternative coefficients and the fixed fractions, checks every source
guard and the five exact signed margins, and retains all eight
fallbacks and both full terminal errors. The
[certificate](../../certificates/source_norms/source-budgets/fractional_deep_global.json)
stores the exact cost rows, shared budgets and full comparison.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/fractional_deep_global.py --check
```

The finite certificate verifies this concrete consumption of the
ordinary general inequalities. It does not replace the infinite-tail
proofs, construct an odd covering family, or settle unrestricted
Erdos7. The new global decrement is13/200 from K0; the preceding1/20
is an alternative comparison, not another credit to add.

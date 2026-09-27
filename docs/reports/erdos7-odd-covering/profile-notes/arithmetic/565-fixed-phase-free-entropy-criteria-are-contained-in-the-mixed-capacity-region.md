# Fixed phase-free joint entropy criteria are contained in the mixed-capacity region

Within the fixed pure-head depths and exponential parameter of [report534](534-one-entropy-budget-controls-every-pure-prime-chain.md), two valid joint-entropy certificates add no original family beyond [report539](539-a-weighted-mixed-inventory-certifies-one-entropy-law.md)'s already proved mixed-capacity region. This holds after optimizing every fractional singleton allocation and every allocation/density partition; it also holds for the stronger envelope retaining supports and depths but declaring every mixed query subset compatible.

The two quantitative bounds are

    Gamma_single >= (7/2) sum_(d in F) kappa(d),
    log Z_pf >= (49/15) sum_(d in F) kappa(d).

Thus success of either certificate forces Report539's actual mixed capacity v below2/3. This is a containment of sufficient EXISTENCE CLASSES. It does not negate [report540](540-pivot-layer-multiplicities-control-one-entropy-budget.md)'s stronger conclusion for every nu in G, and it is not a no-go theorem for other cutoffs, exponential parameters, source laws, or phase-sensitive joint moments. The results are ordinary mathematics with exact rational checks, not new Lean verification.

## 1. Fixed source, labels, and budget

Use P={3,5,7,11,13,17,19}, product Haar probability H, and a finite inclusion-minimal distinct-modulus original core M0 with the same full survivor U. All original phases are fixed. Removing a redundant original does not remove its numerical label from the unused-query inventory.

Retain exactly Report534's setup:

    (n3,n5,n7,n11,n13,n17,n19)=(8,7,7,7,7,7,7),
    B=10^9,
    Lambda=6075000000000/7235955529>800,
    C=4522277/500000,
    delta=565/51-C=51863873/25500000.

Its class G consists of probabilities supported on U with nu<=Lambda H and

    R_unused(nu)+D_H(nu)<=log Lambda.

Fix one nu in G and choose every maximizing query phase under that same nu. Let E_p be the occupied pure original depths at most n_p. Their original forbidden cylinders are pairwise disjoint: otherwise a nested original would be redundant. Write D_p for their complement, D=product_p D_p, and

    f_pure=sum_p sum_(j in E_p) 1_(A_(p,j)).

The original U is contained in D. Passing to D only enlarges an integration domain; it changes no original, query phase, or source law.

For a finite subset F of shallow mixed core labels let A_d be its simultaneously selected maximizing cylinder and L_F=sum_(d in F)1_(A_d). Let T be the remaining shallow mixed core labels. The pure and deep tails are those already retained in C; only T receives the additional density payment Lambda sum_(d in T)1/d.

## 2. One valid combined exponential moment

For p with fixed n=n_p define

    M_p=sum_(k=0)^(n-1) (p-1)e^k/p^(k+1)+e^n/p^n
          -sum_(j=1)^n p^-j,

    N_(p,r)=sum_(k=r)^(n-1) (p-1)e^k/p^(k+1)+e^n/p^n, 1<=r<=n,
             e^n/p^r, r>n,
    c_(p,r)=N_(p,r)/M_p.

For S subset F, let chi(S)=1 if all selected p-local cylinders in S are compatible at every p; otherwise chi(S)=0. For each p used by S put r_p(S)=max_(d in S,p|d)v_p(d). Empty products have value1. Define

    Z_comp(F)=sum_(S subset F)(e-1)^|S| chi(S)
                         product_(p used by S)c_(p,r_p(S)).       (ED1)

Then

    integral_U exp(f_pure+L_F)dH <= (product_p M_p) Z_comp(F).     (ED2)

Proof. Expand exp(L_F)=product_d[1+(e-1)1_(A_d)]. An incompatible subset gives zero. A compatible subset fixes, on every touched coordinate, one cylinder at the maximum depth. Expand the pure-coordinate exponential as well. All coefficients are nonnegative, and each cylinder intersection has mass at most p to minus its maximum depth. Fill missing head queries and nest them along the restricted cylinder to obtain N_(p,r); discarding the pure forbidden restriction here is a valid upper bound. If a coordinate is untouched, use the existing pure moment M_p, including its disjoint original-union subtraction and numerical filling of missing pure depths. Independence of Haar coordinates gives the product, and summing gives ED2. The different termwise upper bounds need not be attained by a common hypothetical phase layout.

The entropy variational inequality, used ONCE for f_pure+L_F, gives

    R_pure,head(nu)+R_F(nu)-D_H(nu)
      <=sum_p log M_p+log Z_comp(F).

Adding the retained unused-label inequality cancels the same D_H. Consequently

    R_P(nu)<C+log Z_comp(F)+Lambda sum_(d in T)1/d.              (ED3)

The corrected sufficient test is log Z_comp(F)+Lambda sum_T1/d<delta. A separate mixed entropy inequality cannot be added after the pure inequality has already spent this cancellation.

## 3. Weighted singleton profiles

For each d in F choose nonnegative lambda_(d,p), zero unless p|d and v_p(d)<=n_p, with sum_p lambda_(d,p)=1. Pointwise,

    1_(A_d)<=sum_p lambda_(d,p)1_(A_(d,p)).

Put w_(p,j)=sum_(d in F,v_p(d)=j)lambda_(d,p), s_(p,k)=sum_(j<=k)w_(p,j), and

    K_p(w)=sum_(k=0)^(n-1)(p-1)e^(k+s_(p,k))/p^(k+1)
              +e^(n+s_(p,n))/p^n-sum_(j=1)^n p^-j,
    Gamma_single=sum_p log(K_p(w)/M_p).                         (ED4)

Report540's local positive-expansion proof extends to these nonnegative real weights: exp(a1_A)=1+(exp(a)-1)1_A has nonnegative coefficients. On the actual disjoint pure forbidden union the integrand is at least1, permitting the same unweighted subtraction. Filling a missing pure depth t increases the numerical bound by at least(e-2)p^-t>0. Thus the combined moment is at most product_p K_p(w), and

    R_P(nu)<C+Gamma_single+Lambda sum_(d in T)1/d.              (ED5)

No projected mixed original is being declared a disjoint pure original. This weighted-moment step reuses Report540's method; the general dominance below is the additional conclusion.

## 4. Coordinate estimates

Define saturated cylinder caps

    a_(p,j)=(p-1)/((p-2)p^j),
    kappa(d)=product_(p|d)a_(p,v_p(d)).

The constant term

    C0_p=(p-1)/p-sum_(j=1)^n p^-j>0

satisfies M_p=C0_p+N_(p,1). Hence log K_p is the logarithm of a positive sum of exponentials of linear functions and is convex. Its derivative in w_(p,j) at zero is c_(p,j). The supporting-plane inequality gives

    Gamma_single>=sum_(d in F)sum_p lambda_(d,p)c_(p,v_p(d)).   (ED6)

The following exact lower bounds suffice:

| p |3|5|7|11|13|17|19|
|---|---:|---:|---:|---:|---:|---:|---:|
| c_(p,1) is greater than |8/9|5/8|2/5|1/4|1/5|3/20|2/15|

For completeness, these bounds can be verified by rational inequalities alone. The function N/(C0_p+N) increases with N, and N_(p,1) increases with e. Set e0=8/3, except e0=19/7 for p=5. With r_p the displayed lower bound, the residual(1-r_p)N_(p,1)(e0)-r_p*C0_p is respectively

    88274560/387420489,
    2210844423/257357187500,
    17163626/428830605,
    903608075/56824590636,
    15520847117/686155033395,
    305756930599/17948213557020,
    443984558738/29323462397895.

Every numerator is positive. The needed exponential bounds follow from the usual positive Taylor sums; already163/60=19/7+1/420<e. The upper bound e<11/4 is the same one used in the retained entropy estimates.

For1<=j<n,

    N_(p,j)=(p-1)e^j/p^(j+1)+N_(p,j+1),
    N_(p,j+1)>=e^(j+1)/p^(j+1),

so N_(p,j)<p*N_(p,j+1). For j>=n, equality holds. Thus a_(p,j)/c_(p,j) is nonincreasing over ALL positive depths, strictly decreasing only before n. This controls actual depths beyond the head without a cutoff claim.

For p>=5, substituting e=11/4 in N_(p,1)/(C0_p+N_(p,1)) gives a value strictly below2/3. The exact positive margins, in prime order5,7,11,13,17,19, are

    171609325/5821208889,
    11157648389/50375992305,
    419902832053/1065214478049,
    294405939625/670752103173,
    10593566432509/21385289492745,
    23773573459733/46226236060353.

Therefore0<c_(p,j)<=c_(p,1)<2/3 whenever p>=5.

## 5. Every successful singleton allocation was already in Report539

For a mixed d and one chosen p|d, the product of the other a-factors is at most b_p=4/15 if p=3, and at most b_p=2/3 otherwise. Raising a depth decreases an a-factor, and extra prime factors are below1. At depth1 the differences

    (2/7)r_p-b_p*a_(p,1)

are respectively

    8/105,1/1260,0,17/4158,6/5005,11/10710,32/33915.

They are nonnegative. The depth monotonicity proves

    kappa(d)<=(2/7)c_(p,v_p(d))

for every eligible allocated coordinate. Combining with ED6 proves

    Gamma_single>=(7/2)sum_(d in F)kappa(d).                    (ED7)

For density-paid labels,

    kappa(d)<=Dmax/d<(9/1600)*Lambda/d,
    Dmax=4096/935<9/2, Lambda>800.

Report539 includes every pure depth in its actual K_d and mixed capacity v. Its actual caps satisfy K_d<=kappa(d), and its retained full deep-tail estimate is Dmax*tau_P(10^9)<1/10000. Therefore any successful ED5 test yields

    v<(2/7)delta+1/10000
      =25936399/44625000<2/3,                                  (ED8)
    2/3-25936399/44625000=3813601/44625000.

This implication holds after arbitrary fractional allocation optimization and arbitrary F/T partition optimization. Report539 already constructs a full actual-survivor law in G with the required query bound throughout this region.

## 6. Even the compatible support-depth envelope is contained

Set chi(S)=1 for all S in ED1 and call the result Z_pf. This retains all supports and depths but discards their actual incompatibilities.

For each p the sequence c_(p,j) is positive, decreases to0, and starts below1 because C0_p>0. Choose an integer-valued X_p with Pr(X_p>=j)=c_(p,j), and choose these X_p independently. Then

    Z_pf=E exp(sum_(d in F)I_d),
    I_d=1_{X_p>=v_p(d) for every p|d},
    r_d=Pr(I_d=1)=product_(p|d)c_(p,v_p(d)).                     (ED9)

This is a probability representation of the numerical envelope, not a replacement of the actual source. Each exp(I_d) is a nonnegative increasing function of independent coordinates. Product-measure association, applied repeatedly, gives

    log Z_pf>=sum_(d in F)log(1+(e-1)r_d).                      (ED10)

For one coordinate and an independent copy X', the covariance of increasing bounded functions f,g is one half of E[(f(X)-f(X'))(g(X)-g(X'))], which is nonnegative. Induction over the independent coordinates gives the two-function association inequality: conditioning preserves monotonicity of the coordinate averages. Repeating that inequality gives the displayed product form, since a product of nonnegative increasing functions is increasing. All functions here are bounded and there are finitely many coordinates and labels. No independence of the mixed events themselves is asserted.

The root bounds in Section4 give c_(3,1)/a_(3,1)>4/3 and c_(p,1)/a_(p,1)>7/3 for p>=5. The all-depth comparison preserves these inequalities. Every mixed label contains either3 and another prime, or at least two primes>=5, so

    r_d>=(28/9)kappa(d),    0<r_d<2/3.                          (ED11)

The second inequality uses at least one p>=5. The function log(1+(e-1)r)/r decreases for r>0, by concavity of its numerator and its zero value at r=0. Hence for0<r<=2/3,

    log(1+(e-1)r)/r
      >(3/2)log(19/9)>21/20.

For the last inequality, e<11/4 and the exact comparison(11/4)^7<(19/9)^10 imply log(19/9)>7/10. Equations ED10--ED11 now yield

    log Z_pf>=(49/15)sum_(d in F)kappa(d),                      (ED12)

strictly if F is nonempty. For F empty both sides are0. A successful phase-free/density test therefore implies

    v<(15/49)delta+1/10000
      =51872203/83300000<2/3,                                  (ED13)
    2/3-51872203/83300000=10983391/249900000.

Thus the stronger numerical envelope also certifies only families already in Report539's existence region.

## 7. One actual twenty-label family defeats every allocation/density split

Reuse [report562](562-joint-deletion-certificates-and-an-actual-query-antichain.md)'s irredundant originals A_S=[0]_(d_S), with

    d_S=3*product_(q in S)q,
    S a three-element subset of{5,7,11,13,17,19}.

That report supplies private CRT points and the simultaneous maximizing queries[1]_(d_S) under one actual survivor-Haar law. The twenty labels and their arithmetic realization are existing results, not a new construction here.

For an allocated label ED6 gives a cost at least r_(max S). For a density-paid label the cost exceeds800/d_S. Every choice of fractional allocations and every partition therefore has total cost greater than the sum of the twenty independent minima of these two numerical lower bounds. Equality in this relaxation is not claimed realizable by the original Gamma.

The five labels for which the density lower bound is smaller are

    6783,7293,8151,10659,12597.

The other fifteen lower costs sum to12/5. Thus

    Gamma_single+Lambda sum_(d in T)1/d
      >12/5+800*(1/6783+1/7293+1/8151+1/10659+1/12597)
      =13891628/4849845=2.864344736...>delta,                    (ED14)

with exact gap402763799413/484984500000. In fact the allocated label inequalities are strict even if T is empty, by the strict root bounds. The fixture belongs to a separately certified positive region; it refutes the fixed certificate's success on this fixture, not the noncoverage target or existence of another good law.

## 8. Relation to the existing library and verification boundary

Report540 already proves the integer profile moment and reverse-pivot entropy estimate. Its three displayed examples are separately checked to lie inside Report539, while their every-nu-in-G conclusion remains stronger than an existence theorem. Sections5--6 above replace those three example comparisons by two general containment statements: all eligible fractional allocations and density splits, and the full compatible support-depth envelope. The result does not weaken the universal source-law conclusions of540.

Inside the declared ED1 framework, retaining actual query-phase incompatibility chi(S), or subtracting a valid positive mixed-original deletion contribution from the SAME combined moment, remains outside these exclusions. Changing the head cutoffs, exponential parameter, exact pure-inventory moments, or source construction is also outside the theorem. None of these possible routes is proved successful here.

The [standard-library consumer](../../frontier/cover-geometry/fixed_entropy_phasefree_dominance.py) writes the [exact result](../../frontier/cover-geometry/fixed_entropy_phasefree_dominance.json). Its104 exact rational checks pass under python3 -I -S -B -O. The checks reconstruct the coordinate lower/upper bounds, finite head and terminal-depth identities, both capacity thresholds, the logarithm certificate, and the exact twenty-label partition lower bound. They inherit the full tail inequality from539 and the actual twenty-label realization from562. The all-depth comparison, joint-moment estimate and association implication are proved above; they are not inferred from finite sampling. No source-law reset, full CRT scan, original-inventory regeneration or Lean build is performed.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_entropy_phasefree_dominance.py
```

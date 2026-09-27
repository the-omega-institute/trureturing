# A mixed-free first-eleven slot closes the unchanged PA law

Let Q={5,7,11,13,17,19}. Fix a finite family of nonunit Q-smooth
original moduli, with at most two original occurrences at each numerical
modulus and all residues fixed globally. If every numerical modulus

    5^a*7^b*11, a,b>=1,

has at most one original occurrence, the existing increasing-order PA
construction supplies one probability law nu on the complete actual
survivor satisfying

    R_Q(nu)<=910573262387495024737/180978450310680422400
            =5.031390537516154...<257/51.                         (AM1)

Both pure originals at11 are allowed. So are both occurrences at every
5^a*11 or7^b*11, all mixed5/7 cofactors at11-depth e>=2, all old5/7
originals, and every later13/17/19 label. All finite heights and all
original residues in these permitted inventories are arbitrary. The
conclusion retains every query height under this same law.

The genuinely additional consumer is this mixed-root inventory condition.
The underlying conditional convex comparison, actual PA construction,
row-loss inequality and complete-query mass identity are reused from
[reports348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md),
[538](538-near-maximal-mixed-packing-preserves-the-anchor-query-hinge.md),
[558](558-first-eleven-inventory-and-an-actual-phase-counterexample.md) and
[559](559-pure-union-savings-control-all-four-later-rows.md). The decomposition below is an ordinary consequence
of those results, not a new Lean theorem or a new external-literature
claim. It does not settle the arbitrary two-copy Q problem or unrestricted
Erdos #7.

## 1. One actual source, fixed slots, and the complete comparison

Write S5,S7 for the actual pure-coordinate survivors, with Haar masses
x>=1/2 and y>=2/3. Put

    sigma=1_(S5 x S7) d(H5 x H7),
    lambda0=1_(complete actual old5/7 survivor) d(H5 x H7).

These are UNNORMALIZED measures, lambda0<=sigma, and
lambda0(1)=xy-m with0<=m<=1/12. In particular, lambda0 is not a
separately chosen product source after mixed deletions.

For every e>=1, assign the at most two actual originals at d*11^e to
slots j=1,2, with at most one occurrence of each old numerical cofactor d
in each slot. This assignment is made once, independently of the sampled
old point and of every query. For i=(e,j), retain the complete weights

    beta_i=5/11^e, sum_(e>=1,j=1,2) beta_i=1.

At z=(z5,z7), let A_i,B_i,C_i count respectively the active nonunit old
cofactors5^a,7^b,5^a7^b (a,b>=1) in slot i. Activity means membership in
the fixed old projection of that actual original; the current11 residue
is not reselected after z is known. Set

    h_i=(A_i+B_i-1)_+,
    g_i=(A_i+B_i+C_i-1)_+,
    G11=sum_i beta_i*g_i,
    I11=integral G11 d lambda0.

Pure cofactor-one originals enter the actual pure11 union, not A,B,C.
Absent slots have A=B=C=0 but retain their beta weight.

The reused complete old-query comparison is

    F11=x/42+y/20+59/840,
    integral (L-2)_+ d lambda0<=F11,                            (AM2)

for every old query L including the unit and with at most one fixed
cylinder for each nonunit numerical cofactor. Completing absent query
labels is a comparison operation only; it does not add actual originals.

## 2. The exact amount assigned to the missing mixed grid

Apply the same conditional convex comparison to only the two axis label
families5^a and7^b, with payoff(s-1)_+. Each normalized pure restriction
has depth-e cylinder cap1/(w_p*p^e). Multiplying the comparison back by
xy gives the raw independent auxiliary measures

    pi_p(N=1)=w_p-1/p,
    pi_p(N=n)=(p-1)/p^n, n>=2,
    mass(pi_p)=w_p,
    integral (N-1) d pi_p=1/(p-1),
    integral (N-2)_+ d pi_p=1/[p*(p-1)],
    pi_p(N>=2)=1/p.

Every expectation below is integration against pi5 tensor pi7, of total
mass xy; the auxiliary measures are not silently normalized.

The axis count after adding the unit is N5+N7-1. Its threshold-two hinge
therefore has integral

    J_axes=integral (N5+N7-3)_+ d(pi5 x pi7)
       =x/42+y/20+1/35.                                       (AM3)

Indeed, for integers n,m>=1,

    (n+m-3)_+=(n-2)_++(m-2)_++1_(n>=2,m>=2).

The axis comparison followed by lambda0<=sigma gives

    H_i:=integral h_i d lambda0<=J_axes,
    chi_i:=J_axes-H_i>=0.

The complete-grid hinge and the axis hinge obey the pointwise identity

    (nm-2)_+-(n+m-3)_+=(n-1)*(m-1), n,m>=1.

The raw auxiliary first moments therefore give the parameter-independent
difference

    F11-J_axes=1/[(5-1)*(7-1)]=1/24.                            (AM4)

The arbitrary phase version is supplied by the existing conditional
comparison; it does not assume that the actual axis cylinders themselves
are nested. Finite label comparison followed by monotone completion is
valid because the displayed full geometric moments are finite.

Now retain the ACTUAL mixed contribution to overload:

    z_i=g_i-h_i,
    zeta_i=integral z_i d lambda0,
    mu_i=integral C_i d lambda0.

For nonnegative integer counts,0<=z_i<=C_i. Moreover, each mixed old
numerical cofactor occurs at most once in a fixed slot and its old Haar
cylinder has mass5^-a*7^-b. Since lambda0 is a Haar restriction,

    0<=zeta_i<=mu_i<=sum_(a,b>=1)5^-a*7^-b=1/24.              (AM5)

This uses no independence of the actual mixed events. A mixed cofactor
with A=B=0,C=1 has z_i=0: one active label need not add overload.

Write chi_bar=sum beta_i*chi_i and similarly zeta_bar,mu_bar. Nonnegative
summability and the complete beta identity give the exact source gap

    I11=J_axes-chi_bar+zeta_bar,
    F11-I11=1/24+chi_bar-zeta_bar
           >=1/24-mu_bar>=0.                                (AM6)

No beta tail is renormalized. In particular, infinitely many absent slots
contribute J_axes times their total weight to chi_bar, while their zeta and
mu contributions are zero. Only the actual original family is finite.

## 3. Same-row loss and the complete-query consumer

Let r11 be the Haar mass of the actual pure11 forbidden union and
delta=1-5*r11 in[0,1]. Report559 PU3, at a11=1/3, states for the actual
row loss ell11 that

    (3+delta)*ell11<=G11.

Integrate against the SAME lambda0. If Loss11=integral ell11 d lambda0,

    Loss11<=I11/(3+delta),
    E11:=I11/3-Loss11>=delta*I11/[3*(3+delta)]>=0.

The absolute PA saving S11=F11/3-Loss11 consequently satisfies

    3*S11=1/24+chi_bar-zeta_bar+3*E11,
    S11>=(1/24+chi_bar-zeta_bar)/3
            +delta*I11/[3*(3+delta)].                        (AM7)

These are credits in one source and one row. No reciprocal-cap credit or
unproved downstream coefficient is inserted.

For completeness, the exact existing increasing-order identity is

    (T-2)*lambda_fin(1)-Phi
      =-c0+A5*d5+A7*d7+A57*d5*d7
        +(T-2)*(1/12-m+S11+S13+S17+S19),                     (AM8)

where T=257/51, d5=x-1/2,d7=y-2/3, all A coefficients are positive,
all four S terms are nonnegative, and

    kreq=6168733163201163811/1650097635185615616000,
    c0=(T-2)*kreq.

Thus AM7, together with the retained anchor and later-row credits, is a
same-law sufficient condition whenever their sum in mass-saving units
exceeds kreq. A coarser stand-alone sufficient condition is

    1/24+chi_bar-zeta_bar+delta*I11/(3+delta)>3*kreq.           (AM9)

The actual final lambda_fin is the unchanged PA subprobability. Existing
PA estimates give positive mass and, for every finite complete query L,

    lambda_fin(L-1)<=2*lambda_fin(1)+Phi.

One final normalization nu=lambda_fin/lambda_fin(1), finite labelwise
maximization under this same nu, and increasing query boxes yield the
complete nonunit norm bound. No finite original height truncates query
heights, and no query changes the chosen law or the slot assignment.

## 4. One missing mixed root slot is sufficient

Suppose a collection Omega of slots has no mixed5^a7^b old cofactor, and
let omega=sum_(i in Omega) beta_i. For these slots zeta_i=0. For every
other slot,1/24+chi_i-zeta_i>=0 by AM5. Therefore

    F11-I11>=omega/24,
    S11>=omega/72.                                          (AM10)

The same proof gives an explicit numerical-inventory consumer. If
c_(a,b,e) is the actual multiplicity of the first11 numerical label
5^a*7^b*11^e, with a,b,e>=1, put

    B_mix=sum_(a,b,e>=1) 5*c_(a,b,e)/(5^a*7^b*11^e).

It counts neither pure/axis first11 labels nor labels involving later
primes. Summing the fixed-slot Haar caps in AM5 gives

    mu_bar<=B_mix<=1/24,
    S11>=(1/24-B_mix)/3.

Thus B_mix<1/24-3*kreq is sufficient. This is an explicit consumer of
AM5--AM7. Under the opening root-multiplicity condition,

    B_mix<=(1/24)*(5/11+10*sum_(e>=2)11^-e)=1/44,

so the same saving5/792 follows directly. This estimate completes the
entire geometric inventory and does not truncate original heights.

The bounds in AM10 also hold when Omega consists of slots with zeta_i=0,
even when syntactically present mixed labels add no overload.

Any omega>72*kreq suffices. The exact threshold is

    72*kreq=6168733163201163811/22918022710911328000
           =0.2691651562184819....

One exponent-one slot has weight5/11, which exceeds this threshold.
Under the numerical condition in the opening theorem, place every
singleton occurrence of5^a7^b*11 in slot1. There is no conflict: each
different old numerical cofactor has its own two-slot assignment, and
there is at most one original occurrence at this full label. Slot2 then
contains no mixed old cofactor. Pure11 and all axis-label occurrences can
still use both slots. This assignment changes neither actual originals
nor the actual PA kernel.

Consequently

    F11-I11>=5/264,
    S11>=5/792>kreq,
    Delta:=(T-2)*(5/792-kreq)
      =1416183295737692063/180978450310680422400>0.

By AM8, (T-2)*lambda_fin(1)-Phi>=Delta. Since0<lambda_fin(1)<=1,

    R_Q(nu)<=T-Delta/lambda_fin(1)<=T-Delta,

which is exactly AM1. The other anchor credits, pure-union shortage,
later-row savings and cap improvements were discarded in this bound.

This criterion is distinct from Report558's at-most-one pure11 original
and Report544's missing slots at two of55,77,385. It allows both pure11
originals and both55 and77 occurrences. It is a new sufficient class
relative to those stated inventory criteria, not a claim that every
family in the class previously lacked any noncoverage certificate.

## 5. Necessary conditions for failure of the first-row certificate

If S11<=kreq, AM6--AM7 force simultaneously

    chi_bar<=3*kreq,
    zeta_bar>=1/24-3*kreq
      =5583096515903388063/183344181687290624000,
    24*zeta_bar>=16749289547710164189/22918022710911328000
      =0.7308348437815181...,
    E11<=kreq-(1/24+chi_bar-zeta_bar)/3.

Thus a first-row certificate that remains insufficient must consume at
least73.0834 percent of the complete mixed-grid bound through actual
overload, while the axis-comparison slack and the local loss slack are
small. The same occupancy lower bound follows for mu_bar, but occupancy
alone does not imply it for zeta_bar.

If omega0 is the total beta weight of slots with zeta_i=0, necessarily
omega0<=72*kreq. Anchor and later-row credits can still certify a family
that fails this stand-alone criterion. Conversely, being unproved by this
criterion supplies no covering, no all-laws lower witness, and no upper
bound on actual survival.

In Report559 Section8's specific channel family, a mixed cofactor never
overlaps either axis event and contributes at most one to the count.
Its zeta_i is zero at every slot, so AM10 gives S11>=1/72. That report's
stronger family-specific S11>=31/1260 is retained; it is not republished
as a new result.

The still missing arbitrary-family estimate must control the joint
compatibility of large mixed overload, small axis-comparison slack, and
small actual row-loss slack under fixed residues and the same old source.
The identities above identify these quantities but supply no universal
positive gap across all inventories.


## 6. Verification and remaining scope

The [standard-library producer](../../frontier/cover-geometry/first11_axis_mixed_gap.py)
writes [exact results](../../frontier/cover-geometry/first11_axis_mixed_gap.json).
It reconstructs the complete PA hinges from full auxiliary means and
finite low-product corrections, rather than truncating their tails.
Its nine literal arithmetic fixtures retain the old joint Haar
restriction, actual first-eleven cylinder unions, fixed slots, and the
complete absent-slot weights. They include a fully forbidden fibre and
a mixed cylinder that contributes occupancy but no overload.

All182 explicit checks pass with Python optimizations enabled, including
the numerical mixed-inventory cap and saving on all nine fixtures. The
ordinary comparison and loss arguments above establish the universal
quantifiers in AM1; the fixtures check the arithmetic and definitions,
and do not substitute for those arguments. No Lean was added or run.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/first11_axis_mixed_gap.py
```

The numerical-label assumption in AM1 remains substantive. There is no
universal estimate here for arbitrary first-eleven multiplicities, no
replacement of the common law by separate optimal query laws, and no
reduction from arbitrary prime support to this fixed Q. The unrestricted
Erdos #7 goal remains open.

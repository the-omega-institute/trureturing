[Index](../marked_head_profile.md) · [Previous](18-actual-bb-kernels-with-fixed-old-second-moment-need-not-be-uniformly-continuous.md) · [Next](20-genuine-current-kernels-and-positive-charge.md)

<a id="1-same-law-inputs-and-definitions"></a>
### 1. Same-law inputs and definitions

Fix an arbitrary finite family of distinct odd moduli supported on
3,5,7,11,13,17,19, with at most one actual forbidden class per modulus.
All residues, missing classes and finite exponent heights are arbitrary.
Work on its full product residue space, enlarged by harmless unused
coordinates if necessary. A complete test on an old period Q is

    A(x)=sum_(d|Q) 1_{x=a_d mod d},

with an independently chosen test residue at each original divisor,
including the unit divisor. Test residues need not be forbidden
residues. Deleting a forbidden constraint does not delete its test
label. At a current prime p, different p-exponent blocks of a complete
test may use different old test layouts.

Let nu13 be the actual supported law supplied by PP1--PP5: start with
the uniform actual357 survivor law, apply the pure-survivor AP kernels
at thresholds T11=4,T13=6, then condition once on all actual survivors.
The exact certificate `arbitrary_head_profile_certificate.json` gives

    rho13 >=171474522380088889/498009616542900000>0,
    dnu13/dHaar <=D=13530827317392000000/171474522380088889,
    sup_A E_nu13 A^2 <=J=42035473165849976389/171474522380088889.

These are three observations of the same law. The separate PP6
full-Haar T4 step at17 is not used here. In this proof the next steps
are pure-survivor AP17/8 and AP19/8, with no conditioning between them.

At a current prime p, let P be the actual pure-power survivor set,
lambda its Haar mass, and m=Haar restricted to P divided by lambda.
At most one pure forbidden class occurs at each positive depth, so

    lambda >=1-sum_(e>=1)p^-e=(p-2)/(p-1)=s_* >0.

The finite-height bound is in fact strict. For a mixed forbidden mask
B_x in the current fibre, set alpha(x)=m(B_x). Put

    delta=7/(p-2), C=1/(1-delta),
    a(alpha)=1/(1-min(alpha,delta)),
    b(alpha)=C(1-delta/alpha)_+, with b(0)=0.

The normalized physical kernel has m-density
`a(alpha) 1_(B_x^c)+b(alpha) 1_(B_x)`. Its killed kernel retains only
the first summand. Physical kernels exist on every old history,
including alpha=1; killed kernels are subprobability kernels.
Their conditional full-Haar density cap is c=C/s_*.

The exact constants are

| p | delta | C | s_* | c | L_p=max(C^2,C/delta) |
|---|---|---|---|---|---|
|17|7/15|15/8|15/16|2|225/56|
|19|7/17|17/10|17/18|9/5|289/70|

<a id="2-localized-complete-test-energy"></a>
### 2. Localized complete-test energy

For a prime q and nonnegative integer a define

    Phi_q(a)=(a+1)^2+2(a+1)/(q-1)+(q+1)/(q-1)^2.

If nu<=D Haar on an old product space, then, for every complete old
test A and cylinder C(r),

    integral_(C(r)) A^2 dnu
      <=D/r product_(q old) Phi_q(v_q(r)).               (WT1)

Indeed, expand A^2 over two original test labels. Their intersection
with C(r) is empty or a cylinder of modulus lcm(r,d,e). At each old
prime, enlarge the finite pair of exponents to all nonnegative ones:

    sum_(i,j>=0) q^-max(a,i,j)=q^-a Phi_q(a).

The terms through max(i,j)=a contribute (a+1)^2q^-a; the remaining
terms contribute sum_(j>a)(2j+1)q^-j. Summing this geometric tail gives
the displayed identity. Product factorization proves WT1, independently
of test residue compatibility.

The fully summed coefficient and its finite part are

    Sigma_q=sum_(a>=0)q^-a Phi_q(a)
           =q(q^2+4q+1)/(q-1)^3,
    Sigma_(q,b)=sum_(a=0)^b q^-a Phi_q(a).              (WT2)

All sums in the estimates below use this full infinite value; no
truncated probability distribution is normalized.

<a id="3-mixed-mask-and-pure-base-stability"></a>
### 3. Mixed-mask and pure-base stability

The functions a and b are globally Lipschitz with constants C^2 and
C/delta respectively. Below the clipping point a'=1/(1-alpha)^2;
above it a is constant. Below the clipping point b=0; above it
b'=C delta/alpha^2. Continuity at delta and the explicit endpoint
values give the bounds on the closed unit interval.

First fix one pure base m and nested mixed masks B0 subset B. Put
E=B\B0. On the common good and common bad regions the kernel
coefficient changes by at most L_p m(E). On E, both physical
coefficients lie in [0,C], so the change is at most C; the killed
version satisfies the same bound. Thus, for either kernel,

    |k_B-k_B0| <=C 1_E+L_p m(E).                        (WT3)

Suppose E is contained in a union of actual mixed cylinders indexed
by (r,e), namely C_old(r) times C_current(p^e). Conversion from m to
Haar in WT3 is essential: the point term costs C/lambda and the
average term costs L_p/lambda^2. Expand a full test L and use WT1,
first with a current cylinder and then with the whole current space.
For a common old law nu<=D Haar this yields

    integral L^2 d|Q_B-Q_B0|
      <=sum_(r,e) [D/r product_(q old)Phi_q(v_q(r))] p^-e
          *[(C/s_*)Phi_p(e)+(L_p/s_*^2)Phi_p(0)].       (WT-mixed)

For the average term, m(E_x)<=lambda^-1 sum_(r,e)
1_(C_old(r))(x)p^-e. Integrating a current test pair then contributes
Phi_p(0), proving the second coefficient without optimizing a
different test on each old row. Both physical and killed versions
hold for masks depending on the entire earlier history.

Next fix the raw mixed mask in the full current ambient space and
compare nested pure bases P subset P0. Write lambda=Haar(P),
lambda0=Haar(P0), and kappa=lambda0-lambda. The total variation distance
(supremum over events, half the L1 distance) between their normalized
uniform laws is kappa/lambda0, so |alpha-alpha0|<=kappa/lambda0.
On P0\P the Haar density difference is at most C/s_*. On P the
coefficient and normalization changes give

    |f(alpha)/lambda-f(alpha0)/lambda0|
      <=L_p kappa/(lambda lambda0)+C kappa/(lambda lambda0)
      <=(L_p+C)kappa/s_*^2,

for f=a or b. The same estimates hold after killing because the raw
mixed mask remains fixed. If P0\P is covered by pure cylinders at
depths e in E, and every complete old test has square expectation at
most J, then

    integral L^2 d|Q_P-Q_P0|
      <=J [(C/s_*)sum_(e in E)p^-e Phi_p(e)
         +((L_p+C)/s_*^2)Phi_p(0)sum_(e in E)p^-e].    (WT-pure)

To justify use of J rather than D, expand each current test pair.
Its old factors A_i,A_j obey E A_i A_j<=J by Cauchy--Schwarz, even
though their original residues differ. For the changed pure region
the current pair sum is p^-e Phi_p(e); for the normalization term it
is Phi_p(0). No future survivor normalization is assumed.

<a id="4-an-explicit-reference-and-fully-summed-tails"></a>
### 4. An explicit reference and fully summed tails

At17 and19 keep actual pure constraints of depth e<=8. Keep actual
mixed constraints only when the current depth is e<=8 and every old
cofactor exponent is at most20. Directly delete the other forbidden
constraints in the reference, retaining the full original ambient
space and every original test label. First delete mixed tails on the
fixed actual pure base; then delete pure tails with the remaining raw
mixed mask fixed. WT-mixed and WT-pure bound these two changes.

If a retained actual pure class modulo p exists, one may instead
place the removed forbidden classes redundantly inside that class
while retaining every original forbidden-modulus label. This optional
construction must use an actual retained class. If modulus p is
absent, use direct deletion; no new pure class is invented.

For old prime set S, box b=20 and current depth h=8, write

    U_S=product_(q in S) Sigma_q,
    V_S=product_(q in S) Sigma_(q,20),
    Z_S=product_(q in S) Phi_q(0),
    R_S=U_S-V_S,
    H_S=V_S-Z_S,
    t0_p=1/[(p-1)p^8],
    tPhi_p=Sigma_p-Sigma_(p,8),
    Theta_p=(C/s_*)[Sigma_p-Phi_p(0)]
              +(L_p/s_*^2)Phi_p(0)/(p-1).

The unit old cofactor has weight Z_S, not1. The discarded mixed
indices split disjointly into old cofactors outside the box (all
positive current depths) and old cofactors inside the box but current
depth above8. The latter exclude the unit cofactor. Consequently

    old_error   =D R_S Theta_p,
    mixed_error =D H_S [(C/s_*)tPhi_p
                         +(L_p/s_*^2)Phi_p(0)t0_p],
    pure_error  =J [(C/s_*)tPhi_p
                         +((L_p+C)/s_*^2)Phi_p(0)t0_p],
    epsilon_p=old_error+mixed_error+pure_error.          (WT4)

At17 use S={3,5,7,11,13} and the D,J of section1. At19 use
S={3,5,7,11,13,17} and the unconditioned physical17 bounds

    D17<=2D,
    J17<=(89/64)J.

The second follows by keeping the zero-current-exponent test pair at
coefficient1 and applying the cap2 to every other pair:
1+2(Phi17(0)-1)=89/64. These same bounds apply to either reference
or actual physical17 law. The killed17 measure is dominated by its
physical17 law, so it also obeys the required D,J bounds.

The exact all-depth coefficients are Theta17=6613/7168 and
Theta19=2869/3780. Exact rational recomputation gives the following
display decimals (the JSON fractions, not the decimals, are used):

| step | old cofactor error | mixed depth error | pure depth error | epsilon |
|---|---:|---:|---:|---:|
|17|0.000153431002431096|0.000031881166792166|0.000000468509674939|0.000185780678898201|
|19|0.000375105420972540|0.000031542144531736|0.000000213990105974|0.000406861555610249|

The errors are uniform in the original finite heights and arbitrary
forbidden/test residues. Missing forbidden classes only reduce the
nonnegative sums.

<a id="5-propagation-assigned-charges-and-the-w483-criterion"></a>
### 5. Propagation, assigned charges, and the W483 criterion

For two old finite positive measures define

    Delta2(sigma,tau)=sup_(complete old A) integral A^2 d|sigma-tau|.

For a common current kernel K of mass at most1 and full-Haar prefix
cap c p^-e, expansion over the current test exponents gives

    Delta2(sigma K,tau K)
      <=[1+c(Phi_p(0)-1)] Delta2(sigma,tau).             (WT5)

Indeed, total variation is dominated by |sigma-tau|K. The zero-zero
pair costs at most Delta2 because the kernel has mass at most1.
Every other pair costs at most c p^-max(i,j) Delta2 by
Cauchy--Schwarz under |sigma-tau|. Summing those positive pairs
gives c(Phi_p(0)-1). This proves WT5 for physical or killed kernels
and history-dependent masks. At19 its factor is59/45.

Let mu17=nu13 K17 be the actual physical17 law, eta17=nu13 K17^-
its killed law, and use a superscript0 for the corresponding reference.
Compare actual and reference17 kernels under the same nu13. Then
compare the19 kernels under the actual mu17, and separately under
eta17. The latter is dominated by mu17, so WT4 is valid there too.
Propagate the old-law difference through a common reference19 kernel.
Thus both the final physical and final killed weighted differences
are at most

    epsilon_square=(59/45)epsilon17+epsilon19.           (WT6)

For clarity, b17 and b19 below denote actual assigned mixed-event
probabilities, not arbitrary scalar upper bounds. With the physical
prefix laws they are

    b17=1-(nu13 K17^-)(1),
    b19=1-(mu17 K19^-)(1),
    B=b17+b19.

Since every complete test contains the unit, WT4 also bounds plain
L1 error. Hence |b17-b17^0|<=epsilon17. For b19, split the comparison
by first changing the19 kernel under actual mu17 (cost epsilon19),
then changing mu17 to mu17^0 under the same reference killed19
kernel (cost epsilon17 by L1 contraction). Therefore

    |B-B0|<=2epsilon17+epsilon19.                        (WT7)

These assigned charges are taken under physical prefix laws; later
normalized kernels preserve their expectations. Their sum bounds
the actual final bad-event union, even though the last killed law
also removes the earlier bad event.

At W=483 the exact arithmetic in the certificate gives

    epsilon_square+483(2epsilon17+epsilon19)
      =0.3766287078433556... <377/1000.                 (WT8)

Consequently it suffices to establish, for the reference and every
complete original test L,

    E_ref[L^2-1]+483 B0 <=483-377/1000.                  (WT9)

The physical laws are probabilities, so subtraction of the constant1
introduces no extra error. Put eta=377/1000 minus the exact WT8
allowance; the certificate proves eta>0. WT6--WT8 imply for the actual
full masks

    E_actual[L^2-1]+483 B <=483-eta<483.                (WT10)

This implies the full-test criterion used in SH28. Since L^2-1>=0,
the strict margin already gives B<=1-eta/483<1, without an additional
positivity premise. The final actual survivor mass rho is at least
1-B>0. Discarding the bad union and conditioning once gives

    E_survivor L^2
      =1+rho^-1 integral_survivors(L^2-1)dmu
      <=1+rho^-1 E_actual(L^2-1)<=484.

Thus a certificate of WT9 would supply actual17/19 continuation with
positive survival and supported complete-square bound484. WT9 has
not been established by this tail calculation; unrestricted Erdős #7
also requires the remaining prime continuation or another full proof.

<a id="6-exact-computational-scope"></a>
### 6. Exact computational scope

Only the17/19 forbidden masks were reduced above. The incoming nu13
is the full actual AP(4,6) law, and the complete test inventory remains
untruncated. True finite joint marginals of nu13 can be inputs to a
reference calculation, but this proof supplies neither their exact
finite computation nor a continuity bound for truncating that AP law.
The existing finite-core approximation for the different AO
full-Haar11/13 law cannot be substituted for it.

If a further computation truncates the test exponents to a vector h,
that is a separate approximation. Through unconditioned AP17/19
the full physical Haar density is at most(18/5)D. Writing L_h for the
sum of the retained original test indicators, direct pair expansion
gives the optional uniform bound

    E(L^2-L_h^2) <=(18D/5)
      *[product_p sum_(a>=0)(2a+1)p^-a
           -product_p sum_(a=0)^(h_p)(2a+1)p^-a],       (WT11)

over p in{3,5,7,11,13,17,19}. A discarded pair has at least one
exponent exceeding h, so the product difference counts all such
pairs using their nonnegative Haar intersection bounds. WT11 is not
included in the377/1000 allowance and must be paid separately.

The exact verifier pins the upstream AP source certificate by SHA-256,
checks all rational factors and tails, and compares the entire saved
JSON to recomputation. Its default mode only validates; `--write`
explicitly regenerates the certificate. Duplicate JSON keys and
changed numeric fields are rejected, including under `python3 -I -O`.
Finite coefficient and prefix fixtures check the implementations of
the formulas; they are not substitutes for the arbitrary-height proofs
above. No canonical formal status is asserted by these files.

Reproduce the [weighted-kernel tail certificate](../certificates/weighted_kernel_tails_certificate.json)
with the [standalone verifier](../verify_weighted_kernel_tails.py):

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_weighted_kernel_tails.py
```

<a id="a-stronger-generic-profile-from-actual-pure-exclusions"></a>
## A stronger generic profile from actual pure exclusions

For the same actual supported AP(4,6) law considered in PP1--PP5,
the complete-test square bound improves to

    Gamma13 <=8416748733302130673/43949004608153173
             =191.511703355864... .                       (PR1)

The previous bound was245.141217379656... . The law and its thresholds
are unchanged. Every original finite exponent height, arbitrary actual
residue and missing class is included. The proof uses twelve cases
according to actual low pure exclusions, then takes a single common
profile. No forbidden residue is changed or added and no test label
is removed. This is an ordinary proof with exact arithmetic, not an
unrestricted Erdős7 solution or an end-to-end Lean proof.

<a id="actual-source-law-and-twelve-exhaustive-cases"></a>
### Actual source law and twelve exhaustive cases

Let S be the full actual survivor set for an arbitrary finite family
of distinct nonunit moduli supported on3,5,7. Its uniform probability
nu is the source law. The same-law observations CM8, BS10 and SD1--SD6
give

    s:=Haar(S)>=53/432,
    sup_L E_nu L^2<=G=3849/106,
    sup_L E_nu(L-1)<=R=1649/360.                          (PR2)

Here L is a complete original-divisor test with its own independently
chosen residue at every divisor, including the unit. The R bound is
the stronger sum of cylinder maxima, so it bounds every such test.

Partition the actual family into three ternary cases:

* A: the actual modulus3 class is absent;
* B: the actual modulus3 class is present, while the actual modulus9
  class is absent or is contained in that forbidden modulus3 root;
* C: the actual modulus3 and9 classes are present and the modulus9
  class lies outside the forbidden modulus3 root.

Cross these with presence or absence of the actual modulus5 class,
and presence or absence of the actual modulus7 class. These twelve
cases are disjoint and exhaustive, including all small finite heights.

The actual pure-power survivor densities have lower bounds

| ternary case | pure3 lower l3 | same uniform35 R35 upper | same uniform357 square upper |
|---|---:|---:|---:|
|A|5/6|17/12|5273/258|
|B|11/18|47/24|14543/438|
|C|1/2|15/7|3849/106|

For A, only ternary exponents at least2 can remove pure mass, whose
sum is1/6. For B the root exclusion costs1/3, an ineffective9 class
adds no mass, and exponents at least3 cost at most1/18. For C the
full positive-exponent geometric sum costs at most1/2. The pair R35
bounds and the A/B square bounds are exactly the same-uniform-law
fallback cases of P11--P12, N9 and SD6; no balanced or PG1 law is used.

The quinary lower l5 is3/4 when modulus5 is present and19/20 when it
is absent. The septenary lower l7 is5/6 when modulus7 is present and
41/42 when absent. These again follow from the full remaining pure
geometric sums, not a finite truncation.

<a id="stronger-density-in-missing-class-cases"></a>
### Stronger density in missing-class cases

Let s35 be the actual uniform ambient survivor density on3,5, and let
x,z be its actual pure3 and pure5 survivor densities. All mixed35
classes together have ambient density at most

    sum_(a,b>=1)3^-a5^-b=1/8,

so s35>=l3*l5-1/8=:s35_*>0. The uniform actual35 law has the R35
bound of the table. At7, the actual pure survivors have mass at least
l7; every new mixed class d7^e costs at most its old cylinder mass
times7^-e. Thus

    s>=s35(l7-R35/6)
      >=s35_*(l7-R35_upper/6).                          (PR3)

The bracket is positive in every case. This is the ambient-density
version of the same-law recurrence in N9; no conditioning on individual
old cells is involved.

A second useful estimate is the actual linear numerator bound proved
in CM2, including its missing-class fallback paragraphs:

    (s35-s35*R35/5)/(xz)>=53/135.

In particular, if modulus7 is absent, adding the extra pure7 mass
1/7 relative to5/6 gives

    s >=(5s35-s35*R35)/6+s35/7
      >=(53/162)l3*l5+s35_*/7.                         (PR4)

With modulus7 present the same formula holds without the final
s35_*/7 term. This conclusion uses CM2's linear numerator itself;
it does not infer it from the weaker final scalar CM8 statement.
In case C with modulus5 present and modulus7 absent, PR4 is

    s>=53/432+1/28=479/3024.

For completeness the verifier also compares CM8, the bound
(53/135)l3*l5*l7 from CM1 under the actual pure-survivor product,
and the ordinary reciprocal-sum bound
`s>=-3/16+sum_(missing p in{3,5,7})1/p`.
Taking the strongest of these valid bounds and PR3--PR4 gives:

| ternary case | 5 absent,7 absent | 5 absent,7 present | 5 present,7 absent | 5 present,7 present |
|---|---:|---:|---:|---:|
|A|373/756|43/108|373/1008|43/144|
|B|5371/18144|2993/12960|655/3024|73/432|
|C|13/60|1/6|479/3024|53/432|

Denote the bound in the relevant cell by s_* and put D=1/s_*.
All bounds apply to the same original uniform357 law nu.

<a id="complete-test-comparison-inside-the-retained-pure-geometry"></a>
### Complete-test comparison inside the retained pure geometry

Retain only the following exclusions when defining a reference
product set P. These are actual exclusions, used as geometric
information about S subset P; they do not alter the actual family.

In case A, impose no reference ternary exclusion. In B retain the
actual modulus3 exclusion. In C retain the actual modulus3 and9
exclusions. At5 and7 retain the actual first-root class when it exists
and impose no reference exclusion when it is absent. The reference
coordinate Haar masses are therefore

    u3=1 in A, 2/3 in B, 5/9 in C;
    u5=1 if absent, 4/5 if present;
    u7=1 if absent, 6/7 if present.                      (PR5)

In C the extra modulus9 class lies in one of the two surviving3 roots,
so removing it costs exactly1/9; the other surviving3 root remains
entirely available. For every coordinate p and exponent e>=1, every
test cylinder has conditional reference probability at most
`c_p p^-e`, where c_p=1/u_p and c_p<=p. The unit prefix has probability1.

Let independent nonnegative integer variables K_p satisfy

    Pr(K_p>=e)=c_p p^-e, e>=1,
    V=product_(p=3,5,7)(1+K_p).

Then for every complete original test and every increasing convex
function f,

    E_(Haar conditioned on P) f(L)<=E f(V).              (PR6)

The comparison is the capped version of the report's comonotone
comparison following SH4. To see why every original label is retained,
fix the other coordinates and view the test as a nonnegative weighted
sum of current-coordinate prefix indicators, one per original label.
An increasing convex cost is maximized when indicators of given
probabilities are nested. Enlarging each probability to its cap can
only increase the cost. Use a common nested indicator for each exponent,
then repeat at the next coordinate. The resulting full labelled sum
is the product of the three prefix counts. For finite original heights
these counts are truncated; extending each count to K_p adds only
nonnegative terms. This argument neither uses row-dependent test choices
under nu nor moves any actual forbidden residue.

For t>=1, apply PR6 to the nonnegative hinge f(v)=(v-t)_+ and use
S subset P:

    H_nu(t):=sup_L E_nu(L-t)_+
      <=D*(u3*u5*u7)*E(V-t)_+.                         (PR7)

This differs from encoding an old scalar count: the actual root
exclusions give a smaller integration domain before the comparison.
Missing roots are explicitly kept as u_p=1.

The exact comparator probabilities and mean are

    Pr(1+K_p=1)=1-c_p/p,
    Pr(1+K_p=v)=c_p(p-1)p^-v, v>=2,
    E V=product_p(1+c_p/(p-1)).                         (PR8)

For an integer h>=1,

    E(V-h)_+=E V-h+sum_(n<h)(h-n)Pr(V=n).              (PR9)

Only finitely many product probabilities enter the correction; its
omitted tail is supplied by the full mean, with no renormalization.

The existing integer majorants used in PP3 further give, in each branch
with its own same-law square bound G_branch,

    H_nu(1)<=R,
    H_nu(2)<=(G_branch-1+17R)/30,
    H_nu(3)<=(G_branch-1+2R)/15.                        (PR10)

These follow pointwise for positive integer L from
`(L-2)_+<=(L^2+17L-18)/30` and
`(L-3)_+<=(L^2+2L-3)/15`. Take the minimum of PR7 and the applicable
PR10 bound, then the maximum over all twelve branches. The exact
verifier checks that case C with5 and7 present dominates all twelve
branches at every retained integer h=1,...,12.

The common first six hinge bounds are

    h1=1649/360,
    h2=2159489/572400,
    h3=6759/2597,
    h4=776841/454475,
    h5=20500987/15906625,
    h6=1501750547/1670195625.                           (PR11)

The JSON retains h7 through h12 too. For noninteger t between retained
integers, the chord joining the upper values bounds the actual convex
hinge. For t<=1, use H_nu(t)<=1+R-t. No global optimality of these
profiles is asserted.

<a id="the-unchanged-ap46-continuation"></a>
### The unchanged AP(4,6) continuation

Start with the original uniform357 law nu. Apply the same actual
pure-survivor AP kernels as in PP4, with thresholds T11=4 and T13=6,
caps c11=5/3,c13=2, and no intermediate conditioning. In particular
the law has not been chosen differently for different branches.

The existing AP full-tail comparison with PR11 gives

    b11<=h4/6,
    b13<=[(28/33)h6+(100/363)h3+(19300/483153)h2
                 +(887/322102)R+1/966306]/6.

The second formula retains the complete auxiliary11 multiplier tail.
It is PP4's identical expression with the stronger same-source profile.
Consequently final survivor mass is at least

    rho13=1-b11_bound-b13_bound
         =43949004608153173/99601923308580000>0.        (PR12)

The unchanged unconditioned physical square bound is324599/3816, and
its Haar density bound is1440/53. Deleting the actual bad union saves
at least its mass from every test square because L>=1. One final
conditioning therefore gives

    Gamma13<=1+[(324599/3816)-1]/rho13
            =8416748733302130673/43949004608153173,
    dnu13/dHaar<= (1440/53)/rho13
            =2706165463478400000/43949004608153173.    (PR13)

These are stronger observations of the same full actual AP13 law.
They do not establish a17/19 joint correlation criterion or later-prime
continuation. Further restrictions on actual pure powers may improve
the profile in additional cases, but arbitrary higher pure classes can
also be redundant inside the retained exclusions; no uniform extra
deletion is assumed.

<a id="existing-consumers-of-the-stronger-same-law-observations"></a>
### Existing consumers of the stronger same-law observations

The physical fourth-moment bound in PP5 is unchanged:
Kphysical13=114643048312/536625. Substituting PR12 in the existing
unit-floor conditioning argument gives

    Gamma4_13<=1+(Kphysical13-1)/rho13.                 (PR14)

The exact resulting fraction is in the new certificate. This is a
stronger bound on the same law; it does not select a different kernel.

The separate PP6 full-Haar T4 step at17, with delta=1/2, also admits
the same direct substitution. Put g=PR1's square bound. Its assigned
charge is at most g/256, its survival is at least1-g/256>0, and its
supported complete square is at most

    1+[(89/64)g-1]/(1-g/256)
      =1054.2479524075604... .                          (PR15)

This17 kernel is distinct from the pure-base AP17/8 kernel below;
its conditioned output is not substituted into the WT17/19 chain.

Finally, the previously proved WT4 bounds for the pure-base AP17/8
and AP19/8 mask truncations are linear in their incoming D,J. Let
Dold,Jold be PP's previous bounds on the same actual supported13
law, and Dnew,Jnew be PR13,PR1. In each old WT step, multiply the
old-cofactor and mixed-current errors by Dnew/Dold, and the pure-current
error by Jnew/Jold. The common unconditioned17 multipliers2 and89/64
remain unchanged. Thus the exact rescaled errors are

    epsilon17=0.0001449714082004838...,
    epsilon19=0.0003174881146077773... .

The old weighted propagation factor59/45 and charge bound
2epsilon17+epsilon19 are unchanged. At W=483 the total allowance is

    (59/45)epsilon17+epsilon19
       +483(2epsilon17+epsilon19)
      =0.2938967014159167... <294/1000.                 (PR16)

Accordingly the sufficient reference criterion becomes
`E_ref[L^2-1]+483 B_ref<=483-.294` for every complete original test.
The remaining strictly positive arithmetic slack gives B_actual<1
and the same supported-square bound484 if that reference criterion
is proved. It has not been proved here. Only the17/19 forbidden masks
are truncated; the incoming AP13 law and all original test labels
remain full, exactly as in WT1--WT11. The earlier WT certificate is
an immutable pinned input, not overwritten with new bounds.

The adjacent verifier pins the five source certificates by SHA-256,
reconstructs all twelve branches and complete geometric means, and
checks the independent closed13 charge formula. Default mode compares
the entire saved JSON; `--write` explicitly regenerates it. Its finite
one-coordinate fixtures test the prefix comparison implementation.
These numerical checks do not replace the ordinary arbitrary-height
argument above or claim a new Lean declaration.

The [pure-root profile verifier](../verify_pure_root_profile.py) reconstructs the
[exact certificate](../certificates/pure_root_profile_certificate.json) with the same full-law
source certificates. It can be run from any working directory:

```sh
python3 -I -O /absolute/path/to/verify_pure_root_profile.py
```

<a id="exact-equality-in-the-killed-unit-floor-for-genuine-bb17-and-bb19"></a>
## Exact equality in the killed unit floor for genuine BB17 and BB19

For each `p in {17,19}`, there is a uniform complete actual357 survivor law, an actual pure-base BBMST step with `delta=7/(p-2)`, positive assigned bad mass, and one complete original test `L` such that

`integral_bad L^2 dP = P(bad) > 0`,

equivalently `integral_bad (L^2-1) dP=0`. Thus no universal testwise replacement of the killed unit floor by `(1+epsilon) P(bad)`, for any fixed `epsilon>0`, follows from actual357 uniformity and the genuine current kernel. This statement concerns a complete fixed test; it does not assert that this test maximizes the current square supremum.

<a id="the-full-original-rectangle-and-actual-old-law"></a>
### The full original rectangle and actual old law

Put `Q=315=3^2*5*7`, and let

`D=(1,3,5,7,9,15,21,35,45,63,105,315)`.

At every original nonunit modulus `d|315`, put the forbidden class `0 mod d`. The eleven original classes are retained, including redundant ones. Their complete actual survivor set is

`S={x mod315:gcd(x,315)=1}`,

which has144 points. Let `nu` be uniform on `S`. It is the product of the uniform laws on the six units modulo9, four nonzero residues modulo5, and six nonzero residues modulo7.

At the current prime put the pure forbidden class `0 mod p`. List the eleven nonunit divisors increasingly as `d_1,...,d_11`. At the distinct original mixed modulus `d_i p`, put the CRT class

`x=1 mod d_i`, `y=i mod p`.

There are exactly23 original forbidden labels: eleven old, one pure-current, and eleven mixed. The period is exactly `315p`. Every nonunit divisor of this period has its one original forbidden label. The certificate stores all23 literal modulus/residue pairs for each prime.

The normalized actual pure-current survivor base `m` is uniform on `y=1,...,p-1`. The mixed roots1 through11 are distinct. Define the independent complete old layouts

`C(x)=sum_(d|315) 1_(x=1 mod d)`,

`A(x)=sum_(d|315) 1_(x=2 mod d)`.

Their residues differ already modulo3,5,7. No identification of the test and forbidden layouts is used.

The actual row union has exact base mass

`alpha(x)=(C(x)-1)/(p-1)`.

This is an exact union identity because every active original mixed label uses a distinct current root. The unit cofactor is absent exactly once.

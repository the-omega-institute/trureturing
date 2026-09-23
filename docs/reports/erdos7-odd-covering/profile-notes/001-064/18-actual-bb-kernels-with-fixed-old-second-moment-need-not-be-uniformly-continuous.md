[Index](../../marked_head_profile.md) · [Previous](17-higher-moments-retain-the-full-old-inventory-in-a-law-changing-perturbation.md) · [Next](19-1-same-law-inputs-and-definitions.md)

<a id="actual-bb-kernels-with-fixed-old-second-moment-need-not-be-uniformly-continuous"></a>
## Actual BB kernels with fixed old second moment need not be uniformly continuous

The obstruction in (AM9) persists when both current kernels are actual
BBMST kernels for their respective forbidden masks. Keep its old family,
old probability \(\nu_N\), and put \(n=N+1\),

\[
 w_N=\nu_N(\{0\})
     =u_N+\frac{1-u_N}{2\cdot3^{N-1}},\qquad
 w_N\to0,\qquad w_Nn^2>1.
\]

Add the pure forbidden class zero modulo17 and every mixed original
class zero modulo \(3^j17\), \(1\le j\le N\). All mixed classes
are redundant inside the pure class. The actual pure-survivor BB kernel
is therefore uniform on roots1 through16 in every old row. In a second
family change only the original class labelled \(3^N17\) to the CRT
residue \((0\bmod3^N,3\bmod17)\). Only old row zero acquires a mixed
bad root, of pure-base mass \(1/16<7/15\). At distortion parameter
\(7/15\), the actual BB kernel in that row becomes uniform on the other
15 roots. Every other row is unchanged.

Both actual kernels preserve the same old law, charge zero bad mass and
have complete survivor mass one. The same two laws also arise from full-Haar
T4 at delta=1/2, since the raw bad masses are 1/17 and 2/17. Their pure-base density caps are at most
\(16/15<15/8\). If their joint probabilities are \(P_N,P'_N\),

\[
 \|P'_N-P_N\|_1=w_N/8\longrightarrow0.
\]

Retain every original divisor test, including the unit. Write a complete
load as \(L=A+Z\), where \(A\) is its old-only load and \(Z\) is
its positive17 block. The old projections of the latter form another
complete old load \(C\). By (AM9) and Cauchy--Schwarz,
\(E A^2,E C^2,E AC\le5\). Uniform current roots give
\(E_yZ\le C/16\), \(E_yZ^2\le C^2/16\); hence
\(E_{P_N}L^2\le95/16\). Coherent zero old tests with every current
test at root2 attain this bound.

For an arbitrary fixed layout set \(a=A(0)\), \(z_r=Z(0,r)\).
Then \(a\le n\), \(\sum_{r\ne3,\,1\le r\le16}z_r\le n\),
and the exact change is

\[
 \frac{w_N}{240}
 \left(2a\sum_{r\ne3}z_r+\sum_{r\ne3}z_r^2\right)
 -\frac{w_N}{16}(2az_3+z_3^2)
 \le\frac{w_Nn^2}{80}.
\]

The same coherent zero/root2 layout attains this inequality and the
baseline maximum simultaneously. Therefore the complete maxima are

\[
 \Gamma_2(P_N)=95/16,\qquad
 \Gamma_2(P'_N)=95/16+w_Nn^2/80,
 \qquad \Gamma_2(P'_N)-\Gamma_2(P_N)>1/80.             \tag{AC1}
\]

The ratio of this gap to the joint L1 distance is exactly \(n^2/10\).
Thus an unchanged complete old second moment, a common current density
cap and unchanged charge/normalizer do not imply a height-uniform L1
continuity modulus. The old spike law is still not asserted to be
BBMST-generated. Its unbounded Haar density is precisely the premise
excluded by the actual-law construction below. The finite-core verifier
checks the exact formulas at eight finite heights; the ordered-label
argument above proves the full maxima and the unbounded conclusion.

<a id="uniform-cylinder-and-fourth-moment-bounds-for-arbitrary-old-families-through13"></a>
## Uniform cylinder and fourth-moment bounds for arbitrary old families through13

This statement covers arbitrary forbidden residues and arbitrary finite
heights on the prime support {3,5,7,11,13}. It specifies one admissible
law for each such family. It does not claim the bounds for every
supported law, an arbitrary low-square spike, or every BBMST schedule.

All original labels are retained. Start with the full physical357
period Q, including heights needed by moduli with later primes. Let
S be its actual complete survivor set and take mu=Unif(S). At11 and13
use the T4 normalized BBMST kernels on the FULL uniform current fibre,
with delta=1/2 at both steps. Their bad masks include both pure and
mixed classes assigned to that step. Do not condition between steps.
Finally condition once on avoiding both new forbidden unions. Call the
physical law xi and the final supported law nu.

<a id="existing-source-facts-and-a-positive-actual-normalizer"></a>
### Existing source facts and a positive actual normalizer

Problems/erdos-7-odd-covering-systems.md supplies the following ordinary
mathematical facts with exact certificates:

* CM8: every such finite357 family has Haar survivor density s>53/432.
* SD1--SD6: the SAME uniform complete-survivor law has complete-test
  square supremum at most G=3849/106, including all missing-class and
  small-height branches.
* T1--T5: each normalized delta=1/2 full-Haar BBMST step has pointwise
  Haar density at most2, square multiplier
  1+2*(3p-1)/(p-1)^2, and actual assigned violation probability at most
  the incoming physical square bound divided by(p-1)^2. The old
  marginal is preserved on every history, including all-bad fibres.

Consequently D0=432/53 is a valid initial Haar density bound. The
actual sequence has

    J11=(41/25)*G,
    b11<=G/100=3849/10600,
    b13<=J11/144=52603/127200,
    J13=(55/36)*J11=578633/6360.

The retained actual probability is therefore at least

    rho*=1-b11_bound-b13_bound=28409/127200>0.          (AO1)

This is a proved lower bound for the specified chain, not an assumed
normalizer. Later normalized kernels preserve the earlier violation
probability, so a union bound applies to the two violations under the
one final physical law. Conditioning is well-defined. Since every
complete test load L includes the unit label and L^2>=1,

    Gamma2(nu)<=1+(J13-1)/rho*
              =11473869/28409 <403.882.                (AO2)

The physical law xi is bounded by Dpre=4D0=1728/53 times the entire
old Haar law. The final supported law is therefore bounded by

    D=Dpre/rho*=4147200/28409 <145.982                 (AO3)

times that SAME Haar law. Thus every original cylinder satisfies
nu(C(a,d))<=min(1,D/d). This statement uses the full original d, not
its projection to a fixed low period.

The T4 charge bound used here belongs to the full-Haar kernel. It
must not be combined with AP's different pure-survivor caps5/3 and
2 while retaining the same charge denominator. Those are a
different actual chain. No PG1-specific hypothesis is used here.

<a id="the-haar-fourth-moment-and-the-original-label-transfer"></a>
### The Haar fourth moment and the original-label transfer

For a prime p define

    F4(p)=sum_(j>=0)[(j+1)^4-j^4]*p^(-j)
         =p*(p^3+11p^2+11p+1)/(p-1)^4.

At any finite height, expand an original complete load to its fourth
power as ordered quadruples of original divisor labels. For each
prime, compatible prefixes intersect with Haar probability p^(-j),
where j is their maximum depth; incompatible tuples have probability0.
There are (j+1)^4-j^4 exponent quadruples with maximum j. Summing the
caps over all tuples therefore gives product_p F4(p). Coherent nested
test residues attain the finite-height version. No labels are merged.

In particular,

    F4(3)=30, F4(5)=285/32, F4(7)=140/27,
    F4(11)=1914/625, F4(13)=2275/864,
    H4_357=16625/12,
    H4_3571113=19304285/1728.

For the initial uniform actual357 survivor law, apply the density
bound to L^4-1>=0, rather than spending density on the unit:

    E_mu L^4 =1+s^(-1)*integral_S(L^4-1) dHaar
             <=1+D0*(H4_357-1)
             =598121/53=:K0.                         (AO4)

Here the positivity and density bound for S are precisely CM8.

More generally, suppose every complete old test has fourth moment
at most K, and a normalized next-prime kernel has cylinder caps
c*p^(-e) at every full old history. Its complete new test fourth
moment is at most

    K*[1+c*(F4(p)-1)].                               (AO5)

To prove this, keep one arbitrary new test fixed and expand its
fourth power. The four current depths are e1,e2,e3,e4. If all are
zero, normalization preserves the old fourth moment. Otherwise the
current intersection is empty or one cylinder at their maximum
depth, to which the cap applies. After that bound, summing the four
old labels leaves the product A_e1*A_e2*A_e3*A_e4 of four complete
old test loads. Holder gives

    E(A_e1*A_e2*A_e3*A_e4)
       <=product_i(E A_ei^4)^(1/4)<=K.

The current residues may depend on the original old label. They
have already been bounded tuple by tuple, so this dependence causes
no old-layout identification. Counting the current exponent tuples
gives AO5. No independence of the actual sequential coordinates is
assumed.

For the specified full-Haar chain c=2 at both primes. Hence

    Kphysical13=K0*(2F4(11)-1)*(2F4(13)-1)
               =3530785420609/14310000.

Now use the actual final survival lower bound AO1 and L^4>=1 again:

    Gamma4(nu)<=1+(Kphysical13-1)/rho*
               =7061548613243/6392025
               <1104743.585.                         (AO6)

The two unit-floor savings occur at different operations: AO4 at
initial uniform-survivor conditioning and AO6 at final BBMST-chain
conditioning. Omitting the initial saving gives a valid but larger
bound. The endpoint is uniform over all finite original heights and
all forbidden old residues for this specified constructed law.

<a id="a-concrete-next-observation-full-original-label-tails"></a>
### A concrete next observation: full original-label tails

For k>=1 let

    Fk(p,h)=sum_(j=0)^h[(j+1)^k-j^k]*p^(-j),
    Hk=product_(p=3,5,7,11,13) Fk(p,infinity).

Let L_h contain exactly those original test labels whose exponent
at every p is at most h_p. Expanding the nonnegative difference of
powers and applying the SAME original-label intersection bounds gives

    E_nu(L^k-L_h^k)
       <=D*[Hk-product_p Fk(p,h_p)].                 (AO7)

In particular this supplies explicit uniformly vanishing errors for
the complete-square objective and fourth moment. It justifies keeping
finite joint residue observations while charging every omitted
original high label. It does not treat a finite enumeration as the
unrestricted theorem. The moments are evaluated under one actual law;
there is no separate law chosen for each test.

A more focused observation for the17 weighted charge retains the
energy inside an original old cylinder. If d=product p^(a_p), then

    sup_(T,b) E_nu[L_T^2*1_(C(b,d))]
      <=(D/d)*product_p[(a_p+1)^2+2(a_p+1)/(p-1)
                                      +(p+1)/(p-1)^2].  (AO8)

Indeed conditional Haar on C(b,d) fixes its a_p initial digits;
the complete-label square bound is the product of the displayed
fixed-prefix geometric moments. Multiply by Haar(C)=1/d and D.
This retains the polynomial growth in queried depth together with
its exponentially decreasing cylinder probability. Summing AO8
over any omitted old cofactor region yields a convergent explicit
bound on its contribution to E[alpha17*L_T^2]. The remaining finite
cofactor observations can retain the actual charge/test intersection,
which the scalar Gamma2 bound discarded.

These bounds remove the arbitrary-spike obstruction within this
specified family of actual admissible laws. They do not by themselves
lower the scalar17/19 continuation seed to its required range: the
square seed AO2 is still above that range, and the root's tested
Haar hinge relaxation at17 did not improve its second-moment charge
bound. The next missing estimate is on the retained finite joint
charge/test data, with AO7--AO8 paying the complete high-label tails.

<a id="source-and-validation-scope"></a>
### Source and validation scope

The report clauses CM8, SD1--SD6 and T1--T5 are ordinary source
proofs with exact arithmetic certificates; they are not asserted to
have an end-to-end Lean proof. The existing frozen declaration
SequentialKernelCylinder.selected_cylinder_bound supplies the
history-dependent selected-cylinder step. FI6 supplies the already
used ordered original-label moment expansion, and pinned Mathlib
MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg supplies Holder
instances. The BBMST source is arXiv:1811.03547, sections2 and6;
no new theorem of that paper or literature-priority claim is asserted.

The [finite-core verifier](../../verify_finite_core_approximation.py)
independently checks rational constants,
the positive two-prime normalizer, both unit-floor steps, finite
coherent-prefix Haar moments and explicit infinite tails. It does
not enumerate all forbidden families or all test layouts. AO1--AO8
are ordinary proofs; no Lean declaration is added.

<a id="uniform-finite-core-approximation-of-the-actual-supported-law-through13"></a>
## Uniform finite-core approximation of the actual supported law through13

Use exactly the AO full-Haar construction above for each arbitrary finite
forbidden family F on primes3,5,7,11,13, and denote its actual supported law
by nu_F. Its source density bound is D0=432/53, its proved final survival
lower bound is s*=28409/127200, and its final density is at most
D=4147200/28409. Its construction preserves the old marginal at11 and13
and conditions only after both steps. This subsection does not change
to the different pure-survivor construction used in (PP1).

<a id="complete-haar-moments-and-original-test-tails"></a>
### Complete Haar moments and original-test tails

Let G_p have P(G_p>=j)=p^-j. Ordered original-label tuples are bounded in
Haar measure by the cylinder at their maximum exponent in each coordinate.
Thus the complete Haar second and fourth moments are bounded by the products
of E(1+G_p)^2 and E(1+G_p)^4. The five fourth factors are

    30, 285/32, 140/27, 1914/625, 2275/864,
    H4=19304285/1728.

They include every original cofactor and every higher power. The density bound
therefore gives Gamma4(nu_F)<=D*H4=46330284000/28409. The sharper actual
quartic transfer in the companion moment result is compatible with this
bound; it is not needed for the approximation argument.

For a box b=(b3,b5,b7,b11,b13), retain the original test labels whose exponent
vectors lie in the box, including the unit. Set

    S_p(b)=1+sum_(j=1)^b (2j+1)p^-j,
    S_p(infinity)=p(p+1)/(p-1)^2,
    H2=product_p S_p(infinity), H2_box=product_p S_p(b_p).

For any density bounded byD, expanding L_full^2-L_box^2 keeps exactly the
ordered label pairs with at least one member outside the box. Their Haar
intersections are at most1/lcm, so

    0<=Gamma_full(nu)-Gamma_box(nu)<=D*(H2-H2_box).

No test label disappears from the target maximum: outside pairs enter the
explicit nonnegative bound. For finite physical exponents a use min(a,b)
in the box; the infinite product remains a valid uniform bound. The exact
one-coordinate remainder is

    S_p(infinity)-S_p(b)
      =p^-b[(2b+1)/(p-1)+2p/(p-1)^2].

<a id="continuity-of-the-actual-construction-in-the-forbidden-core"></a>
### Continuity of the actual construction in the forbidden core

Compare two forbidden families F,F' agreeing at all original moduli inside
b. Uniformly lift their constructions to a common finite physical period.
Partition the omitted reciprocal sums by largest prime:

    D3=35/16,
    B3=product_(p=3,5,7) [p/(p-1)*(1-p^(-b_p-1))],
    B4=B3*(11/10)*(1-11^(-b11-1)),
    T357=D3-B3,
    T11=D3/10-B3*(1-11^-b11)/10,
    T13=(77/32)/12-B4*(1-13^-b13)/12.

These exact tails partition the full five-prime original-divisor tail:
T357+T11+T13=1001/384-product_p[p/(p-1)*(1-p^(-b_p-1))].
Every original divisor is counted once; pure11 and13 classes are included.

The symmetric difference of the two357 survivor sets has ambient mass at
most2T357. Both densities are at least1/D0. Their normalized uniform laws
therefore differ in L1 by at most4D0T357.

For any two bad masks on a fixed Haar fibre, the physical and killed T4
kernels at delta=1/2 have L1 difference at most4 times the mask symmetric
mass. This follows by the nested-mask argument through their union: at a
newly bad point the lost density is at most2; normalization controls the
opposite sign. The same bound for killed laws follows from the monotone
good coefficient. A change of old probability contracts under a fixed
normalized kernel. At11 the old density is at mostD0 and the mask average
is at most2D0T11. At13 the physical old density is at most2D0, giving mask
average at most4D0T13. Hence the two physical13 laws differ in L1 by at most

    D0*(4T357+8T11+16T13).

Their full survivor events have Haar symmetric difference at most
2(T357+T11+T13), and both physical densities are at most4D0. Restricting
physical measures to those events therefore gives killed L1 difference at
mostD0*(12T357+16T11+24T13). Both killed masses are at leasts*. Normalizing
them costs at most2/s*, proving

    ||nu_F-nu_F'||_1
      <=L(b):=D*(6T357+8T11+12T13).

Total variation in the probability convention is half this L1 quantity.
This argument uses the actual BB construction, not density domination alone;
bounded-density high-digit oscillations would prevent a uniform TV claim for
arbitrary supported probabilities.

Now take F' to consist of precisely the original forbidden classes of F
inside the box. Its actual law is computed on the finite core and lifted
with independent uniform higher digits. This core law need not avoid F's
omitted high classes: it approximates the actual supported nu_F with the
proved L1 error. The full law nu_F retains all forbidden classes.

<a id="approximating-the-actual-complete-maximum"></a>
### Approximating the actual complete maximum

Both final densities f,g are at mostD, so |f-g|<=D. For every complete test,
Cauchy--Schwarz and the Haar fourth moment give

    |E_f L_T^2-E_g L_T^2|
      <=sqrt(||f-g||_1 * integral |f-g|L_T^4)
      <=sqrt(D*H4*L(b)).

The same bound holds for inside-box tests. Combine it with the original-test
tail estimate and take maxima over the same respective test domains:

    |Gamma_full(nu_F)-Gamma_box(nu_core)|
      <=D*(H2-H2_box)+sqrt(D*H4*L(b)).

For the lower direction, extend every box layout to the full original test
inventory; the added indicators are nonnegative. Thus the bound does not
assume that full and truncated maxima have the same maximizing layout.

Uniform cutoffs in all five coordinates give the certified accuracies

    cutoff20: absolute Gamma2 error <1,
    cutoff24: absolute Gamma2 error <1/10,
    cutoff28: absolute Gamma2 error <1/100.

For each row the verifier checks R<tolerance and
D*H4*L(b)<(tolerance-R)^2 exactly, with R=D*(H2-H2_box). It also checks that
the previous uniform cutoff fails this sufficient bound. No optimality among
nonuniform boxes or lower bound on the true approximation error is claimed.
All heights below a chosen cutoff use the intersection with the physical
inventory. Nonnegative geometric tails prove monotonicity at every height.

The core law and its finite maximum are computable rational objects, but the
certificate does not enumerate a particular family-specific core maximum.
It verifies the uniform error modulus. This theorem applies to arbitrary
residues through13; it neither extends to unrestricted prime support nor
settles the remaining17/19 continuation bounds. The argument is ordinary
mathematics supported by exact arithmetic, not an end-to-end Lean theorem.

<a id="a-cubic-tail-for-queried-original-cylinders"></a>
### A cubic tail for queried original cylinders

For an arbitrary queried old cylinder C(a,d), where d=product p^h_p, its
Haar conditional law fixes those h_p digits. The complete original test
square therefore satisfies

    E_nu[L_T^2*1_C(a,d)] <=(D/d)*product_p Phi_p(h_p),
    Phi_p(h)=(h+1)^2+2(h+1)/(p-1)+(p+1)/(p-1)^2.

The query residue may differ from the original old forbidden residue; it
represents an old projection of a subsequent current-prime forbidden label.
It may be chosen independently for every current depth.

Summing this bound over queried original old labels outside a box preserves
both complete test-label axes. Put

    T_p=F3_Haar(p)=p*(p^2+4p+1)/(p-1)^3,
    U_p(b)=p^-b*((b+2)^2/(p-1)+(4b+7)/(p-1)^2
                        +3*(p+1)/(p-1)^3),
    K_box=product_p T_p-product_p(T_p-U_p(b_p)).

Indeed p^-h Phi_p(h)=sum_(i,j>=0)p^-max(i,j,h), while U_p(b) is its
sum over h>b. In the following identity Fk(p,b) denotes the finite
Haar moment already defined above, not the fixed-prefix quantity Phi_p(b). The third exponent alone is
restricted. Equivalently its inside sum is F3(p,b)+(b+1)*(F2_Haar(p)-F2(p,b)); this identity follows
by splitting the common maximum at b. Products of the complete nonnegative
sums give

    sum_(queried d outside box) E_nu[L_T^2*1_Cd] <=D*K_box.

The full five-prime cubic sum is10110619519/44236800. If the query-unit
label is excluded exactly, subtract H2, leaving9464854399/44236800. No
assumption identifies different original test or forbidden residues.

For17 let alpha_high be the Haar fraction covered by the high-old-cofactor
new classes. Summing positive current depths gives

    E_nu[L_old^2*alpha_high]<=D*K_box/16.

For the complete current test load and the actual union B_high, its two
current test exponents are unrestricted while the current query exponent
is positive. Their exact sum is F3_Haar(17)-F2_Haar(17)=595/2048. A full-Haar
T4 BB kernel has density at most1 on all its actual bad points, so

    E_nuK17[L_full^2*1_B_high]<=D*K_box*(595/2048).

For a merely c-capped kernel without bad-subset domination one must retain
an additional factor c. This claim concerns bad subsets, not the full
change in BB charge when additional classes are inserted.

In fact beta_delta(alpha)=(alpha-delta)_+/(1-delta) is monotone and
1/(1-delta)-Lipschitz. For the same old law and the masks from a core and
its full extension, alpha_core<=alpha_full<=alpha_core+alpha_high, hence

    E_nu[L_old^2*(beta_delta(alpha_full)-beta_delta(alpha_core))]
       <=D*K_box/[16*(1-delta)].

The unweighted charge increment uses the smaller reciprocal old-label
tail in place of K_box. The coefficient is necessary to account for changes
in density on already bad core points. At delta=1/2 the denominator is8.

These identities give explicit error budgets for finite same-law joint
charge/test observations. They do not supply the missing low-cofactor
observations or a strict improvement of the full17 bad charge. All finite
heights are bounded by the complete nonnegative geometric sums; the
verifier retains literal small three-label checks and45 prefix-moment
fixtures without presenting them as a proof of the universal quantifiers.


<a id="an-arbitrary-residue-supported-seed-below256-after13"></a>
## An arbitrary-residue supported seed below256 after13

For every finite distinct odd family supported on {3,5,7,11,13}, with
arbitrary original heights and residues, there is one explicit supported
law with

    Gamma13 <= 42035473165849976389/171474522380088889
             <245.141218.                            (PP1)

The construction starts with the uniform actual357 survivor law and
uses AP's pure-survivor BBMST kernels with thresholds T11=4,T13=6,
followed by one final conditioning. This is a different law from the
two full-Haar delta=1/2 kernels in AO1--AO8. The assertion retains
all original divisor test labels and all finite physical exponents.

<a id="one-source-law-and-its-simultaneous-observations"></a>
### One source law and its simultaneous observations

Let mu be the uniform complete actual357 survivor law. CM8, SD1--SD6
and BS10 in Problems/erdos-7-odd-covering-systems.md give on this SAME
law, including missing head classes and arbitrary residues/heights,

    dmu/dHaar <=D0=432/53,
    E_mu L^2 <=G=3849/106,
    E_mu L <=M=1+R,  R=1649/360,

for every complete original test load L. Here R is the sum of the
nonunit cylinder maxima; BS10 explicitly identifies its arbitrary
actual-head and uniform-law scope. No nonuniform two-root-law
estimate is substituted.

Let A=(1+G3)(1+G5)(1+G7), with independent geometric variables
P(Gp=n)=(p-1)/p^(n+1). Then E A=35/16. Successively centering all
test prefixes in each independent Haar coordinate makes those
indicators nested and maximizes every nonnegative increasing convex
cost. At zero fixed low depth this is the comonotone comparison in
the report following SH4. It changes test residues only for this
upper comparison; it changes no forbidden class or actual law.
Completion of the finite heights adds nonnegative terms. Consequently

    H(h):=sup_L E_mu(L-h)_+ <=D0 E(A-h)_+.             (PP2)

For an integer h, this expectation is exactly

    E A-h+sum_(n<h)(h-n)*P(A=n).

Only finitely many product probabilities are needed; its entire
infinite tail is included through the exact mean35/16.

For h=2,3 the following positive-integer inequalities improve PP2:

    (L-2)_+ <=(L^2+17L-18)/30,
    (L-3)_+ <=(L^2+2L-3)/15.

Above the respective thresholds, the differences are
(L-6)(L-7)/30 and(L-6)(L-7)/15, nonnegative for every integer L.
Below the thresholds the displayed polynomials are nonnegative
for L>=1. All their moment coefficients are nonnegative. Thus the
simultaneous profile needed below is

    H1<=R,
    H2<=h2=2159489/572400,
    H3<=h3=424267/143100,
    H4<=h4=4733643/2272375,
    H5<=h5=121526801/79533125,
    H6<=h6=8571397321/8350978125.                      (PP3)

The first two nontrivial bounds are(G-1+17R)/30 and(G-1+2R)/15;
h4,h5,h6 come from PP2. All are bounds for every original layout on
one mu. For h in [j,j+1], the chord of the two integer upper bounds
is valid. For h<=1, H(h)<=M-h because L>=1.

<a id="the-actual-normalized1113-chain"></a>
### The actual normalized11/13 chain

Use the actual pure-power survivor bases at11 and13 and AP's
normalized kernel with

    T11=4, delta11=1/3, c11=5/3;
    T13=6, delta13=5/11, c13=2.

Here c_p bounds conditional Haar cylinder densities at every full
earlier history, and c_p<=p as required by AP1--AP5. The pure
survivor bases are nonempty by their geometric exclusion sums.
The actual kernels are normalized even on completely mixed-bad
rows. There is no intermediate conditioning.

At11 the actual assigned bad probability is at most b11=h4/6.
For13 let N=1+K11 be AP's independent comparison multiplier:

    P(N=1)=28/33,
    P(N=n)=50/(3*11^n) for n>=2,
    E N=7/6.

For N=1,2,3, use respectively H6,2H3,3H2. Since L is a positive
integer, the exact identities at N=4,5 are

    E(4L-6)_+ =2(E L-1)+2E(L-2)_+,
    E(5L-6)_+ =4(E L-1)+E(L-2)_+.

For N>=6, NL-6>=0 and E(NL-6)_+<=NM-6. The full N>=6 tail has
probability5/483153 and first moment61/966306. AP2 therefore gives

    b13 <= [ (28/33)h6+(100/363)h3+(19300/483153)h2
                         +(887/322102)R+1/966306 ]/6
         =153632313644558711/498009616542900000.

The actual common final surviving mass is at least

    rho*=1-b11_bound-b13_bound
         =171474522380088889/498009616542900000>0.      (PP4)

Normalized later kernels preserve earlier violations, so this sum
is a union bound under the same final physical law. AP5 gives

    J13<=G*(23/15)*(55/36)=324599/3816.

One final conditioning on the actual survivor event, retaining
the unit-floor saving, now yields

    Gamma13 <=1+(J13-1)/rho*,

which is PP1. No profile observation is taken from a different law.

<a id="density-fourth-moment-and-a-concrete-next-prime"></a>
### Density, fourth moment and a concrete next prime

The physical Haar density cap is D0*c11*c13=1440/53. The same
supported law therefore has

    D13<=13530827317392000000/171474522380088889.

Using AO4's K0=598121/53 and the original-label quartic transfer
AO5, its physical fourth moment is at most

    Kphysical=K0*(1664/375)*(1843/432)=114643048312/536625.

The supported fourth moment is at most

    1+(Kphysical-1)/rho*
      =106393040395571160497689/171474522380088889
      <620459.757.                                   (PP5)

These caps belong to the new AP(4,6) law, not the earlier AO law.

There is also a concrete admissible17 continuation. Start with the
supported PP1 law and use a FULL-Haar T4 BBMST kernel at17 with
delta17=1/2, whose bad mask includes all pure and mixed17 classes.
Writing f for the exact bound in PP1, its actual retained mass is
at least

    1-f/256=1862004563452779195/43897477729302755584>0.

Its physical square is at most(89/64)f. Conditioning once and using
the unit floor gives

    Gamma17<=1+[(89/64)f-1]/(1-f/256)
            =2984518594775348323619/372400912690555839
            <8014.263.                               (PP6)

Thus the construction supplies actual survivors for every finite
family supported on {3,5,7,11,13,17}. This does not prove an
unrestricted tail continuation: the supplied17 bound does not
pass the19 scalar condition, and PP1 remains above the joint17/19
threshold near123.059. No literature-priority claim is made.

<a id="verification-and-parameter-search-boundary"></a>
### Verification and parameter-search boundary

The adjacent exact verifier reconstructs PP2--PP6 using rational
arithmetic and full auxiliary tails. It also evaluates120 endpoint
threshold pairs from the fixed integer profile: integers1..9 and
100/11 at11; integers1..11 and144/13 at13. The chosen(4,6) pair
has the smallest certified supported square among those pairs.
The comparison concerns this specified profile upper certificate,
not the actual best law or all possible observations.

For this chord-based certificate, after multiplying by
(10-T11)(12-T13), its numerator and denominator are separately
affine on each integer threshold interval. The13 breaks are still
integers because T13/N crosses an integer only at an integer T13.
On positive-denominator intervals the ratio is monotone or constant;
a zero-denominator boundary has positive numerator. Thus endpoints
suffice for this certificate. This observation is not needed for
the validity of the concrete(4,6) result.

The construction reuses CM8, SD1--SD6, BS10, AP1--AP6 and the
report's Haar comonotone comparison. It is an ordinary proof with
an exact arithmetic certificate, not a new Lean declaration or
an end-to-end Lean verification of the arbitrary-family extraction.

The [arbitrary-head profile verifier](../../verify_arbitrary_head_profile.py)
reconstructs the [exact certificate](../../certificates/arbitrary_head_profile_certificate.json)
from pinned numerical inputs for CM8, SD and the joint density bound.
The finite-core and moment estimates for the AO law have their own
[certificate](../../certificates/finite_core_approximation_certificate.json). Both programs
are independent of the working directory:

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_arbitrary_head_profile.py
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_finite_core_approximation.py
```

<a id="weighted-forbidden-mask-tails-for-the-actual-ap46-restart"></a>
## Weighted forbidden-mask tails for the actual AP(4,6) restart

The following ordinary proof controls changes of the forbidden masks
at17 and19. From the full supported AP(4,6) law at13, retain old
cofactor exponents through20 and current prime depths through8 in
those two masks. For the actual thresholds T17=T19=8, the total error
in the SH28 functional at W=483 is less than377/1000. Every original
test label and every original ambient height is retained.

This is a continuity bound and a sufficient criterion. It does not
produce the required reference correlation certificate. In particular,
it neither truncates the incoming13 law nor makes its joint marginals
computable from a finite initial family. Its arbitrary-height statement
is ordinary mathematics; the accompanying exact program verifies
constants and finite coefficient fixtures, not Lean-kernel proofs.

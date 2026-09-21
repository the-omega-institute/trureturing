# The actual near-J source and the unit refund

This note continues [339](339-irredundant-source-seven-labels-bound-the-actual-surplus.md), retaining its actual source family and source laws.

## The actual near-J sources cannot attain their entrywise square envelopes

The same finite family F_N also supplies a strict loss between its actual
square maximum and the sum of independently maximized pair masses. This
is a concrete application of[28's saturation criterion(LCZ4)](../001-064/28-zero-local-losses-do-not-imply-a-common-maximizing-original-layout.md#5-exact-saturation-and-why-this-is-not-a-counterexample-to-full-arc-consistency)
inside the source family above. F12 satisfies the current near-J guard;
F3, although used below to check the formulas, is outside that guard.
No uniform loss for all sources in the guard is asserted.

Put Q_N=105^N. For a finite positive measure m on this actual period, set

    c_m(d)=max_b m(x=b mod d),
    E_N(m)=sum_(d,e|Q_N)c_m(lcm(d,e)),
    Gamma_Q_N(m)=max_layout integral L^2 dm.

Every test retains one independent residue at every divisor, including
its unit. CRT bounds each ordered square term by the displayed cap.
The five terms(1,d),(d,1),(d,d),(d,e),(e,d), for d|e and 1<d<e,
share the same d-residue. If

    A_j=m(x=j mod d),
    B_j=max_(b=j mod d)m(x=b mod e),

their total is at most max_j(3A_j+2B_j). Consequently the same-law
entrywise envelope has the valid local correction

    kappa=3max A+2max B-max_j(3A_j+2B_j),
    Gamma_Q_N(m)<=E_N(m)-kappa.                         (PG1)

This retains near-maximal choices as well as maximizers. Every other
ordered-term loss is nonnegative. The correction includes the diagonal
term(d,d) exactly once; no factor is borrowed from another estimate.

### The original actual source has incompatible mod9 and mod63 maxima

Retain t,q,u,z,a and the raw35 masses n of the F_N construction. Subscripts
in this paragraph are literal residues modulo9; n3 is the earlier nB.
The actual unnormalized mod9 masses are

    alpha=((1-a)n0,(1-2a)n3,n1,n4,n7), S=sum alpha.

For each surviving cell j, the exact largest mod63 subcylinder is

    beta_j=max_(b=j mod9)mu(x=b mod63)=n_j/(7u).         (PG2)

The upper follows from mu<=Lambda tensor Haar7/u. The same seven root4
misses every original seven restriction and attains this cap in every
cell. Thus PG2 concerns the full joint actual source, not a product
substitution for its old marginal.

For every N>=3,

    1/27<=t<1/18, 31/125<=q<1/4, 1/6<a<6/35.

The unique maxima of alpha and beta are respectively at cells4 and3.
Indeed n3 exceeds all other raw masses, alpha4-alpha3=[2a(1-q)-q]/9>0,
alpha0<=94/2025<1/18<alpha4, and alpha1,alpha7<alpha4.
For gamma_j=3alpha_j+2beta_j, its unique maximum is at3: the other
root1 cells are dominated by4, while

    gamma3-gamma0=z[(3-a)t-a/3]>0,
    gamma3-gamma4=[q(21u+8)-6]/(63u)>0.

The first bracket is at least1/21 on the containing box. The second
numerator is greater than81/250, using u>5/6. Applying PG1 with d=9,e=63
therefore gives

    kappa_N=3(alpha4-alpha3)>0,
    Gamma_Q_N(mu/S)<=(E_N(mu)-kappa_N)/S.               (PG3)

At N=12 the exact values are

    kappa12=20114411648143778/8448051270263671875,
    kappa12/S12=593867946705620973561/53448309681763197033148
              =0.0111110706819649... .

As N tends to infinity, kappa_N tends to1/420 and S to3/14, so the
normalized gap tends to1/90. The mean-sharpness construction above does
not supply a layout saturating this square envelope.

### The fixed reweighted source has a different shared-label conflict

Use precisely RW1's cell weights r=(11/8,5/4,1,1,1), and put
m=mu_r=r*mu, T=mu_r(1). Write v_j=r_j*alpha_j. In PG1 now take d=3,e=9:

    A0=v0+v3, A1=v1+v4+v7, A2=0,
    B0=max(v0,v3), B1=max(v1,v4,v7), B2=0.

Here B0=v3 and B1=v4 for all N>=3. The root0 comparison follows from

    (v3-v0)/z=-(1+9a)/72+11(1-a)t/8>=13/1890>0;

the root1 comparison is inherited from alpha. Set

    DeltaA=A1-A0
      =1/3-7q/9-z(21-31a)/72+t[11(1-a)z/8-q],
    DeltaB=B0-B1=5(1-2a)z/36-(1-2q)/9.

For N>=4 use t>=4/81. On the containing box, DeltaA increases with t
and a and decreases with q. For example, its three derivatives obey
`partial_t>=677/1120`, `partial_a>=17/64`, `partial_q<=-241/432`.
Thus DeltaA>=DeltaA(4/81,1/4,1/6)=7/1728>0. DeltaB increases with q
and decreases with a, giving DeltaB>=199/15750>0 at q=31/125,a=6/35.
Both maxima are therefore unique and lie at different roots. PG1 yields

    kappa_r,N=min(3DeltaA,2DeltaB)>0 for N>=4,
    Gamma_Q_N(mu_r/T)<=(E_N(mu_r)-kappa_r,N)/T.          (PG4)

At N=3 both individual maxima lie in root0 and this cluster's gap is
exactly zero. No claim of a common cluster-maximizing root for all N
is needed. At N=12, the second branch of PG4 is the smaller one and

    kappa_r,12=435812164190143141/16896102540527343750,
    kappa_r,12/T12=25734272483263762332909/240369043020445468666057
                 =0.1070615090857388... .

In the limit, DeltaA tends to61/6720 and DeltaB to13/1008. Hence
kappa_r,N tends to13/504, T to1619/6720, and the normalized gap to520/4857.
These are the actual cell weights and the same forbidden sets as RW1;
the mod9/mod63 maximizer argument for mu was not transferred to mu_r.

The existing sharpness producer records the cell masses, cluster
maximizers and exact gaps at its verification heights, as well as these
limits. It reuses the source reconstruction and private-witness checks
above. The arbitrary-N claims follow from the displayed box arguments,
not from a finite scan. This cluster calculation supplies no complete
Gamma value; (FS1) and (FS7) below separately close both F12 maxima.
For tests at a larger complete height H>=N, the same
five terms retain this loss only after E_N is replaced by the matching
larger-height envelope E_H on the Haar lift of the same actual source.

PG3 and PG4 are counterexamples to saturation of these entrywise
envelopes on the current actual sources. RW5/RW10 and the assigned
square bounds use different WF/A2/Jensen expressions; no comparison
identifying those expressions with E_N has been proved here. The gaps
cannot simply be subtracted from the through41 bounds, M2, or a scalar
recurrence floor. The weighted all-height maximum and a uniform useful
gain through later physical kernels remain unresolved;339d establishes
the plain F_N maxima for every N>=12.

### An exact six-label cluster retains all joint choices

For N>=12, the actual source admits a stronger exact calculation on
D={1,3,7,9,21,63}. This includes all36 ordered terms of its six-label
square. It does not compute the square maximum for all divisors of Q_N.

The complete mod63 marginal follows from the same literal originals.
In each mod9 row j, the following seven roots have full mass n_j/(7u);
one further root has reduced mass n_j*(u-5/7)/u. Every other entry is zero.

| mod9 row j | Full seven roots | Reduced seven root |
| --- | --- | --- |
| 0 |0,3,4,5|2|
| 3 |3,4,5|0|
| 1,4,7 |0,2,3,4,5|1|

Pure7 removes root6 and width (1-u)-1/7 inside root1. On old root0,
P1 removes root1 and the deeper P cylinders remove that width inside
root2. On old cell3, Q1 also removes root2 and deeper Q removes that
width inside root0. The seven mask is identical at every raw35 point
in a row, proving this actual joint marginal. The existing source
partition checks all63 masses directly at its verification heights.
For mu_r, multiply each entire row by its declared cell weight.

For either measure m put

    E_D(m)=sum_(d,e in D)c_m(lcm(d,e))
          =c_m(1)+3c_m(3)+3c_m(7)+5c_m(9)+9c_m(21)+15c_m(63),
    M_D(m)=max_layout integral L_D^2 dm.                (PG5)

The exact search keeps all3*7*9*21=3969 choices at labels3,7,9,21.
For their load L0=1+I3+I7+I9+I21, the best final63 residue adds exactly
max_y m(y)[2L0(y)+1]. Thus all250047 layouts are covered, including
incompatible residues and residues outside individual maximizing sets.
The producer clears one common rational denominator, compares integer
objectives, retains every maximizing layout and directly checks its
pointwise square. No common-center restriction is imposed on the search.

A finite box certificate extends this optimization to every N>=12.
Allow independent parameters

    t in[t12,1/18], q in[q12,1/4], u in[5/6,u12],
    t12=(1-3^-10)/18, q12=(1-5^-12)/4, u12=(5+7^-12)/6.

After multiplying masses by u>0, full entries are n_j/7 and reduced
entries n_j*(u-5/7). Each entry, and hence each fixed layout's scaled
square, is separately affine in t,q,u. Its difference from any fixed
competitor is the convex interpolation of the eight corner differences.
At all eight corners, exhaustive search for both laws gives exactly
three centered maximizers: mod9 cell4 with seven root3,4,5 for mu, and
mod9 cell3 with seven root3,4,5 for mu_r. The same three layouts therefore
maximize throughout the box. In particular centers4 and3 are respective
fixed witnesses. This is a computed conclusion about this cluster.

The corner checks also establish the fixed cap choices, except that
the plain21 cap can change old root inside the containing box. Its exact
formula is max(n0+n3,R)/(7u), where R=n1+n4+n7. Directly evaluating PG5
at a maximizing layout yields, with A0r=(11/8)(1-a)n0+(5/4)(1-2a)n3,

    E_D(mu)-M_D(mu)=[9(max(n0+n3,R)-R)+15(n3-n4)]/(7u),
    E_D(mu_r)-M_D(mu_r)=3(R-A0r).                       (PG6)

These are valid for every N>=12. On the actual family, write
h=3^(2-N),v=5^-N. Then n0+n3-R=[h(1+v)-6v]/36>0, since
h/v=9(5/3)^N>6. The maximum in the first formula can be removed there.

| Law | M_D divided by source mass, N=12 | Exact normalized gap, N=12 |
| --- | --- | --- |
| mu/S |664143379826325168668383/106896619363526394066296|35632431348732953309967/106896619363526394066296|
| mu_r/T |1591571349732425795009615/240369043020445468666057|27167753242115761212321/240369043020445468666057|

The two gaps are0.333335437181... and0.113025175375... . Their limits
are1/3 and183/1619, while the normalized maxima tend to671/108 and
10720/1619. The local layout set is fixed and finite, so its maximum is
continuous in the marginal masses; the limiting values follow either
from PG6 or the exact limiting marginal calculation.

All remaining full-layout terms retain their original entrywise bounds.
Thus PG6 replaces the overlapping five-term correction in PG3/PG4;
it is not added to it. The limiting plain correction grows by a factor30.
For the currently used reweighting, the additional limiting correction
is only29/4857. This remains a same-source cluster improvement, not a
uniform guard bound or a subtraction from the different WF/A2 estimates.

## The actual near-J source can attain the unit refund exactly

For the actual F12 source above, a true square-maximizing complete layout
and five actual later APs attain the old-marginal unit refund with positive
charge. This brings [15's clean-cylinder mechanism](../001-064/15-a-clean-cylinder-makes-all-current-prime-pair-caps-exact.md)
and [01's uniform 315 unit-refund obstruction](../001-064/01-survivor-reduction.md#uniform-sharp-head-obstruction-to-an-excess-energy-rebate)
into the present near-J guard. The argument uses one jointly realizable
layout throughout; its true maximum is not replaced by an entrywise cap
sum. It is an ordinary deduction from the existing mechanisms.

Retain the literal F_N residues above, N>=3, and put Q_N=105^N. Let R_N
be the set avoiding all its original classes, including mixed 7, and H_N
normalized Haar measure on this period. Thus

    dmu=1_(R_N) dH_N/u, S=mu(1), nu=mu/S.                (UR1)

Every complete layout has one independent residue for each divisor of
Q_N, including its unit once. Its maximum Gamma_Q_N(nu) is attained,
because the layout space is finite. At N=12 the source has 204 original
classes, delta=1-qJ=0.00003388634450980418...<1/4000 and
rho=0.0642857815054542...>3/50, as verified above.

### Two clean coordinates preserve a true maximum

The entire roots x5=4 mod5 and x7=4,5 mod7 avoid every original involving
their respective coordinate. Also x5=20 mod25 avoids every original
involving 5: at depth 1 the possible residues are 1,2,3; at depth 2 they
are 5,10,15; at larger depths they are divisible by 25. There is no original
involving both 5 and 7. Consequently the exact survivor mask factors as

    1_(R_N)(x3,x5,x7)=A3(x3) A35(x3,x5) A37(x3,x7),

where all original exclusions remain in these zero-one factors.

Start with any complete layout. Replace the 7-component of every test
with positive 7-exponent e by 4 mod 7^e, keeping its other components fixed.
For an ordered pair whose maximum 7-exponent is k>0, its original
7-intersection is empty or one depth-k cylinder. At each fixed (x3,x5),
its Haar integral against A37 is at most 7^-k. The replacement gives the
nested clean cylinder 4 mod 7^k and attains 7^-k. The other-coordinate test
conditions are unchanged, so this ordered-pair integral cannot decrease.
Pairs with both 7-exponents zero are unchanged. Summing proves that the
complete square does not decrease. Next replace every positive 5-component
by 4 mod 5^b; the same argument applies using A35. Both replacements are
global legal residue choices, made once for each original test label.

Applying these operations to an attained maximizer gives a maximizer L*
whose positive 5 and positive 7 tests all follow their nested 4 paths:

    integral (L*)^2 dnu=Gamma_Q_N(nu).                   (UR2)

The N pure 3 original cylinders are pairwise disjoint, with one at each of the
depths 1,...,N. Their survivor set A_N in Z/3^N Z has (3^N+1)/2 points.
The N nonunit pure 3 tests of L* cover at most
sum_(h=1..N)3^(N-h)=(3^N-1)/2 points. Hence some a in A_N misses all
those tests; at N=12 the exact comparison is 265721>265720. On

    C_a={x3=a mod3^N, x5=20 mod25, x7=5 mod7},

the source survives completely, while every nonunit test of L* is false:
positive 5 and positive 7 tests miss their respective coordinate, and the
remaining tests are the pure 3 ones just excluded. Therefore L*=1 on C_a.
For general N, existence follows from finite maximization and this count.
At N=12, (FS1) below identifies the complete centered4 layout as a maximum.

### Five actual next 11 labels charge precisely that cylinder

Adjoin the pure class 10 mod 11. For i,j in {0,1}, adjoin one class with
numerical modulus 11*3^N*25^i*7^j and CRT conditions

    x3=a mod3^N, x11=i+2j mod11,
    x5=20 mod25 if i=1, x7=5 mod7 if j=1.               (UR3)

These five odd numerical moduli are distinct and new, and every old
exponent remains within Q_N. The extended family has N^2+5N+5 classes,
hence 209 at N=12. Every old private integer lifts to a private integer
by choosing its 11-digit 9. Each new mixed class has the private CRT point
(a,20,5,i+2j): its old coordinates survive, and its 11-digit distinguishes
it from the other four new classes. The pure 11 class is private at
(4,4,4,10). The point (4,4,4,9) still survives all classes. Thus this is
an irredundant actual extension and a noncover, with period 11*Q_N.

Use the full-Haar 11 base and the existing head parameter delta11=3/10.
At an old source point x, the number of active mixed classes is

    m(x)=1_(x3=a)(1+1_(x5=20 mod25))(1+1_(x7=5 mod7)).

Their 11-digits are distinct and differ from the pure forbidden digit 10,
so the actual forbidden fraction is alpha(x)=(1+m(x))/11. For the
normalized BBMST clipped kernel K11, the actual forbidden row mass is
b(x)=(alpha(x)-3/10)_+/(7/10). Its complete table is

| m |0|1|2|4|
| --- | ---: | ---: | ---: | ---: |
| alpha |1/11|2/11|3/11|5/11|
| b |0|0|0|17/77|

Exactly m=4 occurs on C_a. Put P=nu K11, let B11 be this actual new
forbidden union, and let kappa=P restricted to B11. Since nu is already
supported on all old survivors, kappa is the actual first-hit charge.
For the projection pi to old coordinates its pushforward is

    eta=pi_*kappa=(17/77)1_(C_a)nu <= nu,
    ell_N=eta(1)=17/(77*175*3^N*u*S), 0<ell_N<=17/77<1.                 (UR4)

Here nu(C_a)=1/(175*3^N*u*S), since C_a is entirely surviving. Also
pi_*P=nu, so integrating any old load against eta is precisely integrating
its pullback against kappa. No already removed mixed 7 mass is charged.

Extend Gamma homogeneously to finite positive measures. Every complete
old L>=1 gives integral L^2 d(nu-eta)<=Gamma_Q_N(nu)-ell_N.
The same L* from UR2 attains equality because L*=1 on C_a. Thus

    Gamma_Q_N(nu-eta)=Gamma_Q_N(nu)-ell_N,
    Gamma_Q_N((nu-eta)/(1-ell_N))
      =(Gamma_Q_N(nu)-ell_N)/(1-ell_N).                 (UR5)

Equivalently, the minimum over complete L of
Gamma_Q_N(nu)-integral L^2 dnu+integral(L^2-1)deta is zero.
At N=12 the exact positive charge is

    ell_12=46895305009765625/3527588438996371004187768
          =1.3293870818759043...*10^-8.                 (UR6)

### Old 3 reweighting and the scope of the obstruction

The proof applies separately to every strictly positive r on Z/3^N Z:
set T=integral r dmu and nu_r=r*mu/T, with 0<T<infinity. In each compression
comparison r(x3) is a fixed nonnegative multiplier. Choose a maximizer
for this law and then its uncovered a. The same extension gives

    eta_r=(17/77)1_(C_a)nu_r,
    ell_r=17*r(a)/(77*175*3^N*u*T)>0,                  (UR7)

and UR5 holds with nu_r,eta_r,ell_r. This includes the stated cell weights
r=(11/8,5/4,1,1,1). The maximizing layout and a may change with r;
no single choice is claimed to work simultaneously for all weights.

For the unweighted sequence, 3^N*ell_N tends to 68/9625 and
ell_N/(1-qJ) tends to 34/86625. The charge therefore tends to zero while
qJ tends to 1 and rho tends to 9/140>3/50. This rules out an extra rebate
required to be strictly positive for every positive actual charge in
this guard. This depth-N construction alone leaves open bounds with a
macroscopic charge requirement or an explicit loss allowance. UR5 concerns only the old-marginal square;
it does not assert saturation of a complete 11 transfer. No value of true
Gamma, Lean result, or unrestricted odd-covering
conclusion is supplied.

### The same extension has a complete next11 bound

Root9 is entirely clean. Its actual root mass c for m=0,1,2,4 is respectively
1/10,1/9,1/8,10/77. By the same clean-root comparison, the full killed square
maximum on period11*Q_N is the maximum, over independent old layouts A0,A1, of

    integral[(1-b)A0^2+c(2A0*A1+A1^2)]dnu.

Put J=Gamma_Q_N(nu), E={x3=a mod3^N}, and

    Jp_N=1+sum_(j=1..N)(2j+1)/p^j,
    W_N=(N+1)^2*J5_N*J7_N/(3^N*u*S).

The actual domination nu<=Haar/(u*S), followed by expansion of every original
pair on E, gives integral_E A^2 dnu<=W_N: its three-coordinate pair has at
most(N+1)^2 choices, and each five/seven intersection costs at most its
corresponding p^-max depth. Now 0<=c-1/10<=(23/770)1_E and
2A0*A1+A1^2<=A0^2+2A1^2. Cauchy--Schwarz gives the upper bound below;
A0=A1=L* and L*=1 on C_a give the lower bound:

    (13/10)J-ell_N <= Gamma_(11Q_N)(nu K11^-)
                   <= (13/10)J-ell_N+(69/770)W_N.        (UR8)

Divide by1-ell_N for the normalized killed law. For nu_r replace W_N by
max(r)(N+1)^2*J5_N*J7_N/(3^N*u*T), using its own L*,a,ell_r. Since
J5_N<=15/8 and J7_N<=14/9, the error is O(N^2*3^-N) for the plain law
and the stated fixed cell weights. This controls exactly this five-label
extension, with every old test retained, rather than arbitrary future
inventories. Its coefficient approaches13/10; unit-refund sharpness does
not supply the coarser full-cap coefficient107/77.

### A separate fixed-depth extension retains a positive charge floor

For the plain source law and, separately, the fixed weights
r=(11/8,5/4,1,1,1), a further compression gives a hole of depth at most4.
This stronger version uses the literal F_N restrictions; it does not
apply to an arbitrary positive function r(x3). Assume N>=4.

After the two clean-coordinate compressions, map every three-prefix
of every test by the following common rule, keeping its exponent:

| Depth | Original positive-source prefix | Image |
| --- | --- | --- |
|1|root0 or1|the same root|
|2|row0 or3 modulo9|the same row|
|2|row1,4 or7 modulo9|row4|
|at least3|root1|4 modulo its original power of3|
|at least3|root0, row3|3 modulo its original power of3|
|at least3|root0, row0|18 modulo its original power of3|

Prefixes lying in a pure3 forbidden class may be mapped to any of the
allowed images of their depth: every original pair involving such a
prefix has zero source integral. For any compatible pair with positive
source integral, the displayed images remain compatible. At each fixed
(x5,x7), its old three-intersection is one cylinder at the larger depth.
For depth at least3 the image has the same Haar width and avoids every
pure3 original. In root1, row4 retains precisely the common 3*5 exclusions;
row1 has additional 9*5 exclusions and row7 has additional higher3*5
exclusions. The seven masks are identical throughout root1. On rows0 and3,
the five/seven masks are constant; the path18 also removes any deeper
pure3 exclusion from row0. Thus the image permits every fixed (x5,x7)
permitted throughout the original cylinder, and possibly more. At depth2
the same row domination applies, and depth1 is unchanged. The two stated
weightings are constant on every moved positive-source row. Integrating
proves that every ordered-pair term cannot decrease. An originally
incompatible or zero-mass pair cannot decrease either.

Applying this legal simultaneous map to a true maximizer therefore
retains a true maximizer L*. All its pure3 tests of depth at least3 now
follow one of the three paths3,4,18. Consider

    E1={x3=1 mod9},   E2={x3=12 mod27},
    E3={x3=54 mod81}, (h_i,a_i)=(2,1),(3,12),(4,54).

All three cylinders avoid every pure3 original and every canonical test
of depth at least3. There is one pure3 test at each of depths1 and2.
If the depth1 test chooses root0, it misses E1, and the depth2 image,
which is0,3 or4, also misses E1. If it chooses root1, it misses E2 and E3;
their distinct mod9 rows3 and0 prevent the single depth2 test from meeting
both. Hence some E_i is missed by every nonunit pure3 test. On

    C_i=E_i intersect{x5=20 mod25,x7=5 mod7},

the actual source survives and L*=1. Use UR3 with(h_i,a_i) in place of
(N,a), leaving every old exponent and original class unchanged. This
selects one of three explicit five-label inventories. The same actual
private-point and kernel arguments give

    eta_i=(17/77)1_(C_i)nu,
    ell_i=17/(77*175*3^h_i*u*S),
    Gamma_Q_N(nu-eta_i)=Gamma_Q_N(nu)-ell_i.             (UR9)

Since h_i<=4 and u*S=H_N(R_N)<=1,

    ell_i>=17/(77*175*81)=17/1091475>0.

The source-specific lower bound17/(77*175*81*u*S) tends to
68/779625>0. For the fixed weighted law replace S by T and multiply the
numerator by r(a_i mod9). These three weights are1,5/4,11/8; since
min_i r(a_i)/3^h_i=11/(8*81) and u*T<=11/8, the same uniform floor
17/1091475 holds. The chosen i and maximizer can differ between the two
laws, and no limiting selected i is asserted.

These are guarded sources for every N>=12. Indeed delta_N decreases
with N and delta12<1/4000. Put v=7^-N, M=(1-q)(1/3-t) and
c(v)=(1-v)/5-6/[7(5+v)]. The exact formulas give
rho=T2+c(v)M, T2=(1-q)/90+(1-t)/20+1/360. On this range
T2>=7/120, M>=5/24, c(v)>=c(7^-12)>0, hence

    rho>=51316401261402157493/798255130763894466005>3/50.

Thus a positive extra old-square rebate cannot hold for every extension
even with a charge requirement ell>=c0 for any0<c0<=17/1091475. A larger
charge requirement or an explicit error allowance remains unaddressed.
This is separate from UR3--UR8's depth-N inventory: substituting h_i forN
in the fibre width of UR8 removes its vanishing-error conclusion.

The quantifier is: for each of the two fixed source laws there exists a
later inventory attaining UR9. For UR7 the broader quantifier is: for
each positive old3 reweighting there exists its own depth-N inventory.
Neither gives a single later inventory working for every weighting.
These results do not exclude choosing the head law after seeing the
complete future family, or jointly optimizing all new blocks.

The existing producer checks the three clean cylinders, all six shallow
test choices, actual private integers for all three inventories, the
kernel table and exact charge floors at its applicable verification
heights. These geometric conclusions do not require computing Gamma;
the complete F12 maxima are established below.

## Both complete F12 squares have an exact centered maximizer

For the actual204-class F12 constructed in339, let Q=105^12 and let
nu=mu/S be its normalized surviving law. Each complete layout has one
arbitrary residue at every divisor d of Q, including the unit. Then

    Gamma_Q(nu)=max_layout integral L^2 dnu
      =2036574313467845778288943/80172464522644795549722
      =25.402416223497948... .                         (FS1)

A maximizing layout puts every test at the residue of4 modulo its own
modulus. This optimizes all2197 labels and their complete square on the
actual source. The fixed weighted law has the same maximizing layout,
with its separate exact value in(FS7). The period and original inventory
are both fixed at N=12. These results do not establish another height,
a statement about every source, or an unrestricted covering conclusion.

### Actual cylinder masses and the common compression

Apply the simultaneous clean5/7 compression in(UR2), followed by the
common three-prefix map above. A maximum is retained, and every positive
five or seven test follows its nested4 path. The remaining three choices
are0/1 at depth1,0/3/4 at depth2, and18/3/4 at depths at least3.
These transformations are performed once per original test label, so all
pair intersections still belong to one legal layout.

Here is the actual mass formula used by the certificate. In the row order
(0,3,1,4,7), put

    eta=(1/9-t,1/9,1/9,1/9,1/9),
    n=((1-q)(1/9-t),(1-q)/9,(1-3q)/9,
       (1-2q)/9,(1-2q)/9-tq),
    sigma=(u-1/7,u-2/7,u,u,u), Z=sum sigma_j*n_j=uS.

Write m(a,r,b,e) for the nu-mass of the test with three residue r at
depth a and clean residues4 at depths b,e. An exponent0 imposes no
condition. For a<=2, let v_j be n_j if b=0 and eta_j if b>0, restricted
to rows congruent to r modulo3^a. For a>=3, only row r modulo9 contributes:
its pure value is3^-a, and its raw35 value is(1-q)3^-a on paths3/18 or
(1-2q)3^-a on path4. Use the raw35 value when b=0 and the pure value
when b>0. Then exactly

    m(a,r,b,e)=[sum_j v_j*(sigma_j if e=0 else1)]
                 /[Z*5^b*7^e].                       (FS2)

The clean positive7 cylinders avoid every original seven restriction;
positive5 cylinders avoid every original five restriction. This proves
the two cases in(FS2), with all original exclusions through depth12
retained. The normalized pair mass is zero for incompatible three
prefixes. Otherwise it is(FS2) at the coordinatewise maximum exponents
and the deeper three prefix. These are actual intersections, not their
separate cap maxima.

The retained[exact source API](../../frontier/source-budgets/source_full_square.py)
implements these masses. The[flow verifier](../../frontier/source-budgets/verify_source_full_square.py)
independently partitions each coordinate by the literal original APs and
all queried tests before comparing the6084 canonical cylinder masses.
It checks the three-prefix intersection rule and both nested-coordinate
rules against those partition masks. The complete centered layout is
integrated a second time from these original-membership counts.

### A two-choice upper comparison preserves the common root assignment

The169 labels with a=0 are fixed. At each of the2028 remaining labels i,
call the unique root1 choice g_i good, and the one or two root0 choices
bad. Good/bad intersections are zero because their three residues differ
modulo3. For a choice r at i, let u_i(r) be its diagonal mass plus twice
the sum of its intersections with every fixed label. For i<j define

    a_i=max_(r bad at i)u_i(r)-u_i(g_i),
    G_ij=2*m(i,g_i;j,g_j),
    B_ij=2*max_(r bad at i,s bad at j)m(i,r;j,s).

All G_ij and B_ij are nonnegative. For an actual layout, put s_i=1
exactly when label i uses a bad choice. Its square gain above the all-good
centered layout is at most

    F(s)=sum_i a_i*s_i
      +sum_(i<j)[-G_ij*(s_i+s_j)+(G_ij+B_ij)*s_i*s_j]. (FS3)

Both good gives pair gain0, a mixed pair gives-G_ij, and both bad gives
at most B_ij-G_ij. Each s_i is shared by every occurrence of its label.
Only the remaining choices within the bad root are maximized separately;
this is an upper comparison and asserts no simultaneous attainment of
those maxima.

Set b_ij=G_ij+B_ij and d_i=2a_i+sum_(j!=i)(B_ij-G_ij). For binary s,

    2F(s)=sum_i d_i*s_i-sum_(i<j)b_ij*abs(s_i-s_j).     (FS4)

Choose a positive integer D making every D*d_i and D*b_ij integral.
Join source to i with capacity D*d_i when d_i>0, join i to sink with
capacity-D*d_i when d_i<0, and put one edge of capacity D*b_ij in each
direction between i and j. Let R=sum_(d_i>0)D*d_i. The cut whose source
side contains exactly the indices with s_i=1 has capacity

    R-2D*F(s).                                        (FS5)

Any nonnegative capacity-feasible flow conserved at every other vertex,
with source-to-sink value v, implies F(s)<=(R-v)/(2D) for every layout.
Thus a feasible flow with v=R proves all gains nonpositive. The actual
all-good layout attains gain0, closing the maximum. No claim that a flow
search algorithm found a maximum is needed.

### Exact complete certificate and its scope

The retained[sparse integer flow](../../certificates/source_norms/source-budgets/source_full_square_flow.json)
has

    D=160344929045289591099444,
    R=v=209626201609934585576758.

The verifier reconstructs all2055378 unordered free-label pairs and all
4111200 positive directed capacities. It checks all31364 saved nonzero
flows against their actual capacities and conservation at all2030
vertices. Omitted flow entries are zero; duplicate, unknown and malformed
entries are rejected. It checks that v equals the full sum of positive
source capacities. Some cylinder masses require scale2D internally; each
final graph capacity is checked to divide exactly back to scaleD.

For the centered layout, the number of ordered exponent pairs with
maximum a is2a+1. Consequently its complete square is exactly

    sum_(a,b,e=0..12)(2a+1)(2b+1)(2e+1)
                         *m(a,4 modulo3^a,b,e),       (FS6)

which gives(FS1). There is no omitted-label or omitted-pair tail in this
certificate. The existing `source_mean_sharpness.py --check` replay now
includes this source and flow verification and records its exact result
in the existing sharpness certificate. The flow checker can also be run
directly with `python3 -I -S -O` and uses only the standard library.
This is an ordinary mathematical proof with exact finite verification;
no new Lean declaration or frozen theorem is asserted.

### Three pure9 test branches close the fixed weighted law

For the same actual F12 and the fixed row weights
r=(11/8,5/4,1,1,1), let nu_r=r*mu/T. Its complete maximum is

    Gamma_Q(nu_r)
      =16622960794401007994531582/721107129061336405998171
      =23.051998967253425... .                         (FS7)

The complete centered4 layout again attains this value. The source API
uses(FS2) with each row multiplied by r_j and Z replaced by uT. Its
normalization and all6084 cylinders are checked against the same literal
original APs, with the declared row weights. Both the source inventory
and all2197 test labels, including the unit once, remain complete.

After the proved simultaneous compression, the pure9 test has exactly
three possible residues0,3,4. Fix this one test in turn to c=0,3,4.
This divides layouts into three exhaustive branches; it does not
condition the source probability law on a residue event. Every integral
in all three branches uses the identical nu_r. Let a=(2,0,0) be this
test label, and write I_c for its indicator at residue c.

The169 labels of three-exponent0 and the fixed pure9 test now form the
170 fixed labels. The other2027 labels retain their good/bad root choices.
Their branch unary is exactly

    u_i^c(r)=u_i(r)+2*m(i,r;a,c).                      (FS8)

Thus the anchor's intersections are retained. For the branch reference
layout put L_c=L_4+I_c-I_4, where L_4 is the complete centered load, and
let C_r=integral L_4^2 dnu_r. Its exact baseline shift is

    Delta_c=integral[2L_4*(I_c-I_4)+(I_c-I_4)^2]dnu_r. (FS9)

The verifier sums the first term over all original test labels and the
second as m(I_c)+m(I_4)-2m(I_c intersect I_4). This retains the fixed test's
diagonal and every interaction, including its interactions with the
other fixed labels.

Use the graph of(FS3)--(FS5) on the remaining free labels, with unaries
(FS8). If its source capacity is R_c and a feasible flow has value v_c,
every actual layout in branch c has square at most

    U_c=C_r+Delta_c+(R_c-v_c)/(2D).                   (FS10)

The fixed test changes unaries and the reference constant, while mixed
good/bad free pairs still have zero mass. This remains an upper bound
when the residual choices within the bad root are optimized separately
for each pair. Neither their joint attainability nor equality of U_c
with the branch optimum is required.

The exact certificates for
[c=0](../../certificates/source_norms/source-budgets/source_full_square_r0_flow.json),
[c=3](../../certificates/source_norms/source-budgets/source_full_square_r3_flow.json), and
[c=4](../../certificates/source_norms/source-budgets/source_full_square_r4_flow.json)
all use D=1442214258122672811996342. They give

| Fixed pure9 test residue c | Exact U_c-C_r | U_c, decimal approximation |
| --- | --- | --- |
|0|-1360086135549916732057219/1442214258122672811996342|22.10894482124856|
|3|-134181193906862145805493/480738086040890937332114|22.77288400257087|
|4|0|23.051998967253425|

In branch4, Delta_4=0 and the feasible flow saturates every source edge:

    R_4=v_4=4250337641076669357482784.                 (FS11)

The other two branch upper bounds are strictly below C_r. Every canonical
layout therefore has square at most C_r, and the legal complete centered4
layout attains C_r. The simultaneous compression proves(FS7) over all
original layouts. This does not claim uniqueness of a maximizing layout
or a restriction on the pure9 residue before compression.

For each branch the verifier reconstructs all2053351 free-label pair
blocks and4108729 positive directed capacities. It checks391109,238026,
and461363 nonzero flow entries, respectively, and conservation at all2029
vertices. All source integrals, baseline shifts and graph calculations
are exact. The weighted witnesses use the existing lossless compressed
certificate format; its reader restores and verifies every original flow
triple before the same independent capacity checks run. The source law
is never replaced by a relaxed marginal or a separately normalized row.

The existing sharpness producer now verifies all four flow certificates
and records both exact maxima. A standalone complete replay is

    python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/verify_source_full_square.py --all

These two source values remove an optimization gap for the specified
finite family. They do not supply a uniform maximum over all admissible
sources or prove that the later-prime survival inequalities close.

The [square allocation and reweighted-source results](339c-the-square-allocation-and-the-reweighted-source.md) continue in339c.

The [complete plain-source square at every height N≥12](339d-the-complete-plain-source-square-at-every-height.md) extends the ordinary-law conclusion to the whole actual source family, with compressed-layout and pair-marginal LP uniqueness.

# Joint residual laws must retain conditional ratios and query incidence

For the continuation criterion `566s>49 R_P(sigma)`, optimizing an
arbitrary Q-prior before product/deletion is equivalent to optimizing a
specific class of survivor laws with fixed ternary conditionals. The
empty selector contains every other selector's feasible set in this
optimization. This removes selector enumeration, but does not remove
the conditional-law restriction.

Actual distinct-odd-modulus families identify separate limits: fixing
the ternary conditional can strictly worsen the optimal complete query
norm; retaining a prescribed low-query Q marginal can force unbounded
joint query cost; positive deleted mass can leave every nonunit query
maximum unchanged. Neither a marginal-only transport nor a mass-only
compulsory debit supplies the missing unrestricted estimate.

These are ordinary proofs and exact arithmetic, not new Lean
verification. The general all-height LP already exists in
[report530](530-one-supported-law-controls-unused-and-deep-occupied-labels.md);
the weighted query-hinge incidence framework already exists in
[report562](562-joint-deletion-certificates-and-an-actual-query-antichain.md).
The new use here is to delimit the proposed source class and give
actual-family counterexamples to two stronger shortcuts. No claim of
external novelty, unrestricted noncoverage, or a covering is made.

## 1. The exact image of product/deletion

Fix one actual finite family on `P={3,5,7,11,13,17,19}`, and write
`Q=P\{3}`. Choose positive finite heights resolving every original.
Let T be the cells of the actual pure-3 survivor, with positive
normalized Haar weights u_t. Let X be the finite Q-cell space, and
let chi(t,x) be the indicator of the complete original survivor U.
All original numerical labels and globally fixed phases enter this
single mask. Set

    c_x=sum_t u_t chi(t,x), X_+={x:c_x>0}.

For an arbitrary Q-prior w, product/deletion gives

    sigma_w(t,x)=u_t chi(t,x) w_x,
    s(w)=sum_x c_x w_x.

If s(w)>0, its normalized Q-marginal is pi_x=c_x w_x/s(w), and

    mu_w(t,x)=pi_x u_t chi(t,x)/c_x.                 (JB1)

Conversely, every probability pi on X_+ occurs: choose

    Z(pi)=sum_(x in X_+)pi_x/c_x,
    w_x=(pi_x/c_x)/Z(pi), s(w)=1/Z(pi).

Direct substitution proves JB1. Dead-cell prior mass changes s but
does not enlarge the set of normalized laws. If X_+ is empty, no
positive surviving mass exists and there is no normalized law of this
form. Otherwise the exact image is

    C_u(U)={pi_x u_t chi(t,x)/c_x : pi a probability on X_+}. (JB2)

This fixes the ternary conditional on every live Q-fibre. It is not
the unrestricted simplex of all probabilities supported on U.

Suppose a selector A imposes only w(W_A)=1 with W_A subset X, and the
empty selector permits all X. Keep chi, u and the objective fixed.
Then

    Gamma_A=sup_w [566s(w)-49R_P(sigma_w)]
             <=Gamma_empty,
    max_A Gamma_A=Gamma_empty.                       (JB3)

This is feasible-set inclusion. It does not eliminate the selector
from a prescribed PA construction whose law or bounds depend on A.
It applies precisely when arbitrary supported Q-priors are optimized
with no extra selector-dependent constraint.

Homogeneity gives

    566s(w)-49R_P(sigma_w)=s(w)[566-49R_P(mu_w)].

Therefore, when X_+ is nonempty,

    Gamma_empty>0 iff min_(mu in C_u(U)) R_P(mu)<566/49. (JB4)

This is a sign equivalence. Gamma_empty need not equal 566 minus49
times the minimum: s(w) varies with pi. The minimum is attained after
the finite reduction below. Equality at the threshold is insufficient.

## 2. Exact finite computation retains all query heights

Let K=product_p p^H_p with every H_p>=1. A finite positive measure mu
whose K-cells have Haar tails satisfies, for d P-smooth and g=gcd(d,K),

    max_a mu([a]_d)=(g/d)max_a mu([a]_g).

This is the existing Haar-lifting identity in
[report472](472-deeper-boundary-queries-give-a-coherent-nine-prime-noncoverage-class.md).
Summing each saturated coordinate's geometric tail gives

    gamma_g=product_(p:v_p(g)=H_p) p/(p-1),
    R_P(mu)=sum_(g|K,g>1) gamma_g max_a mu([a]_g).     (JB5)

All H_p are positive, so gamma_1=1 and the unit term is exactly
mu(1), not a geometric-tail surcharge. This identity applies to both
probabilities and unnormalized restrictions.

Averaging an arbitrary Q-prior over unresolved Q-tail translations
preserves the original survivor mask, the fixed ternary source and
surviving mass. Every query maximum is convex and invariant under
these translations, so this averaging cannot increase R. Consequently
JB5 gives an exact finite LP for JB4. With

    D_(g,a,x)=c_x^(-1) sum_(t:(t,x)=a mod g)u_t chi(t,x),

minimize sum_(g>1)gamma_g z_g subject to

    pi_x>=0, sum_x pi_x=1,
    z_g>=sum_x D_(g,a,x)pi_x for every g,a.

This reuses report530's LP with the fixed ratios JB1. Tail averaging
is different from altering the resolved ternary conditional. The
latter operation need not decrease R, as the next example shows.

## 3. Actual-family obstruction to conditional uniformization

Use the distinct odd originals `2 mod3` and `1 mod15`. Give the actual
pure-3 survivor roots0,1 equal weights, with Haar tails. In CRT
coordinates (t mod3,x mod5), the x=0 fibre permits both ternary roots;
the x=1 fibre permits only t=0.

An arbitrary joint survivor law assigns mass1/2 to each of (1,0) and
(0,1). Replacing the ternary conditionals by JB1 while retaining its
Q-marginal gives

    before: (1,0):1/2, (0,1):1/2;
    after:  (0,0):1/4, (1,0):1/4, (0,1):1/2.

The after-law is realized by Q-prior w_0=1/3,w_1=2/3, followed by
product/deletion with raw surviving mass2/3. Both laws are supported
on the same actual U. Their cylinder maxima are

| Law | mod3 | mod5 | mod15 |
| --- | ---: | ---: | ---: |
| before | 1/2 | 1/2 | 1/2 |
| after | 3/4 | 1/2 | 1/2 |

With Haar tails, JB5 yields

    R=(3/2)M_3+(5/4)M_5+(15/8)M_15,
    R_before=37/16, R_after=43/16, increase=3/8.       (JB6)

Independent Haar on the other primes multiplies 1+R by
product_(p in P\{3,5})p/(p-1), so the strict increase persists on P.
This refutes a contraction claim for this particular conversion. It
does not by itself establish different optimal values. The following
calculation proves that stronger separation for the same actual family
and its general prime parameter version. Neither result obstructs the
continuation threshold after optimizing the Q-marginal.

### 3.1. The fixed ternary source has a strictly worse optimum

For any prime p>=5 put n=p-1 and use the actual originals
`2 mod3` and `1 mod(3p)`. Keep u equal to normalized pure-3 Haar.
Then, over arbitrary probability laws with the stated support,

    min_(mu supported on U) R_{3,p}(mu)
      =3/4+7p/(4n^2)-p/(2n^3),
    min_(mu in C_u(U)) R_{3,p}(mu)
      =3/4+7p/(4n^2).                                (JB6a)

Both minima are attained, and their positive difference is p/(2n^3).
In particular p=5 gives161/128 and83/64, with gap5/128.

First average over the unresolved ternary and p-adic tails. The actual
survivor and the fixed u are invariant. Cylinder maxima are convex and
translations permute their phases, so no maximum increases. This
preserves both the full supported-law domain and C_u(U). Hence both
minimizations reduce exactly to the first-root masses with Haar tails,
whose full-height norm is

    R=(3/2)M3+(p/n)Mp+(3p/(2n))M3p.                  (JB6b)

Call p-root1 bad: only its ternary root0 survives. All other n roots
are good and permit both ternary roots. Write b for the bad-cell mass
and r0,r1 for the row masses. Every supported law satisfies

    r0+r1=1, M3>=max(r0,r1),
    Mp>=(1-b)/n, M3p>=b, M3p>=r1/n.

Define positive weights

    c2=p/n^2, c1=3p/(2n)-c2,
    alpha=(3/2+c1/n)/2, beta=(3/2-c1/n)/2.

For n>=4, c1/n<=15/32<3/2, so all weights are nonnegative.
Apply the preceding inequalities with these weights:

    (3/2)M3 >= alpha*r0+beta*r1,
    (p/n)Mp >= (p/n^2)(1-b),
    (3p/(2n))M3p >= c2*b+(c1/n)r1.

Adding cancels b and r1 and gives

    R>=alpha+p/n^2=3/4+7p/(4n^2)-p/(2n^3).

This is a dual lower bound for EVERY supported law. Its attainer gives
the bad cell mass1/(2n), each good row1 cell mass1/(2n), and each good
row0 cell mass(n-1)/(2n^2). Both rows have mass1/2. The p-query maximum
is (2n-1)/(2n^2), and the joint maximum is1/(2n). Substitution in JB6b
attains the bound, with positive mass at every surviving cell.

In C_u(U), every good column splits equally. Thus

    M3=(1+b)/2, Mp>=(1-b)/n, M3p>=(1-b)/(2n),
    R>=3/4+7p/(4n^2)+[3/4-7p/(4n^2)]b.

The last coefficient is positive because

    3n^2-7p=(n-4)(3n+5)+13>0.

Its minimum is attained by b=0 and mass1/(2n) at every good cell.
This is realized by a p-prior uniform on the good roots, with no
deletion loss. No full-support condition is imposed in JB6a. If one
adds that requirement, the fixed-class value is only an infimum as
b decreases to zero; the unrestricted class still attains its own
smaller minimum.

Unused prime coordinates cannot improve either optimum. Average over
their whole additive groups: U and u are invariant, and every query
maximum again cannot increase. The result has independent unused Haar
coordinates. Therefore for any finite unused prime set F,

    min R_{{3,p} union F}=(1+min R_{3,p}) product_(q in F)q/(q-1)-1

in each respective law class. The exact optimal gap is multiplied by
that same Euler factor. For p=5 and F={7,11,13,17,19}, the minima are
66898267/26542080 and11419147/4423680, with gap323323/5308416.

The restriction on u is material. If its ternary weights may change,
take u'_0=(n-1)/(2n-1), u'_1=n/(2n-1), p-prior bad mass1/n, and each
good-root mass(n-1)/n^2. Product/deletion on the SAME U has mass
2(n-1)/(2n-1); normalization gives exactly the unrestricted attainer.
Thus this example does not separate all product/deletion sources from
all joint laws. It separates the source with the stipulated fixed
ternary Haar conditional.

The different actual family `2 mod3, 4 mod5, 0 mod15, 1 mod45` does
separate those larger classes: [Report573](573-free-product-priors-still-miss-the-optimal-joint-law.md)
proves that its unrestricted complete-query optimum203/144 is strictly
below the infimum over product/deletion laws even when both priors may
vary. That result uses an exact dual, its entire optimal face and two
necessary product cycles. It does not obstruct the continuation gate.

The [exact primal/dual producer](../../frontier/cover-geometry/fixed_ternary_variational_gap.py)
and its [data](../../frontier/cover-geometry/fixed_ternary_variational_gap.json)
check163 identities and inequalities for ten prime instances, including
the dual's constant value on every surviving cell and the reweighted-u
attainer. The algebra above supplies the arbitrary-prime quantifier.

### 3.2. A small marginal query norm need not admit a small joint lift

There is a stronger obstruction to keeping a prescribed Q marginal.
It does not require fixed ternary conditionals. Write M_m(mu) for a
query maximum under one supported probability mu, and let its Q
marginal be nu. Suppose that, on the actual survivor U, a Q-cylinder
A=[0 mod K] forces ternary residue0 mod3^N. Here K is Q-smooth.
For any a>=1 and Q-smooth d, put g=gcd(d,K). Partition the mu-mass
above A into the d/g compatible d-residues and, when a>N, into the
3^(a-N) compatible ternary residues. At least one joint cylinder has
mass at least their average:

    M_(3^a d)(mu)>=nu(A)(g/d)3^(-max(a-N,0)).

Let H_p=v_p(K) and

    A(K)=sum_(d Q-smooth,d>=1)gcd(d,K)/d
        =product_(p in Q)[H_p+p/(p-1)].

Each coordinate sum has H_p+1 terms equal to1 and a geometric tail
1/(p-1). Summing ALL positive ternary exponents gives N+1/2. The
zero-ternary nonunit queries are exactly those of nu. Consequently

    R_P(mu)>=R_Q(nu)+(N+1/2)nu(A)A(K).               (JB6c)

All numerical query labels are counted once. No independence,
conditional uniformity or Haar tails of mu are assumed; nonnegative
summation remains valid if its norm is infinite.

To realize this on actual original families, put
D=7*11*13*17*19=323323. For e=1,...,N and v=1,2 take the original
modulus and globally fixed CRT residue

    m_(e,v)=3^e 5^(2e-2+v)D,
    t=v3^(e-1) mod3^e, x_Q=0 mod[5^(2e-2+v)D].       (JB6d)

These2N odd numerical moduli are distinct, each uses all seven primes,
and every numerical Q cofactor occurs only once. Their ternary
cylinders specify the first nonzero digit and are pairwise disjoint,
so the actual originals are also disjoint and irredundant. Every Q
fibre permits0 mod3^N. On A_N=[0 mod K_N], K_N=5^(2N)D, this is its
entire ternary survivor: all Q constraints match and the forbidden
ternary mass is sum_(e=1)^N 2*3^(-e)=1-3^(-N).

There are no pure3 originals, so u is H3. Put

    r_H=R_Q(H_Q)=157435/165888,
    a_N=A(K_N)=(2N+5/4) product_(p in Q,p!=5)(1+p/(p-1)),
    eta_N=H_Q(.|A_N),
    epsilon_N=(2-r_H)/(a_N-1-r_H),
    nu_N=(1-epsilon_N)H_Q+epsilon_N eta_N.

Here0<epsilon_N<1. Every query maximum of both mixture components
occurs at phase0, so

    R_Q(nu_N)=(1-epsilon_N)r_H+epsilon_N(a_N-1)=2<B_*.

But every joint probability on the same actual U with Q marginal nu_N
satisfies, by JB6c,

    R_P(mu)>=2+(N+1/2)nu_N(A_N)a_N
            >=2+(N+1/2)epsilon_N a_N
            >2+(N+1/2)(2-r_H).                       (JB6e)

The last bound tends to infinity while the marginal norm stays2.
For N=12, there are24 original labels and the middle bound is

    93813694601/6187327488=15.162231962498...>566/49.

This nu_N is an explicit low-query marginal, not the claimed PA
output for a chosen projected family. Its cost alone does not encode
the correspondence needed for a joint extension.

Supported lifts do exist. Each actual fibre has Haar mass c_x>=3^-N,
so the law with Q marginal nu_N and conditional H3(.|U_x) is obtained
by product/deletion from raw prior w proportional to nu_N/c. The
normalizing integral is finite. Here nu_N is the target marginal,
not that raw prior. Starting from raw H3 times nu_N instead gives
marginal proportional to c_x nu_N after deletion; JB6e does not
assert failure for this different, forward reweighting.

### 3.3. The prescribed marginal can even be the unchanged Haar law

For a source-provenance variant, keep the two Q cofactors fixed:
d_1=5D,d_2=25D. For each e=1,...,N and v=1,2 use modulus3^e d_v,
ternary phase v3^(e-1) mod3^e and Q phase0 mod d_v. The full numerical
labels remain distinct and every (d,e) occurs at most once. On the
fixed cylinder A=[0 mod25D], the survivor again forces0 mod3^N.

Take the SAME marginal nu=H_Q for every N. It has R_Q=r_H<1 and is
the actual empty-input PA output: with no selected forbidden Q events,
the pure source and every normalized PA row are unchanged Haar. JB6c
now gives

    R_P(mu)>=r_H+(N+1/2)A(25D)/(25D),
    A(25D)=2407405/18432,
    A(25D)/(25D)=481/29767680.                        (JB6f)

For N=1000000 the lower bound is
9166519379/535818240=17.107516494772554...>566/49.
The displayed family is specified by its formula; no enumeration of
its two million labels or enormous ternary period is used to prove
the result. The bound grows linearly in N with one fixed Haar marginal.

The empty selected input is not asserted to be a good selector for
these actual families. In both JB6d and JB6f, every original projection
lies inside E=[0 mod5D]. Choose instead pi_good=H_Q(.|E^c). Every
remaining fibre is untouched, so H3 times pi_good is in C_u(U).
Every nonunit Q query has a phase1 cylinder disjoint from E, attaining
its undeleted Haar mass. Thus

    R_P(H3 times pi_good)
      =1/2+(3/2)r_H/(1-1/(5D))
      =343904070269/178784575488<2.                   (JB6g)

This very family therefore admits a small joint query law after
changing the marginal. JB6c–f refute preservation of an arbitrary
supplied low-query marginal; they do not refute optimization over pi,
the two-copy PA existence theorem, or noncoverage. Their missing
interface is the relation between the chosen marginal and the actual
fibres, which R_Q alone does not preserve.

The [fixed-marginal producer](../../frontier/cover-geometry/fixed_marginal_lift_obstruction.py)
and [data](../../frontier/cover-geometry/fixed_marginal_lift_obstruction.json)
retain the24 exact CRT labels, rational complete-query bounds, inverse
product/deletion profile, and the fixed-cofactor Haar formulas. Finite
ternary checks verify small depths. The partition argument and the
geometric sums above establish arbitrary depth and arbitrary joint
law, without a numerical LP solver or new Lean theorem.

### 3.4. Saturated shallow projections give a nonempty actual PA obstruction

The prescribed marginal can come from a nonempty selected family whose
two slots are already forced by the actual shallow originals. Fix h>=1,
put J=2*3^h-1 and d_j=5^j D for j=1,...,J, with the same D=323323.
List in increasing order all nonzero residues modulo3^(h+1) that are0
or1 modulo3 as r_1,...,r_J. In particular r_J=3^(h+1)-2 is1 modulo3.
For any N>=h+1 take these globally fixed CRT originals:

| Numerical modulus | Ternary phase | Q phase |
|---|---|---|
|3|2 modulo3|vacuous|
|d_j|vacuous|5^(j-1) modulo5^j, zero moduloD|
|3d_j|1 modulo3|2*5^(j-1) modulo5^j, zero moduloD|
|3^(h+1)d_j|r_j modulo3^(h+1)|zero modulo d_j|
|3^e d_v, h+2<=e<=N, v=1,2|v3^(e-1) modulo3^e|zero modulo d_v|

There are1+3J+2(N-h-1) distinct odd nonunit numerical labels.
At each actual cofactor d_j the exponents0 through h already require
the two different phases in rows2 and3. A selector using at most two
phases at that label and covering these shallow projections must select
both. Consider exactly this selected Q inventory, without auxiliary
labels. This prescription is independent of N.

Its actual PA law nu is explicit. The rows before19 are Haar. The
old coordinates trigger a forbidden19-root precisely when the roots
at7,11,13,17 are all zero and the first nonzero5-digit, at some depth
j<=J, is1 or2. These5-adic cylinders are pairwise disjoint, so every
triggered row excludes just root0. Its normalized density is19/18,
below the PA cap9/5; every row has mass one. Thus

    dnu/dH_Q<=19/18,
    R_Q(nu)<=(19/18)r_H=2991265/2985984<2<B_* .      (JB6h)

On A=[0 modulo K], K=5^J D, no trigger occurs, so nu(A)=1/K.
There all the zero-Q tail projections act. The pure3 original removes
root2; the r_j originals remove every other nonzero allowed prefix
modulo3^(h+1); the deeper originals remove each first nonzero digit
through depth N. The actual ternary survivor above A is exactly0
modulo3^N. Every selected-survivor fibre still admits the cylinder0
modulo3^N, so lifts preserving nu do exist; the obstruction is their
query cost. Applying JB6c and the universal marginal bound
R_Q(nu)>=r_H gives, for EVERY supported lift preserving this same nu,

    R_P(mu)>=r_H+(N+1/2)A(K)/K,
    A(K)/K=[(J+5/4)/K] product_(p in Q,p!=5)(1+p/(p-1)).
                                                        (JB6i)

This lower bound is unbounded in N while the actual PA input, marginal
and density bound remain fixed. For h=1, J=5,

    A(K)/K=37/148838400.

At N=50000000 the bound is2108386799/157593600,
or13.378632120847547...>566/49. This is a symbolic family and rational
formula; it does not require enumerating its100000012 original labels
or constructing its ternary period.

Every original is essential. Private witnesses can be specified in
CRT: for d_j use ternary0 and a5-adic first nonzero digit1 at depth j;
for3d_j use ternary r_J and digit2 at depth j; in both cases set the
D roots to zero. For3^(h+1)d_j use ternary r_j and Q=0 moduloK.
For each deeper original use its own ternary phase and Q=0 moduloK.
For the pure3 original use root2 and Q=1 moduloK. The increasing
ordering of the r_j ensures that the mixed shallow witness avoids
every smaller-cofactor head; larger-cofactor heads have an incompatible
Q projection. The other exclusions follow from the disjoint nonzero
ternary prefixes and the distinct first nonzero5-digit cylinders.

This does not force every possible PA-based construction to fail.
For example, all Q-bearing originals lie in E=[0 moduloD]. Let
pi_good=H_Q(.|E^c), and keep u equal to Haar conditioned on the actual
pure3 survivors0,1. The product u times pi_good survives every original
and is in the same fixed-u class, with

    R_P<=(3/4)+(7/4)r_H/(1-1/D)
        =517222215343/214540959744<3.                (JB6j)

This is an upper bound, not an optimum claim. Auxiliary selected labels
can change the PA input as well: selecting0 moduloD removes all those
Q projections without using a third slot at any d_j. Consequently the
obstruction concerns preserving the marginal generated by the specified
actual shallow inventory, not arbitrary selector design or optimization
over marginals. The adjusted marginal of
[Report574](574-four-level-query-hinge-removes-pointwise-overlap.md)
is also outside the preservation requirement.

The [saturated-source producer](../../frontier/cover-geometry/saturated_shallow_pa_lift_obstruction.py)
and [exact data](../../frontier/cover-geometry/saturated_shallow_pa_lift_obstruction.json)
give534 exact checks on six small literal families, all private CRT
witnesses, the PA trigger partition, and the large-depth rational
bound. The arbitrary-depth proof is JB6c plus the explicit prefix
construction above. No new Lean theorem is claimed.

## 4. Deletion debit depends on every competing query phase

Fix one probability rho and actual forbidden union D. Put sigma=rho|D^c.
For a numerical query label d, write M_d=max_a rho([a]_d). Then

    c_d=M_d-max_a sigma([a]_d)
       =min_a {M_d-rho([a]_d)+rho(D intersect [a]_d)}. (JB7)

The maximizing phase may change after deletion. A large intersection
with just one old maximizing cylinder supplies no positive debit by
itself. Since the residue alphabet is finite,

    c_d=0 iff some old maximizing cylinder is rho-a.e. disjoint from D.

Assuming R_P(rho)<infinity, nonnegative convergence gives

    R_P(sigma)=R_P(rho)-sum_(d>1)c_d.                 (JB8)

Thus if R_P(rho)<=A, rho(D)<=delta and simultaneous certificates
0<=t_d<=c_d are available, a sufficient continuation condition is

    566(1-delta)>49(A-sum_d t_d).                     (JB9)

Finite certified sums suffice. They remain valid after enlarging D;
the extra deleted mass must be charged under the same rho. This is
an incidence requirement, not a conclusion from deleted mass alone.

## 5. Positive mass loss with zero complete-query debit

Take product Haar rho on P and d=product_(p in Q)p=1616615. For every
finite H>=2 use one original at each numerical modulus3^e d,
2<=e<=H, with Q roots all0 and ternary residue

    a_e=(3^(e-1)-3)/2 mod3^e.

The ternary digits, from the lowest, are0, then e-2 ones, then0.
For f>e the f-cylinder has digit1 where the e-cylinder ends in0,
so all these originals are pairwise disjoint. CRT shows that they
are nonempty and irredundant; labels are distinct odd nonunits. Their
total Haar mass is

    delta=(1-3^(-(H-1)))/(6d)>0.

Every original lies in first root0 at every prime of P. For EVERY
nonunit P-smooth query m, the single coherent phase choice `1 mod m`
is disjoint from every original: any prime dividing m witnesses the
root disagreement. It retains Haar mass1/m, and deletion cannot
increase any cylinder mass. Hence

    R_P(rho|D^c)=R_P(rho)=product_p p/(p-1)-1,
    (rho|D^c)(1)=1-delta<1.                          (JB10)

This refutes every mandatory positive debit proportional only to
rho(D), even on finite actual irredundant families. The empty selected
PA input realizes this Haar source; e=0,1 originals are absent and
d exceeds the finite cofactor window in report569. Normalizing the
restriction increases its query norm, rather than preserving it.
JB10 concerns sums of actual query maxima; it does not contradict
report562's auxiliary query-hinge debit or report569's suffix payoff.

## 6. An exact joint profile can still outperform additive mass charging

For comparison, let nu_p be uniform on n_p allowed first roots with
Haar tails, and let E_p contain t_p<n_p of those roots. Put

    c_p=1-t_p/n_p, r_p=p/[(p-1)n_p],
    E=product_p(1+r_p), F=product_p(c_p+r_p), C=product_p c_p.

Let nu_3 have finite complete query norm R3, and let A have nu_3 mass w.
Assume every positive ternary depth has a maximizing cylinder disjoint
from A. On the explicit product source rho=nu_3 times product_Q nu_p,
delete D=A times union_p E_p. Then

    s=1-w+wC,
    R_P(sigma)=(1+R3-w)E+wF-s,
    Delta_R=w(E-F-1+C).                              (JB11)

To prove the formula, a Q-query with support J can select a clean root
at each queried coordinate. Its maximum, summed over positive queried
exponents, is r_J[(1-w)+w product_(p notin J)c_p]. Summing over J
gives (1-w)E+wF. Positive ternary queries attain their undeleted
maxima by assumption, contributing R3 E. Subtract the unit mass s.
These are all maxima under the same sigma.

When delta=w(1-C)>0, product expansion gives

    0<=Delta_R/delta<=E-1-product_p r_p<E-1.

Thus if R_Q=E-1<=B_* from report569, deletion strictly decreases
566s-49R_P(sigma). The debit mitigates the mass cost; it does not
create extra continuation budget in this parameter family.

For report569's actual22-original example, n_p=p-2,t_p=1,w=3/41 and
R3=81/82. The exact joint calculation gives

    delta=47063/1035045,
    R_P(sigma)=98378082487523/25755231744000,
    566s-49R_P(sigma)=534947350215869/1515013632000>0.

This model recovers the benefit of retaining overlap on one law.
Its realizable distinct-star cases already lie in report547's scope;
general measurable A and t_p do not automatically have such an
original-family realization.

## 7. Reproducibility and remaining mathematical obligation

The standard-library
[producer](../../frontier/cover-geometry/joint_residual_query_boundaries.py)
and its [exact data](../../frontier/cover-geometry/joint_residual_query_boundaries.json)
check JB6, actual product/deletion, JB11's22-original specialization,
and the JB10 families H=2,...,7. There are40 named checks and45,906
bounded congruence comparisons. The proofs above establish the general
quantifiers; those finite checks are diagnostics.

For unrestricted original families the remaining requirement is either
a uniform bound below566/49 on a demonstrably sufficient common-law
class, or a same-law mass/incidence estimate strong enough for JB9.
An LP representation does not prove its uniform threshold. Equal
marginals do not justify changing the conditionals. Positive forbidden
mass does not guarantee a compensating reduction of maximum queries.
The fixed-marginal obstruction adds a necessary change of scope: a
successful existence proof must choose the marginal together with the
actual fibres, or prove the needed compatibility for its specific
supplier. It cannot promise to retain every marginal satisfying only
the scalar Q-query bound. Whether optimizing pi in C_u(U) always passes
the threshold for an arbitrary actual family remains unresolved.

[Report572](572-compatible-fibres-lift-one-six-prime-query-law.md)
provides a positive compatibility condition: if the chosen marginal
is supported on actual fibres of pure-3 mass at least c0, its lift
has R_P<=R_Q+[R_3(u)/c0](1+R_Q). A class with two selected shallow
phases through exponent3 and at most two active residual numerical
cofactors per surviving Q point meets the continuation threshold.
This separate incidence premise is not implied by a small R_Q.

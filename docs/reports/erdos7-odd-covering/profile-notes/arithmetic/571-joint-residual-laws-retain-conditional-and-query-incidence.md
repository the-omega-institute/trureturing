# Joint residual laws must retain conditional ratios and query incidence

For the continuation criterion `566s>49 R_P(sigma)`, optimizing an
arbitrary Q-prior before product/deletion is equivalent to optimizing a
specific class of survivor laws with fixed ternary conditionals. The
empty selector contains every other selector's feasible set in this
optimization. This removes selector enumeration, but does not remove
the conditional-law restriction.

Two actual distinct-odd-modulus examples identify separate limits:
conditional uniformization can increase the complete query norm, and
positive deleted mass can leave every nonunit query maximum unchanged.
Thus neither a marginal-only transport nor a mass-only compulsory
query debit supplies the missing unrestricted estimate.

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
does not prove that the optima over the two law classes differ, and
both displayed costs remain below the continuation threshold.

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

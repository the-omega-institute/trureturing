# One supported law controls unused and deep occupied query labels

For P={3,5,7,11,13,17,19}, [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) implies the uniform actual-survivor bound

    H(U)>=alpha7=7235955529/6075000000000.              (PR1)

Here every original family is finite, has pairwise distinct nonunit P-smooth numerical moduli, and has one arbitrary globally fixed residue per modulus. H is normalized Haar on the full P-adic product, and U is its complete actual survivor. The bound follows by integrating report467's supported probability with density at most1/alpha7. In particular(PR1) applies to every other finite family satisfying these same numerical-label rules.

Legal replacement and addition of classes give a different common-law conclusion. There is one probability nu supported on U for which the sum of maximum cylinder probabilities over every unused numerical label is at most

    log(H(U)/alpha7)<=log(1/alpha7)<27/4.              (PR2)

The fixed mixture below controls all unused labels and all occupied labels above10^9 with total query sum below6.737016, while retaining density at most Lambda7 and full actual survivor support. The Gibbs refinement and fixed mixture below establish these bounds simultaneously. Controlling the remaining occupied labels under that same law is unresolved. These statements are ordinary proofs using(PR1), finite minimax and compactness; they are not new Lean results or an unrestricted Erdős#7 resolution.

Two further sufficient interfaces are available: actual joint coverage
reduces the replacement charge, and an exact finite density-constrained
LP on shallow originals transfers to every deeper extension with a
quantified conditioning loss. The required finite bound11.03257 remains
unproved. A35-label irredundant counterexample shows why the necessary
shallow exponential and pair moments cannot alone settle that gap.

## Legal phase resampling preserves the original quantifiers

Let M be the set of actual original numerical moduli and C_d=[a_d]_d its fixed classes. Take a finite query set J of nonunit P-smooth labels. For each d in J fix a phase distribution theta_(d,a)>=0 with sum_a theta_(d,a)=1, and set

    w_d(x)=theta_(d,x mod d).

Let F=J minus M and O=J intersect M. Fix replacement probabilities r_d in[0,1] for every d in M, independently of x and of the query phase choices, with

    c=sum_(d in M) r_d/d <alpha7,
    beta=alpha7-c>0.

For every d in O, retain its original class with probability1-r_d; otherwise replace it with one phase sampled from theta_d. For each d in F, add one phase sampled from theta_d. All choices for different numerical labels are independent, and original labels outside O remain fixed. A chosen phase applies globally to its complete numerical modulus. Every outcome still has exactly one class per occupied numerical label, so(PR1) applies to its actual survivor.

On x in U the averaged survival probability is exactly

    product_(d in F)(1-w_d(x))
      *product_(d in O)(1-r_d*w_d(x)).

To bound survival outside U, assign each point to one original class containing it, using a fixed ordering. If its assigned label is not in O, it cannot survive. If it is d in O, survival requires that class to be replaced, with probability at most r_d. The assigned region has Haar mass at most1/d. Thus averaging(PR1) proves

    alpha7 <=sum_(d in O) r_d/d
       +integral_U product_F(1-w_d)*product_O(1-r_d*w_d),

and consequently

    beta<=integral_U product_F(1-w_d)*product_O(1-r_d*w_d).
                                                               (PR3)

No original label is duplicated, no original phase is selected separately at different points, and U in this inequality remains the complete survivor of the fixed original family.

## Finite minimax and one law for every query depth

Put g_J=sum_F w_d+sum_O r_d*w_d. Since1-z<=exp(-z) for z in[0,1],

    beta<=integral_U exp(-g_J)
         <=H(U)*exp(-min_U g_J).

Therefore every fixed finite phase mixture has

    min_U g_J<=C=log(H(U)/beta).                      (PR4)

Resolve the finite original and query moduli in one finite LCM. The payoff is bilinear between a probability on its actual survivor residues and the product of the finitely many phase simplexes. Finite minimax applied to(PR4) gives a supported probability nu_J with

    sum_(d in F) max_a nu_J([a]_d)
      +sum_(d in O) r_d*max_a nu_J([a]_d)<=C.

Lift it to the full adic product with Haar tails; the original survivor is clopen. Probabilities on the compact U form a compact space. Each finite query inequality defines a closed subset, since cylinder probabilities and their finite maxima are continuous. A finite union of query inventories gives the finite intersection property for these subsets. Thus a single supported probability satisfies

    R_unused(nu)+sum_(d in M) r_d*q_d(nu)
       <=log(H(U)/(alpha7-c)),
    q_d(nu)=max_a nu([a]_d).                          (PR5)

The countable sum is the supremum of its finite subsums. The r_d and C were fixed before passing through finite query sets. This is a simultaneous all-depth law, without a separate favorable measure for each label. Setting every r_d=0 proves(PR2).

## A finite inventory of remaining occupied labels

For a numerical cutoff B define the complete reciprocal tail

    tau_P(B)=sum_(d>B, P-smooth)1/d
      =product_(p in P)p/(p-1)-sum_(d<=B, P-smooth)1/d.

The finite sum here includes the unit label; all query sums exclude it. Set r_d=1 for actual occupied d>B and zero for the others. Then c<=tau_P(B). Whenever beta_B=alpha7-tau_P(B)>0,(PR5) gives one law with

    R_unused(nu)+sum_(d in M,d>B)q_d(nu)
       <=log(H(U)/beta_B)<=-log(beta_B).              (PR6)

At B=10^9, the exact finite inventory contains15524 nonunit P-smooth labels, and

    tau_P(B)=0.000004930123186154228364479541535...,
    beta_B=0.001186173667595738775750746795913...,
    -log(beta_B)=6.737022557764285813862807900996...<6.737023.
                                                               (PR7)

The full tails are calculated by the Euler product minus the exact finite sum, not by truncating an infinite series without a remainder bound.

Let T=565/51. A sufficient remaining task is to choose a law in the nonempty set specified by(PR6) such that

    sum_(d in M,d<=B)q_d(nu)<T+log(beta_B)
       =4.341408814784733793980329353905... .          (PR8)

Both sums must use this same nu. This is a sufficient route to R_P<T, not an equivalent reformulation imposing no additional restriction on candidate laws. The remaining objective uses a fixed finite inventory of numerical labels; U and the admissible common-law set still depend on all original classes at arbitrary finite heights. No uniform finite-state algorithm follows from the cutoff alone.

## Necessary joint correlations for a finite dual certificate

Suppose a finite query system J and its fixed phase weights satisfy

    f(x)=sum_(d in J)w_d(x)>=T for every x in U.

Write O_B=J intersect M intersect{d<=B}, h=sum_(d in O_B)w_d and g=f-h. Applying(PR3) with replacement probability one on the queried occupied labels above B yields

    beta_B<=integral_U exp(-g)
           <=exp(-T)*integral_U exp(h).

Thus, with U_B the survivor of all actual original classes at labels at most B,

    integral_(U_B)exp(h)>=integral_U exp(h)
                         >=beta_B*exp(T)>384/5.       (PR9)

The threshold384/5=76.8 is certified with exact positive Taylor sums. Every factor retains the same theta; this is a joint moment requirement, not a product of separately optimized bounds.

There is also a second-order consequence. Set q=69/20 and a=T-q=7781/1020. For E={x in U:h(x)>q}, the preceding lower bound on integral_U exp(-g) gives

    H(E)>=beta_B-exp(-a)>0.

For numbers in[0,1] with sum greater than3+9/20, the smallest possible pair sum is strictly greater than3+3*(9/20)=87/20. This follows by concentrating all but at most one of the numbers at0 or1 while keeping their sum fixed. Therefore

    sum_(d<e, d,e in O_B) sum_(a mod d,b mod e)
      theta_(d,a)*theta_(e,b)*H(U intersect[a]_d intersect[b]_e)
       >1/329.                                       (PR10)

Replacing U by U_B preserves this inequality. The index set is exactly the shallow occupied labels in the finite query system, so every theta displayed is defined. The constant follows from

    (87/20)*(beta_B-1/S50(7781/1020))>1/329,
    S_n(x)=sum_(j=0)^n x^j/j!<exp(x), x>0.

(PR9)–(PR10) are necessary for a finite dual system meeting the stated pointwise threshold. They do not assert that an infinite critical value R_*=T automatically has a finite dual certificate attaining T.

The [arithmetic consumer](../../frontier/cover-geometry/phase_resampling_arithmetic.py) and [exact data](../../frontier/cover-geometry/phase_resampling_arithmetic.json) retain the exact tail and Taylor certificates for(PR7),(PR9),(PR10). The consumer checks only those arithmetic implications; the legal-resampling, minimax and compactness arguments are the ordinary proof above.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/phase_resampling_arithmetic.py
```

## The same common law can also retain a density bound

The finite minimax step has a constructive variational refinement.
Keep the same original U, replacement probabilities r_d, beta and finite
query inventory J. Set h=H(U)>0, rho=H|U/h, and define

    Z(theta)=integral_U exp(-g_theta) dH>=beta.

The finite product of phase simplexes is compact, and Z is differentiable
and convex on it. Choose a minimizer theta_star and set

    dnu_star/dH=1_U*exp(-g_theta_star)/Z(theta_star).

Since g_theta_star>=0, this probability has density at most1/beta.
For every feasible theta, the right derivative toward theta at a minimum
is nonnegative:

    -Z(theta_star)*E_nu_star(g_theta-g_theta_star)>=0.

Thus theta_star maximizes the linear query payoff under this same
nu_star. Its expected payoff is exactly the finite weighted sum of
labelwise cylinder maxima. The relative entropy identity gives

    R_weighted,J(nu_star)+KL(nu_star || rho)
       =log(h/Z(theta_star))<=log(h/beta).            (GD1)

In particular this obtains the query bound and density bound on one
probability, rather than combining estimates from different measures.

Pass to all finite query inventories inside the compact set of
probabilities supported on U and dominated by H/beta. Domination is
closed in the weak topology; each finite query sum is continuous, and
relative entropy to rho is lower semicontinuous. Unions of finite query
inventories again give the finite intersection property. Consequently
one all-depth probability satisfies

    nu<=H|U/beta,
    R_weighted(nu)+KL(nu || rho)<=log(H(U)/beta).      (GD2)

Only the inequalities are passed to the limit. This does not assert an
infinite phase minimizer, a global Gibbs formula, or a positive density
lower bound for this limiting nu.

### Pay the deep occupied labels under that same density bound

Take r_d=0 for every occupied label, so beta=alpha7 and
Lambda7=1/alpha7. The same law then satisfies

    R_unused(nu)+KL(nu || rho)<=log(H(U)/alpha7),
    nu<=Lambda7 H.

Each occupied deep label costs at most Lambda7/d, so

    R_unused(nu)+sum_(d in M,d>B)q_d(nu)+KL(nu || rho)
       <=log(H(U)/alpha7)+Lambda7*tau_P(B).           (GD3)

For B=10^9, its uniform right side is at most
log(Lambda7)+Lambda7*tau_P(B)=6.737013967890102... .
It is strictly smaller than the earlier uniform cost -log(beta_B),
because x<-log(1-x) for x=Lambda7*tau_P(B) in(0,1).
This improvement uses the newly constructed density bound, not an
inheritance assertion about the arbitrary minimax law of(PR5).

### Restore full survivor support with a fixed mixture

Let mu be report467's one all-depth law for this same actual family:

    (1/5)H|U<=mu<=Lambda7 H,
    R_P(mu)<=70871/3375.

Set epsilon=1/10^7 and nu_hat=(1-epsilon)*nu+epsilon*mu. Convexity of
each cylinder maximum and the common density cap give

    (1/50000000)H|U<=nu_hat<=Lambda7 H,
    R_unused(nu_hat)+sum_(d in M,d>B)q_d(nu_hat)
      <=(1-epsilon)*log(Lambda7)
           +epsilon*(70871/3375)+Lambda7*tau_P(B)
       <842127/125000=6.737016.                      (GD4)

Thus the complete actual survivor support, both density inequalities,
and the combined query estimate belong to this single mixed law. There
is no claim that the mixture retains the original joint entropy budget
in(GD2).
The remaining shallow occupied-label contribution still has to be
controlled under the same nu_hat or another single law satisfying the
required joint budgets; neither construction settles that step.

For the strict arithmetic in(GD4), x0=53863/8000=6.732875 satisfies
alpha7*S50(x0)>1 and hence log(Lambda7)<x0. Substitution gives

    A_epsilon=(1-epsilon)*x0+epsilon*(70871/3375)
                   +Lambda7*tau_P(B)<842127/125000.

The [Gibbs-mixture consumer](../../frontier/cover-geometry/phase_resampling_gibbs.py)
and [exact bounds](../../frontier/cover-geometry/phase_resampling_gibbs.json)
consume the pinned alpha7 and reciprocal tail from(PR7). They check the
Taylor direction, mixture coefficient and strict rational margin;
the variational and compactness arguments are the ordinary proof above.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/phase_resampling_gibbs.py
```

## A finite sufficient certificate with an explicit original-tail payment

The cutoff alone does not make the complete original survivor finite in
height. A density bound does permit a quantitative transfer from a law
constructed using only the shallow original family. This gives a separate
sufficient route to the total query target; it does not assert that the
Gibbs law already has the missing shallow bound.

Fix B>=19 and D>0 with D*tau_P(B)<1. For the same actual original family
let M_B={d in M:d<=B}, and let U_B be the survivor of exactly those
original classes, with their actual phases. Suppose a probability mu_B
supported on U_B has

    mu_B<=D H,                 R_P(mu_B)<=r.

Numerical distinctness and the union bound give

    mu_B(U_B minus U)
       <=sum_(d in M,d>B)mu_B(C_d)
       <=D*sum_(d in M,d>B)1/d
       <=delta_B=D*tau_P(B)<1.                       (FT1)

Condition this one law on the complete original survivor U. The resulting
probability nu=mu_B|U/mu_B(U) satisfies simultaneously

    nu<=D/(1-delta_B) H|U,
    R_P(nu)<=r/(1-delta_B).                          (FT2)

Indeed each cylinder probability is at most its mu_B probability divided
by mu_B(U); take each maximum and then the nonnegative all-label sum.
No deep original class is replaced by a projected shallow class. Its
actual full phase is used in U and paid in(FT1). Nor are query costs from
different probabilities combined.

### The shallow density-constrained optimum is an exact finite LP

Set

    L_B=lcm{d: d<=B, d is P-smooth},
    k_p=max{k: p^k<=B},
    C_D(U_B)=inf{R_P(mu): mu(U_B)=1, mu<=D H}.

Assume this set is nonempty. Averaging any feasible mu over Haar
translations in the kernel of reduction modulo L_B preserves U_B,
total mass and the density bound. For every numerical query label d,
translation only permutes its residue classes, and convexity of the
maximum gives

    q_d(averaged mu)<=q_d(mu).                       (FT3)

Thus Haar averaging decreases the full nonnegative query sum. The
averaged law is the Haar-tail extension of a probability v on Z/L_B Z.
The feasible v form a compact finite polytope. The complete-tail identity
already used in [report475](475-two-center-density-and-query-bounds-lose-original-survivor-realizability.md#exact-all-depth-tail-sum)
gives, with q_1(v)=1,

    1+R_P(v extended by Haar)
       =sum_(c divides L_B) w_B(c)*q_c(v),
    w_B(c)=product_(p: v_p(c)=k_p) p/(p-1).           (FT4)

For completeness, if c=gcd(d,L_B), each descendant query cylinder has
probability (c/d) times the corresponding c-cylinder probability. Hence
q_d=(c/d)q_c. Summing these factors over all d with the same gcd gives
w_B(c). This retains all query labels above B, including labels not
dividing L_B; they are not discarded or counted as one unweighted label.

Consequently C_D(U_B) is the minimum of the rational linear program

    minimize sum_(c divides L_B)w_B(c)*y_c - 1
    subject to
      0<=v_x<=D/L_B,                sum_x v_x=1,
      v_x=0 for x outside U_B mod L_B,
      y_1=1,
      y_c>=sum_(x=a mod c)v_x       for every c|L_B and a mod c.
                                                               (FT5)

Here D is rational for a rational LP. The minimum exists; all weights
are positive, so each y_c can be taken equal to the indicated maximum.
Together(FT1)--(FT5) give a finite sufficient certificate for every
arbitrary-height extension of a fixed shallow family. They also give

    C_D(U_B)<=C_D(U),
    C_(D/(1-delta_B))(U)<=C_D(U_B)/(1-delta_B),

where an infeasible density-constrained infimum is interpreted as
infinity. The first inequality alone keeps the same density cap; the
upper transfer explicitly permits its inflation.

### A fixed numerical target for the finite certificate

For B=10^9 and D=Lambda7, report467 guarantees feasibility for every
shallow original family. The retained reciprocal-tail data give

    delta_B=0.004139121396732251436452023947...,
    T*(1-delta_B)=11.032576400212672116439306009...,
    D/(1-delta_B)=843.046871902750045312006602... .

In particular, the following finite hypothesis would suffice:

    For every choice of absent or one fixed residue at each nonunit
    P-smooth numerical label d<=10^9,
           C_Lambda7(U_B)<=1103257/100000=11.03257.   (FT6)

Under(FT6), condition its minimizing law on the actual full U and mix
epsilon=1/10^7 of report467's full-support law for that same U. Then

    R_P(nu_hat)
      <=(1-epsilon)*11.03257/(1-delta_B)
             +epsilon*(70871/3375)
       <565/51,
    H|U/50000000<=nu_hat<=D_hat H,       D_hat<844.

The strict query margin exceeds0.0000054. This
mixture makes no claim to the separate Gibbs entropy budget(GD2).

The unresolved hypothesis(FT6) is genuinely finite: its periods and
constraints depend only on the fixed shallow labels, not on the deeper
original phases or heights. But its direct period has61 decimal digits:

    (k_3,k_5,k_7,k_11,k_13,k_17,k_19)=(18,12,10,8,8,7,7),
    L_B=1713598183708474921576632438503877316470966933909293701171875,
    number of divisors of L_B=14084928.

No LP in(FT6) has been solved here, and no efficient enumeration or
compressed representation of all shallow original phase patterns is
established. This is a density-constrained sufficient route, not an
equivalence with the unrestricted supported-law optimum. Failure of(FT6)
would not refute the seven-prime query target or Erdős#7.

The [tail-transfer arithmetic](../../frontier/cover-geometry/phase_resampling_finite_transfer.py)
and [result](../../frontier/cover-geometry/phase_resampling_finite_transfer.json)
consume the retained alpha7 and reciprocal tail, compute the finite
period dimensions, and check the strict conditional query and density
bounds. They do not enumerate shallow families or solve the LP.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/phase_resampling_finite_transfer.py
```

## Actual joint coverage gives a smaller replacement charge

Keep the full actual original family M and its globally fixed classes
C_d. For every S subset M define its exact covering cell

    E_S={x: {d in M:x in C_d}=S},
    U=E_empty.

Fix r in[0,1]^M before varying any finite query inventory or phase
mixture. The joint leakage bound is

    L(r)=sum_(nonempty S subset M) H(E_S)*product_(d in S)r_d
         <=sum_(d in M)r_d/d.                        (JL1)

For beta=alpha7-L(r)>0, the existing Gibbs argument gives one probability
on the same full U with

    nu<=H|U/beta,
    R_unused(nu)+sum_(d in M)r_d*q_d(nu)+KL(nu||H(.|U))
       <=log(H(U)/beta).                             (JL2)

This applies the finite coverage/reliability polynomial to the existing
resampling construction; it is not a new general reliability theorem.

### Every covering original must be replaced

For a finite query set J write O=J intersect M and F=J minus M. At
x in E_S, an original covering label outside O prevents survival. If
S is contained in O, the exact averaged survival probability is

    product_(d in S) r_d*(1-w_d(x))
      *product_(d in O minus S)(1-r_d*w_d(x))
      *product_(d in F)(1-w_d(x)).                    (JL3)

For nonempty S this is at most product_(d in S)r_d. Thus the exterior
survivor mass is at most the part of(JL1) with S subset O, and hence at
most L(r), uniformly in J and theta. The inside-U product remains the
one in(PR3). Averaging the same legal-family mass bound and subtracting
this exterior bound gives the exponential lower bound used in(GD1),
with beta=alpha7-L(r). That beta and the vector r are fixed throughout
the finite-query compactness step, proving(JL2).

Equivalently, L(r) is exactly the expected newly surviving Haar mass
after independently deleting original d with probability r_d, before
installing any replacement classes. Replacement phases can only lower
that mass. The exact phase-dependent exterior mass is(JL3), not L(r).

In particular, replacing just one label d costs its actual private mass
times r_d. Simultaneous replacements require the higher-order terms.
For the actual nested originals0 mod3 and0 mod9,

    L(r_3,r_9)=(2/9)r_3+(1/9)r_3*r_9.

Replacement phases1 at both labels miss the whole old union, so this
is the exact exterior leakage. Omitting the quadratic term is false.
For the disjoint originals0 mod3 and1 mod9, replacement phases2 at both
labels instead give exact leakage r_3/3+r_9/9. Thus the old bound can be
attained; oddness and numerical distinctness alone do not imply a
uniform strict saving.

### Partial replacement of a fixed block

Let A be a subset of original labels and V the survivor of the retained
originals M minus A. Take r_d=s on A and zero outside it. Put

    a_k=H({x in V: exactly k originals in A cover x}),
    delta_A=H(V)-H(U)=sum_(k>=1)a_k.

Then, for0<=s<=1,

    L_A(s)=sum_(k>=1)a_k*s^k
           <=a_1*s+(delta_A-a_1)*s^2.                (JL4)

The coefficient a_1 is the sum of the full-family private masses of
the labels in A. At s=1 the cost is delta_A, the region newly exposed
by deleting the entire block. If delta_A=0, these occupied labels can
receive query weight one at zero leakage. This zero-cost case also
follows by applying(PR2) to the smaller family with exactly the same U;
it does not allow simultaneous deletion of individually redundant
labels whose joint deletion changes U.

A separate low-order upper bound is

    L(r)<=sum_d H(E_{d})*r_d
             +sum_(d<e)H(C_d intersect C_e)*r_d*r_e.  (JL5)

Here E_{d} denotes E_{ {d} }. For a point covered by at least two
originals, its product of all replacement probabilities is no greater
than the sum of pair products at that point. Integrate this inequality;
no independence of the original covering events is assumed. Actual
intersection masses equal zero for incompatible residues and otherwise
1/lcm of the original labels. Exclusive masses retain all remaining
original constraints, so their computation can still involve arbitrary
finite original heights.

### A joint sufficient query budget and its full-replacement limit

Take A=M intersect{d<=B}, fix0<s<=1 and certify ell(s)>=L_A(s) with
ell(s)<alpha7. Write beta_s=alpha7-ell(s), m=H(U), and

    a_deep=sum_(d in M,d>B)1/d,
    f_0=sum_(d unused, d>1, P-smooth)1/d
        =product_(p in P)p/(p-1)-1-sum_(d in M)1/d.

The same Gibbs law has R_unused>=f_0 and occupied-deep cost at most
a_deep/beta_s. Rearranging(JL2) therefore gives

    R_P(nu)+KL(nu||H(.|U))/s
      <=[log(m/beta_s)-(1-s)*f_0]/s+a_deep/beta_s.    (JL6)

A bound strictly below T on this right side suffices for the total
query target. All terms concern this one probability. A weaker
certificate may use m<=1 and a_deep<=tau_P(B). More generally, for any
fixed vector r with beta=alpha7-L(r)>0,

    R_P(nu)+KL(nu||H(.|U))
      <=log(m/beta)+sum_(d in M)(1-r_d)/(beta*d).      (JL7)

The cylinder payment1/(beta*d) can be reduced to
min(1,max_a H(U intersect[a]_d)/beta) under the same law. No estimate
showing that(JL6) or(JL7) crosses T for every original family is proved.

[Report531](531-fixed-cardinality-resampling-beyond-the-uniform-leakage-bound.md)
closes the uniform-s independent branch of(JL6): with its stated
reciprocal-tail payment, it never improves the elementary
uniform-survivor range h>A/T. The same report gives a different joint
sampling rule, selecting a fixed number of labels per block, that
preserves the Gibbs interface with a smaller hypergeometric leakage
charge. [Report532](532-fixed-quota-and-reciprocal-payment-obstructions.md)
also excludes the resulting uniform fixed-quota scalar certificate and
the full reciprocal-density payment in(JL7), including nonuniform
marginals. Actual survivor-cylinder payments and phase-sensitive
estimates remain unresolved.

Even computing the exact covering cells does not make full replacement
of all shallow labels automatically feasible. At s=1 let U_deep be
the survivor of only the original labels above B. Then

    L_A(1)=H(U_deep)-H(U)>=1-tau_P(B)-H(U).

Thus positive beta requires

    H(U)>1-alpha7-tau_P(B).                           (JL8)

If any actual original label d has1/d>=alpha7+tau_P(B), the bound
H(U)<=1-1/d already excludes positive beta for this choice. This is a
limitation of the full-shallow, phase-free leakage bound. Partial
replacement, a smaller block or a bound retaining the phase factors in
(JL3) is not excluded.

## Irredundant shallow originals can pass both moment tests with query cost below3

The exponential and pair conditions(PR9)--(PR10) cannot be closed by
unconditional opposite moment bounds, even after requiring every original
class to have a private integer. The following actual family admits a
full-support law within the Gibbs unused-plus-entropy budget and with
total all-depth query cost below3, while one fixed query phase choice
passes both necessary moment thresholds by a wide margin.

For each three-element S subset P, take the original class

    C_S=[0]_(d_S),       d_S=product_(p in S)p.

There are35 distinct odd numerical labels, all greater than1 and at
most13*17*19=4199. Each has a private CRT integer: set the first roots
to0 at the primes in S and1 at all other primes. A different
three-element subset contains a prime outside S, so its original class
does not contain this integer. The family is irredundant on its union.

Its complete survivor and mass are

    U={x: at most two p in P have x=0 mod p},
    L=product_(p in P)p=4849845,
    L*H(U)=sum_(Z subset P, |Z|<=2)product_(p notin Z)(p-1)
           =4608000,
    H(U)=307200/323323.                               (IM1)

The count has29 terms. There is no chosen subset of survivors in(IM1).

Query precisely these35 occupied labels, always at phase1. All query
phases differ from their own forbidden original phase0. With k(x) the
number of first roots equal to1, the same query load is

    h_theta(x)=sum_(d in M)1_[1]_d(x)=binomial(k(x),3).

The all-one root cylinder lies in U, has Haar mass1/L and load35.
Since exp(1)>2,

    integral_U exp(h_theta)dH
       >=exp(35)/L>34359738368/4849845>7000>384/5.     (IM2)

For the same phases, consider root vectors with exactly five roots
equal to1. Their remaining two roots can be any non-1 values; such a
vector has at most two zero roots and lies in U. There are

    sum_(p<q in P)(p-1)(q-1)=1872

such vectors, each with10 simultaneous queries and hence45 query
pairs. Therefore

    sum_(d<e in M)H(U intersect[1]_d intersect[1]_e)
       >=45*1872/L=432/24871>1/329.                  (IM3)

Nevertheless the probability rho=H|U/H(U) has full support on U and,
for every P-smooth numerical query label at arbitrary depth,

    q_d(rho)<=1/(d*H(U)).

The complete geometric product then gives, on this one law,

    R_P(rho)
      <=[product_(p in P)p/(p-1)-1]/H(U)
       =68780825113/33973862400<3,
    d rho/dH=323323/307200 on U.                     (IM4)

This includes all higher query depths. Relative entropy to the uniform
law on U is zero for rho itself. Also H(U)/alpha7>27>exp(3), so

    R_unused(rho)+KL(rho||H(.|U))<3<log(H(U)/alpha7).

It also has density below Lambda7 and combined unused-plus-deep cost
below3. Thus the example belongs to the same constrained class in which
the shallow-label solution is being sought.

The missing condition is the pointwise dual premise: the actual survivor
x=2 has h_theta(2)=0. These phases do not satisfy f>=T throughout U.
Conditions(PR9)--(PR10) remain necessary for such a dual; the example
shows that those moments alone, even with irredundancy and nonoriginal
query phases, are not sufficient obstructions to a good common law.
It refutes the proposed universal shallow exponential-moment ceiling,
not the seven-prime query target or Erdős#7.

The [fixed counterexample checker](../../frontier/cover-geometry/irredundant_shallow_moment_obstruction.py)
and [exact data](../../frontier/cover-geometry/irredundant_shallow_moment_obstruction.json)
retain all35 original labels and their private integers. The1225
private-point/class checks, the29-term survivor count, and the strict
rational inequalities passed. The complete period was not enumerated;
the ordinary proof establishes the all-depth implications. No Lean
verification is claimed.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/irredundant_shallow_moment_obstruction.py
```

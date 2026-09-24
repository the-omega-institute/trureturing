# One supported law controls unused and deep occupied query labels

For P={3,5,7,11,13,17,19}, [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) implies the uniform actual-survivor bound

    H(U)>=alpha7=7235955529/6075000000000.              (PR1)

Here every original family is finite, has pairwise distinct nonunit P-smooth numerical moduli, and has one arbitrary globally fixed residue per modulus. H is normalized Haar on the full P-adic product, and U is its complete actual survivor. The bound follows by integrating report467's supported probability with density at most1/alpha7. In particular(PR1) applies to every other finite family satisfying these same numerical-label rules.

Legal replacement and addition of classes give a different common-law conclusion. There is one probability nu supported on U for which the sum of maximum cylinder probabilities over every unused numerical label is at most

    log(H(U)/alpha7)<=log(1/alpha7)<27/4.              (PR2)

The fixed mixture below controls all unused labels and all occupied labels above10^9 with total query sum below6.737016, while retaining density at most Lambda7 and full actual survivor support. The Gibbs refinement and fixed mixture below establish these bounds simultaneously. Controlling the remaining occupied labels under that same law is unresolved. These statements are ordinary proofs using(PR1), finite minimax and compactness; they are not new Lean results or an unrestricted Erdős#7 resolution.

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

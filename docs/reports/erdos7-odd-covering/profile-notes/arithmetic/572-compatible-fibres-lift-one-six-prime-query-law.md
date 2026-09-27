# A bounded residual-overlap class admits a fixed-conditional lift

For P={3,5,7,11,13,17,19}, put Q=P\{3}. A finite actual family has one globally fixed residue for each pairwise distinct odd nonunit P-smooth numerical modulus. Pure3 originals may have arbitrary finite heights. For every nonunit numerical Q-cofactor d, choose a single fixed set A_d of at most two projected residues that contains all projections of its originals 3^e d with 0<=e<=3. Only the finite actual cofactor inventory may have nonempty A_d. Let V be the Q-survivor of all these selected classes.

For x in V, call a cofactor d active if some actual original 3^e d, e>=4, has an unselected projected phase matching x modulo d. Assume that AT EACH SAME x in V at most two distinct numerical cofactors are active. The active set may vary with x, but all originals and all selected A_d were fixed globally. This is a condition on actual Q-cylinder incidence, not on prime-support size or separately selected favourable phases.

Under these hypotheses, the complete actual survivor U admits one probability in C_u(U), where u is normalized Haar on the complete actual pure3 survivor, with

    R_P <= B+(27/25)(1+B)
        =6199418183523781383463/539719033471556471250
        =11.486380503663476... <566/49,              (FS1)

    B=432040125182653876501/86355045355449035400.

Every original height, every complete numerical query label and its maximizing phase remain included. The result permits arbitrary Q-only originals; they enter the selected Q family. It is ordinary mathematics using [Report569](569-complete-suffix-debits-close-the-six-prime-query-target.md)'s existing two-copy supplier, not a new Lean result or a claim about unrestricted P-families.

## 1. A compatible-fibre lift preserves the pure-Q query contribution

Take ANY actual survivor mask chi(t,x), the fixed source u on its pure3 survivor, and a probability nu on Q. Let

    c(x)=integral chi(t,x) du(t).

Suppose c(x)>=c0>0 for nu-almost every x. Define the single joint law

    mu(dt,dx)=chi(t,x)u(dt)nu(dx)/c(x).             (FS2)

Its Q marginal is exactly nu. Its ternary conditional at x is precisely u restricted to U_x and normalized; hence mu belongs to the fixed-conditional class C_u(U).

This is also an actual product/deletion construction. Let

    Z=integral 1/c(x) dnu(x),
    w(dx)=nu(dx)/(c(x)Z).

Then 1<=Z<=1/c0, w is one probability, and restricting u times w to U gives raw mass1/Z. Normalizing gives exactly FS2. Here nu is the target Q marginal; w is the raw prior. No raw prior is substituted separately for different queries.

Let q_m be the maximum probability of a residue cylinder at numerical modulus m. For a>=1 and Q-smooth d>=1,

    q_(3^a d)(mu)<=q_(3^a)(u) q_d(nu)/c0.

Indeed, for every pair of phases r,b, the defining integral is at most
u([b]_d)u([r]_(3^a))/c0. This uses no independence assertion about mu. For a=0 the nonunit queries are exactly the Q-marginal queries. Nonnegative summation therefore gives the general bound

    R_P(mu)<=R_Q(nu)
              +[R_3(u)/c0](1+R_Q(nu)).             (FS3)

The unit Q cofactor d=1 occurs once for every a>=1; the global unit is excluded. All positive ternary heights are included in R_3(u). Since the complete pure3 forbidden Haar mass is at most sum_(e>=1)3^(-e)=1/2, the actual normalized pure3 source satisfies

    u([r]_(3^a))<=2·3^(-a), R_3(u)<=1.              (FS4)

The improvement over dividing an entire product query budget by c0 is substantive: pure-Q queries retain the same marginal and receive no 1/c0 multiplier. The bad-fibre examples in Report571 do not satisfy the quantitative reserve c(x)>=25/27 used below. Their much smaller positive fibre minima give only weaker bounds in FS3; no good-lift assertion follows from R_Q alone.

### Unequal fibres can be retained as a query profile

The pointwise minimum is a sufficient simplification, not the complete
boundary. For any positive Q-measure eta write

    C_Q(eta)=sum_(d Q-smooth,d>=1) q_d(eta),
    r_a(x)=max_r u([r]_(3^a) intersect U_x)/c(x),
    m_a=max_r u([r]_(3^a)).

The same one-law cylinder calculation before replacing c(x) by c0 gives

    R_P(mu)<=R_Q(nu)+sum_(a>=1) C_Q(r_a nu)
            <=R_Q(nu)+R_3(u) C_Q(nu/c).             (FS3a)

Indeed a fixed joint cylinder integrates one conditional probability,
which is at most r_a(x) in that Q-cylinder. Take its Q maximum and sum.
The second bound uses r_a(x)<=min(1,m_a/c(x)) and the positive
homogeneity of C_Q. Infinite nonnegative sums are legitimate; the
bound is useful when its right side is finite.

More explicitly, partition the chosen Q support into finitely many
sets S_j with c(x)>=k_j>0 on S_j. The query maximum is subadditive,
so with nu_j=nu restricted to S_j,

    R_P(mu)<=R_Q(nu)+sum_j G(k_j) C_Q(nu_j),
    G(k)=n+1/(k*3^n), n=floor(log_3(2/k)), 0<k<=1.  (FS3b)

To obtain G, bound r_a by min(1,2/(k*3^a)). Its first n terms are1;
its complete geometric tail sums to1/(k*3^n). This preserves all
heights and all strata in one law. No general bound on the stratum
query costs is claimed. FS7 below uses the uniform special case whose
compatibility premise follows from actual numerical-label incidence.

## 2. Numerical-label uniqueness bounds each active tail

More generally, fix integers h>=0 and M>=0. Suppose the globally selected A_d contain every actual Q projection at ternary exponents0 through h. For x in the selected survivor V, every unmatched mixed original has e>h. By numerical distinctness there is at most one original with each exact pair (d,e). Consequently the complete forbidden ternary union for ONE active d has u-mass at most

    sum_(e>h)2·3^(-e)=3^(-h).                       (FS5)

This holds with arbitrary ternary phases and arbitrary finite heights; distinct ternary cylinders need not be disjoint. If at most M distinct d are active at this same x, the union bound on its actual ternary fibre gives

    c(x)>=1-M3^(-h).                               (FS6)

Pure3 classes have already been removed in u. Every e=0 Q-only original is selected and thus absent on V. Originals with a selected projected phase are absent at EVERY height on V. No original label, phase, or common source has been changed.

The selected Q family has at most two classes per nonunit numerical cofactor. Report569 SD1 supplies ONE probability nu supported on V with R_Q(nu)<=B. Apply FS2 to this same nu and the COMPLETE actual mask. If c0=1-M3^(-h)>0, FS3 and FS4 give

    R_P(mu)<=B+(1+B)/(1-M3^(-h)).                   (FS7)

Thus a sufficient numerical condition is

    M3^(-h)<1-(1+B)/(566/49-B)
             =2305626180867071404702
                /27706989537234114087851
             =0.08321460466748469... .             (FS8)

The old entire-budget conditioning criterion instead permits only

    delta<1-49(1+2B)/566
          =0.04717204967465627... .

For h=3,M=2, c0=25/27 and FS1 follows. The old bound at this same worst-case reserve is (1+2B)/(25/27)=11.886625907650533..., which fails the gate. This is a comparison of sufficient estimates at the class-wide reserve, not a claim that some actual family attains the worst-case deletion or that Report569's actual weighted test fails on every member.

### Retaining the actual pure-3 mass

Let w3=H3(S3) for the complete actual pure-3 survivor. Instead of
replacing w3 by1/2, use

    R_3(u)<=1/(2w3),
    c(x)>=1-M/(2w3*3^h).

Whenever the latter reserve is positive, the same proof gives

    R_P(mu)<=B+(1+B)/(2w3-M*3^(-h)).                (FS8a)

In particular, if the actual family has no pure-3 original, then
w3=1. Choose A_d to be exactly its actual exponent0 and exponent1
projections. There are automatically at most two, because the full
numerical labels are distinct. If every x in V activates at most
three distinct residual numerical cofactors at exponents e>=2, then
h=1, M=3, c0=1/2, and

    R_P(mu)<=1+2B
      =475217647860378394201/43177522677724517700,
    566-49R_P(mu)>=1152813090433535702351
                         /43177522677724517700>0.  (FS8b)

Q-only originals and all remaining phases and finite heights are
allowed subject to that same pointwise incidence premise. A global
bound of three mixed numerical Q cofactors is a sufficient special
case. Absence of pure-3 originals does not imply the incidence bound.
This corollary supplies a common-law continuation certificate; no
larger support-free conclusion is asserted.

## 3. Arbitrary pure23/29 continuation

The same Report569 supplier also has density nu<=Lambda_Q H_Q,

    Lambda_Q=9/alpha_min,
    alpha_min=7575003978548161/73724315753088000.

By FS2, mu<=2Lambda_Q H_P/c0. Independently condition the23 and29 coordinates on their complete actual pure-power survivors. All additional mixed originals touching23 or29 retain arbitrary fixed phases, arbitrary P-smooth cofactors and arbitrary finite heights.

Report569 SD15–16's actual pure-coordinate common-law count gives the remaining probability at least

    [566-49R_P(mu)]/567.

The pure-coordinate density factors are22/21 and28/27. Combining these with the SAME mu and FS1 yields the actual nine-prime Haar lower bound

    H(U_extended)>=
      [566-49 FS1] c0 alpha_min/11088
      =1709481952235674937813
         /62903178645754948300800000
      =0.000027176400128565523... >1/37000.           (FS9)

The law FS2 is supported on U, but can omit genuine surviving fibres outside V. This does not assert that the final extended conditioned law retains the core query cap or fixed-conditional description. Positivity and finite CRT give an actual uncovered integer for every family in the stated class.

## 4. Concrete actual-family witness to the expanded structural scope

The ten fixed originals are supplied by the following CRT data:

- Pure3: 2 mod3.
- At d=5 and at d=7, use exponents e=0,1,4,5 with Q phases0,1,2,3 respectively, and ternary phase0 whenever e>0.
- Q-only triple: 2 mod385.

Choose A_5=A_7={0,1}, A_385={2}. The only residual active cofactors are5 and7, hence the pointwise count is at most two. The e=4 and e=5 originals give a third and fourth projected phase at each small cofactor, so this example is outside Report569 SD21's through-five finite-window class. The modulus385 original is essential and Q-only, so it is outside Report547's star support class, Report561's all-three-rooted class and Report570's allowed non3 pair support class. The independent program finds private witnesses for all ten originals on the true period93555; no redundant Q-only ornament is being used to claim a larger scope.

For this selected Q family the actual PA supplier is explicit. The allowed mod5 roots2,3,4 and mod7 roots2,...,6 are uniform. At11, the pair of previous roots(2,2) excludes11-root2 and renormalizes its other ten roots; the other pairs keep all eleven roots uniform. Later Q coordinates are Haar. On the allowed385-cells this gives weights1/150 for the special pair and1/165 otherwise. It is one supported probability. Its inverse-reweighted raw prior and complete actual fibre lift are calculated without an LP.

Exact complete-query summation, including geometric tails beyond the resolved heights, gives for this example

    R_P(mu)=6621447999031/2123283456000
           =3.1184946034030605... .                 (FS10)

This small example verifies the construction and separates structural classes. It is not a sharpness example for FS1, and some members, including this example, can also pass Report569's more general actual weighted-residual test. The new uniform conclusion is FS7–FS8 for the bounded-overlap class, rather than a claim that none of its members had other certificates.

## 5. Relation to earlier results and remaining boundary

- Report530's unrestricted-law LP and density transfers do not impose the fixed ternary conditional. FS3 gives an explicit supported lift with a new quantitative compatibility premise, without solving that LP.
- Report547 already places all stars in C_u(U) via uniform Haar conditioning; that result is reused as context, not reproved. The current class admits essential Q-only triple and larger supports.
- Report561's arbitrary rooted-support construction does not in general preserve the stipulated ternary conditional. No transfer of its law into C_u(U) is assumed here. The two structural classes overlap but neither contains the other.
- Report569 supplies the entire six-prime law. Its two-phase-through-five class allows unlimited residual activation; the current class needs phases only through-three but controls residual activation at each actual Q point. Neither structural hypothesis implies the other. The weighted actual-loss criterion from that report remains valid and can overlap this new class.
- Report570 permits certain non3 pairs and rooted triangles under a different joint law. The essential Q-only triple in the explicit example excludes inclusion in its support class.
- Report571 proves that R_Q alone cannot guarantee a good lift. Here the SAME supplied marginal is coupled to the actual fibres by c(x)>=25/27; this is the missing compatibility premise made quantitative. A family with many simultaneously active residual cofactors need not satisfy it.

No bound is proved on residual activation for an arbitrary actual family.
[Report574](574-four-level-query-hinge-removes-pointwise-overlap.md)
replaces the pointwise premise by a same-law positive-part moment and
adjusts the marginal, provided two phases cover exponents0 through4.
[Report575](575-periodic-cofactor-selector-rebuilds-a-compatible-marginal.md)
instead derives the pointwise bound from a periodic selector on a
two-coordinate exponent antichain with three globally coherent tail
phases. Neither result resolves arbitrary shallow multiplicities and
arbitrary tail-phase geometry.

## Reproducibility

The [exact producer](../../frontier/cover-geometry/compatible_fibre_overlap_lift.py)
and its [data](../../frontier/cover-geometry/compatible_fibre_overlap_lift.json)
validate the rational gates and nine-prime density conversion, all ten
original phases and private witnesses, pointwise activation, the
explicit PA Q-law, inverse raw prior, and exact all-height query norm.
It uses only the Python standard library and preserves its checks
under optimization:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/compatible_fibre_overlap_lift.py

The arbitrary-family conclusion is FS2–FS8, not an inference from the
finite example. The general fibre-profile inequalities FS3a–b are
ordinary nonnegative-sum arguments. No new Lean verification is claimed.
No large-prime tail extension is asserted: this Haar bound alone is
smaller than the retained two-million-cutoff charge in Report570.

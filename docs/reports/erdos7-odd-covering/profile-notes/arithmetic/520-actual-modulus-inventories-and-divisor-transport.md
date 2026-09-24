# Actual modulus inventories and divisor transport preserve noncoverage

Let P={3,5,7,11,13,17,19}. A finite family of pairwise distinct odd numerical
moduli greater than1 need not satisfy the full Euler-product budgets of
[report519](519-two-outside-prime-groups-preserve-the-finite-template-separator.md)
to use the same noncoverage certificate. It suffices that the three actual
finite inventories defined in A1 admit the divisor-supported payments A4.

Precisely, partition all outside prime coordinates into two fixed finite
groups R,S. Impose the finite old templates of
[report518](518-finite-prefix-templates-allow-arbitrary-old-residue-tails.md):
choose p in{7,11,13,17,19}, two first-root-distinct prefixes of depths11,7,6
at3,5,p, and one common depth4 prefix at each other old prime. Each complete
original later label d*n_R*n_S must choose one fixed selector simultaneously
at all three split coordinates, through the minimum of its exponent and the
prescribed depth. Other old coordinates match their common prefixes through
that same minimum rule. All deeper old digits and all outside phases may
vary arbitrarily per label; old-only classes are arbitrary.

If A4 holds for all three accounts, the original family does not cover the
integers. The actual old source gives mass greater than1/20000 to old points
with positive original later-fibre survival. The proof below also gives an
all-height structural family permitting23,29,31 together, including all three
in a single original modulus, beyond every full-Euler partition of that support.

This is a sufficient condition on actual moduli, not a theorem for every
finite prime support or arbitrary old residues. The weighted-mask bounds
reuse reports497/502/503; finite flow is standard. The new arithmetic bridge
connects these actual inventories and divisor payments to the existing source
separator, including the strict finite-period endpoint needed by its rows.
These are ordinary mathematical deductions, with no new Lean verification.

## Actual moduli determine three finite expense accounts

Fix P={3,5,7,11,13,17,19}. Partition the actual outside prime coordinates into two disjoint finite groups R,S, each disjoint from P. The partition is fixed for the ENTIRE family; it is not selected independently for different old labels. Empty groups are allowed. No complete Euler-product budget is assumed.

Take a finite original family of congruence classes with pairwise distinct odd numerical moduli greater than1, supported on P union R union S. Every later modulus has its unique actual factorization

    m=d*n_R*n_S,  n_R*n_S>1.

Here d is P-smooth, n_R is R-smooth, and n_S is S-smooth. For now use the full-common comparison model: every complete original label has ONE fixed A/B old-reference selector modulo d, shared by all tested points and estimates. Selectors may differ for different complete numerical labels with the same d. All original outside residues are fixed but arbitrary. The final section applies this model to the finite-template original family by518's one simultaneous repair.

Let D be the finite set of old cofactors appearing in original later labels. Let E be a finite divisor-closed set of P-smooth integers containing D and1, for example all divisors of lcm(D). If D is empty take E={1}. Extend all expense functions by zero to E minus D.

Define from the actual PRESENT complete labels, once for the family,

    b_d^R =22 * sum_(m=d*n_R, n_R>1 present) 1/n_R,
    b_d^S =28 * sum_(m=d*n_S, n_S>1 present) 1/n_S,
    b_d^M =616* sum_(m=d*n_R*n_S, n_R>1,n_S>1 present)
                                                    1/(n_R*n_S).       (A1)

These are finite rational sums. A missing numerical modulus contributes zero. Different labels retain their multiplicity even if some cylinder sets coincide. No old reciprocal factor1/d is inserted: at a fixed old point, matching its old cofactor is a zero/one activation.

For a finite list of old points i and weights w_i>=0, put

    h_d(w)=max(sum_i w_i 1[x_i=A mod d],
               sum_i w_i 1[x_i=B mod d]),
    N(w)=sum_(all labels in the certified old boxes) h_d(w).

Each e in E with a nonzero mask belongs to the full matching divisor boxes of the tested points; labels outside those boxes have h_e=0. No duplicate target label is added to the certificate inventory. The boxes may contain further labels beyond E. These finite profile arguments are used away from the null full-reference paths, as in [report491](491-all-split-common-patterns-force-six-shallow-classes.md); the actual source density bound makes those paths null for the source as well.

Let alpha_i,beta_i be actual union losses on the pure R/S coordinate groups. Let gamma_i be actual incremental mixed loss from the pure-surviving product. Let raw_i be the SUM of active original mixed-cylinder masses, so gamma_i<=raw_i. Set

    t_i=22alpha_i, u_i=28beta_i,
    y_i=616gamma_i, c_i=616raw_i.

Because one selector is fixed for each original label, the weighted union bounds give simultaneously

    w*t <=sum_d b_d^R h_d(w),
    w*u <=sum_d b_d^S h_d(w),
    w*y <=w*c <=sum_d b_d^M h_d(w).                    (A2)

The inequality also bounds the RAW additive mixed quantity c, which will matter at the zero-pair endpoint. The two pure survivor sets depend on disjoint actual coordinate groups. Therefore

    0<=t_i<=22, 0<=u_i<=28, y_i>=0,
    (22-t_i)(28-u_i)-y_i=616s_i,                       (A3)

where s_i is the actual later-fibre survivor fraction. Internal intersections among pure cylinders need no independence assumption. No independence between different old points is used.

## Divisor transport preserves every weighted budget

A simple sufficient test is b_d^R,b_d^S,b_d^M<=1 for every d. Then A2 is bounded by N(w), exactly as in the old numerical model. This test measures the finite actual inventory, so it need not follow from full Euler products.

A strictly more flexible sufficient form is a supplied nonnegative rational transport matrix T^X for EACH account X in{R,S,M}, indexed by source d in E and destination e in E, with

    T^X_(d,e)=0 unless e divides d,
    sum_e T^X_(d,e)>=b_d^X,
    sum_d T^X_(d,e)<=1.                              (A4)

Surplus row payments can be trimmed to give equality. The matrices are separate accounts; each may spend the same old-label column capacity once because the R-only, S-only and mixed originals are different complete numerical labels. This does not assert that the maximizing continuous allocations of the three accounts are simultaneously realized by some other arithmetic family.

For the SAME global references, e|d implies both cylinder inclusions

    1[x=A mod d]<=1[x=A mod e],
    1[x=B mod d]<=1[x=B mod e]

at every old point. Thus h_d(w)<=h_e(w) for all w>=0. It follows that

    sum_d b_d^X h_d(w)
      <=sum_(d,e) T^X_(d,e) h_d(w)
      <=sum_(d,e) T^X_(d,e) h_e(w)
      <=sum_e h_e(w)<=N(w).                          (A5)

Combining A2-A5 proves the original simultaneous budgets

    w*t<=N(w), w*u<=N(w), w*y<=w*c<=N(w).             (A6)

This is accounting on the ORIGINAL family, not a replacement of its congruence classes by ancestor moduli. The original residue modulo d, its outside phase and its selector are untouched. An ancestor absent from the original family may be a valid virtual inventory column because the established old-box bound already counts it; it is never added as an original forbidden class.

The unit e=1 is a SINGLE column of capacity1. Every d has that ancestor, but no label receives a private copy of its budget. In particular an overloaded unit-cofactor account b_1^X>1 cannot be repaired by ancestor transport. Paying several descendants requires enough unused total capacity in their actual common down-set.

A supplied finite matrix A4 is checkable using rational arithmetic, integer divisibility, row sums and column sums. Its existence is a separate finite feasibility problem; the theorem does not call an optimizer or report solver status as evidence.

For completeness, a standard capacitated Hall condition characterizes this feasibility:

    sum_(d in A) b_d^X <= |{e in E: e|d for some d in A}|
    for every A subset E.                            (A7)

Necessity follows by summing the paid rows over their allowed destination columns. Sufficiency is the usual finite max-flow/min-cut argument: source-to-d capacities b_d, d-to-divisor arcs, divisor-to-sink capacities1. Every finite cut has capacity at least the total demand by A7, so a full flow supplies T; rational capacities permit rational flow. This is a standard flow theorem, not a new project result.

Because E is divisor-closed, A7 is equivalent to the simpler family

    sum_(d in U) b_d^X<=|U|
    for every divisor-closed U subset E.              (A8)

For necessity take A=U. For sufficiency take U to be the divisor closure of A, so b(A)<=b(U)<=|U|. These are genuine joint budgets; a test using only the total demand over E can miss a bottleneck in a proper down-set. If an account is infeasible, the same standard min-cut theorem supplies a finite failed Hall set A with b(A)>|Div_E(A)|. This is a checkable budget-overload obstruction on actual numerical old labels, not an original covering counterexample or a new matching theorem. A claimed cover in the finite-template scope must make at least one account fail, hence has such an overloaded set for every chosen global partition R,S.

## Finite odd periods exclude the qualitative pair's closed endpoint

A4/A6 gives closed budgets, not generic strictness. For the specific (21,26,35) zero-only pair used by509, finite odd arithmetic rules out the equality case.

Take two actual old points with the required inventory upper bounds. The old four-corner argument from506 gives

    R_x+R_y>=35,  R_i=(22-t_i)(28-u_i).                (A9)

Let L be the lcm of all ACTUAL outside cofactors n_R*n_S in the finite family; take L=1 if there are no later classes. L is odd. Every mixed cylinder has measure1/n with n|L; its two-point activation count is0,1 or2. Therefore the RAW mixed total has the form

    c_x+c_y=616I/L, I a nonnegative integer.           (A10)

A6 at w=(1,1) bounds this by the joint inventory, hence by35. Equality would imply616I=35L, with the left side even and the right side odd. Thus

    c_x+c_y<=35-1/L<35.                              (A11)

The actual increments y_x,y_y also have a common odd denominator L because each is a union-minus-union count on the same finite product carrier; however raw A10-A11 already supplies the required strict bound and does not need a phase computation. More generally this parity argument excludes equality to any odd integer endpoint N. In the present scope the outside primes are also disjoint from7 and11, so gcd(L,616)=1: an integer value of616I/L must then be a multiple of616, excluding every integer endpoint0<N<616. The35 proof needs only the weaker parity observation. This does not create new zero-exclusion types unless the relevant relaxed argument also forces such an endpoint.

Using A3, y<=c and A9-A11 gives

    616(s_x+s_y)>=1/L>0.                             (A12)

So the two fibres cannot both be zero. In fact s_x+s_y is an integer multiple of1/L, hence its positivity gives s_x+s_y>=1/L. This latter observation is optional; it is a finite-period bound, not a height-independent positive threshold.

Consequently ALL509 rows remain valid for exact-zero supports under A4: the ordinary pair, triple and quad rows use A6/A3, qualitative pairs use A12, binary cliques use their pair constituents, and upward order uses original-label activation inclusion. Safe Q<=19 still gives1/77. No extra uniform factor eta<1 is required in the mixed transport columns.

Empty R or S causes no difficulty. There are then no mixed classes, c=y=0, and the same argument is stronger. Empty original later inventory has L=1 and s=1 everywhere on the old source. No finiteness assertion is inferred from a countable completion: L uses only original finite outside cofactors.

For a fixed original outside period, all rows can additionally be used at

    theta_family=min(1/3696,1/(2L)),

because qualitative pair survivor sums are at least1/L. This is explicitly family-dependent. It must not be reported as a uniform positive theta over unrestricted outside heights.

## A general23/29/31 family admitted by actual inventories

Fix R={23}, S={29,31}. For EACH original old cofactor d choose an integer K_d>=0, and impose this structural condition on EVERY original later label with that d:

    m=d*23^j*29^k*31^ell,
    j>=0, 0<=k<=K_d,
    ell=0 OR ell>=K_d+1,
    j+k+ell>0.                                      (A13)

The original family remains finite, all full numerical moduli remain distinct, and all original residues and selectors may vary by full label subject to the declared old-reference/template conditions. In particular k>0 and ell>0 may occur together: this does not forbid mixed29/31 labels or classes involving all three outside primes. K_d may be selected as a bound on the actual29 exponents for that d, then checked against its actual31 exponents.

For a fixed K write

    U_K=sum_(k=0..K)29^(-k)=(29-29^(-K))/28,
    V_K=sum_(ell>=K+1)31^(-ell)=31^(-K)/30,
    W_K=U_K*(1+V_K)-1.

W_K is the reciprocal sum over the allowed NONUNIT S-cofactors. It includes every allowed29/31 co-occurrence and does not count the unit cofactor as a pure-S label. Direct algebra gives

    28W_K=1-rho_K,
    rho_K=29^(-K)-(29-29^(-K))*31^(-K)/30
         =29^(-K)*[1-((29-29^(-K))/30)*(29/31)^K]>0. (A14)

For all K>=0, the bracket is positive because (29-29^(-K))/30<29/30<1 and (29/31)^K<=1. This is an all-K inequality, not a finite numerical sample. The same algebra for integers r>q>=2 gives a reciprocal bound below1/(q-1) when q exponents are at mostK and r exponents are zero or at leastK+1: its strict step is q^(K+1)-1<(r-1)r^K. The stated23/29/31 family is the concrete specialization used here, without adding finite positive-instance certificates.

At each d, the actual finite inventories are therefore bounded by

    b_d^R <=22*sum_(j>=1)23^(-j)=1,
    b_d^S <=28W_(K_d)=1-rho_(K_d)<1,
    b_d^M <=616*(1/22)*W_(K_d)=1-rho_(K_d)<1.        (A15)

Only an upper bound uses the complete23 tower and the allowed31 tail; no missing class is added to the actual family. The diagonal transport T_(d,d)=b_d satisfies A4. Thus A13 is a directly checkable general family with all three outside primes allowed, reusing ALL509 rows and the518 noncoverage bridge.

No partition of the full support{23,29,31} meets the two FULL Euler budgets from519: one bin must contain two primes, and even the smallest product excess for a pair here, from29 and31, is59/840>1/22. A15 succeeds because it keeps the actual missing29/31 exponent bands instead of charging every smooth cofactor. This proves a scope enlargement of the sufficient-condition theorem, not a claim about arbitrary phases violating A13 or a positive finite-instance construction.

Because D is finite, rho_*=min_(d in D)rho_(K_d)>0 when D is nonempty. If desired, A15 gives a height-independent threshold for the declared collection of K_d:

    theta_K=min(1/3696,35rho_*/1232).

It is uniform in the remaining finite23 and31 heights but depends on the actual K_d bounds. The main exact-zero conclusion does not need this quantitative strengthening.

## More extra primes and a remaining unit bottleneck

The same missing-band idea extends to any finite set T of additional odd primes besides23,29. For each old d retain k<=K_d at29. For every ell in T require its exponent to be either zero or at least L_(ell,d)>=1. Define

    B_d=product_(ell in T)
           (1+ell^(1-L_(ell,d))/(ell-1))-1.

This counts all permitted simultaneous extra-prime occurrences, rather than assigning independent budgets to separate subsets. The sufficient inequality is

    B_d < 29^(-K_d)/(29-29^(-K_d)).                  (A16)

Indeed the S inventory is at most U_(K_d)*(1+B_d)-1, and A16 makes it strictly less than1/28. For each fixed finite T and K_d such depths exist because every extra-prime tail tends to zero as its starting depth increases. This permits arbitrarily many outside prime directions with sufficiently delayed actual exponents; it does not allow arbitrary low-exponent occurrences for free.

Ancestor transport can accept further finite inventories failing the diagonal test when their expenses can share unused divisor-column capacity. It cannot fix every family. A unit-cofactor account has only destination1. For example if actual unit-cofactor labels23,29,31 are all present, any two-group partition places two of them in one account; even their two first-level reciprocal contributions exceed the corresponding unit budget (22 or28 scaling). No ancestor transport can remove that bottleneck. This obstructs the present sufficient-condition test, not the existence of an uncovered integer or another proof method.

The partition R,S must remain global. Assigning the same prime to different pure groups according to d would generally make the two pure survivor sets overlap in their coordinate dependence and invalidate A3. Likewise old labels are not merged to remove repeated projected moduli, and virtual ancestor columns are not free new reference choices.

Where A4 fails, further possible inputs are selector-specific mixed capacities, phase-compatible union savings, or the existing conditional-tail source construction with its own quantitative hypotheses. Failure of this accounting test is not an original covering counterexample.

## The same finite-template source separator still applies

Apply the finite-template conditions from518 to the original family supported on P union R union S: choose one p in{7,11,13,17,19}; two first-root-separated prefixes at3^11,5^7,p^6; one prefix at q^4 for each remaining old q. Every complete original label d*n_R*n_S has ONE fixed selector simultaneously choosing its three split prefixes through the queried depths. All deeper old digits and all outside phases are arbitrary by label. Exponent-zero conditions, including d=1, are vacuous.

Suppose its three ACTUAL finite expense accounts A1 admit A4. Repair only the old residues to518's one pair of full-common references, preserving every full modulus, outside phase and selector. The numerical d,n_R,n_S, hence A1 and the supplied transports, are unchanged. Divisibility monotonicity A5 holds for those repaired global references even though the original deep tails did not follow global paths.

The old-only family and completed-and-charged source nu are unchanged. All509 zero-support rows now hold for the repaired family by A6-A12. Hence the same exact517 prices and direct nonworst separator give repaired positive-fibre source mass at least delta_p. Original and repaired fibre sets coincide off the same518 old-coordinate exceptional set E, whose source mass is at most epsilon518_p. The independently checked source separation remains

    delta_p-epsilon518_p>1/20000.

Therefore

    nu({original later fibre survival>0})>1/20000.       (A17)

The original finite family does not cover the integers. A finite CRT period supplies an uncovered original residue and positive natural density for that individual family. This conclusion covers A13 and A16 and any other actual finite inventory with a valid ancestor certificate. It does not require a full Euler budget or a uniform positive whole-fibre Haar floor.

Quantitative statements are separate. If theta_family above or another established common positive threshold applies, then nu({s_original>=theta})>1/20000. With the inherited actual source cap nu<=(27/2)H_old this gives

    H_full(original survivors)>theta/270000.

The period-based theta_family depends on L; the structural theta_K depends on the declared K_d. Neither is a new universal height-independent density floor for arbitrary prime support. Numerical source certificates remain the original ones; the new proof is their actual-inventory scope bridge.

## Reproduction and evidence boundary

The retained finite-template source arithmetic is reproduced by

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite_prefix_template_source.py

Its input is the existing exact five-role source result. The source construction
and its verification boundary are inherited through reports517--519 and the
[library entry](../../../../../Library/Arith/schroeder2026nine.md) for Michael
Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1.
The old row certificates, source geometry and rational prices are unchanged.

A proposed transport can be checked by factoring the actual complete moduli,
checking their uniqueness and fixed prime partition, calculating A1, and
checking nonnegative rational entries, divisibility support and A4 row/column
sums. The existing source CLI does not perform these new input checks or solve
the flow problem. The finite matrix criterion, raw-mixed endpoint argument
and all-K inequalities above are ordinary proofs; no optimizer result,
positive finite-instance certificate, new source calculation or Lean result
is being substituted for them. An infeasible account gives a failed budget
test, not a covering counterexample. Unrestricted Erdős#7 remains unresolved.

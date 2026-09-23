[Index](../../marked_head_profile.md) · [Single-prime lifting](451-original-phase-trimming-gives-a-summable-single-prime-lift.md) · [Original completion](378-saturated-prime-fibres-and-mixed-tail-incidence.md)

# Exponent assignment controls arbitrary two-prime tail graphs

The exponent-assignment lift controls the weighted original ternary-depth completion load while preserving an arbitrary given core marginal. Every tail label may use one OR two outside primes, with arbitrary finite exponents and independent original residues. There is no degree, cycle, treewidth or number-of-primes restriction. Arbitrary interaction graphs and fixed-marginal conditioning already have other project constructions; the all-height completion estimate is the additional obligation addressed here.

The price is an explicit large-prime threshold. For a fixed head divisor inventory Q, put D=tau(Q). If every outside prime is at least

    B=3^(2560 D^2),

one supported lift has total original mixed completion load from these primes strictly below1/4. The threshold is not optimized. The construction does not cover labels involving three outside primes, and it does not supply the necessary core margin. In particular, absorbing smaller primes into Q changes D and the threshold; that operation cannot be treated as a free reduction of unrestricted Erdős #7.

This is an ordinary mathematical proof with exact finite controls. No new Lean certification, public-literature priority or unrestricted covering conclusion is asserted. Normalized conditional kernels, finite union bounds and elementary prime-count estimates are standard; the original exponent assignment and its joint tail account are given below.

## 1. Original input and the marginal that must be preserved

Let K be odd and coprime to3, let Q divide K, and let P be a finite set of primes coprime to3K. Resolve the original ternary height by H>=1 and the original outside heights by J_p>=1. There is at most one original residue alpha_d for each numerical modulus d>1. The permitted labels are:

* arbitrary core labels dividing3^H K;
* single outside-prime labels3^e a p^f;
* double outside-prime labels3^e a p^f q^g, q<p.

Here a divides Q,0<=e<=H,1<=f<=J_p and1<=g<=J_q. Missing labels are allowed. There is no assumption of comparable-class disjointness, divisor closure or shared phases. All full original labels remain distinct; in particular different f,g or e are not identified after projection.

Let S in Z/K avoid every original3-free core class, and let mu be any probability supported on S. Assume such a probability is supplied. Write X_p=Z/p^J_p with normalized Haar law H_p. For a full tail label d, let C_d be its literal cofactor cylinder on Z/K times product_p X_p, obtained by retaining its original residue modulo d/3^e.

We construct ONE probability nu on this carrier such that its K-marginal is mu, it avoids every original3-free class, and

    L_tail(nu)=sum_(tail originals d with e>=1)
                       3^(1-e) nu(C_d) < 1/4.               (EA1)

This is the original weighted completion task of378 and451. It does not identify C_d with the full original congruence, and no complete-layout Gamma bound is claimed.

## 2. Assigning each early cylinder to an actual endpoint

First suppose every outside prime is at least B0=3^(128D). Define

    Ehat_p=floor(log_3(p)/(128D))-1,
    E_p=min(H,Ehat_p),
    s_pq=min{s>=0 : q^s>=p^2},                 q<p.          (EA2)

Then E_p>=0 and s_pq<=1+2 log(p)/log(q). Each single-prime label at ternary depth e<=E_p is assigned to p. A double-prime label at depth e<=E_p is assigned by its ORIGINAL outside exponents:

    g<=f+s_pq : assign its p^f projection to p;
    g> f+s_pq : assign its q^g projection to q.              (EA3)

At a fixed core point x, include a projection only when x matches that original label's a-coordinate. Let F_p(x) be the union of all literal p-adic cylinders assigned to p, over every incident edge and its single-prime labels. Equal projected cylinders may be merged as sets, but the estimates below count the original labels before any such merger.

An early original event is killed because one of its actual coordinate projections is excluded. This can delete more points than the original event, so positivity of every remaining coordinate domain must be proved; it is not assumed from local consistency.

For one edge(q,p), the union-bound charges at its two endpoints are at most

    to p: D(E_p+1)[p/(p-1)^2+s_pq/(p-1)],
    to q: D(E_p+1)q^(-s_pq)/(q-1)^2.                       (EA4)

Indeed, for each e,a and f the first case permits at most f+s_pq values of g. Its projected p-mass sum is

    sum_(f>=1)(f+s_pq)p^(-f)
       =p/(p-1)^2+s_pq/(p-1).

For the other case the projected mass is

    sum_(f>=1) sum_(g>f+s_pq)q^(-g)
       =q^(-s_pq)/(q-1)^2.

These infinite sums majorize the actual finite heights; they do not introduce new original classes. The single-prime charge is at most D(E_p+1)/(p-1). The factor E_p+1 includes e=0, which is essential for actual3-free support.

## 3. Elementary prime estimates and the shared coordinate budget

We use the standard elementary bounds

    pi(t)<=7t/log(t),                              t>=2;
    sum_(q prime,q<t)1/log(q)<=15t/log(t)^2,        t>=exp(32). (EA5)

Here is a self-contained derivation with deliberately loose constants. Let theta(t)=sum_(q<=t)log(q). The product of primes in(n,2n] divides the central binomial coefficient, which is at most4^n. Summing this at n=1,2,4,... gives theta(t)<4t log(2)<3t. Splitting prime counts at sqrt(t) then gives

    pi(t)<=sqrt(t)+2theta(t)/log(t)<=7t/log(t),

using log(t)<=sqrt(t). To obtain the second bound, primes at most sqrt(t) contribute at most sqrt(t)/log(2), and larger primes contribute at most2pi(t)/log(t). For log(t)>=32, the decreasing function u^2 exp(-u/2) satisfies u^2 exp(-u/2)<=1024/exp(16)<1/2<log(2), giving sqrt(t)/log(2)<=t/log(t)^2. This proves(EA5). These elementary estimates are not asserted as new prime-number results.

Fix an outside vertex p. The total charge from its smaller neighbors is bounded by summing over ALL primes q<p, hence it is independent of its graph degree. Set z=p/(p-1)<=8/7. By(EA5),

    sum_(q<p)[p/(p-1)^2+s_pq/(p-1)]
      <= z[7(z+1)+30]/log(p)
      <= (360/7)/log(p)<52/log(p).

Also D(E_p+1)<=log(p)/(128log(3)). Since p>=B0>exp(32), these inequalities apply and the smaller-neighbor charge is at most52/128. The single-prime charge is at most1/128, using log(p)<=p-1 and log(3)>1.

For larger neighbors r>p, assignment(EA3) gives p^(-s_rp)<=r^(-2). Therefore their TOTAL charge is at most

    [1/(128log(3)(p-1)^2)] sum_(r prime,r>p)log(r)/r^2
      <= (log(p)+1)/[128log(3)p(p-1)^2]
      <= 1/128.

The middle inequality follows by overcounting with all integers r>p and integrating the decreasing function log(t)/t^2 from p to infinity. Thus every actual x satisfies

    H_p(F_p(x))<=54/128=27/64<1/2.                         (EA6)

This is one shared budget for all original classes assigned to p. It includes all smaller and larger neighbors, even in a complete graph of arbitrarily many outside primes. No edge is given a fresh copy of the available mass.

## 4. The one law and its complete original tail estimate

Define

    k_p(x,.)=H_p(. | F_p(x)^c),
    nu(x,(y_p)_p)=mu(x) product_p k_p(x,y_p).                (EA7)

By(EA6), each row is defined and normalized, with density at most2 relative to H_p. Hence nu preserves the entire core marginal mu. Every3-free tail label was assigned at e=0 and has a deleted endpoint, so nu is supported on the actual residual R_3 avoiding ALL original3-free classes. The kernels can depend on the actual core point and original phases; their product is conditional on x, not an assertion of unconditional independence.

The same law gives an original single-coordinate cylinder mass at most2p^(-f), and an original two-coordinate cylinder mass at most4p^(-f)q^(-g). For an edge(q,p) all e<=E_p terms vanish simultaneously. Write gamma=1/(128D). If any later terms remain, E_p=Ehat_p and

    3^(-E_p)<=9p^(-gamma).

If H<=Ehat_p, that entire tail has zero contribution and needs no use of this estimate. Summing all finite original exponents by geometric upper bounds gives

    single tail at p <=27D p^(-gamma)/(p-1),
    pair tail at(q,p)<=54D p^(-gamma)/[(p-1)(q-1)].          (EA8)

All incident pair tails may be added because these are upper bounds on the linear sum of original event masses under(EA7), not duplicated lower credits for a deletion union. Using p-1>=p/2 and sum_(q<p)1/(q-1)<=1+log(p), and then overcounting the largest prime by all integers, yields

    L_tail(nu)<=54D sum_(n>=B)
                         (3+2log(n))n^(-1-gamma),          (EA9)

whenever every outside prime is at least an integer B>=B0. This convergent bound contains every original label in the admitted inventory, including labels on every edge of a complete outside graph and all original prime powers.

## 5. An explicit quarter-budget and its covering consumer

The summand in(EA9) is decreasing for n>=1. Its integral and first term give

    sum_(n>=B)(3+2log(n))n^(-1-gamma)
      <=2 B^(-gamma)[(3+2log(B))/gamma+2/gamma^2].           (EA10)

Take B=3^(2560D^2). Then B^(-gamma)=3^(-20D) and log(3)<2. Direct substitution in(EA9)--(EA10) gives

    L_tail(nu)
      <=145138176 D^4/3^(20D)
      <=145138176/3486784401 < 1/4.                        (EA11)

For the second inequality, D is a positive integer and the ratio of successive terms D^4/3^(20D) is at most16/3^20<1. The strict final comparison is the integer inequality580552704<3486784401. These bounds prove(EA1) for arbitrary finite original heights and tail sizes, without enumerating a period or testing primes up to B.

Let L_core(mu) be the original3-bearing core completion load excluding pure powers of3. Since(EA7) preserves mu,

    L_comp(nu)=L_core(mu)+L_tail(nu).

The existing whole-cover necessary condition is L_comp(nu)>=B_H=(3+3^(1-H))/2 for every law on R_3. It follows that any supplied core law with

    L_core(mu)<=B_H-1/4                                   (EA12)

certifies noncoverage after adjoining ALL the admitted large-prime single and double tails. The core law's existence and(EA12) remain separate requirements. A scalar Gamma bound does not automatically provide them.

This does not close the unrestricted goal. Classes containing three or more outside primes have not been assigned or bounded. The astronomical cutoff leaves smaller outside primes untreated by this theorem. Enlarging Q to absorb them increases tau(Q) and changes the bound, and cannot be assumed to terminate. No known whole-cover candidate is declared impossible unless all its original labels and the actual core margin meet the displayed hypotheses.

## 6. Exact controls and relation to earlier interfaces

The construction uses451's normalized complement kernels with an additional exponent assignment: the small endpoint's deep exponents pay a summable reverse charge, while the large endpoint's forward charge is controlled by the number of smaller primes. This particular construction needs no degree restriction. It does not identify graph relabelings with arithmetic symmetries, or recompute a residue separately in different kernels.

[Chapter07](../../problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md), equations(RK1)--(RK5), already permits arbitrary co-occurrence graphs with bounded original outside-prime support. Its capped kernels can also be run separately at each fixed core point and then conditioned within that point's surviving fibre, preserving an arbitrary mixture of core points whenever the pointwise survival estimates hold. Neither arbitrary graphs nor preservation of mu alone is claimed as new here. The additional combined conclusion(EA1) is uniform in H: it deletes selected ORIGINAL ternary depths and bounds the remaining weighted completion under that same supported law. Treating the ternary projections as distinct cofactor moduli would lose original labels; simply counting them at every depth introduces H.

Chapter06's blocked-fibre and tree elimination results, and Chapters04c/54's capped-law continuations, provide related interfaces. Their general kernels and arithmetic task interfaces are reused; no new generic kernel or Gram wrapper is introduced. No literature-priority assertion follows from this comparison.

The [exact checker](../../frontier/cover-geometry/two_prime_tail_assignment.py) and [data](../../frontier/cover-geometry/two_prime_tail_assignment.controls.json) inspect finite original arithmetic inputs and the shared projected-cylinder budgets. The uniform all-graph claim and its infinite sums are established by the proof above, not by finite enumeration. The checker remains active with Python optimization enabled.

The fixture uses the triangle on101,103,107, outside heights5, ternary height2 and cuts(0,1,0). These moderate primes do not meet the uniform cutoff; the fixture instead checks its own exact finite budgets. Its2440 distinct odd original classes include both four-prime and five-prime supports. It checks260030 comparable disjoint pairs,180 early singleton assignments,864 assignments to the larger endpoint and36 to the smaller endpoint. All21528 conditional cylinder queries use one law;5218 active-head early event queries vanish, and17996 CRT membership checks verify actual3-free witnesses. The66 kernels are normalized and preserve the entire22-atom core marginal. A separate enumeration of125 points checks624 laminar-cylinder queries, including nested and overlapping descriptions. Ignoring pair labels leaves positive mass on an original forbidden pair class, providing a negative control. The theorem does not require comparable disjointness, although this fixture satisfies it.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_prime_tail_assignment.py
```

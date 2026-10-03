# A mass-preserving actual PG1 redistribution decreases every complete fourth-moment supremum

One change to an actual supported kernel preserves its survivor mass and strictly decreases both the physical and survivor-restricted complete fourth-query suprema, at every finite 17-adic height. The construction reuses the actual family and source of [Report16, GC1–GC6](../../001-064/16-a-common-dual-test-law-for-redistributing-charged-bad-mass.md#a-global-cap-perturbation-improves-the-actual-survivor-law-at-every-finite-height), with a smaller transfer and a fourth-power comparison. All numerical labels and original residues stay fixed.

This is an ordinary mathematical proof with exact finite checks, not Lean verification. It does not identify this source with [Report779's eight-prime source](779-the-original-capped-source-lowers-the-general-eight-prime-tail-cutoff.md), give a gain uniform over arbitrary families, or prove unrestricted Erdős #7.

## Exact original source and operation

Reuse the canonical PG1 law mu on its 75 actual survivors modulo 315, with denominator D=1000000007. Its two required masses are mu(2)=13119398/D and mu(314)=16622259/D=:mu_star. All eleven nonunit numerical divisors of 315 occur as old original labels, with their pinned PG1 phases. There are twelve complete old query slots including the unit.

At p=17 and every finite H>=1, add the exact CS2 comb: for each depth 1<=e<=H the pure label 17^e has prefix 15*(17^(e-1)-1)/16, and the eleven mixed labels d*17^e, with d the increasing nonunit divisors of 315, have old phase 2 mod d and current prefix 15*(17^(e-1)-1)/16+j*17^(e-1), j=1,...,11. Thus there are 11+12H distinct odd nonunit original labels. All complete query labels are the 12(H+1) divisors of Q=315*17^H, with independent fixed phases.

Put s_H=sum_(e=1..H)17^-e, lambda_H=1-s_H. Let n(x) be the number of active nonunit old cofactors centered at 2. Use exactly Report16's normalized BB kernel q_0: its good Haar density is

    c_H(x)=1/max(1-(n(x)+1)*s_H, lambda_H*(1-7/15)),

with the stated bad density. At x_star=314, n=1, charge is zero and 1<=c_H(x_star)<=8/7. Root2 is entirely good there. The clean roots are R_H={12,13,14,15,16} if H=1 and {12,13,14,16} otherwise. They are entirely good at every old point. All original labels and actual forbidden phases stay fixed.

Let U_j,H be uniform probability inside current root j. Change only the row x_star, using

    t=1/1048576,
    q_t=q_0+t U_2,H-(t/|R_H|) sum_(j in R_H) U_j,H.

The exact Report16 cap checks apply: available recipient capacity is at least 41/952>t and each donor root has mass at least 1/17>t/|R_H|. The modified row stays normalized, retains the same old marginal and global Haar cap (15/8)/lambda_H, and moves mass exclusively between actual survivor points. Physical mass, every actual bad mass and final survivor mass rho_H are unchanged; rho_H>=|R_H|/17>0.

For every complete query T define L_T as the sum of all numerical-divisor indicators. Let V_4(q) be max_T E_(mu q)L_T^4. Let W_4(q) be max_T integral L_T^4 over the actual survivor restriction of mu q (unnormalized). The claim is

    V_4(q_t)<=V_4(q_0)-epsilon,
    W_4(q_t)<=W_4(q_0)-epsilon,
    epsilon=3*mu_star*t=49866777/1048576007340032>0.

Consequently the normalized supported fourth-query supremum decreases by at least epsilon/rho_H. The same source also has all four-query mixed integrals at most W_4(q_0)-epsilon by Holder, so any prior certified upper bound K for W_4(q_0) may be replaced by K-epsilon without changing mass.

## The complete-query upper value is attained by one actual query

Fix ANY full query T and retain its old-coordinate query phases, separately for every current exponent e. At old point x let A_e(x) be the number of matching old slots at exponent e. Then 0<=A_e<=12 and A_0>=1. Expand L_T^4 over ordered quadruples of full numerical labels. For a tuple whose largest current exponent is e>0, the actual current-prefix intersection is empty or one depth-e cylinder, and its physical or killed conditional mass is at most c_H(x)*17^-e. For the all-zero-exponent term use A_0^4 physically, and (1-beta_H(x))*A_0^4 after killing.

Call the resulting upper value U_4(T), respectively U_4^S(T). These are not independently optimized tuple bounds: simultaneously move EVERY positive-current-exponent query to the same nested path inside one globally clean root, retaining ALL its old phases. This is a single legal complete query. Every tuple of current prefixes now intersects at its maximum depth and has density exactly c_H(x) everywhere on that cylinder. Thus the upper value is attained on the baseline law:

    U_4(T)<=V_4(q_0), U_4^S(T)<=W_4(q_0).

All following gaps use the same fixed T and compare it to this one attainable upper value. No claim that the original query was coherent is made.

## Uniform upper bounds for added root mass

For any full query and any fixed root, its conditional fourth moment is at most

    M_4=12^4*[1+17*sum_(e>=1)((e+1)^4-e^4)*17^-e]
       =13611483/32.

Expand into ordered numerical-label quadruples: there are at most 12^4 choices for each exponent tuple, and a tuple with positive maximum e has conditional root probability at most 17^(1-e). The all-zero tuple contributes at most 12^4. This accounts for the entire infinite exponent inventory and bounds every finite H. Dropping donor subtraction therefore bounds the perturbation increase by mu_star*t*M_4, for both physical and killed integrals.

## Cases with a uniform missing-term gap

Let z be the first root of T's pure17 slot. In the quartic expansion the 15 ordered tuples using only the unit slot and that pure17 slot, and at least one copy of the latter, have the same prefix indicator. Hence the square proof's three-term gaps become fifteen-term gaps:

* z in {1,...,11}: at old point 2, c_H-bad_density has root integral at least 14/187. Gap >=G_spoke=15*mu(2)*14/187.
* z=0: pure forbidden root; gap >=G_pure=15/17.
* z=15 and H>=2: this root contains the pure depth-two forbidden cylinder; gap >=G_spine=15/289.

These cover z outside R_H. If z is clean but some depth-one query active at x_star uses a different root, its intersection with the pure17 query is empty. The twelve ordered quadruples containing those two distinct slots and two unit slots have missing cap >=G_split=12*mu_star/17.

Each listed G exceeds mu_star*t*M_4+epsilon. Exact differences are positive rational numbers in the checker. All other expanded terms have nonnegative cap gaps, so no discarded term can cancel these gaps. Thus the perturbed query is below its attainable baseline upper value by epsilon in all these cases.

## Remaining case: a coherent depth-one row, arbitrary deeper phases

Now z in R_H and every depth-one slot active at x_star uses root z. At the donor root z the fourth-power increment above the unchanged old baseline is at least (A_0+1)^4-A_0^4>=15. Since that root is one of at most five equal donors, donor subtraction decreases the integral by at least 15*mu_star*t/|R_H|>=epsilon. Other donor roots only improve this lower bound.

On recipient root2, no depth-one label hits. Let a_e<=12 count the active old slots whose current prefix starts with root2 at depth e>=2, put

    B(y)=sum_(e>=2) sum_(those a_e labels) 1_(current prefix),
    S=sum_(e>=2)17^-e*a_e.

Every such label is disjoint from the pure17 query on root z. The twelve ordered terms consisting of that label, the pure17 slot, and two units therefore supply an additional cap gap >=12*mu_star*c_H(x_star)*S>=12*mu_star*S. These terms are distinct for distinct deep labels.

For k=1,...,4, group exponent k-tuples by their MINIMUM e and maximum e+j. For j=0 their count is 1. For j>=1 the exact number is

    N_k(j)=(j+1)^k-2*j^k+(j-1)^k.

Their coefficient product is at most a_e*12^(k-1), and their intersection probability conditioned on recipient root2 is at most 17^(1-e-j). This proves

    E_root2 B^k <=17*12^(k-1)*R_k*S,
    (R_1,R_2,R_3,R_4)=(1,9/8,179/128,1035/512),

where R_k=1+sum_(j>=1)N_k(j)17^-j. Consequently, with A_0<=12,

    E_root2[(A_0+B)^4-A_0^4]
      <=17*12^3*sum_(k=1..4) binom(4,k)R_k*S
      =(4315977/8)*S=:C_4*S.

The old-only term A_0^4 cancels exactly because transferred mass totals zero. Since

    12-t*C_4=96347319/8388608>0,

the pre-existing missing pure/deep terms pay for the ENTIRE recipient increase. The independent donor decrease still gives epsilon. This covers arbitrary finite heights, all arbitrary deeper query phases, and the H=1 case S=0.

Every query in both physical and killed domains has now been bounded by its attainable baseline upper value minus epsilon. Taking maxima proves both claimed supremum decreases. No finite enumeration is used to infer the universal query or height quantifiers.

## Research meaning and boundary

This is a concrete Pareto improvement of (actual survivor mass, full fourth-query bound) for the same labelled family and law. It has the correct order-four interface for [Report734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md): the mass is unchanged while a valid unnormalized fourth-query bound improves by epsilon. The fixed cap of the kernel is unchanged as well. An already justified quartic-tail reserve m-K*tau therefore improves by epsilon*tau if its other hypotheses match this source. In particular that use must keep every future old cofactor within the declared old heights; the present theorem varies the 17-height, not the 3/5/7 heights.

It is NOT a universal ninth-prime bridge. The proof uses the fixed PG1 old inventory, the real globally clean roots of the specified comb, positive masses at the two specified old rows, and twelve old slots. [Report17](../../001-064/17-higher-moments-retain-the-full-old-inventory-in-a-law-changing-perturbation.md) has square-objective improvements with more old heights using higher-moment tails; it does not establish this fourth-supremum assertion, and its conditions are not silently substituted here. The source in Report779 has different actual kernels and no uniform bound supplied for the needed clean/donor/recipient incidence gaps. A general extension must supply common-source quantitative versions of precisely these gaps (or another payoff-sensitive rule), and must retain complete old cofactor labels in the continuation.

## Exact verification

The standalone [checker](../../../frontier/cover-geometry/pg1-quartic-gain/pg1_quartic_gain.py) reconstructs the pinned PG1 source and each actual original CRT class, derives the geometric constants from Eulerian-number power sums, and independently enumerates 28 minimum/maximum exponent-tuple cases. At heights 1 and 2 it checks 22,950 actual source points, with 6 and 85 changed survivor points respectively. Normalization, every actual bad mass, survivor mass and conditional density caps agree as claimed. It also checks 52 specified full-query layouts, including every proof case and noncoherent higher-prefix examples, against the simultaneous clean-layout cap. These finite samples check the implementation; the ordinary proof above bears the full-layout and full-height quantifiers. The check succeeds with assertions disabled as well.

The [retained exact result](../../../frontier/cover-geometry/pg1-quartic-gain/pg1_quartic_gain.json) is compared with a fresh reconstruction by default. Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/pg1-quartic-gain/pg1_quartic_gain.py
```

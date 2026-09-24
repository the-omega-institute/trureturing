# Reordered PA rows certify a single root17 occurrence

For any finite actual two-copy family on Q={5,7,11,13,17,19}, at most one original occurrence at numerical modulus17 is sufficient for a supported law satisfying

    R_Q<=3037410451116503083351/604169434494311759438
       =5.027414956300806... <257/51.                    (O1)

Every other numerical label may occur twice, all full residues are globally fixed and arbitrary, and every finite height is allowed. The law processes the later primes in the fixed order13,11,19,17. This adds a root17-only condition to [report559](559-pure-union-savings-control-all-four-later-rows.md), which used increasing order and required simultaneous root17/root19 scarcity.

The two orders provide alternative supported laws. Their sufficient regions are genuinely different and have realizable pure-data points in both differences. Keeping both certificates strictly enlarges report559's baseline pure-union sufficient region; the argument never adds savings belonging to different actual laws.

These are ordinary mathematical arguments with exact rational computations, not new Lean results or a resolution of unrestricted two-copy covering or Erdős #7.

## 1. Any fixed later-prime order gives a legitimate process

Retain the actual5/7 anchor and its pure-product comparison. Choose a permutation sigma of11,13,17,19 before constructing the law. Assign each original containing a later prime to the LAST prime in its support under sigma. Each original is then imposed once, when its other coordinates are already available. Its old cofactor can contain a numerically larger prime; it is still an ordinary cylinder on the previous coordinates.

Keep the original's full numerical label and residue. At each current exponent distribute its at most two occurrences into two fixed slots, with at most one old-cofactor occurrence per slot. This is the same numerical multiplicity argument as [report348 CP5](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md). Conditional cylinder bounds and completed-row domination require a declared coordinate order, not increasing numerical primes. The generic conditional comparison is invariant under this reindexing.

Changing the order can change the actual row kernels and final law. For each chosen order, however, all losses, output queries and the final normalization refer to that ONE actual construction.

## 2. Exact optimization of the unrefined constant-cap certificate

For a fixed cap tuple, the independent auxiliary comparison law after a subset A of later primes depends only on A. The actual prefix does not have this property and is not treated as if it did. The complete final auxiliary hinge is also independent of the order.

The edge adding q to A has certified loss

    cost(A,q)=a_q F_(t_q)(A),
    a_q=2/(q-1-2t_q).

A16-subset shortest-path recurrence therefore minimizes accumulated certified loss over all24 orders. Its final mass is alpha=1/4-min_order sum cost. Because the final comparison numerator is the same for every route, this minimum loss simultaneously minimizes each query ratio h-1+Phi_h/alpha.

The common worst anchor corner and the continuous-cap endpoint reduction in report348 CT apply separately to every fixed order. The resulting integer ranges remain

    t11=0,...,4; t13=0,...,5; t17=0,...,7; t19=0,...,8.

Since the known global incumbent is below6 and the certificate is at least h-1, any improvement has an integer representative h<=6. This suffices for the global minimum; it does not assert h<=6 suffices to optimize each separate restricted subfamily of schedules.

The exact2160-tuple scan gives

    t=(2,2,4,4), ordered by numerical primes11,13,17,19,
    C=(5/3,3/2,2,9/5),
    sigma=(13,11,19,17), h=3,
    alpha_*=52945498078747367/514629637441920000,
    Phi_*=22496082952171/69510823782400,
    B_*=157471921154183512277/30602497889515978126
       =5.145721167033602... .                          (O2)

This is the global optimum of the SPECIFIED unrefined constant-cap comparison certificate with these anchors, all constant caps and all fixed later orders. It improves the old increasing-order5.1497954735... but remains above257/51. The optimum is not over actual survivor laws, refined pure-union bounds, adaptive coordinate orders or different anchors.

There are1349 cap tuples admitting positive mass under some order, versus999 under increasing order;1905 tuples improve their mass certificate when reordered. At the winning tuple, explicitly summing all24 orders independently confirms the subset-DP minimum and its unique best order. The fixed-order old minimum and feasible-count999 are recovered exactly.

## 3. Pure-union savings are valid for each chosen order

Keep the caps and thresholds in O2. The coefficients attached to numerical primes remain

    a11=1/3, a13=1/4, a17=1/4, a19=1/5.

Let r_q be the actual Haar mass of the complete pure-q forbidden union, and put

    theta_q=(q-1)r_q/2 in[0,1], delta_q=1-theta_q.

The pure union depends only on its q-coordinate, irrespective of the processing order. Report559's local inequality consequently applies to each chosen order. With actual stage loss Loss_q and the corresponding comparison prefix hinge F_q^sigma(x,y), it gives

    Loss_q<=a_q F_q^sigma(x,y)/(1+a_q delta_q).           (O3)

For clarity, let beta_(e,j)=(q-1)/(2q^e) and let n_(e,j) count active nonpure old cofactors. The same union bound gives, with

    G_q=sum beta_(e,j)*(n_(e,j)-(t_q-1))_+,

the endpoint inequality

    (1+a_q delta_q)ell_q<=a_q G_q.

For each fixed slot,1+n_(e,j) is a legal old query under the SAME actual prefix. The completed comparison bounds its hinge by F_q^sigma. Integrating and using sum beta=1 proves O3. No increasing-prime hypothesis was used.

Write f_q^sigma=F_q^sigma(1/2,2/3). For the new order the exact values, in processing order, are

| q | f_q^sigma |
| --- | ---: |
|13|97/840|
|11|15329/87360|
|19|202266823897/1875745872000|
|17|19655687364626449/128657409360480000|

Define the one-order savings quantity and its threshold

    Gamma_sigma(theta)
      =sum_q a_q^2 f_q^sigma delta_q/(1+a_q delta_q),
    k_sigma=Phi_* /(T-2)-alpha_*, T=257/51.

For the new order,

    k_new=1955600250091208797/542419637863783680000
         =0.0036053271555450453... .                    (O4)

The old threshold is0.0037384049474789155... . Their difference is exactly the gain in the unrefined certified mass; Phi_* is unchanged.

## 4. Preserve the anchor dependence when consuming the savings

Hold the actual theta values fixed in the comparison and define

    alpha_theta(x,y)
      =xy-1/12-sum_q [a_q/(1+a_q delta_q)]F_q^sigma(x,y).

By O3 and the actual mixed bound m<=1/12, the same final actual subprobability has mass at least alpha_theta(x,y). At the common worst corner,

    alpha_theta(1/2,2/3)=alpha_*+Gamma_sigma(theta)>0.

Normalize only the auxiliary anchor measures for the following comparison. Decreasing x or y increases their normalized coordinate tails and every normalized hinge. The coefficients a_q/(1+a_q delta_q) are fixed and nonnegative. Hence alpha_theta(x,y)/(xy) decreases as x or y decreases, while Phi(x,y)/(xy) increases. Positivity at the baseline implies positivity throughout the anchor rectangle, and

    R_Q(nu_sigma)
      <=2+Phi(x,y)/alpha_theta(x,y)
      <=2+Phi_* /(alpha_*+Gamma_sigma(theta)).           (O5)

This proves Gamma_sigma>=k_sigma sufficient, with a strict query bound when the inequality is strict. It retains one actual law and one normalization. Queries maximize each numerical label only in finite inventories under that law, followed by monotone exhaustion.

The raw-margin alternative can also be checked directly. For the new order,

    (T-2)alpha(x,y)-Phi(x,y)
      =-c_new+A5*d5+A7*d7+A57*d5*d7,
    d5=x-1/2, d7=y-2/3,
    c_new=1955600250091208797/178473558264857856000,
    A5=2953112387489112713/1784735582648578560,
    A7=6671775633279962077/6677582111950464000,
    A57=38489005826224139/13355164223900928.

All three coefficients are positive. They are recomputed for this order; the old NC4 coefficients are not silently reused. Thus the actual packing credit and these pure deficits may be retained, but O5 already supplies the sharper stated uniform root bound.

## 5. A single root17 occurrence now suffices

If numerical modulus q has at most one original occurrence, every deeper pure label may still occur twice. Its actual pure union satisfies

    theta_q<=((q-1)/2)*(1/q+2/[q(q-1)])=(q+1)/(2q).

With all other nonnegative savings discarded, O3 yields these new-order lower bounds:

| Root label with at most one occurrence | Guaranteed saving | By itself exceeds k_new? |
| --- | ---: | --- |
|11|15329/1991808|Yes|
|13|97/32480|No|
|17|19655687364626449/4888981555698240000|Yes|
|19|202266823897/108376428160000|No|

For root17 the strict excess is

    19655687364626449/4888981555698240000-k_new
      =4277784212899587349/10305973119411889920000>0.

Inserting this saving into O5 proves O1. Root11 similarly has the bound

    R_Q<=54016792154957590759/10963908514953536042
       =4.926782459128035... .

The increasing order retains the root13 sufficient condition from report559. Applying the same O5 consumption to that old order gives

    R_Q<=Phi_old/(alpha_old+47/9280)+2
       =5.001828872583618... <T.

One may select either complete construction according to which sufficient condition is met. No partial-row saving from one order is added to a saving or numerator from the other. Likewise a transported-deletion lower bound and a pure-union lower bound on the SAME stage saving cannot be added without a separate joint inequality.

Consequently any all-supported-laws lower witness strictly above T must have two original occurrences at EACH of11,13,17. If identical classes can be repeated as two occurrences, the two root residues at each of these primes must be distinct, since equal residues have the same union bound as a single root occurrence. This statement imposes no new double-root requirement at19.

## 6. The enlarged region contains actual families

The new order does not dominate the old order throughout theta-space. Both differences can be exhibited by actual finite pure originals.

For each q in{11,13,17,19} and e=1,...,4, take the two pure classes

    j*q^(e-1) modulo q^e, j=1,2.

These cylinders are pairwise disjoint: their first nonzero base-q digit occurs at depth e and is j. If the second root17 class alone is omitted, then

    (theta11,theta13,theta17,theta19)
      =(14640/14641,28560/28561,44216/83521,130320/130321).

The exact comparison margins are

    Gamma_old-k_old
      =-7548829866953346084320022897302337451
          /8394292133886227731825429236210668928000<0,
    Gamma_new-k_new
      =2300138979776467859234951078558331889
          /5518738773143194702584192231418778880000>0.     (O6)

Conversely, omit only the second root13 class. The actual theta vector is

    (14640/14641,15378/28561,83520/83521,130320/130321),

and the old margin is strictly positive while the new margin is strictly negative; the exact fractions are retained in the data.

Any finite nonpure originals can be added while preserving the two-copy condition, without changing these pure unions. Pure5/7 originals can also vary arbitrarily. Thus the differences are not merely unattainable numeric parameter points. The union of the two baseline Gamma sufficient regions strictly contains report559's region and applies to a larger class of actual families with arbitrary remaining geometry. This does not assert that every family in the difference lacked some other earlier noncoverage proof, or that failure of either sufficient criterion is a lower bound on the actual query norm.

## Exact evidence and remaining boundary

The all-order grid program and data are

[all-order program](../../frontier/cover-geometry/pa_later_order_cap_grid.py)
and [exact grid](../../frontier/cover-geometry/pa_later_order_cap_grid.json)

with2167 checks and data SHA256
`2dcb0e0800daf3ce06c5f8fcb21a9d859532e222b0e1fa8e6289d236c3f5f43f`.
A separate closed-form calculation verifies the winning four hinges, alpha and Phi. The ordinary arbitrary-order, worst-corner and rounding arguments are independently audited; the full2160 grid itself is the primary program's exact computation.

The small producer for the two-order pure-union consequences is

[pure-union program](../../frontier/cover-geometry/reordered_pure_union_savings.py)
and [result data](../../frontier/cover-geometry/reordered_pure_union_savings.json)

with25 checks and data SHA256
`d6d2e29c6bee3b837ea33dcd59dd427b6e02c636287b38d28a91b9aa53e38045`.
It computes both orders using full means and the closed low-product formulas at thresholds2,3,4, reconstructs all four anchor corners and each order's raw coefficients, and checks the two realizable finite theta differences. It does not import a prior producer or scan original families. An independent low-product convolution and savings calculation checks64 displayed fields. Both scripts accept --output, default beside their own file, and their JSON contains no temporary path dependency.

All tests use explicit runtime failures under Python -O. These finite computations do not replace the displayed source-comparison proofs. No new Lean verification is claimed. Dense pure unions can still make both Gamma values small; the unrestricted two-copy target and Erdős #7 remain unresolved.

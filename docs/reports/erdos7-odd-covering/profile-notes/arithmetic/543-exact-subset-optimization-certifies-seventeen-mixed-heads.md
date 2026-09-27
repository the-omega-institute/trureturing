# Exact subset optimization of the actual two-depth boundary

The sharp two-depth interface of[report542](542-an-actual-sharp-nine-cell-interface-for-two-depth-stars.md) admits an exact subset dynamic program for EVERY selected set of numerical labels3p and9p, p in Q={5,7,11,13,17,19}. Its two role masks retain the shared prime identity, and all4096 choices of the two masks are computed in the same tables. The global block supremum needs only the five-cell low-pure mask; the exact computation retains both of its possible anchor-root types. A complete mixed-loss consumer of these tables certifies the same survivor-Haar entropy law for at most seventeen shallow mixed originals, retaining all other pure and deeper originals.

These are ordinary proofs, exact integer computation and a reuse of the existing same-law budget. No Lean result or resolution of unrestricted Erdős#7 is claimed.

## Existing foundation and the new boundary cost

The underlying subset-partition method is existing project machinery.[Report416](416-exact-independent-layout-tree-separation-and-actual-laws.md) allocates two independently named roles per depth through disjoint child masks and reconstructs literal layouts. The PT2 recurrence in[report25](../001-064/25-eliminating-current-heights-with-a-common-old-test-distance-profile.md) shares one subset-convolution table across all requested masks and counts its3^k disjoint-pair trials. The recurrences here reuse that design for report542's different exact union task.

The present boundary retains one parent role3p and one child role9p for each selected outside prime. The roles are distinct numerical originals. Their joint leaf avoidance factor is1-2c_p when both occur on the same cell, not(1-c_p)^2. This specific cost, the actual sharpness theorem from542, and the five-cell dominance argument below are what connect the subset computation to the complete mixed-loss budget.

Throughout the exact optimization,

    c_p=(p-1)/[p(p-2)]

is the SATURATED outside-root cap. Report542 identifies the resulting incidence optimum with the supremum over finite actual irredundant families, allowing outside phases and pure layouts to be constructed. It is not the optimum for an arbitrary preassigned complete family. All upper-bound applications retain their actual phases and their one complete pure-product source rho0.

## Anchor linearization preserves the exact objective

Let J be an allowed low-pure ternary mask with N cells. A complete incidence layout has avoidance coefficients

    z_j=product_(p in Q)(1-c_p*n_(p,j)),
    n_(p,j)=1_(the3p parent covers j)+1_(the9p child equals j).

Report542's sharp response is

    Phi_J(z)=1-[sum_j z_j-(1/2)max_j z_j]/(N-1/2).

For any fixed vector,

    sum_j z_j-(1/2)max_j z_j
       =min_(h in J) sum_j lambda^h_j z_j,
    lambda^h_h=1/2, lambda^h_j=1 otherwise.                         (SO1)

The two finite minima, over layouts and over the chosen anchor h, commute. It is therefore enough to minimize an ADDITIVE weighted avoidance cost for each anchor type. One must then take the best anchor type. An anchor restricted to a particular root-size orbit need not maximize avoidance across cells in a different orbit; its separate branch value is a linearized response, not by itself the complete Phi optimum.

The allowed root sizes are(3,3,3),(2,3,3),(3,3),(2,3). Within-root leaf permutations and permutations of equal-size roots give respectively1,2,1,2 anchor orbits. These symmetries transport all incidences together and do not change a fixed original phase table separately in each cell.

## Five cells dominate every other low-pure mask

For fixed selected role sets I,K, write Opt_N(I,K) for the maximum sharp response over incidences on the N-cell mask. Then

    Opt_9<=Opt_6<=Opt_5,
    Opt_8<=Opt_5.                                                  (SO2)

This is an analytic comparison of the free-incidence optimization for every I,K, not a conclusion inferred from the computed4096 tables.

To prove it, write g_j=1-z_j, choose a coefficient-minimizing cell h, and express Phi as the weighted mean with weight1/2 at h and1 elsewhere. For a three-root mask, delete a root of least weighted mean. The weighted mean on the remaining cells cannot decrease. If h remains, the inherited weights are again the same half-anchor weights. If h is deleted, the uniform mean on the remaining M cells is no larger than their half-minimum envelope because

    (S-m/2)/(M-1/2)-S/M=(S-M*m)/[2*M*(M-1/2)]>=0.

Move every parent role in the deleted root to a surviving root and every deleted child role to a surviving cell. None of these roles previously acted on a retained cell, so the retained multiplicities can only increase. Each prime still has at most one role of each kind; same-cell coincidence is admissible using the distinct outside roots from542's construction. Thus every retained g_j weakly increases. Deleting one root sends9 cells to6, and8 cells to either5 or6.

For a six-cell mask, remove a minimum cell h and move any child roles it carried to another allowed cell. Parents remain in nonempty roots. Before relocation, the remaining five-cell uniform mean dominates the old envelope:

    (S-m)/5-(S-m/2)/(6-1/2)=(S-6*m)/55>=0.

The five-cell half-minimum envelope is larger still, and relocation cannot decrease it. This proves SO2, including empty I or K.

The comparison reconstructs a DIFFERENT admissible finite family through542's sharpness theorem. In particular deleting the size-two root of the eight-cell mask removes its old forbidden child as well; the new six-cell family has a pure3 class and no redundant pure9 class inside it. SO2 does not add pure classes to one fixed family while pretending its phases, source law and complete survivor are unchanged.

For exact global optimization only the(2,3) mask and its TWO anchor orbits are therefore required. The retained computation also evaluates the other masks as an independent check of every instance of SO2.

## Two role masks, one exact leaf cost

For each surviving root r let A_r contain the primes whose selected3p parent is placed there, and let B_r contain the primes whose selected9p child lies there. The A_r partition I. Independently, the B_r partition K. A_r and B_r MAY overlap; a prime's two roles may also be in different roots.

Inside a root, assign its child roles by an ordered partition B_r=D_1 disjoint-union ... disjoint-union D_s, where s is the number of allowed leaves. Empty assignments are allowed. Its leaf avoidance factor is exactly

    f(A,D)=product_(p in Q)[1-c_p*(1_(p in A)+1_(p in D))].           (SO3)

Thus the shared-prime interaction is settled before any root costs are added. It is not represented by independent parent and child probabilities.

With ordered leaf weights lambda_t from the fixed anchor, define

    G_0(A,empty)=0, G_0(A,B nonempty)=infinity,
    G_t(A,B)=min_(D subset B)
                [G_(t-1)(A,B without D)+lambda_t*f(A,D)].          (SO4)

Induction gives exactly the minimum over all ordered child partitions. In particular an empty child assignment still incurs its positive leaf avoidance cost: f(empty,empty)=1, not zero. Only the initial state with no processed leaf has zero cost.

For the roots with their completed local tables G_r, define

    H_0(empty,empty)=0, H_0(A,B)=infinity otherwise,
    H_r(A,B)=min_(C subset A, E subset B)
                [H_(r-1)(A without C,B without E)+G_r(C,E)].        (SO5)

Every literal incidence pattern uniquely partitions its two sets of named roles in this way. Conversely every such pair of root partitions and ordered child partition specifies one admissible incidence for each selected role. Induction in SO4 and SO5 therefore proves both optimization inequalities. Backpointers recover a complete layout, and542's extremal construction gives actual finite irredundant families approaching its value with globally fixed mixed phases.

The scalar root table is sufficient here because the anchored objective adds across roots AFTER each root's complete set of prime roles is fixed. This does not authorize multiplying in another future block that reuses an already processed prime without its joint information.

## Integer arithmetic and exact table size

Set

    d_p=p(p-2), D0=product_(p in Q)d_p,
    F(A,E)=product_(p in Q)[d_p-(p-1)*(1_A(p)+1_E(p))].

Then f(A,E)=F(A,E)/D0. Unselected primes contribute their d_p factor, so the denominator is common to every partial I,K. Scale leaf weights by two: the anchor costs F, every other leaf2F. All DP steps become addition and comparison of nonnegative unbounded integers. If W is the minimum integer cost after comparing the appropriate anchor orbits, the exact block supremum is

    B(I,K)=1-W/[D0*(2N-1)].                                      (SO6)

For an empty block the terminal value is D0*(2N-1), giving B=0. No empty leaf or root is silently discarded.

For n outside primes and selected sets of sizes i,k, each role-mask table has at most2^(i+k) entries. A leaf-convolution stage takes2^i*3^k submask candidates. A root-convolution stage takes3^(i+k) candidates. These are exact finite bounds, not a polynomial bound as n grows. The same table computes all final selected subsets without restarting the convolution for each endpoint.

The implementation uses n=6 and shares the leaf-kernel table plus five root-local tables, then six outer tables covering all masks/anchor orbits. Its measured mathematical workload is:

| Quantity | Exact count |
| --- | ---: |
| Entries per table | 4096 |
| Stored objective scalar cells | 49152 |
| Separate backpointer payload cells | 40960 |
| Leaf-convolution candidates | 186624 |
| Root-convolution candidates | 3188646 |
| Total convolution candidates | 3375270 |

The state guard was100000 OBJECTIVE SCALAR CELLS. This is not a bound on all Python objects or total memory. The twelve tables stayed below it; a rejected allocation produces no complete optimum. Using SO2 analytically would reduce the two required outer tables to8192 entries and the full objective-table count to32768, but the retained run keeps the other masks to verify the domination.

## Exact endpoints and an independently reconstructed optimum

The [general subset consumer](../../frontier/cover-geometry/two_depth_subset_dp.py) and [retained exact table](../../frontier/cover-geometry/two_depth_subset_dp.json) compute all4096 selected pairs(I,K). They pass150 named checks, including the empty-role costs,64 independent comparisons with541's sharp single-depth formula, and all single-child and same-prime two-role cases. Every one of the4096 winning endpoints is backtracked to literal parent/child incidences and its objective is recomputed directly from SO3. The4096 five-cell domination comparisons also pass.

For the full twelve-role block,

    B(Q,Q)=248235201446/500867742375.                            (SO7)

One recovered optimizer places every3p parent in the three-cell root. All9p children lie in the two-cell root: the19 child occupies the half-weight anchor and all five other children share its other cell. If u(A)=1-product_(p in A)(1-c_p), its response is

    [6*u(Q)+2*u(Q without19)+c_19]/9,

which equals SO7. This layout was reconstructed from the global optimum; it was not imposed as an optimization restriction. The exact incidence optimum corresponds to an actual supremum via542; it need not be attained at finite pure height.

The run measured0.2270129579 seconds through the completed arithmetic and certificate checks, before result serialization, with sampled process peak RSS30130176 bytes at that point. Per-table objective-state and transition counts are retained in the mathematical data. Timing and RSS are emitted to standard output and excluded from the pinned mathematical JSON so repeated exact runs can reproduce its content hash. The reported measurement concerns this six-prime implementation on Python3.14.3, Darwin arm64, Mac17,3 with10 physical CPU cores and34359738368 bytes RAM; it is not a general scaling claim.

The exact table's mask bits follow prime order(5,7,11,13,17,19). Each case records its allowed-cell count N and64-by64 integer minimum matrix. A case is a FIXED ANCHOR-ORBIT branch; take the maximum of1-W/[D0*(2N-1)] over anchor orbits for the full mask response. Taking the maximum over all six cases gives B(I,K), or just use the two N=5 branches by SO2. No floating-point display value decides any comparison.

## Complete-family mixed-loss consumer

Let kappa(d)=d^(-1)*product_(p|d)(p-1)/(p-2), and remove the twelve distinguished labels3p,9p from the other mixed numerical labels. Let S_j be the sum of their j largest remaining distinct kappa values, with S_0=0. For at most n shallow mixed originals, at cutoff10^9, the same complete pure-product source satisfies

    l <= max_(I,K, |I|+|K|<=n)
               [B(I,K)+S_(n-|I|-|K|)]
          +(4096/935)*tau_P(10^9).                              (SO8)

Every actual family's selected block is bounded by its corresponding B(I,K), and the remaining shallow originals by their distinct numerical caps. The complete retained tail bounds all deeper mixed originals. The phases and rho0 are the same throughout each family's inequality; no different branch laws or phase assignments are combined into an asserted realization.

The [inventory consumer](../../frontier/cover-geometry/two_depth_inventory_capacity.py) and [result](../../frontier/cover-geometry/two_depth_inventory_capacity.json) apply the exact table with541's monotone numerical-cap frontier and the existing pinned complete tail. The mathematical DP input is pinned at SHA256 `d0a9f89564428214cd05630f2a2de40379a45369a68f64fe9e64782bc67f7d17`; the [complete tail input](../../frontier/cover-geometry/phase_resampling_arithmetic.json) is pinned at `da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f`. They inspect finite leading labels from the infinite monotone frontier, not the old15524-label inventory or original phase families. The retained run passed33 exact checks.

At n=17, SO8 is strictly below173/250. Its largest relaxed expression uses all six parent roles and the two child roles45,63, leaving nine nonblock slots. The exact block value is15313717816/33391182825, and the nine nonblock caps sum to59428/255255. Thus the complete upper bound is

    15313717816/33391182825 +59428/255255 +(4096/935)*tau_P(10^9)
      =253711996/366936075 +(4096/935)*tau_P(10^9)
      <173/250.                                                    (SO9)

Report541's unchanged actual-loss bridge consequently puts the ONE uniform law on the complete actual survivor in G and gives its complete query bound R_P<=158050/14399<565/51. Arbitrary pure heights, every deeper mixed original, original numerical distinctness and globally fixed phases are retained.

The n=18 upper expression is larger than173/250. This only marks failure of this sufficient block-plus-cap envelope; it is not an actual-family lower witness, a sharp maximum number of permissible originals, or a failure of the desired conclusion. Likewise the relaxed maxima in SO8 need not be jointly attained by an actual block layout and all remaining shallow originals.

The new algorithm supplies exact block values for arbitrary selected inventories and a complete same-law consumer. Handling further blocks with additional shared outside coordinates, or obtaining a uniform sufficient budget for arbitrary mixed cores, remains unresolved.

[Report547](547-all-height-stars-have-a-common-survivor-law.md) aggregates ALL outside heights of the originals 3*q^b and 9*q^b into fractional parent/child budgets. An extreme-point argument licenses the larger capacities 1/(q-2), and the same subset recurrence then gives the complete all-height star loss at most 443407/681615. There is no mixed-label count cutoff in this structural class. The same full-survivor law has complete query norm at most 2304369/238208; arbitrary original supports involving several outside primes remain outside that result.

## Reproduction

The DP computes and checks the general tables. The budget consumer reads the retained table and existing tail; it does not recompute the DP or regenerate the tail. The consumer rejects changed input bytes before using the bound.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_depth_subset_dp.py --max-states 100000
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_depth_inventory_capacity.py
```

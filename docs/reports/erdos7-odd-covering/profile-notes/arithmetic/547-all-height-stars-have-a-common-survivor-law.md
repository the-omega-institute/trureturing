# All-height stars have a common survivor law

Let P={3,5,7,11,13,17,19}. Every finite family of pairwise distinct P-smooth numerical moduli greater than one, whose mixed moduli all have the form

    3^a*q^b,  a,b>=1,  q in Q={5,7,11,13,17,19},

has a complete actual survivor U with

    H(U)>=1861/23328>0.

There is no bound on the number of originals, either exponent, or the pure-prime heights. All original phases are arbitrary and globally fixed. The ONE law rho=H(.|U) belongs to the existing class G of [report534](534-one-entropy-budget-controls-every-pure-prime-chain.md), and its complete nonunit query norm satisfies

    R_P(rho)<=2304369/238208=9.673768303331542...<565/51.       (AS1)

Consequently, arbitrary additional distinct originals touching 23 or 29, and otherwise supported on P, still cannot cover. Their full survivor has Haar mass at least 17064701/1839366144. The condition on the old P-smooth originals remains essential.

The new step aggregates every outside-prime height into parent and child budgets, then optimizes those budgets jointly on the same ternary boundary. A separate analytic bound applies to an arbitrary finite set of outside primes satisfying a reciprocal budget, without fixing their number or largest member. These are ordinary proofs and exact integer/rational checks, not Lean verification or a resolution of unrestricted Erdős #7.

## 1. One complete source, including every pure height

Fix an irredundant subfamily M0 with exactly the original survivor U. Deleted originals retain their numerical identities as unused queries relative to M0. Every remaining mixed original still has the stated star shape. Fix this core once throughout the argument.

Let S_p be its complete pure-p survivor, including all retained pure heights, and set

    w_p=H_p(S_p), a_p=1/w_p,
    rho0=product_(p in P)H_p(.|S_p), Omega=product_p w_p.

The pure cylinders of an irredundant core are disjoint. The source and cylinder bounds from [report539](539-a-weighted-mixed-inventory-certifies-one-entropy-law.md) give

    w_p>=(p-2)/(p-1), a_p<=(p-1)/(p-2),
    rho_p([c]_(p^b))<=a_p*p^(-b), Omega>=935/4096.

Write ell for the rho0 probability of the union of ALL mixed originals. The actual-loss bridge SC1--SC3 of [report541](541-shared-ternary-roots-certify-sixteen-mixed-heads.md) applies whenever ell<173/250. It puts rho=H(.|U) in the SAME G and gives

    H(U)=Omega*(1-ell),
    R_P(rho)<=(4096/935-1)/(1-ell).                         (AS2)

The task below is to establish its premise uniformly from the star shape. No separately conditioned law is chosen for different depths, primes, or queries.

## 2. Sum all outside heights before optimizing ternary placement

First consider mixed originals at ternary depths a=1 and a=2. For an outside prime q and a ternary root r, let P_(q,r) be the sum of the actual rho_q cylinder masses of the originals 3*q^b whose ternary phase is r. For a modulo-nine cell j, let C_(q,j) be the corresponding sum for 9*q^b with ternary phase j. Every sum uses the fixed original phases.

Numerical distinctness gives at most one original for each pair (a,b) at this q. Hence

    sum_r P_(q,r)<=a_q*sum_(b>=1)q^(-b)<=u_q,
    sum_j C_(q,j)<=u_q,       u_q=1/(q-2).                  (AS3)

Extending these finite sums to geometric series only increases the upper bound; no infinite original family is substituted for the actual one.

On cell j, unite the active cylinders on the SAME q coordinate first. Their actual union mass h_(q,j) is at most P_(q,r(j))+C_(q,j). Only then use independence across different q coordinates under rho0. Since 2u_q<=2/3<1, all factors below are positive, and the actual cell deletion coefficient is at most

    g_j=1-z_j,
    z_j=product_q[1-P_(q,r(j))-C_(q,j)].                    (AS4)

This is a lower bound on actual avoidance, not a claim that overlapping same-prime cylinders are independent. The arrays in AS3 are comparison budgets for one actual law; their extremal allocations need not be realizable original phases.

## 3. Complete pure ternary conditioning and five-cell dominance

After the possible pure originals 3 and 9 have been removed, the allowed modulo-nine cells J have root-size masks

    (3,3,3), (2,3,3), (3,3), (2,3),

with N=9,8,6,5. Higher pure ternary originals have total scaled deletion at most 9*sum_(e>=3)3^(-e)=1/2. Thus [report542](542-an-actual-sharp-nine-cell-interface-for-two-depth-stars.md), NB3--NB4, bounds the actual shallow mixed union by

    Phi_J(g)=[sum_j g_j-(1/2)min_j g_j]/(N-1/2).

This statement holds for every nonnegative coefficient vector, including AS4. Every pure height is included in the deficit; N does not truncate the pure inventory.

The five-cell comparison SO2 of [report543](543-exact-subset-optimization-certifies-seventeen-mixed-heads.md) extends to the fractional budgets AS3. To see this directly, write Phi as a weighted mean, with weight 1/2 at a minimum cell and weight one elsewhere. In a three-root mask, delete a root of least weighted mean. The retained weighted mean cannot decrease. Move each removed parent budget into a retained root and each removed child budget into a retained cell. These moves preserve the total budgets and can only increase retained g_j. If the anchor was deleted, the new half-minimum envelope is at least the retained uniform mean.

For the six-cell mask, put S=sum g and m=min g and delete a minimum cell. Then

    (S-m)/5-(S-m/2)/(11/2)=(S-6m)/55>=0.

The new five-cell half-minimum envelope is at least its uniform mean. Move child budgets from the deleted cell to a retained one; each root remains nonempty. Every factor stays nonnegative because its total per-prime load remains at most 2u_q. Therefore every allowed mask is dominated by the five-cell mask with root sizes two and three.

These are comparisons of relaxed upper bounds. They do not modify the original family, its phases, or rho0.

## 4. Every prime budget has an extremal parent and child

On the five-cell mask, fix an anchor h and weights lambda_h=1/2, lambda_j=1 otherwise. Its weighted avoidance is

    W_h=sum_j lambda_j*product_q[1-P_(q,r(j))-C_(q,j)].

The exact envelope satisfies

    Phi(g)=1-(2/9)*min_h W_h.                            (AS5)

Fix all prime blocks except q. The objective W_h is affine in the entire q block and nonincreasing in each of its parent and child loads. Its feasible parent and child sets are simplices with total budgets u_q. A minimum is attained with the entire parent budget on one root and the entire child budget on one cell. Starting at a global minimizer on the compact product of simplices, replace one prime block at a time by such a vertex; the objective remains minimal. There are finitely many primes.

Consequently it suffices to optimize

    z_j=product_q(1-u_q*n_(q,j)),
    n_(q,j)=1_(j in the q-parent root)+1_(j is the q-child cell).

This proves the reduction for arbitrarily many original outside heights. The roles now represent WHOLE height columns. Substituting u_q into an individual-label table without AS3--AS5 would not justify that reduction.

## 5. Exact six-prime bound and the complete ternary tail

For Q={5,7,11,13,17,19}, put

    d_q=q-2, D=product_q d_q=378675,
    F(A,E)=product_q[d_q-1_(q in A)-1_(q in E)],

where A is a root's parent-role mask and E a leaf's child-role mask. The leaf avoidance is F(A,E)/D. Double the weights: an anchor costs F, and an ordinary leaf costs 2F.

The subset-partition recurrence SO4--SO5 of report543 applies with this new integer leaf cost. For a fixed parent mask, partition its child inventory over the root's ordered leaves, minimizing the sum of their weighted F costs. Then split the six parent roles and six child roles independently between the two roots. Induction over leaves proves the local minimum; the 64*64 complete root splits exhaust the outer choices. Both anchor-root orbits are required.

| Anchor root size | Minimum doubled cost | Shallow deletion upper bound |
| --- | ---: | --- |
| 2 | 1517020 | 378211/681615 |
| 3 | 1569570 | 122567/227205 |

The deletion response is 1-cost/(9D), so the first row is the global maximum. A literal minimizer has roots A={A0,A1}, B={B0,B1,B2}, anchor A1, and placements

| q | 5 | 7 | 11 | 13 | 17 | 19 |
| --- | --- | --- | --- | --- | --- | --- |
| Parent root | B | A | B | B | B | B |
| Child cell | B0 | A0 | B1 | A0 | A0 | A0 |

Its avoidance numerators on (A0,A1,B0,B1,B2) are

    (181440,302940,89600,156800,179200).

Their doubled anchored sum is 1517020, and the anchor has the greatest avoidance. This certifies the stated relaxed optimum; it is not an assertion of actual-family sharpness.

Every remaining mixed original has a>=3. The complete saturated tail, with NO cutoff on either exponent, is

    sum_q sum_(a>=3,b>=1) 2*3^(-a)*(q-1)/(q-2)*q^(-b)
      =(1/9)*sum_q 1/(q-2)=7244/75735.

It is disjoint from the two shallow ternary columns already included. The union bound under the SAME rho0 now gives

    ell<=378211/681615+7244/75735
       =443407/681615<173/250,
    173/250-443407/681615=1413529/34080750>0.             (AS6)

Applying AS2 proves AS1 and H(U)>=1861/23328. All query heights are included; the constant does not come from a finite query-depth sample.

## 6. An arbitrary finite outside-prime set under one budget

There is also an analytic bound which does not fix the number or size of the outside primes. Let R be any finite set of primes at least eleven and take

    Q={5,7} union R, P={3} union Q,
    t=sum_(q in R)1/(q-2)<=1/3.

Retain the same hypothesis that every mixed modulus is 3^a*q^b. The source bounds, aggregation, five-cell dominance and extremal allocations above apply unchanged.

For fixed anchor weights, keep 5 and 7 exactly and define

    b_j=lambda_j*(1-n_(5,j)/3)*(1-n_(7,j)/5),
    S=sum_j b_j, Rmax=max_(root C)sum_(j in C)b_j, M=max_j b_j.

The following finite inequalities hold simultaneously:

    S>=79/30,  3S-Rmax-M>=28/5.                         (AS7)

Here is the complete table of minima. Each row examines the five child positions for each prime; within-root symmetry leaves two anchor representatives.

| 5-parent root size | 7-parent root size | Anchor root size | Minimum S | Minimum 3S-Rmax-M |
| --- | --- | --- | --- | --- |
| 3 | 3 | 3 | 14/5 | 29/5 |
| 3 | 3 | 2 | 79/30 | 28/5 |
| 3 | 2 | 3 | 41/15 | 6 |
| 3 | 2 | 2 | 8/3 | 17/3 |
| 2 | 3 | 3 | 14/5 | 29/5 |
| 2 | 3 | 2 | 43/15 | 28/5 |
| 2 | 2 | 3 | 91/30 | 6 |
| 2 | 2 | 2 | 49/15 | 31/5 |

An independent arithmetic reduction verifies the table. For nonnegative w_j and fixed 7-parent root C, minimizing over its child gives

    min_child sum_j w_j*(1-n_(7,j)/5)
      =sum_j w_j-[sum_(j in C)w_j+max_j w_j]/5.

For the S column use w_j=lambda_j*(1-n_(5,j)/3). For the second column use

    3S-Rmax-M=min_(root C,cell k)sum_j[3-1_(j in C)-1_(j=k)]*b_j,

whose bracket is nonnegative, and apply the same child elimination. This proves AS7 by the listed finite cases; no actual original-family enumeration is involved.

For the other prime factors, the product inequality product(1-x_i)>=1-sum x_i gives

    W_h>=S-sum_(q in R)u_q*sum_j b_j*n_(q,j)
        >=S-t*(Rmax+M)
        >=(1-3t)S+(28/5)t
        >=79/30-(23/10)t.

The last step uses precisely t<=1/3. Combining AS5 with the complete a>=3 tail gives

    ell<=56/135+(23/45)t+(1/9)(1/3+1/5+t)
       =64/135+(28/45)t<=92/135<1.                    (AS8)

Thus the full original survivor satisfies

    H(U)>=(5/16)*product_(q in R)[(q-2)/(q-1)]
                   *[71/135-(28/45)t]>0.

This allows arbitrarily many outside primes provided the displayed reciprocal budget holds. The seven-prime G constants are not asserted for this variable carrier. At R={11,13,17,19}, AS8 gives 256688/378675; AS6 supplies the stronger fixed-carrier estimate by optimizing all six factors jointly.

## 7. Arbitrary 23/29 extensions use the same supported law

Return to the seven-prime theorem AS1. Any additional original supported on P union {23,29} and touching 23 or 29 has a unique numerical label

    d*23^j*29^k,  d P-smooth, j+k>0.

Use rho tensor H23 tensor H29. One common rho must bound all old-coordinate cylinder queries. The unit cofactor contributes one, and numerical distinctness plus the complete outside tail give the actual added union bound

    added loss <=(1+R_P(rho))*sum_(j+k>0)23^(-j)*29^(-k)
               <=(1+2304369/238208)*(51/616)<1.

This is the existing common-law tail consumer, as in [report527](527-four-projected-phases-preserve-arbitrary-later-residues.md), Q4. No outside phase or old cofactor height is restricted. The remaining relative probability is at least

    1-(51/616)*(1+2304369/238208)=17064701/146736128.

Since rho is uniform on the ENTIRE old survivor, multiplying by its Haar lower bound gives

    H(full extended survivor)
       >=(1861/23328)*(17064701/146736128)
        =17064701/1839366144>0.                       (AS9)

The complete old source is used once. AS1 is not asserted as a query bound for the newly conditioned extended law.

## 8. Verification and remaining boundary

The [six-prime program](../../frontier/cover-geometry/all_height_star_grid.py) and its [result](../../frontier/cover-geometry/all_height_star_grid.json) passed 64 named exact checks. They check all 4096 integer leaf factors, both anchor minima and their reconstructed literal layouts, the separately displayed minimizing layout, complete tails, the existing G budget and AS9. The optimization uses 186624 local partition candidates and 8192 complete root splits.

The independent [two-prime program](../../frontier/cover-geometry/star_fractional_two_prime_bound.py) and its [result](../../frontier/cover-geometry/star_fractional_two_prime_bound.json) passed 61 named exact checks. These include 200 symmetry representatives, all 500 literal layouts with every anchor, 500 root/maximum linearizations, 400 analytic child-elimination candidates, the eight-row table and the general t=0 and t=1/3 endpoint constants. Separate witnesses are stored for both minima in each row; the two minima need not occur together.

Both programs use exact integers and fractions, import no project producer or old data, and check explicit exceptions even under Python optimization. The mathematical result hashes are respectively `7fe4b22ba06257118bef182cb718070cce67e064bc55e9bc31afb82f60f4fe9b` and `5775d37d5bdbeadbe5c63c0c0dd59102333b6f52170b0988c21258bb50a0bf49`. The all-height and variable-carrier conclusions also require the ordinary aggregation, dominance and extreme-point arguments above; a finite table by itself would not prove them.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_height_star_grid.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/star_fractional_two_prime_bound.py
```

The structural hypothesis covers the complete unbounded collection of star labels. It does not cover old moduli with several outside primes, such as 3^a*5^b*7^c, or old mixed moduli not involving 3, such as 5^b*7^c. Their shared outside supports do not satisfy the separate parent/child simplex model AS3--AS4. Treating such a support as an independent new coordinate would discard its correlation with the existing prime factors.

This closes an unrestricted-height star subclass, not the unrestricted distinct odd covering problem. A common quantitative law for arbitrary original mixed supports remains unresolved.

[Index](../../marked_head_profile.md) · [Row/tree flow](443-one-supported-law-couples-rows-and-tree-prefixes.md) · [Occupied-child restrictions](445-occupied-branch-restrictions-and-weighted-root-caps.md)

# Direct child-tree flow and bounds from actual branch incidence

These are ordinary finite-flow deductions with exact rational construction controls. No new Lean certification, literature-priority claim, or resolution of unrestricted Erdős #7 is asserted.

A direct flow preserves the literal second-five child until it reaches an actual source point. It gives one law with pure mod25 cap 1/9 and child/seven-prefix cap 3 kappa/10. For four first-five roots, if each root/first-seven-prefix contains at most one child, the resulting complete original-label bound is 353/45 at seven-height two and 1178/135 at height three, both below nine. Allowing one designated root to contain two children gives 1157/135 at height two; allowing two such roots gives 394/45. The incidence conditions are additional source hypotheses.

## General weighted direct flow

Let F be an actual subset of four distinct first-five roots, five literal second-five child digits at each root, and the leaves Y of a finite rooted seven-prefix tree. Children need not be occupied. Give every non-root prefix v a nonnegative rational capacity kappa(v). Assume that for every pair of different roots and every choice of three literal children in each root, the union of the two restricted seven projections supports a probability satisfying all kappa caps.

Choose nonnegative rational coefficients gamma_r. For each a in {0,...,5}^4 put

    T(a) = sum_r min(1/3, (5-a_r)/9),
    I(a) = {r : a_r >= 3},
    w_r = a_r gamma_r/3,  r in I(a).

Require T(a)>=1 when |I(a)|<=1; otherwise require

    T(a) + min(1, (sum_I w_r)/2,
                     sum_I w_r - max_I w_r) >= 1.             (D1)

Then ONE rational probability nu on the actual F satisfies simultaneously

    nu(root r) <= 1/3,
    nu(child (r,c)) <= 1/9,
    nu(Y_v) <= kappa(v),
    nu(child (r,c), Y_v) <= gamma_r kappa(v).                  (D2)

Use the following directed finite network:

    source -> root r                         [1/3]
           -> child (r,c)                    [1/9]
           -> private downward seven tree   [gamma_r kappa(v)]
           -> actual child/leaf bridge      [1]
           -> public upward seven tree      [kappa(v)]
           -> sink.

The private tree is separate for each literal child; the public tree is common. Only actual points of F have bridges. A unit flow on those bridges is the desired law. Conservation gives all four cap families under that same law.

To prove every cut costs at least one, first dispose of a cut crossing an actual bridge. Otherwise count the source-side child nodes as a_r. If root r is sink-side its top edge costs 1/3; if source-side its sink-side child edges cost (5-a_r)/9. Thus the top portion costs at least T(a).

Write R for the public-prefix cut cost and L_rc for the private-prefix cut cost at an active child, before multiplying by gamma_r. If R>=1 the assertion follows. Otherwise set t=1-R>0. For two roots in I and any triples of their active children, follow the source-to-sink path of each actual projected point. Since neither its top edges nor its bridge crosses, a private or public prefix edge must cross. The projected witness law and the union bound give

    sum_(chosen c under r) L_rc + sum_(chosen c under s) L_sc >= t.

Averaging the triples gives x_r+x_s>=1, where

    x_r = 3 sum_(active c under r) L_rc / (a_r t).

For nonnegative x with all these pair inequalities, the complete-graph fractional cover bound is

    sum_I w_r x_r >= C,
    C = min((sum_I w_r)/2, sum_I w_r-max_I w_r).

Indeed, if all x_r>=1/2 use half the total weight W. Otherwise choose a minimum x_j=z<1/2; every other x_r>=1-z. The weighted sum is at least (W-w_j)+(2w_j-W)z, hence at least min(W-w_j,W/2)>=C. Therefore the private and public cut cost is at least R+C(1-R)>=min(1,C). Condition D1 finishes the cut proof. Finite max-flow/min-cut supplies the law. Separate projected witnesses need not be compatible with one another.

Two useful coefficient vectors are

    gamma = (3/10,3/10,3/10,3/10),
    gamma = (1/5,1/3,1/3,1/3),                               (D3)

with any root designated for the smaller coefficient in the second vector. Both satisfy D1. Here is a finite case proof: inactive a_r<=2 contribute exactly 1/3. For a fixed active set, increasing a_r by one lowers T by 1/9, while the minimum in D1 increases by at most gamma_r/3<=1/9. Its worst case is therefore a_r=5 at every active root. The minima indexed by active-root count 0,...,4 are respectively

    uniform:    4/3, 1, 7/6, 13/12, 1;
    designated: 4/3, 1, 1,   19/18, 1.

The constructor also checks all 1296 patterns with exact fractions.

## Arithmetic source condition and incidence transfer

Let F subset Z/25 x Z/7^K, K>=1, have exactly four occupied first-five roots and meet every product of a complete ternary five-tree of height two and a complete five-ary seven-tree of height K. The fifth first-five root is empty. Joining it to any pair of occupied roots shows that each pair/child-triple projection blocks every five-ary seven-tree. The complement duality of [375](375-deep-prime-prefix-projections-and-tree-contraction.md) supplies a complete ternary tree in that projection, and its uniform law satisfies kappa(v)=3^(-B) at prefix depth B. Thus D2 applies.

For a root r define m_r as the maximum, over first-seven digits u, of the number of distinct literal children c with an actual source point (r,c,y) satisfying y mod7=u. Every deeper seven prefix lies inside one such first-digit cylinder. Under the SAME D2 law,

    nu(root r, Y_v) <= m_r gamma_r 3^(-B), B>=1.             (D4)

This is a statement about joint incidence, not the separate counts of occupied five and seven branches.

For clarity, a complete layout b assigns an independent residue b_d to every divisor d of L=25*7^K, including d=1. Write

    load_b(x) = sum_(d|L) 1[x=b_d mod d],
    Gamma_L(nu) = max_b E_nu load_b^2.

The law is chosen before any layout. Put

    S_K = sum_(B=0)^K (2B+1)3^(-B) = 3-(K+2)3^(-K),
    beta = max_r m_r gamma_r,   G = max_r gamma_r.

Intersecting two independently phased congruence cylinders gives either the empty set or one cylinder at their LCM. There are (2A+1)(2B+1) ordered exponent pairs with maximum (A,B). D2 and D4 therefore give

    Gamma_L(nu) <= S_K + 14/9 + (S_K-1)(3 beta+5G).          (D5)

All 3(K+1) original numerical labels and all 9(K+1)^2 ordered pairs remain. In particular 14/9=3(1/3)+5(1/9) is the contribution from nontrivial pure-five labels.

If every m_r<=1, use uniform gamma=3/10. Then

    Gamma_L(nu) <= S_K+14/9+(12/5)(S_K-1).

At K=1,2,3,4 this is 268/45, 353/45, 1178/135, 1229/135. Since S_K increases, exactly K<=3 is below nine for this formula.

If one designated root has m_r<=2 and all others have m_r<=1, put gamma=1/5 there and 1/3 elsewhere. This gives beta<=2/5, G<=1/3, and

    Gamma_L(nu) <= S_K+14/9+(43/15)(S_K-1).

At K=1,2,3 this is 289/45, 1157/135, 3877/405. Exactly K<=2 is below nine for this formula. These conditions allow full five-child fibres; they are not inferred from product blocking alone. The standalone complete five-ary seven projection required of a minimum-cover residual is compatible with these results, but is not needed for their proofs.

## Two doubled roots: intersect the caps of the same law

Suppose two designated roots have m_r<=2 and the other two have m_r<=1. Choose

    gamma=(1/5,1/5,2/5,2/5),

with the smaller coefficients at the doubled roots. These also satisfy D1. Since 2/5 exceeds1/3, the preceding monotonicity proof must be replaced. For q=|I|>=2, examine each affine branch of the minimum separately. In the half-sum branch, every coefficient gamma_r/6-1/9 is negative, so the minimum occurs at a_r=5. The smallest active gamma sums for q=2,3,4 are2/5,4/5,6/5, giving

    T+(sum_I w_r)/2 >= (4-q)/3+(5/6)sum_I gamma_r >=1.

For T+sum_(r in I except j)w_r, choose a_j=5, every other low-weight a_r=5, and every other high-weight a_r=3. If ell counts the low-weight roots in I excluding j, the branch minimum is

    (7+2q-2ell)/9+(q-1-ell)/15.

Its least values for q=2,3,4 are1,1,58/45. The branch T+1 is automatically at least1, and |I|<=1 was already handled. Thus D2 holds with these coefficients under one actual law.

Now beta<=2/5 and G<=2/5. Direct use of D5 gives409/45 at K=2. But the law ALSO has pure-child mass at most1/9. Every child/seven-prefix cylinder lies inside that child, so its cap is the minimum of both bounds. At (A,B)=(2,1),

    cap(2,1) <= min(1/9,(2/5)/3)=1/9.

There are15 ordered exponent pairs with this maximum. The correction saves15(2/15-1/9)=1/3 without changing the law or any phase quantifier. Hence

    Gamma_L(nu) <= S_K+14/9+(16/5)(S_K-1)-1/3.              (D6)

At K=1,2,3 this is289/45,394/45,443/45. Thus exactly K<=2 is below nine for this formula. The constructor intersects the pure-five, pure-seven and joint bounds before summing all original pairs.

For comparison,409/45 is the exact optimum of the UNINTERSECTED D5 expression for the two-double multiplicity profile and D1. Indeed, with A=max gamma and B=max(2gamma_1,2gamma_2,gamma_3,gamma_4), the fully active cut requires sum gamma>=6/5, while sum gamma<=B+2A and B>=A. Therefore

    3B+5A=(8/3)(B+2A)+(B-A)/3>=16/5.

The displayed coefficients attain it. D6 shows why that restricted optimization is not an obstruction to the source or even to a better estimate from the SAME network caps. Intersecting already available bounds removes the purported threshold failure.

## A source family outside the previous two selectors

For K>=2 use literal five roots r=1,2,3,4 and children c=0,...,4. At root1 use the following child/first-seven-column incidences, each with second-seven digits 0,...,4:

    c0 -> {1}, c1 -> {6}, c2 -> {2,3}, c3 -> {4,5}, c4 -> empty.

At roots r=2,3,4 use c -> g=c+1. At column g=1 take second digits E_r={r-1,r}; at g=2,...,5 take all second digits 0,...,4. Every later seven digit is in 0,...,4. This defines F_K with 96*5^(K-2) points and occupied-child counts (4,5,5,5).

Each root/first-seven cylinder contains at most one child. Both first-prime zero roots are absent, and the entire mod25 cylinder21 (r=1,c=4) is absent. The latter retains the necessary pure-prime exclusion of the divisor-closed extremal model in [350](../321-384/350-extremal-paired-branch-and-source-support.md). The exact seven projection is

    {1,2,3,4,5,6} x {0,...,4}^(K-1),

so it contains a complete five-ary tree. These necessary residual conditions do not assert realization by an actual covering system.

For two roots in {2,3,4}, their child triples give column triples C,D in {1,...,5}. If C differs from D, their union has at least four columns, including three among 2,...,5 with full five-ary tails. If C=D omits1, all three tails are full. Otherwise column1 has second digits E_r union E_s, containing at least three digits, and the other two tails are full. Each restricted pair projection contains a complete ternary seven-tree.

A child triple at root1 includes at least two occupied children. Every such pair except {c0,c1} supplies at least three full columns by itself. The exceptional pair supplies full columns1,6; any child triple at another root supplies at least two additional full columns among2,...,5. Thus every restricted pair again contains a ternary seven-tree. Every ternary first-five choice includes two occupied roots, and every ternary seven-tree meets every five-ary seven-tree recursively. This proves full product blocking.

Call a root individually robust if every one of its child triples blocks every full seven test tree. None is robust. At root1 choose {c0,c1,c4} and a seven test excluding first columns1,6. At any other root choose columns{1,2,3}; a seven test excludes2,3 at its first level and uses the five second digits outside E_r under column1. These tests miss the respective restricted fibres.

Every one of the nineteen occupied-child deletions destroys product blocking. For a deletion at a full root r, choose another full root s. If deleting column1, select {1,h,i} at both roots, with two distinct h,i in {2,3,4,5}. If deleting column j>1, use {j,h,i} at r and {1,h,i} at s, with h,i outside{j}. Only h,i remain full, while column1 has just E_s. For a deletion at root1, choose a surviving two-column child among c2,c3, with columns h,i. At root1 select the deleted child, the already empty c4, and this surviving child; at a full root s select columns{1,h,i}. This gives the same remaining projection. In all cases use first-five roots{0,r,s}; a legal seven test excludes h,i at the first level and E_s at the second level under1. Later test branches can be completed arbitrarily. The modified source misses this product test.

Further deletions cannot repair a missed test. Every blocking subsource must therefore retain all nineteen occupied children, including all three full roots. Neither selection nor a mixture of blocking subsources can reach [445](445-occupied-branch-restrictions-and-weighted-root-caps.md)'s at-most-one-full-root condition. The absence of robust roots also excludes the three-robust-root consumer of [444](444-uniform-subtree-restrictions-couple-two-prefix-trees.md). This separates the stated abstract source criteria while retaining the indicated necessary residual exclusions; it does not exclude every other sufficient theorem or prove arithmetic realization. The K=2,3 sources satisfy the preceding incidence bounds.

## What the direct flow adds, and what remains missing

For full child fibres, report445 gives root<=1/3, child<=1/5, pure seven<=kappa, root/seven<=kappa/2 and child/seven<=3kappa/10. Uniform direct flow retains the root, pure-seven and child/seven bounds and improves the child marginal to 1/9. The pure 1/9 marginal alone was already available in [376](376-complete-prime-chain-transport-and-joint-prefix-laws.md); its simultaneous combination with the child/seven bound is the additional conclusion here. The direct network does not by itself retain the root/seven half factor, so the two full cap systems are not mutually dominant.

If one could additionally impose root/seven<=beta*kappa on the uniform direct law at K=2, its complete LCM bound would be

    58/9+(14/3)beta.

Thus beta<23/42 would suffice; beta=1/2 would give 79/9. Without the incidence condition, this simultaneous assertion remains unproved. Merging child copies at a root/seven node and later splitting them can send a path to a different child's actual bridge, losing the association with its original child budget. That modification is not a valid proof of the extra cap.

For the one-doubled-root hypothesis, the coefficient43/15 in D5 is optimal within D1 and this maximum-cap expression. Let t be that root's coefficient. Two fully active roots force t>=1/5, and four fully active roots force sum gamma>=6/5. Consequently

    3 beta+5G >= 6t+(5/3)(6/5-t) >=43/15.

The displayed designated coefficients attain equality. This is an obstruction to retuning this particular certificate, not a lower bound on an actual source's Gamma. Improved support-dependent bounds or a moment estimate that retains simultaneous phase information are outside it.

The results do not establish the incidence conditions for all actual extremal residuals, arbitrary five/seven heights, or simultaneous transport of the full outside-cofactor tests. They make no assertion of projective compatibility as K or the source changes. Unrestricted Erdős #7 remains open.

## Exact construction controls

The [standard-library constructor](../../frontier/cover-geometry/direct_child_tree_caps.py) reuses the exact `projected_capacity` and `_unit_flow` primitives of report443. The general interface accepts all rational nonnegative prefix capacities and any gamma passing D1; it checks the 600 pair/triple projection premises, actual support, normalization and every final cap. The incidence consumer checks literal CRT transport, every original cylinder cap and the complete LCM sum. A maximum-cylinder sum is an upper bound on Gamma, not an optimized game value.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/direct_child_tree_caps.py
```

The retained [exact laws and data](../../frontier/cover-geometry/direct_child_tree_caps.controls.json) have the following values:

| Actual source | Source points | Positive law atoms | Original labels / ordered pairs | Theorem upper | Law's LCM upper |
| --- | ---: | ---: | ---: | ---: | ---: |
| F_2 | 96 | 31 | 9 / 81 | 353/45 | 346/45 |
| F_3 | 480 | 90 | 12 / 144 | 1178/135 | 769/90 |
| F_2 plus (4,0,2+7v), v=0,...,4 | 101 | 27 | 9 / 81 | 1157/135 | 223/27 |
| F_2 plus (r,0,2+7v), r=3,4; v=0,...,4 | 106 | 33 | 9 / 81 | 394/45 | 77/9 |

The last two sources have multiplicities (1,1,1,2) and (1,1,2,2); adding actual points preserves blocking and the standalone projection. The first two controls also check all four nonrobust witnesses, with capacities2/3,8/9,8/9,8/9, and all nineteen failed occupied-child deletions, each with projected ternary-cap capacity8/9. The two-double source is a control of its incidence theorem; no deletion obstruction is asserted for that enlargement. These finite controls validate the constructions on the stated sources; the general conclusions use the proofs above.

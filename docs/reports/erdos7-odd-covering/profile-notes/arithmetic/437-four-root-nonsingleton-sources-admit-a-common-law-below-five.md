[Index](../../marked_head_profile.md) · [Pair-source law](434-four-root-pair-sources-admit-a-common-law-below-five.md) · [Minimum sources](435-minimum-height-two-sources-and-a-nine-point-flow.md)

# Four-root non-singleton sources admit a common law below five

Let S be an actual source at heights H5=2,K7=1. Select four distinct first-five roots and exactly three distinct active child digits in each selected root. Let N_(r,a) be the actual seven-column neighborhood of each of these twelve children. Assume

1. Every N_(r,a) has at least two elements.
2. For each root r, let B_r be the set of those N_(r,a) having exactly two elements. The four B_r are pairwise disjoint.

There is a constructive probability law supported on 24 actual points of S with

    Gamma(nu) = max_(independent phases a_m)
                E_nu[(sum_{m in {1,5,25,7,35,175}}
                                      1_(z=a_m mod m))^2]
              <= 149/30 < 5 < 46/9.                       (NS1)

The law is selected before any test phases. The global label 7 keeps one shared phase across all roots, and the phases for 5,25,35,175 remain independently variable. No condition on the total seven-column projection is required. The neighborhoods can have any size from two through seven: prior compression to size three is unnecessary.

With exactly three active children per root and all neighborhoods of size at least two, B_r is precisely the root's original bad-pair set. Removing a pair E makes that root bad exactly when one of its neighborhoods equals E. Thus the second hypothesis is the original product-tree condition for this source class.

This closes the mixed pair/triple class, including sources whose neighborhoods cannot be reduced to pair sets disjoint between roots. It does not prove that every admissible source has three selected nonsingleton children in each of four roots, or settle higher source heights or unrestricted Erdős #7. This is a repo-derived ordinary proof with exact computational checks, not a new Lean theorem or a claim of literature priority.

## 1. Exact degree-two incidences control the entire capacity cut

For a seven column c, define

    P_c = #{children whose original neighborhood has exactly two
                          elements and contains c},
    s = max_c P_c,

where repeated equal neighborhoods in one root retain their child multiplicity. These are counts of original two-element neighborhoods, not counts of all source points or selected pairs.

Use the integral network

    source -> child -> column -> sink,

with capacities two on each source-to-child edge, one on each actual child-to-neighbor edge, and eight on each column-to-sink edge. An integral flow of value 24 selects two distinct actual neighbors per child, with at most eight selected points in any column.

For a set U of seven columns, minimization over the child vertices in a cut gives

    cut(U) = 8|U| + sum_child min(2, |N_child minus U|).     (NS2)

Thus the maximum flow equals the minimum of (NS2). All 128 possible column sets fall into four elementary cases:

* U is empty: the cut is 24, since every neighborhood has at least two elements.
* U={c}: only an original exact pair containing c reduces a child's contribution below two. Therefore cut({c})=32-P_c.
* U={c,d}: let P be the number of exact-pair children, T the number of exact-triple children, and m_cd the multiplicity of the pair {c,d}. The deficit below 24 from exact pairs is P_c+P_d<=P+m_cd. The deficit from triples is at most T; neighborhoods of size at least four cause no deficit. Cross-root pair disjointness gives m_cd<=3, and P+T<=12. Hence the total deficit is at most 15 and cut(U)>=16+24-15=25.
* |U|>=3: the column contribution alone is at least 24.

Consequently the exact maximum-flow value is

    maxflow = min(24, 32-s).                               (NS3)

In particular, s<=8 is sufficient and necessary for this network to select all 24 points. The proof uses only the original pair ownership; it does not require the selected pair sets to be disjoint between roots.

## 2. The full-flow branch gives the existing uniform-law bound

If s<=8, choose an integral flow of value 24 and use the uniform law on its selected points. Its simultaneous unnormalized cell caps for the original moduli 1,5,25,7,35,175 are

    24, 6, 2, 8, 3, 1.

Every root has three children, every child has two selected points, and a root-column cell contains at most one point per child. An intersection of two original test classes is either empty or a cell at their least common multiple. The 36 ordered label pairs have lcm multiplicities 1,3,5,3,9,15. The same-law cell-cap calculation of reports 432 and 434 gives

    Gamma(nu) <= (24+3*6+5*2+3*8+9*3+15)/24
              = 59/12 < 149/30.                            (NS4)

The flow may assign the same selected unordered pair to children in different roots. That does not affect any of the displayed simultaneous cell caps.

## 3. The deficient-flow branch retains only a heavy set of original spokes

Suppose s>=9 and choose c with P_c=s. A child whose original neighborhood is an exact pair containing c is called a spoke child. There are s such children. Every other child has at least two neighbors different from c: this is immediate for an exact pair not containing c, and follows from degree at least three for a larger neighborhood.

Retain both neighbors of every spoke child. At each of the remaining 12-s children choose any two actual noncenter neighbors. Call these the exception children. Thus the selected support still has 24 actual points, and every selected incidence of c belongs to an original exact spoke.

For y different from c, the spoke pair {c,y} can occur in only one root. There are at most three such spoke points at y. The exception pairs can repeat between roots, coincide with each other, or coincide with a noncenter original pair in another root. None of those possibilities changes the bound of three for original spokes at a fixed noncenter column.

This is exactly the structural information used in the heavy-column part of report 434. It does not require the stronger global pair-disjointness premise of that report's original constructor. The present constructor therefore constructs and verifies this law directly instead of calling that constructor.

Assign integer masses and normalize as follows:

| s | At c on a spoke child | At its other endpoint | At each exception endpoint | Child mass q | Total |
|---|---:|---:|---:|---:|---:|
| 9 | 9 | 11 | 10 | 20 | 240 |
| 10,11,12 | 4 | 6 | 5 | 10 | 120 |

Every child has mass q and every root has mass 3q. If k and h denote the center and noncenter spoke masses, the exception mass is q/2. For a column y, let C_y be its total mass, D_y the largest root-column mass, and M_y the largest atom mass. The shared bounds are

    s=9:
       C_c<=9k, D_c<=3k, M_c<=k,
       C_y<=3h+3q/2, D_y<=3h, M_y<=h for y!=c;

    s>=10:
       C_c<=12k, D_c<=3k, M_c<=k,
       C_y<=3h+q, D_y<=3h, M_y<=h for y!=c.                 (NS5)

The noncenter column bound counts the at-most-three original spoke points plus at most three or two exception points. It allows all those exceptions to use the same noncenter column, even when their selected pairs repeat between roots.

## 4. The existing shared-phase calculation applies without further structure

For completeness, the exact inputs to report 434's calculation can be checked directly. Let b be the original label-7 phase and d the seven-coordinate of the independent label-35 phase. For the five-label load B from 1,5,25,7,35,

    sum_x w_x B(x)^2
      <= 26q + 3C_b + 5D_d + 2D_b + 2M_b + 2M_d
                    + 2*1_(b=d)*D_d.                     (NS6)

This is the expansion of the square on the single constructed law. The constant 26q is 12q+3*(3q)+3q+2q. The other terms respectively retain the actual global-column, root-column, and point intersections. Incompatible root or child phases only reduce the expression.

The final label 175 selects one point. When b=d, its additional cost is at most 11h. When b differs from d, the 7 and 35 indicators cannot both be one, so that cost is at most 9h. Substituting (NS5) gives:

| Relation between b,d,c | Numerator for s=9, total 240 | Numerator for s>=10, total 120 |
|---|---:|---:|
| b=d=c | 1163 | 594 |
| b=c, d!=c | 1121 | 592 |
| b!=c, d=c | 1049 | 514 |
| b=d!=c | 1171 | 596 |
| b,d,c all distinct | 1083 | 548 |

Hence

    s=9:  Gamma(nu)<=1171/240,
    s>=10: Gamma(nu)<=596/120=149/30.                       (NS7)

Together with (NS4), this proves (NS1) for every source satisfying the two stated hypotheses. The same b is used in every root throughout the proof. No independent marginal laws, independent choices of the global column phase, or separately optimized supports are combined.

## 5. Former pair-selection boundaries are actual consumers

Report 434 gives a 27-point source with exactly one robust root:

    root 1: 01, 03, 14
    root 2: 02, 02, 02
    root 3: 12, 12, 12
    root 4: 012, 012, 012.

Its original bad-pair sets are disjoint, but the first three roots force all three pairs inside {0,1,2}, leaving no available pair for the fourth root under a cross-root pair-disjointness requirement. Here s=6, the present network has flow 24, and its prescribed uniform law has exact Gamma=59/12. The selected pair sets are not disjoint; the common-law theorem nevertheless applies.

The 38-point source from the same report has neighborhoods 012 at every child except root 4's first child, whose neighborhood is 01234. It also has no pair-disjoint reduction, although all roots are robust. Here s=0, the network again has flow 24, and the present prescribed law has exact Gamma=59/12. This provides a direct construction in addition to its previously available robust-root law.

An explicit mixed 25-point source verifies the high branch where exception pairs repeat across roots:

    root 1: 01, 01, 01
    root 2: 02, 02, 02
    root 3: 03, 03, 014
    root 4: 04, 04, 14.

It has s=10. Choosing the two noncenter neighbors of 014 produces pair 14 in root 3, already present in root 4. This is permitted by the current proof. The constructed heavy-column law has exact Gamma=149/30. It attains the bound for this prescribed constructor, not a minimax lower bound against all supported laws.

A mixed 26-point s=9 control similarly attains 1171/240 while repeating an exception pair across roots. A source with only three projected columns checks that no standalone five-column premise is needed. The checks also transport a source to different actual root digits, including root zero, and different child digits inside each root; the complete original-label maximum is preserved.

## 6. Reusable constructor and scope of the checks

The [standard-library constructor](../../frontier/cover-geometry/mixed_neighborhood_common_law.py) accepts arbitrary four-by-three neighborhood records, together with optional actual root and child digits. It checks original pair ownership, chooses the full-flow or original-spoke branch, returns the supported rational law, and verifies normalization and all simultaneous cell caps. It does not require the selected pairs to satisfy the old global ownership condition. Its validation remains active under Python optimization.

For six actual controls, the program compares a separately computed integral maximum flow with all 128 explicit column-cut values and formula (NS3). It reuses report 434's `exact_gamma` finite phase checker, which retains the shared global phase and the other four root assignments, and directly validates an attaining layout in the original CRT coordinates. No new phase enumeration engine is introduced.

The proof of the general theorem is the cut argument and the five-case calculation above. The finite controls validate the construction and its arithmetic, including the two previously impossible pair-disjoint reductions. They do not replace the proof by random samples or finite orbit classifications.

The existing conditional height calculation of report 434 can now consume any actual coarse residual containing one of these configurations. It still requires Chapter 09's actual distinct-label residual and provenance hypotheses at Q0=5^2*7. Under those additional hypotheses, extension only in the five coordinate has the already established bound 16927/2523<9. An abstract source by itself does not establish those hypotheses, a seed with the heights interchanged, or extension in every prime direction.

Run the retained construction and exact controls with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_neighborhood_common_law.py

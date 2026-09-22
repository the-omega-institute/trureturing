[Index](../../marked_head_profile.md) · [Minimum coarse sources](435-minimum-height-two-sources-and-a-nine-point-flow.md) · [Common test boundary](440-joint-test-profiles-as-composable-boundaries.md) · [Actual-family height lift](441-integer-joint-moments-improve-two-axis-height-lifting.md)

# Minimum coarse sources lift through actual fibres

A full product-tree blocker with a missing first-five root and a minimum fifteen-point projection modulo175 permits each coarse cell to be isolated. Its actual fibres therefore inherit their own product-tree conditions. This gives an explicit matching lift from175 to6125 and common-law bounds below nine on two unbounded strips of prime heights. A 540-point blocker shows that the matching condition cannot be extracted automatically from an arbitrary larger coarse source, even when a good common law exists. Keeping the full seven-coordinate inside suitable mod25 fibres instead gives a separate common-law bound of eight.

These are ordinary source theorems. They do not assume that a projected source is the complement of a distinct family whose moduli divide the head carrier, and use no H1 support substitution. No Lean certification, realization as an actual minimum odd cover, or conclusion for every coarse source is claimed.

The reusable inputs are [379](379-root-forest-disintegration-and-residue-costs.md) for the full product-tree interpretation, [431](431-three-robust-five-roots-admit-a-height-two-common-law.md) for one coarse law with three robust roots, [435](435-minimum-height-two-sources-and-a-nine-point-flow.md) for the minimum-source classification, and [440](440-joint-test-profiles-as-composable-boundaries.md) for the common-law boundary discipline. The argument below retains all twelve independently phased original test labels.

## 1. Statement with actual fibres

Identify the fine carrier by CRT as Z/125 x Z/49. Let R be any subset of this carrier. Let pi be reduction to Z/25 x Z/7 and S=pi(R). Assume:

1. The first-five root zero is absent from R.
2. R meets every product T5 x T7, where T5 is a complete ternary subtree of depth3 in the five-adic tree and T7 is a complete five-ary subtree of depth2 in the seven-adic tree. Digits are read from lowest to highest.
3. |S|=15.

Then one can select exactly45 actual points of R and give them equal mass to obtain nu with

    Gamma_175(pi_*nu) = 68/15,
    Gamma_6125(nu) <= 322/45 < 9.                         (ML1)

All maxima defining Gamma retain one freely chosen residue for every divisor, including1. The selected law depends only on R and is chosen before any layout phase. If R additionally avoids seven-root zero and an actual25 class, the selected law preserves those exclusions. No extra excluded class is introduced by the construction.

For an actual normalized minimum-cover residual, these statements apply whenever its6125 projection has the stated minimum coarse projection. Other prime coordinates remain in the provenance of R; ML1 bounds the displayed head tests, not the complete invariant on every outside prime.

## 2. Minimum coarse sources isolate every cell

Projection of the full product-tree condition implies the corresponding height(2,1) condition: extend a proposed coarse pair of trees by arbitrary legal final children and project the resulting witness. By report435, the15-point projection has exactly three occupied first-five roots, each containing five points that form a matching between its five child digits and five distinct seven-root digits. The other two first-five roots are empty. The three rootwise matchings may have different column sets and different bijections.

Fix any coarse point s=(r,a,y) in S. Choose two other child digits b,c in the same root. Let y_b,y_c be their distinct matching columns. Construct a coarse product test as follows:

* The first-five ternary choice consists of r and the two empty roots.
* In root r, the second-five ternary choice is {a,b,c}; choices at the empty roots are arbitrary.
* The seven-root five-element choice is all seven columns except y_b,y_c.

The product of these two coarse trees meets S at exactly s. The target column y is distinct from y_b,y_c, so it is retained. This is isolation by a legal product of trees, not deletion of source points.

Write the actual fine fibre as

    F_s={(u,v) in Z/5 x Z/7:
          (r+5a+25u, y+7v) belongs to R}.

For arbitrary A subset Z/5 with |A|=3 and D subset Z/7 with |D|=5, extend the isolating coarse five-tree at node(r,a) with A and the seven-tree at node y with D. Complete all other selected nodes arbitrarily. These are legal trees of the full depths3 and2. Their witness in R must project to s, hence has (u,v) in F_s intersect (A x D). Consequently

    F_s meets every three-by-five rectangle.              (ML2)

Conversely, for a coarse source consisting of three five-matchings, if every F_s satisfies ML2 then R has the full product-tree property. Any full test first supplies an intersecting coarse point by the matching condition; the last children at that point form one of the rectangles in ML2. Thus checking all15 local rectangle conditions is equivalent to the full tree condition within this minimum-projection class. It is not an equivalence for arbitrary coarse sources.

## 3. Three actual matching edges in each fibre

Any bipartite graph F subset Z/5 x Z/7 satisfying ML2 has a matching of size at least3. Otherwise the finite bipartite matching/vertex-cover theorem gives a vertex cover containing at most2 vertices in total. If it uses a left vertices and b right vertices, a+b<=2. Choose three left vertices avoiding those a and five right vertices avoiding those b. Their rectangle has no edge, contrary to ML2.

Use a deterministic maximum-matching algorithm on each actual F_s and retain three matching edges. Choices for different s may be completely different. Let K_s be uniform on those three edges. The same K_s obeys

    K_s(u=u0)<=1/3,
    K_s(v=v0)<=1/3,
    K_s((u,v)=(u0,v0))<=1/3.                            (ML3)

In general the two tail coordinates are correlated. The atom bound in ML3 is1/3, not1/9; multiplying the two marginal bounds would be invalid.

Give all15 coarse points mass1/15 and use K_s within fibre s. This produces45 distinct actual fine points of mass1/45 and preserves the uniform coarse marginal.

This probability support is not a replacement for the original source
in subsequent tree-blocking arguments. A three-edge matching in a
five-by-seven fibre misses a three-by-five rectangle: choose one of
its matched rows and the two unmatched rows, then five columns avoiding
the matched row's column. The coarse isolation construction lifts this
to a product tree missing the selected45-point support. The original
R retains the assumed blocking property; the selected law retains the
moment bounds proved below.

## 4. All original phases under this one law

The uniform minimum coarse law has simultaneous cylinder caps

| Coarse exponents (A,B) | (0,0) | (1,0) | (2,0) | (0,1) | (1,1) | (2,1) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Mass cap | 1 | 1/3 | 1/15 | 1/5 | 1/15 | 1/15 |

Report435's LCM expansion gives Gamma_175<=68/15. In fact this uniform law attains that value for every such minimum source: three five-element subsets of a seven-element column set share at least one column. Center all six coarse tests at any source point in such a shared column. Its loads have square36 at itself,4 at the four other points in its root,4 at the two other points in its column, and1 at the remaining eight points. The average is68/15.

Expand an arbitrary twelve-label fine load square into all144 ordered pairs of its divisor indicators. The36 pairs whose LCM divides175 are exactly the complete coarse layout square under the coarse marginal, and cost at most68/15. For every other pair, the intersection is empty or one actual cylinder at its LCM. ML3 and the same coarse caps give the following six groups:

| Fine LCM exponents (A,B) | Pair count | Cylinder cap | Contribution |
| --- | ---: | ---: | ---: |
| (3,0) | 7 | 1/45 | 7/45 |
| (3,1) | 21 | 1/45 | 7/15 |
| (3,2) | 35 | 1/45 | 7/9 |
| (0,2) | 5 | 1/15 | 1/3 |
| (1,2) | 15 | 1/45 | 1/3 |
| (2,2) | 25 | 1/45 | 5/9 |

There are2A+1 ordered five-exponent pairs with maximum A and2B+1 ordered seven-exponent pairs with maximum B, so these counts total108. Every incompatible phase intersection contributes zero. The joint(3,2) cap uses the atom bound1/3 in ML3, not an independence assertion. Hence

    Gamma_6125(nu) <= 68/15 + 118/45 = 322/45.

No test phases participate in the selection algorithm. This is one supported law for all complete fine layouts, including inconsistent and nonnested phases.

## 5. Two unbounded-height strips from the same conditional-law argument

The isolation proof works for every H>=2,K>=1 on the literal carrier Z/5^H x Z/7^K, still projecting to25 x7. Assume a missing first-five root, full product-tree blocking at these heights, and a15-point coarse projection. Isolate one coarse cell exactly as in section2, then extend its selected five-tail and seven-tail by arbitrary complete trees of the remaining depths U=H-2,V=K-1. Hence the actual fibre in Z/5^U x Z/7^V meets every product of a complete ternary five-tail tree and a complete five-ary seven-tail tree.

The common-law LP argument of report376, using its product-tree premise, provides one conditional probability K_s on this actual fibre with both sets of prefix caps

    K_s(fixed five-tail prefix of length u)<=3^(-u),
    K_s(fixed seven-tail prefix of length v)<=3^(-v).

Therefore their joint prefix mass is at most3^(-max(u,v)) under that SAME law. It is not bounded here by the product3^(-u-v). The proof also admits a zero-depth coordinate, whose sole prefix has mass1. Mix these15 conditional laws with the uniform coarse marginal.

Put

    R5(U)=sum_(u=1)^U (2u+5)/3^u,
    R7(V)=sum_(v=1)^V (2v+3)/3^v,
    X(U,V)=sum_(u=1)^U sum_(v=1)^V
                         (2u+5)(2v+3)/3^max(u,v).

The same complete LCM expansion yields

    Gamma_(5^H7^K) <= B_HK
       :=68/15 + (4/15)R5(U) + (11/15)R7(V) + X(U,V)/15.  (ML6)

For positive five excess only, the coarse seven weights sum to1+3=4 and both cylinders have coarse mass at most1/15. For positive seven excess only, the coarse five levels contribute1*(1/5)+3*(1/15)+5*(1/15)=11/15. A positive excess in both coordinates lies over one coarse atom, giving the factor1/15 and the joint max-prefix cap above. These estimates include every numerical divisor and all independent phases.

The exact infinite sums are R5(infinity)=4 and R7(infinity)=3. If K<=2, then V<=1 and X(U,1)=5 R5(U); if H<=3, then U<=1 and X(1,V)=7 R7(V). Consequently

    K<=2, arbitrary finite H>=2:
        Gamma <=367/45<9,
    H<=3, arbitrary finite K>=1:
        Gamma <=394/45<9.                                (ML7)

These are uniform bounds for two infinite strips of height pairs. The selected law may depend on the finite source and its heights. They are not assertions of one law on unrelated sources or a projective compatibility of all choices. H=3,K=2 gives R5=7/3,R7=5/3,X=35/3 and recovers322/45; section3 additionally provides the explicit45-point law there.

For comparison, the complete double-height sum is X(infinity,infinity)=123/2 and ML6 gives119/10. To evaluate X, the layer max(u,v)=n has coefficient

    n^2(n+6)(n+4)-(n-1)^2(n+5)(n+3)
       =4n^3+24n^2+22n-15.

Using the geometric moments at1/3 gives123/2. Thus this certificate does not establish the unrestricted two-height target below9. It establishes the strips in ML7 without replacing the actual fine support by free tails.

## 6. A broader good-fibre selector

For arbitrary R, let S_good be the coarse cells whose actual fine fibres have a matching of size at least3. If S_good has three robust coarse roots in the sense of report431, one coarse law mu on S_good simultaneously satisfies

    Gamma_175(mu)<=46/9,
    root<=1/3, child<=1/8, column<=1/3,
    root-column<=1/9, atom<=1/15.                       (ML4)

These extra caps belong to the same laws used in431. Its four generic local cap families are(9,3,3),(8,3,2),(7,2,2),(5,1,1), with local caps row=A/N,column=B/N,atom=1/N. Each gives row<=3/8,column<=1/3,atom<=1/5. The explicit B and A_shared laws and their transposes satisfy these caps; the changed transpose-A law has caps(5/18,1/3,1/6). The remaining explicit laws are uniform instances already covered by these cap bounds. Equal mixing over three distinct roots gives ML4. In particular the child cap is1/8: the original uniform A law has local row mass3/8, so a universal child cap1/9 for this construction would be false.

Choose three matching edges in every mu-positive fine fibre and lift mu uniformly along them. More generally, if these conditional laws have simultaneous new-five, new-seven and joint-atom caps alpha,beta,eta, the same six-group argument gives

    Gamma_6125 <= 46/9 + (91/40)alpha + 5 beta + (7/3)eta.

The coefficient91/40 is7/8+21/15; the beta coefficient is5/3+15/9+25/15=5. With alpha=beta=eta=1/3,

    Gamma_6125 <= 2993/360 < 9.                         (ML5)

The coarse marginal remains the same mu with its46/9 bound. This selector includes nonrectangular and cell-dependent fine supports. A three-matching condition is weaker than requiring a nine-point Cartesian rectangle or seven edges with degree at most3. A tail rectangle blocker has such a matching by section3. Section2 proves this condition in the minimum15-point projection class. For arbitrary larger coarse sources, automatic extraction is false, as the following example shows.

### A product-tree blocker with no good fibre

Define a literal source R in Z/125 x Z/49 by

    (x5,x7)=(r+5a+25u, y+7v),
    r in {1,2,3}, a in {0,1,2}, y in {1,...,6}, v in {0,...,4},
    u in {0,1} if y<=3, and u in {1,2} if y>=4.          (ML8)

It has540 points and54 coarse points. Each of its three coarse roots
is the full three-row by six-column rectangle, hence is robust. Every
fine fibre, however, is exactly a two-row by five-column rectangle.
Its maximum matching has size2, so S_good is empty. R avoids the zero
five-root, the zero seven-root, and every25 class in five-root4.

Nevertheless R meets every full product tree in section1. Fix the
two trees first. In the five-tree successively choose r in {1,2,3},
a in {0,1,2}, and u in {0,1,2}: each selected ternary child set
intersects the respective three-element set. The seven-tree's five
selected roots intersect both {1,2,3} and {4,5,6}. If u=0 choose y
in the first group, if u=2 in the second, and if u=1 in either. At
this y its five selected children meet {0,...,4}, supplying v. This
constructs one point of R in the fixed product. The projections also
meet every standalone ternary tree in either coordinate: the five
projection contains three children at each of its three levels, and
the seven projection has six roots with five children each.

This example has a good common law without any fibrewise three-matching.
Give its540 points equal mass. The exact cylinder maxima are

| Modulus | 1 | 5 | 7 | 25 | 35 | 49 | 125 | 175 | 245 | 875 | 1225 | 6125 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Maximum mass | 1 | 1/3 | 1/6 | 1/9 | 1/18 | 1/30 | 1/18 | 1/54 | 1/90 | 1/108 | 1/270 | 1/540 |

The complete LCM expansion bounds every independently phased layout
by the sum of its ordered-pair cylinder caps. Centering all tests at
(x5,x7)=(26,1), whose literal residue is4901 modulo6125, attains every
listed cap simultaneously. Thus the SAME uniform law has exact values

    Gamma_175=23/6,
    Gamma_6125=265/54<9.                                  (ML9)

ML8 refutes the automatic good-fibre extraction premise, not the
existence of a common law below nine. It also explains why requiring
new-five mass at most1/3 within every fibre is too strong: each fibre
has only two new-five digits, yet ML9 holds. No realization of this
source as an actual odd-cover residual is asserted. A general source
theorem must allow joint mass choices beyond this matching selector.

### Keeping the seven-coordinate inside a coarser fibre

There is a second sufficient condition that does cover ML8. Choose
three distinct first-five roots and three distinct second-five children
at each root. For each of these nine mod25 prefixes s=(r,a), let

    C_s={(u,z) in Z/5 x Z/49:
          (r+5a+25u,z) belongs to R}.

Assume every C_s meets every product of a three-element subset of
Z/5 and a complete five-ary depth2 tree in Z/49. The common-prefix-law
argument of report376 then gives, on each actual C_s, ONE conditional
probability with new-five cap1/3, seven-root cap1/3, and seven-leaf
cap1/9. Joint caps are the minimum of the applicable marginal caps;
no independence is asserted. Choose these nine laws before any layout,
and mix them with equal weights. The resulting law on R has caps

| Modulus | 1 | 5 | 25 | 125 | 7 | 35 | 175 | 875 | 49 | 245 | 1225 | 6125 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Mass cap | 1 | 1/3 | 1/9 | 1/27 | 1/3 | 1/9 | 1/27 | 1/27 | 1/9 | 1/27 | 1/81 | 1/81 |

For example, a mod875 cylinder fixes one of the nine prefixes and
both a new-five digit and a seven root, so its mass is at most
(1/9)min(1/3,1/3)=1/27. A mod6125 cylinder has mass at most
(1/9)min(1/3,1/9)=1/81. Summing the complete LCM expansion gives

    Gamma_6125 <= sum_(A=0)^3 sum_(B=0)^2
                   (2A+1)(2B+1) cap(5^A7^B) = 8.        (ML10)

This premise follows automatically from full product-tree blocking
when R has exactly three occupied first-five roots and exactly three
occupied second-five children at each root. To isolate one mod25
prefix, select its first-five root and the two empty roots, then its
second-five child and the two empty children at that root. Extend the
last five-digit choice arbitrarily and pair with any full seven-tree.
Every source witness must lie in the selected C_s, proving the local
product-tree condition. Extra restrictions on R, including original
excluded classes, are preserved because each law stays on actual points.

ML8 has exactly this three-by-three five-prefix structure. ML10
therefore supplies a general source class beyond the good-fibre
matching selector; it does not require any mod175 fibre to support
three matching edges. The minimum15-point coarse sources instead
have five second-five children per occupied root and are handled by
ML1. The two sufficient conditions leave other source shapes unresolved.

[The joint tree-cap coupling theorem](443-one-supported-law-couples-rows-and-tree-prefixes.md) strengthens the ML10 construction to3044/405 at height(3,2). For exactly the same three-by-three five-prefix class it also gives1196/135<9 at every finite seven-height. It supplies joint prefix caps under one law; the older marginal-only bound8 above remains valid.

The local law also has an integral construction. Scale its mass by9
and use a network with capacities3 from the source to each new-five
digit,9 along each actual pair (u,z),1 from each seven-leaf z to its
seven root, and3 from each seven root to the sink. The common-prefix
law supplies a fractional flow of value9. Integral max-flow therefore
selects nine actual pairs, with no repeated seven leaf and at most
three pairs per new-five digit or seven root. Mixing the nine prefix
laws selects81 actual points of mass1/81 and proves the same caps.

For ML8, an explicit alternative gives every u=0 or u=2 point mass
1/405 and every u=1 point mass1/810. Its mod175 marginal is still
uniform on54 cells; within each mod25 prefix, its three new-five
conditional masses are all1/3.
Direct cylinder counts give Gamma_6125=394/81, attained by centering
all tests at the literal residue1. This is another fixed law on the
same source; ML9 remains the exact value for its original uniform law.

## 7. Exact controls and remaining scope

[The standalone standard-library companion](../../frontier/cover-geometry/minimum_source_fibre_lift.py) accepts arbitrary literal fine residues, checks the minimum coarse matching classification, checks the local rectangle conditions equivalent here to full-depth product blocking, selects actual three-edge matchings, and computes the exact uniform coarse law and fine LCM upper bound. Its consumers use different rootwise coarse matchings, nonstandard child and tail digits, and nonrectangular fine graphs. They verify the construction on actual finite inputs, not by enumeration of every possible source. A control replacing one fibre by a single edge preserves the coarse projection but fails the fine condition; its empty rectangle gives the precise obstruction. The540-point control separately checks the local witnesses used in ML8's quantified tree proof, all54 fibre matching ranks, and the exact common-law values in ML9.

The ordinary isolation and matching proofs establish the quantified source theorem. The program checks the literal CRT labels and rational calculations, including the finite double sums and the exact infinite-strip constants. Its joint-prefix constructor detects empty local product trees, selects integral local flows, and checks all twelve caps and144 ordered LCM terms on one81-point law; the explicit540-point reweighting reuses the same source. ML1 resolves the minimum coarse-source class of the proposed175-to6125 lifting problem, and ML7 extends that class along two unbounded-height strips. ML10 also resolves the separate three-by-three five-prefix class using coarser joint fibres. The arbitrary larger coarse-source case, including interactions that prevent either isolation, remains unproved.

Run the exact controls from the repository root:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/minimum_source_fibre_lift.py

Use `--input <json>` for a supplied minimum-coarse source, or add
`--joint-prefix` for the ML10 constructor. Inputs are lists of literal
residues modulo6125. A failed source premise is rejected.

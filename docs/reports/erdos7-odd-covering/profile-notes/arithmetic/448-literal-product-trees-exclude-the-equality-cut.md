[Index](../../marked_head_profile.md) · [Generic strict cut](447-strict-child-cut-surplus-and-arithmetic-boundaries.md)

# Literal product blocking removes the 65/63 equality cut

This is an ordinary finite-network argument extending [447](447-strict-child-cut-surplus-and-arithmetic-boundaries.md). It is not a Lean-certified declaration, a claim about every old-cap-feasible probability, or a realization by an actual covering system.

Let F be an actual source in Z/25 x Z/49 with four occupied first-five roots and occupied second-five child counts(4,5,5,5), after permuting the roots. Assume that F blocks every product of a complete ternary five-tree and complete five-ary seven-tree, both of height two, and that its standalone seven projection contains a complete five-ary tree. For a first-five root r and first-seven digit g, let M(r,g) be the number of literal children at r having an actual point over g.

Use report447's actual-child network: top capacities1/3 and1/9, private seven-prefix capacities(2/7)3^(-B), actual bridges of capacity2, and common seven-prefix capacities3^(-B), B=1,2. Every edge capacity is an integer multiple of1/63.

If at least one of the three five-child roots satisfies M(r,g)<5 for every g, then every cut has capacity at least66/63. Thus requiring incidence at most two at every root is stronger than needed for this cut improvement. The latter hypothesis will still be used for the moment consequence below.

## Reduction to fully active equality

Put q_r=n_r-2, so q=(2,3,3,3). Literal product blocking implies the projected-law premise of447: for any pair of roots and any q_r actual children at one root and q_s at the other, append the empty children and the empty first-five root to obtain a legal ternary five-tree. Its seven projection blocks every five-ary tree, hence contains a literal ternary tree and supports the uniform ternary-prefix law.

Report447 therefore gives the generic lower bound65/63. To improve it on the1/63 lattice it suffices to exclude a cut of cost exactly65/63. A crossing actual bridge costs2 and cannot occur.

Let a_r count source-side actual child nodes, I={r:a_r>=q_r}, and

    T=sum_r min(1/3,(n_r-a_r)/9).

The actual top cost is at least T. Let R be the common-tree cut cost, and L_rc each private child-tree cut cost before multiplication by2/7. All R and L_rc are nonnegative multiples of1/9.

The non-full-activity cases are already separated from65/63, as follows.

* For |I|=0, T=84/63.
* For |I|=1, T>=1. If the actual top cost is greater than1, its1/9 lattice makes it at least70/63. If the top cost equals1 and R>0, the common cut adds at least1/9. If the top cost equals1 and R=0, the eligible root has all n_r of its children active: any deficit would add a positive contribution to T beyond the three ineligible contributions1/3. Each of its four or five nonempty actual child fibres needs a crossing private edge, since no actual bridge or common edge crosses. The private trees are distinct and their least positive edge capacity is2/63. The total is therefore at least71/63.
* For |I|=2,3 and R<1, the endpoint bounds in447 are72/63 and66/63. If R>=1, the ineligible-root contribution makes the bound at least1+(4-|I|)/3.
* For |I|=4 but a!=n, the half-sum branch of447 is at least1+5/126 and rounds up on the cut lattice to66/63. Its exclusion branches are at least90/63, and the top-plus-one branch is at least70/63. If R>=1, T>=1/9 gives70/63 directly.

Only a=n remains. In particular every actual child node is source-side.

## Classifying fully active equality, including R=1

If R>1, its1/9 lattice gives at least70/63. Suppose R=1 and the total cost is65/63. Any positive top edge would add at least7/63, so the top cost is zero. The private cost must be exactly2/63, hence consists of exactly one depth-two leaf edge. Let its seven residue be y, whether or not that private leaf is an actual source point. Let P be the union of the common cut-prefix cylinders.

Every actual point has a path from its source-side child to the sink. No actual bridge crosses. Outside the single private cut leaf this path must cross a common cut edge, so the full seven projection of F is contained in P union{y}. Put the uniform probability mu on the assumed standalone five-ary tree. A depth-B prefix has mu-mass at most5^(-B), so

    mu(P)<=sum_(common cut prefixes v) mu(v)
         <=(3/5)sum_v kappa(v)=(3/5)R=3/5,
    mu({y})<=1/25.

This cannot cover a set of mu-mass1, since3/5+1/25=16/25<1. Thus R=1 cannot give equality either. The reasoning does not assume that y is actual.

For R<1 write R=k/9, u=9-k and z_rc=9L_rc. Report447 bounds the cut by the integer table

    k:                   0, 1, 2, 3, 4, 5, 6, 7, 8,
    numerator over63:   70,71,72,65,66,67,72,73,74.

Equality65/63 therefore requires k=3, u=6, no positive top cost, and sum_rc z_rc=22. Let p_r be the least sum of q_r child costs at root r. The pair-of-subsets inequalities give p_r+p_s>=6. Sorting the child costs gives

    sum_rc z_rc >= f2(p_0)+f3(p_1)+f3(p_2)+f3(p_3),
    f2(p)=p+2ceil(p/2),  f3(p)=p+2ceil(p/3).

The only tuple attaining22 under these pair inequalities is p=(3,3,3,3). Here is a direct uniqueness check. If the minimum p is at least3, every coordinate is at least3; the value at(3,3,3,3) is7+5+5+5=22, and either function strictly increases when its argument increases. If the minimum is t=0,1,2, all other coordinates are at least6-t. According as the minimum occurs at the four-child root or a five-child root, the lower bounds are respectively

    t=0: 30 or32;
    t=1: 30 or32;
    t=2: 28 or28.

All exceed22.

Consequently the four-child root has total integer private cost7 and least two-child sum3, while each five-child root has total5 and least three-child sum3. These force the sorted shapes

    four-child root: (1,2,2,2),
    each five-child root: (1,1,1,1,1).

For the first shape, if its least entry were0 the other three would each be at least3, contradicting total7; hence the least is1, the second is2 and all remaining entries are2. For a five-child root, a third-smallest entry at least2 would force total at least3+2+2=7; thus its first three entries and then all five entries equal1.

Since a private first-prefix edge has unweighted integer cost3, none occurs in these shapes. Each child of a five-child root has exactly one private depth-two cut leaf. Denote its seven residue by y_c. The four-child root has leaf counts(1,2,2,2), but no further use of its leaves is needed.

## Literal trees force the private leaves to be actual

Now R=1/3. Because common edge capacities are1/3 at depth one and1/9 at depth two, the common cut P has exactly one of two forms: one entire first-seven column, or three depth-two leaves.

At any child c of a five-child root, every actual leaf belongs to P union{y_c}: otherwise its path would cross neither a private edge nor a common edge, while its bridge cannot cross. This containment holds even before knowing whether the cut leaf y_c is actual.

Fix two of the five-child roots and select any three children in each. Literal product blocking says their combined actual seven projection contains a complete ternary depth-two tree.

If P is one entire column, at least two further columns with three leaves each are needed. The six selected private cut leaves are the only possible points outside P. Thus all six must be distinct, outside P and present in the actual selected projection; they form exactly two columns with three leaves each.

If P consists of three leaves, the selected projection is contained in a set of at most nine leaves. A complete ternary depth-two tree has nine distinct leaves. Hence all three public leaves and all six private cut leaves occur, without repetitions; their union is exactly three columns with three leaves each.

In both cases each selected private cut leaf y_c is an actual point of its OWN child c. Indeed it lies outside P and is distinct from every other selected private cut leaf. Every other selected child's fibre is contained in P union its own cut leaf, so no other child can supply y_c. Since the leaf nevertheless occurs in the actual selected projection, it must come from c. This is the step that turns a private cut edge into an actual-incidence witness; private leaf edges by themselves would not suffice.

## Exchanges force five children into one column

Keep the triple at the other full root fixed. In the first root compare triples{c,e,f} and{d,e,f}, where c,d,e,f are distinct. The preceding counting applies to both selections.

In the one-column public case, the two private six-leaf sets share five leaves. Before the exchange there are two columns with three private leaves each. Removing y_c leaves column counts2 and3; adding y_d can restore the required counts only if y_d has the same first-seven digit as y_c.

In the three-public-leaf case, the two nine-leaf sets share eight leaves. Removing y_c leaves column counts2,3,3, and again y_d must fill the same deficient column.

Distinctness used here follows from the preceding counting applied to a triple containing any chosen pair of children; thus the exchange does not silently identify leaves from different children. For any c,d among the five children there are two other children e,f available. It follows that all five y_c have the same first-seven digit. All five are actual in their respective children, so this root has M(r,g)=5 at that digit.

Each five-child root can be paired with another five-child root, so this conclusion holds at all three full roots. It contradicts the assumed existence of even one full root whose incidence maximum is less than5. Thus no cut can have cost65/63. Together with the generic lower bound and the1/63 lattice, every cut is at least66/63.

## Consequence for one common probability and all original labels

A flow of value66/63 can therefore be normalized to ONE supported law. Its root, child, pure-seven and child/seven caps are all the old caps multiplied by

    alpha=63/66=21/22.

If every root/first-seven cylinder meets at most two children, the same law also has root/seven cap alpha*(4/7)3^(-B). Under this stronger incidence assumption the full nine-label LCM sum before scaling is9, as in447. All phases remain independently chosen after the law is fixed. Only the ordered pair(1,1) retains its unscaled contribution1; all80 other terms scale. Hence

    Gamma_1225(nu)<=1+(21/22)(9-1)=95/11<9.

The cut improvement uses literal product blocking and the weak full-root incidence exclusion. The displayed moment bound additionally uses incidence at most two at every root. Neither conclusion follows from the former fractional-projection-only premises without these extra source conditions.

## A sharp generic network still admits a good original-label law

The extra incidence condition cannot be omitted from the cut improvement. There is a117-point literal product blocker with occupancy4555 and standalone five-ary projection whose old network minimum cut is exactly65/63. The [explicit source, cut and matching flow](../../frontier/cover-geometry/literal_child_cut_boundary.py) retain all actual child identities.

Use roots r=1,2,3,4, with four children at root1 and five at every other root. Every child contains the five common seven leaves1+7h, h=0,...,4. Give root r its own private seven column g=r+1. The private second-digit sets at the four-child root are

    {0}, {1,2}, {2,3}, {3,4},

and at any full root the private set of child c is{c}. There are95 common incidences and22 private incidences. Every pair of actual children at root1 has at least three private leaves; every triple at a full root has three private leaves. Any two roots therefore give a ternary seven-tree from their private columns and the common column. The full projection has five columns with five leaves each, so it also has a five-ary tree. The first-five and first-seven zero digits and the mod25 class21 are absent.

Cut the public edge at column1 and every listed private leaf edge, leaving all top edges uncut. No actual bridge crosses, and the cost is1/3+22(2/63)=65/63. A matching flow is explicit. In units1/63, put mass2 on every private incidence; put mass1 on the three common points(1,0,1+7h), h=0,1,2; and put mass2 on(r,c,1+7c) for r=2,3,4 and c=0,1,2. Its total is65 and its root totals are17,16,16,16. Every child mass is at most7, every private first-prefix mass at most6, every private leaf mass at most2, every public first-prefix mass at most21 and every public leaf mass at most7. Following the actual paths gives a feasible flow of value65/63, proving equality with the displayed cut.

This source has incidence maxima(4,5,5,5). Moreover, no subsource with incidence at most two at every root can retain product blocking. To see this without enumerating all subsources, take any two full roots. Incidence at most two in the common column leaves at least three literal children at each root with no common-column point. Choose those triples. All their remaining points lie in the two respective private columns, so their combined projection has at most two first-seven branches and cannot contain a ternary tree. Empty children cause no exception: tests may select them too. Selecting fewer first-five roots cannot repair this failed original product test.

Nevertheless the normalized matching flow is a GOOD law for the original-label moment. Its maximum cylinder masses are

| Original modulus | 1 | 5 | 7 | 25 | 35 | 49 | 175 | 245 | 1225 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Mass, in units1/65 | 65 | 17 | 21 | 5 | 14 | 7 | 4 | 4 | 2 |

Summing these actual-law maxima at the literal LCM of every ordered divisor pair gives107/13<9. The same law is used for all81 terms. These are maximum-cylinder upper bounds, not an optimization of the layout game. Thus the example simultaneously refutes an incidence-free66/63 network claim and an automatic low-incidence-blocker selection claim, while supplying an explicit good law outside that selection class. It does not refute the existence of a good law on every arithmetic residual or assert an actual odd-cover realization. The [retained exact certificate](../../frontier/cover-geometry/literal_child_cut_boundary.controls.json) includes all1260 edge-capacity checks,1143 internal conservation checks and1767 original numerical cylinders.

## Fractional projection feasibility is still a separate premise

Starting from447's121-point saturation source, remove precisely the three actual points

    (r,c,y)=(4,4,5), (4,4,19), (4,4,26).

The remaining118-point source still has occupancy4555, incidence at most two, a standalone five-ary projection and every one of the480 required fractional actual-subset projection laws. The generic65/63 constructor therefore remains applicable. But root2's children{0,1,2} together with root4's children{1,2,4} have seven-column leaf counts

    (0,2,5,5,0,2,0).

Their fractional ternary-prefix capacity is1, since sum_g min(3,count_g)=10>=9; only two columns have three leaves, so they contain no complete ternary depth-two tree. The new literal constructor rejects this missing premise explicitly. This finite countercontrol prevents treating a feasible projected probability as a literal product-blocking certificate.

## Exact constructions and scope

The direct constructor now has an explicit `literal_one_gap=True` mode, separate from `strict_one_gap=True`. It checks actual occupancy4555, height two, the exact prefix capacities and coefficient2/7, a standalone five-ary tree, at least one full root of incidence below five, and every actual pair/subset literal ternary-tree predicate. The numerical consumer additionally requires incidence at most two everywhere. It scales the network by21/22, retains bridge capacity2 before scaling, and constructs a unit law on the actual support. Every marginal, joint cap and original numerical cylinder is checked on that same law. The divisor1 cap remains1. The generic65/63 mode keeps its weaker fractional-premise contract.

The [construction controls](../../frontier/cover-geometry/literal_child_cut_surplus.py) and [exact laws](../../frontier/cover-geometry/literal_child_cut_surplus.controls.json) give:

| Actual source | Points | Positive law atoms | Denominator | Theorem upper | Law's LCM upper |
| --- | ---: | ---: | ---: | ---: | ---: |
| One-gap control from446 | 116 | 37 | 66 | 95/11 | 181/22 |
| Old-cap saturation source | 121 | 38 | 66 | 95/11 | 95/11 |
| Common CRT translation of that source | 121 | 36 | 66 | 95/11 | 278/33 |

The translation is the same common+253 modulo1225 used in447. Each source passes480 fractional and480 literal actual-subset premises; these imply the original pair/triple conditions by adding empty children or taking subsets. The equality controls check all2401 possible clipped root-subset tuples for u=6 and the unique sorted child-cost shapes. Adding the point(2,2,2) to the116-point source gives incidence(2,3,2,2): the weaker core still constructs its scaled law, while the moment consumer rejects the missing incidence-at-most-two premise. Five rejection controls distinguish that stronger consumer premise, the118-point fractional-only source, the117-point sharp high-incidence source and invalid mode combinations. The ordinary proof supplies the unbounded quantification over all sources satisfying the premises; these experiments verify the displayed constructions and boundaries.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/literal_child_cut_surplus.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/literal_child_cut_boundary.py
```

The unified bound across all missing-child occupancy patterns remains79/9, because447's at-least-two-missing-child branch is now the larger bound. The new95/11 applies to the single-missing-child branch. Neither argument proves a general low-incidence theorem or transports the same law through all original outside-cofactor tests. The117-point example specifically shows why selecting a low-incidence subsource cannot be a universal repair even within these literal tree premises. The remaining unrestricted problem requires further actual arithmetic constraints or laws that handle high-incidence fibres directly. No unrestricted Erdős #7 conclusion or new Lean certification is claimed.

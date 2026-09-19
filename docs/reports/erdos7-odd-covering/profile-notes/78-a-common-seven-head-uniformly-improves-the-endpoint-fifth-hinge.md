[Index](../marked_head_profile.md) · [Endpoint source](59-endpoint-linear-source-deletion-bound.md) · [Six-label head](63-six-original-labels-strengthen-the-endpoint-square.md) · [Descendant-five geometry](69-complete-positive-five-tails-in-one-square-layout.md) · [Scalar obstruction](67-exact-endpoint-survival-and-its-scalar-boundary.md)

# A common seven head uniformly improves the endpoint fifth hinge

For actual original-label families approaching source404, surviving
mass S=D=3/20 and carrier(root0,cell1), every independently labelled
complete original357 test A satisfies

    limsup integral_survivor (A-5)_+
        <=30941653/194481000=0.15909859060782286... .       (H1)

This improves the previous uniform upper bound

    U5=2028798479/12155062500=0.1669097529527306...

by189890333/24310125000. In particular it excludes the abstract
load law V of profile67, whose fifth hinge equals U5. The two
additional original test labels retained in the estimate are21
and35. Their old-coordinate projections share one layout with the
six-label zero-seven head, while their seven residues remain arbitrary.

The result does not assume saturation of any test-unit tail or
equality in a test first-moment bound. Its hypotheses concern the
actual forbidden source endpoint. It is compatible with stronger
uniform moment estimates. This is an ordinary endpoint theorem with
exact rational verification, not a neighborhood theorem, a new
global K bound, an unrestricted solution of Erdos #7 or Lean verification.

## 1. An ordered-indicator bridge keeps the seven residues independent

Use the raw35 source measure Lambda of mass1/4 and the actual
surviving old marginal mu of mass3/20. In the source before mixed
seven deletion, the seven coordinate has normalized cylinder caps

    u_e=6/(5*7^e), e>=1,  sum_e u_e=1/5.                 (H2)

Write A0 for all zero-seven original test labels, including the
unit. Keep every positive-seven unit label7^e, and in addition
keep the two original labels21 and35. Let T be the ternary root
chosen by test21, F the first-five slot chosen by test35, and set

    m(x)=1_T(x)+1_F(x),  m(x) in{0,1,2}.

For fixed old coordinates x, their combined positive-seven load R
is a sum of m(x)+1 indicators at depth1, followed by one unit
indicator at every depth e>=2. They need not be nested, aligned,
or disjoint. Let Z contain all remaining positive-seven labels.

For any ordered indicator list J_i and integer k>=0, pointwise

    (sum_i J_i-k)_+<=sum_(i>k)J_i.                      (H3)

Indeed, the first k indicators contribute at most k. List the
m+1 depth1 indicators first and then the higher unit depths.
Integrating the right side of(H3) over the raw seven coordinate
and summing the complete geometric remainder gives

    G_m(k)=7^(-max(k-m,0))/5+(6/35)*max(m-k,0).
    g_m(v)=G_m((5-v)_+).                               (H4)

For example, when k<=m the remainder has m+1-k depth1 caps and
all depths>=2. When k>=m+1 it has precisely the unit depths
e>=k-m+1. These give the two branches of(H4).

For nonnegative loads, with k=(5-A0)_+,

    (A0+R+Z-5)_+<=(A0-5)_++(R-k)_++Z.

Both increments are nonnegative, so mixed-seven deletion may be
dropped for them. The old-coordinate marginal of the retained
first term remains the actual mu. The complete nonunit raw35 cap
sum is1/2 by profile59. Removing exactly the assigned caps of
labels21 and35 from its positive-seven linear budget leaves

    (1/2)*(1/5)-(6/35)*(1/8+1/10)=43/700.

Thus, without replacing the surviving hinge by a raw hinge,

    integral_survivor (A-5)_+
      <=43/700+integral_mu (A0-5)_+
                    +integral_Lambda g_m(A0).          (H5)

The left side uses the full surviving measure; the zero-seven
term on the right uses its old-coordinate marginal mu.
The selected old-coordinate cap for test21 is1/8 and that for
test35 is1/10. Their actual old residues may be different from
those of tests3 and5 in A0.

## 2. One common old head controls both terms in the bridge

Use profile63's head B of the six moduli{1,3,9,5,15,45}.
The five ternary cells and first-five slots are indexed by

    cells=([0]9,[3]9,[1]9,[4]9,[7]9),
    ROOT=(0,0,1,1,1),  slots=(P,A,Beta,Q,H).

Its load is

    B(c,s)=1+1_(ROOT(c)=r3)+1_(c=c9)+1_(s=s5)
             +1_(ROOT(c)=r15,s=s15)+1_(c=c45,s=s45).    (H6)

There are12500 layouts in the field order
(r3,c9,s5,r15,s15,c45,s45). Each of the two additional projections
has2 or5 choices, giving125000 common layouts(B,T,F). Missing
labels can be added. A root or cell outside the surviving source
can be replaced by a surviving one: its previous contribution
was zero there, and the load increases. This justifies the stated
finite layout space for arbitrary original tests.

The selected complete forbidden-cofactor families3,9,5,15 give
the measure domination from profile59

    mu<=w*Lambda,
    w(c,s)=1-[1_(c<2)+1_(c=1)+1_(s=H)
                                      +1_(c>=2,s=H)]/5. (H7)

In particular every w>=2/5>6/35. On each fixed rectangle define

    f_(w,m)(v)=w*(v-5)_++g_m(v), v>=1 integer.

This function is increasing and integer-convex. Below5 the forward
increments of g_m increase geometrically and then equal6/35;
from v=5 onwards g_m is constant and the forward increment of f
is exactly w. Hence the transition to the affine tail preserves
convexity. This statement concerns f, not g_m alone.

Write A0=B+sum_i I_i, ordering the first four old-tail labels as

    (25,27,75,81), exponent pairs((0,2),(3,0),(1,2),(4,0)).

For arbitrary independently chosen tail cylinders, telescoping
with the increasing forward increments gives

    f(B+sum_i I_i)-f(B)
       <=sum_(i=1)^4 I_i*[f(B+i)-f(B+i-1)]
                              +w*sum_(i>4)I_i.        (H8)

Before the i-th indicator, at most i-1 earlier indicators are
active. For i>=5 the comparison argument B+i-1 is at least5,
so its increment is w. This proves(H8) for finite tails; complete
first-moment domination passes it to the increasing limit.

To apply it to(H5), first use(H7) only on the nonnegative difference
(A0-5)_+-(B-5)_+. Add the raw difference g_m(A0)-g_m(B).
Their sum is exactly the left side of(H8) integrated over Lambda.
Consequently the same B and m are retained in the surviving head,
raw head and four selected-tail increments. No independently
maximized zero-seven head is inserted into a different raw head.

## 3. Uniform cylinder coefficients and complete remaining tails

For a nonnegative rectangle function t(c,s), let P_(a,b)(t) bound
the raw integral of t over any old test cylinder3^a*5^b.
For a>=3,b=0, use the pre-late source slot proportions from59:

| Cell | P | A | Beta | Q | H |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0,1 | 0 | 1/5 | 1/5 | 3/20 | 1/5 |
| 2 | 0 | 0 | 0 | 1/20 | 1/5 |
| 3,4 | 0 | 0 | 1/5 | 1/10 | 1/5 |

Call this matrix p. Retaining the shallow full-slot exclusions
and discarding later source deletions gives

    P_(a,0)(t)=3^-a*max_c sum_s p(c,s)*t(c,s).          (H9)

There is no eta factor in p:3^-a already bounds the ternary
mass of this deep cylinder. Dropping pure3 source loss is also
valid because t is nonnegative.

For b>=2, let D be the raw descendant-five coefficient matrix.
Start with eta=(1/18,1/9,1/9,1/9,1/9), repeated across slots;
set to zero all P entries, root1 A entries, and cell2 Beta;
replace the cell3 Beta entry by eta3-1/18=1/18. Then

    Lambda(cell_c times J_b)<=D(c,s)*5^-b

for a depth-b five cylinder J_b in first slot s. The cell3 Beta
subtraction uses the entire b=1 late source family: its disjoint
ternary union has mass sum_(a>=3)3^-a=1/18, and every such label
removes the full Beta slot on its ternary cylinder. It does not
assume that the total late deletion is uniform inside Beta.
Multiplying D entrywise by w recovers exactly profile69's
descendant-five table.

Therefore, for b>=2,

    P_(0,b)(t)=5^-b*max_s sum_c D(c,s)*t(c,s),
    P_(1,b)(t)=5^-b*max_(r,s) sum_(ROOT(c)=r)D(c,s)*t(c,s),
    P_(2,b)(t)=5^-b*max_(c,s)D(c,s)*t(c,s).            (H10)

For the remaining deep mixed labels a>=3,b>=1 the raw Haar cap
3^-a*5^-b applies. Since w<=1, summing the complete old-tail
linear budgets gives

| Tail category | Complete w-weighted upper bound |
| --- | ---: |
| Pure3, a>=3 | 7/225 |
| Pure5, b>=2 | 1/45 |
| 3 times5^b, b>=2 | 1/60 |
| 9 times5^b, b>=2 | 1/180 |
| 3^a times5^b, a>=3,b>=1 | 1/72 |

The total is161/1800. Remove the assigned bounds P_(a,b)(w)
of the four ordered labels in(H8), each once. The complete
remaining old-tail budget is

    161/1800-sum_((a,b) in ORDER)P_(a,b)(w)=497/16200. (H11)

The first four labels are then charged only their smaller
layout-dependent increments from(H8). All other labels remain
in(H11); no finite exponent cutoff has been used.

## 4. An exact common-layout bound excludes the scalar law V

For each head B, use the entry, row and total surviving capacities
of profile63 to maximize integral_mu(B-5)_+. Denote the resulting
LP upper bound by L(B). The checker supplies a feasible dual and
a feasible primal attaining it for every one of the12500 heads.
The raw head uses the exact matrix M(x) of profile59, affine in
the late Beta deletion x in[1/90,1/72]. Thus its maximum is at
one of these two endpoints, for this same fixed(B,m).

With t_i(c,s)=f_(w(c,s),m(c,s))(B(c,s)+i)
                       -f_(w(c,s),m(c,s))(B(c,s)+i-1),
the verified bound for every common layout is

    43/700+L(B)
       +max_(x in{1/90,1/72})sum_(c,s)M(c,s;x)*g_m(B)
       +497/16200+sum_(i=1)^4P_(ORDER_i)(t_i)
       <=30941653/194481000.                           (H12)

All quantities are rational. The unique maximizing layout of
this bound is

    (r3,c9,s5,r15,s15,c45,s45)=(1,4,H,1,H,4,H),
    old root of21=1, old first slot of35=H.

Its five contributions, in the order of(H12), are

    43/700, 1/75, 21443/720300, 497/16200, 7901/330750.

They sum to(H1). This identifies the maximum of the stated bound,
not an actual original family attaining it. Profile67's V has
fifth hinge U5, so it violates(H1) by189890333/24310125000.
In the complete AP11 denominator of profile67, whose coefficient
of U5 is-4/33, this produces the independent guaranteed gain

    (4/33)*(U5-30941653/194481000)
       =189890333/200558531250
       =0.0009468075569585125... .                     (H13)

The other terms of that denominator may use any separately valid
uniform moment and fourth-hinge estimates; this gain requires
no relation between their original test residues.

## 5. Endpoint passage and reproduction

The [checker](../frontier/endpoint_h5_common_seven_head.py) rebuilds
the12500 old-head LP primal/dual equalities and all125000 common
layouts. It verifies the integer-convex increments, complete
ordered-seven tails, descendant-five table and all remaining
linear-tail budgets. The [certificate](../certificates/source_norms/endpoint_h5_common_seven_head.json)
stores the exact maximum, the maximizing layout, aggregate hashes
of the checked tables and the scalar V violation.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_h5_common_seven_head.py --check
```

For arbitrary approaching finite families, pass to subsequences
where each fixed source/test cylinder stabilizes and the finite
head slots are consistently relabelled. The source-saturation
and deletion conclusions of59 apply to every limiting source.
Every original test-tail contribution used here has at most
linear growth and is bounded by complete geometric cylinder-cap
sums, uniformly in its residues. Removing sufficiently deep labels
therefore changes the hinge bound by a quantity tending to zero
uniformly. Apply(H12) to the limiting heads, then pass back to
limsup; no stabilization of an entire infinite family is needed.

## 6. Why retaining the two extra labels matters

There is a quantitative obstruction to using only the unit-seven
tail while charging every positive-seven nonunit linearly. That
sufficient bound would be

    integral_mu(A0-5)_++1/10
                  +integral_Lambda 7^(-(5-A0)_+)/5.    (H14)

In the off-diagonal source constructor of profile50, the region
E=[7]9 times[3]5 is untouched by all source and mixed forbidden
labels, so mu and Lambda both equal Haar measure there. Use

    A0=(1+sum_(a>=1)1_([7]_(3^a)))
                         *(1+sum_(b>=1)1_([3]_(5^b))).

On E, A0>=6, the two integrated factors are7/18 and9/20,
and Haar(E)=1/45. Hence

    integral_E A0=7/40,
    integral_E(A0-5)_+=23/360,
    integral_E 7^(-(5-A0)_+)/5=1/225.

The right side of(H14) is therefore at least

    1/10+23/360+1/225=101/600>U5.

This is a lower bound on that sufficient expression, not on the
actual fifth hinge. It explains the mathematical role of21 and35:
their contributions cannot all be discarded into an independent
linear budget if this particular bridge is to improve U5.

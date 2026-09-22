[Index](../../marked_head_profile.md) · [Shared-column source laws](432-four-root-source-selections-and-the-shared-column-boundary.md) · [Height lifting](../../problem-details/09-quantitative-extension-of-the-old-prime-powers.md)

# A common law for every four-root three-child pair source

Let S be an actual height-(2,1) source in the five-by-seven prefix product. There are four distinct first-five roots. Each root has exactly three active five-child digits, and each child has exactly two distinct seven-column neighbors. For a root r let B_r be the set of its distinct unordered neighbor pairs; a pair repeated within one root is retained with its child multiplicity. Assume that the four B_r are pairwise disjoint.

There is an explicit probability law nu supported on S such that, for every independent choice of the six original phases,

    Gamma(nu) = max_(a_m) E_nu[(sum_{m in {1,5,25,7,35,175}}
                                      1_(z=a_m mod m))^2]
              <= 149/30 < 5 < 46/9.                         (PS1)

One law is chosen before any test phase. The source is fixed input; when it comes from an actual covering-family residual, that family's already fixed phases determine the source, while the test phases in Gamma remain independently quantified. The proof retains a single global phase for label 7 and the original independent phases for labels 5,25,35,175. The standalone assumption of at least five projected columns is not needed for this subclass theorem. Extra source points can receive mass zero if the source contains a configuration satisfying these assumptions.

This is an ordinary mathematical result with an explicit finite constructor. It does not assert that every admissible height-(2,1) source contains such a pair configuration, that all possible source heights have been treated, or that the source is the residual of a distinct-modulus covering family. No new Lean statement or unrestricted Erdős #7 conclusion is claimed.

## 1. The repeated-pair structure bounds column concentration

There are twelve child pairs, counted with multiplicity. For a seven column y let d_y be the number of pairs containing y, and put Delta=max_y d_y. For two different columns u,v,

    d_u+d_v = #{pairs meeting {u,v}} + #{pairs equal to {u,v}}
            <= 12+3 = 15.                                 (PS2)

The last term is at most three: cross-root disjointness allows {u,v} in only one root, which has three children. Consequently a column of degree at least nine is unique.

If c is such a column, call a child an exception when its pair does not contain c. There are 12-d_c exceptions. For every y different from c, all occurrences of the spoke pair {c,y} belong to a single root. That root has only three children. Thus at most three spoke points can carry any particular noncenter column, regardless of their child multiplicities.

## 2. The three explicit weighting rules

Use the following integer masses on actual source points, then divide by the indicated total. Child and root digits retain their actual values.

| Degree regime | Mass at c on a spoke child | Mass at its other endpoint | Mass at each exception endpoint | Mass per child | Total mass |
|---|---:|---:|---:|---:|---:|
| Delta<=8 | 1 | 1 | 1 | 2 | 24 |
| Delta=9 | 9 | 11 | 10 | 20 | 240 |
| Delta>=10 | 4 | 6 | 5 | 10 | 120 |

In the first row there is no distinguished column: every source point simply has mass one. In the other rows the unique maximum-degree column is c. Every point receives positive mass, every child has the same mass q, every root has mass 3q, and the total is 12q. These choices use only the actual source, never the later test phases.

For Delta<=8, the common uniform law has simultaneous maximum masses 24,6,2,8,3,1 in the six original cell families. Every ordered pair of original label indicators is empty or contained in a cell at the least common multiple of its moduli. The 36 ordered pairs have lcm multiplicities 1,3,5,3,9,15, respectively. Hence

    Gamma(nu) <= (24+3*6+5*2+3*8+9*3+15)/24
              = 59/12 < 149/30.                            (PS3)

This is the existing same-law cell-cap argument of report 432 with the degree cap reduced from nine to eight.

## 3. A five-case inequality keeping the shared column phase

For the other regimes write k for the center mass on a spoke, h for its noncenter mass, and q=k+h; each exception endpoint has mass q/2. In both rules, k<=h and q/2<=h. Define the unnormalized cell caps

    C_y = mass of the entire column y,
    D_y = maximum mass of a root-column cell at y,
    M_y = maximum mass of a single source point at y.

Let b be the independent phase of the original label 7. Let d be the seven-coordinate of the independent original label 35. They are the same b and d throughout the source. Write B for the load from the five labels 1,5,25,7,35, before adding label 175. Expanding B^2 and bounding each intersection on this one probability space gives

    sum_(x in S) w_x B(x)^2
      <= 26q + 3C_b + 5D_d + 2D_b + 2M_b + 2M_d
                    + 2*1_(b=d)*D_d.                      (PS4)

For completeness, the constant is

    12q + 3*(3q) + 3*q + 2*q = 26q.

These terms come from the constant event, label 5, label 25, and their intersection. The remaining square terms give 3C_b+3D_d. The five remaining cross terms give 2D_b, 2D_d, 2M_b, 2M_d, and 2*1_(b=d)*D_d. Any incompatible root or child phases only reduce these intersections.

The last original label 175 selects one point. If b=d, then B<=5 and its additional cost is at most 11h. If b differs from d, the label-7 and label-35 indicators cannot both equal one, so B<=4 and the additional cost is at most 9h. This distinction uses the shared original seven-coordinate and does not optimize columns separately in different roots.

For Delta>=10 there are at most two exception children, so (PS2) gives

    C_c<=12k, D_c<=3k, M_c<=k,
    C_y<=3h+q, D_y<=3h, M_y<=h  for y!=c.                   (PS5)

For Delta=9 there are exactly three exceptions, and the corresponding caps are

    C_c<=9k, D_c<=3k, M_c<=k,
    C_y<=3h+3q/2, D_y<=3h, M_y<=h  for y!=c.               (PS6)

The noncenter column bounds include all spoke points from their unique owner root and all possible exception points in that column. The root-column and point bounds hold because every child contributes at most h to a given column.

Substituting these caps into (PS4), including the final point cost, gives all possible phase relations:

| Relation of b,d to c | Delta>=10 numerator bound | At q=10,k=4,h=6 | Delta=9 numerator bound | At q=20,k=9,h=11 |
|---|---|---:|---|---:|
| b=d=c | 37q+56k | 594 | 37q+47k | 1163 |
| b=c, d!=c | 52q+18k | 592 | 52q+9k | 1121 |
| b!=c, d=c | 55q-9k | 514 | 113q/2-9k | 1049 |
| b=d!=c | 80q-51k | 596 | 163q/2-51k | 1171 |
| b,d,c all distinct | 72q-43k | 548 | 147q/2-43k | 1083 |

Therefore

    Delta>=10: Gamma(nu)<=596/120=149/30,
    Delta=9:   Gamma(nu)<=1171/240<59/12,
    Delta<=8:  Gamma(nu)<=59/12.                            (PS7)

These exhaust all sources in the stated pair class and prove (PS1). The proof requires neither an orbit enumeration nor an optimization over probability laws.

## 4. Exact controls and sharpness of the prescribed rules

The [reusable constructor](../../frontier/cover-geometry/pair_source_common_law.py) `construct_common_law` accepts the four child-pair records and optional actual root and child digits. It rejects malformed input and a pair reused in two roots, chooses the appropriate rule, and checks source support, normalization, all simultaneous cell caps, and the five-case inequalities with exact integers and fractions. Its checks remain active under Python optimization.

The finite phase checker evaluates original layouts by retaining b, assigning each of the other four nonconstant original labels to its actual root, and maximizing their remaining local child and column phases. It then checks an attaining layout directly in the literal original CRT coordinates

    z = r+5a+25*(2*(y-r-5a) mod 7).

The independently variable six original moduli remain 1,5,25,7,35,175 throughout. Reduced local choices omit only phases selecting no supported point, since those are dominated by a supported choice for a nonnegative load.

The following source attains 149/30 for the prescribed heavy-column law:

    root 1: {0,1}, {0,1}, {0,1}
    root 2: {0,2}, {0,2}, {0,2}
    root 3: {0,3}, {0,3}, {1,4}
    root 4: {0,4}, {0,4}, {1,5}.

Its bad-pair sets are pairwise disjoint, its projected columns are 0,...,5, and Delta=10. The literal independent phases `(0,1,1,1,1,1)` attain numerator 596 with denominator 120. Thus 149/30 cannot be reduced as the universal upper bound for this particular explicit constructor without changing the rule. This is not a minimax lower bound against all supported laws.

The deterministic source outside the earlier flow, rectangle, singleton and degree-nine criteria is also handled:

    root 1: {0,1}, {0,1}, {0,1}
    root 2: {0,2}, {0,3}, {0,2}
    root 3: {0,4}, {0,4}, {1,4}
    root 4: {0,5}, {0,5}, {1,5}.

Its prescribed law has exact Gamma=149/30, again attained by the literal phases `(0,1,1,1,1,1)`. Its uniform law's previously established value 31/6 is unchanged; the improvement comes from a different single law on the same actual support.

The checks also include a degree-eight source attaining 59/12, a degree-nine source attaining 1171/240, all twelve children containing the center, a one-exception source, and the preceding two-exception sources. Six law checks each exhaust 1792 common-phase/root assignments and all relevant independent local phases. These finite controls check the constructor and arithmetic. The general theorem is supplied by (PS2)–(PS7).

## 5. A correctly aligned conditional height consequence

Suppose additionally that there is one fixed finite family of distinct nonunit moduli, all dividing 5^K*7 for K>=2, and every selected point lies outside every original class whose modulus divides Q0=5^2*7. These are the actual-residual and original-label hypotheses of Chapter 09; an abstract pair source or a projection of a residual involving other primes does not establish them.

For extension only in the five coordinate, the initial five height is two, so k_5=3. Uniformly over every finite later five height, Chapter 09 gives

    B_5 <= 1 + 2*(1/4)/3 + (3/8)/9 = 29/24,
    lambda <= (C-1)/32 = 119/960  for C=149/30.

Hence its existing lifting theorem yields the conditional moment bound

    Gamma_lifted <= ((149/30)*(29/24)-119/960)/(1-119/960)
                  = 16927/2523 < 9.                        (PS8)

This is a consequence for that actual residual if the additional hypotheses hold. It does not supply all residual source classes, a seed with the five/seven heights interchanged, or a simultaneous extension in the other prime coordinate. The older factor 43/32 and square-root cost sqrt(C)/8 correspond to initial five height one; they must not be identified with this height-two source without a separate valid transport.

## 6. Larger neighborhoods cannot always be reduced to disjoint root pair sets

The general two-neighbor law applies once an actual source contains
three selected children in each of four roots, two selected neighbors
at each child, with the distinct selected pair sets disjoint between
roots. Original admissibility and child degree at least two do not
by themselves guarantee such a selection.

### A 38-point boundary already covered by the robust-root method

Take exactly three active children in each of four roots. Initially
give every child the neighborhood `{0,1,2}`. At the first child of
root 4 only, add columns 3 and 4. The neighborhoods are

```
root 1: 012, 012, 012
root 2: 012, 012, 012
root 3: 012, 012, 012
root 4: 01234, 012, 012.
```

There are 38 actual points and five projected columns. Deleting any
two columns leaves at least one neighbor at each of the three
children of every root. Thus all four roots are robust, their
bad-pair graphs are empty, and the original source condition holds.
Every active child's degree is at least three.

Any selection of three children per root must retain all three
active children. In every root, at least two of those children have
entire neighborhood `{0,1,2}`. Therefore that root's selected pair
set contains at least one of

\[
 \{0,1\},\quad\{0,2\},\quad\{1,2\}.
\]

Disjoint pair sets between four roots would require four distinct
pairs from this three-element set, a contradiction.

This source has a successful law from the existing three-robust-root
result (report 431). It is a counterexample only to the proposed
unconditional source reduction, not a new difficult source-law case.

### The reduction can also fail with only one robust root

For a stronger boundary on that reduction, use

```
root 1: 01, 03, 14
root 2: 02, 02, 02
root 3: 12, 12, 12
root 4: 012, 012, 012.
```

There are 27 points and five projected columns. Every active child
has degree at least two. The actual bad-pair graphs are

```
B1 = {01,03,14}, B2 = {02}, B3 = {12}, B4 = empty.
```

They are pairwise disjoint, so the source is admissible, and exactly
one root is robust.

Any selected two-neighbor reduction is forced to use pair `01` in
root 1, pair `02` in root 2 and pair `12` in root 3. Every child in
root 4 can choose only among these three already-used pairs.
Consequently no such reduction exists.

This additionally refutes the implication obtained merely by
excluding sources with at least three robust roots. It does not
assert that this source escapes every other existing law criterion,
and it makes no assertion about its minimax value.

The exact standard-library checker
[pair-selection boundary checker](../../frontier/cover-geometry/pair_selection_boundary.py) independently reconstructs the
bad-pair sets, checks original admissibility and column projection,
enumerates every local pair-set option, and checks that no four
pair-set choices are disjoint. Its output contains the actual sources
and exact local option counts. No numerical optimization, random
sampling or Lean certification is involved.

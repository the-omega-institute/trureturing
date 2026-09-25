# Three-coordinate antichains admit the same periodic selector

## Box-slice theorem

For nonnegative integers N,A,B,C, let

    S={ (a,b,c) in Z_{≥0}^3 : a+b+c=N, a<=A, b<=B, c<=C },
    color(a,b,c)=b+2c mod3.

If S has at least three points, its colors are all of Z/3Z. Equivalently, a slice missing any one color has at most two points. Upper bounds greater than N can be truncated at N.

### General proof

Join two feasible points when one is obtained from the other by transferring one unit from one coordinate to another.

This graph is connected. If x and y are distinct feasible points, choose coordinates i and j with x_i>y_i and x_j<y_j. Replacing x by x−e_i+e_j preserves the coordinate sum and the box bounds: x_i>0 and x_j<y_j<=U_j. It reduces the L1 distance to y by two. Repeating reaches y through feasible points.

A connected graph with at least three vertices has a vertex x of degree at least two. Give coordinates a,b,c weights0,1,2 modulo3. Every feasible transfer i→j changes color by w_j−w_i, which is either1 or2. If two neighbors have different increments, x and those neighbors already exhibit all three colors.

Otherwise take two distinct transfers with the same increment delta. The three possible transfers having that increment form one directed three-cycle. Any two distinct edges of this cycle can be ordered i→j→k. Feasibility of the first gives x_i>0; feasibility of the second gives x_k<U_k. Consequently the direct transfer i→k is also feasible at the ORIGINAL x, irrespective of the intermediate coordinate. Its color increment is2delta, the other nonzero residue. Again the neighbors together with x exhibit all three colors.

This proves the theorem for arbitrary N and arbitrary box bounds. The argument does not assume that the slice is a line or contains an elementary triangle. The latter stronger shortcut is unnecessary.

## Exact limitation at four coordinate directions

The property “every box slice with at least three points contains all three colors” cannot hold for ANY three-coloring on the four-coordinate simplex, already at N=1. Its four points are the four unit vectors. Two must have the same color. Take these two and any third unit vector. The resulting three points have at most two colors. Set the upper bounds to1 on these three coordinate directions and0 on the fourth; the corresponding box slice is exactly the chosen three points and misses a color.

Thus the three-color selector argument with a uniform missing-color slice bound of two cannot extend unchanged to four coordinates. This is an obstruction to that selector property, not an arithmetic covering counterexample or an impossibility theorem for other selectors, larger incidence bounds, or other source constructions.

## Selector on a two-dimensional cofactor inventory

Fix three distinct primes p,q,r in Q={5,7,11,13,17,19}, a nonunit Q-smooth D coprime to pqr, and three fixed global integers r0,r1,r2 with pairwise distinct residues modulo D. The cofactor inventory is

    d_(a,b,c)=D p^a q^b r^c, a+b+c=N.

Allow arbitrary pure3 originals and arbitrary Q-only originals. Every other actual original has modulus3^e d_(a,b,c). At each inventory cofactor, require its actual projections at exponents e=0,1,2,3 to occupy at most one phase a_(a,b,c), including its Q-only original if present. At exponents e>=4 its actual projection must be one of the three global r0,r1,r2. Original ternary phases and all finite heights are arbitrary, and every full numerical modulus has one globally fixed phase.

Choose at each inventory node the selected Q phases

    {a_(a,b,c), if present} union {r_(b+2c mod3)}.

This may use an auxiliary phase or a missing cofactor label in the SELECTED Q input. This finite restriction is allowed explicitly and is used only to choose a law supported on a subset of the actual survivor. It does not insert a new original covering class or alter any original phase. At every other actual Q-only label select its actual phase. Every selected numerical modulus has at most two phases, so Report569 supplies one actual PA law nu with R_Q(nu)<=B and its density bound.

Fix the SAME x in the selected survivor V. A matching tail phase at any inventory node determines x modulo D, hence determines a unique possible global color j. For that j, the complete set of POTENTIAL matching indices is

    S_j(x)={a+b+c=N,
             0<=a<=v_p(x-r_j),
             0<=b<=v_q(x-r_j),
             0<=c<=v_r(x-r_j)}.

Valuations are truncated at N, and the fixed congruence x=r_j modD has already been imposed. This is exactly a box slice of the theorem. If it had at least three points, one would have color(a,b,c)=j. That periodic phase was selected there, contradicting x in V. Therefore at most two potential indices match; actual tail events, which may be missing, are only a subset.

At each selected Q point, at most two numerical cofactors can thus act. The complete pure3 source satisfies u<=2H3, and the complete e>=4 tail at any one cofactor has u-mass at most1/27. Consequently c(x)>=25/27. Report572 supplies the same fixed-u lift and numerical constants:

    R_P <= B+(27/25)(1+B)
        =6199418183523781383463/539719033471556471250
        <566/49.

The actual23/29 extension has the same Haar lower bound>1/37000. This is a two-dimensional indexing inventory of size(N+1)(N+2)/2. The coefficient bound is inherited; the new step is the box-slice selector theorem that proves the pointwise incidence premise.

No analogous claim is made for arbitrary tail projections, two compulsory shallow phases, or more coordinate directions. The selected phases are fixed before sampling x. General auxiliary selected restrictions remain necessary when the actual inventory has gaps.

## Actual 364-original example and source change

Take p=5,q=7,r=11,D=13,N=12 and global tail phases0,1,2. There are91 cofactors. Order their triples lexicographically, indexed j=0,...,90, and at every cofactor d_j use exactly four actual originals:

| ternary exponent e | Q phase modulo d_j | ternary phase modulo3^e |
|---|---|---|
|0|3|vacuous|
|4|1|j mod81|
|5|2|0|
|6|0|0|

These364 full numerical moduli are distinct, odd and nonunit. There are no pure3 originals, so u=H3. Set K=13·5^12·7^12·11^12.

For the old mandatory shallow selector {3} at every cofactor, the selected input has only row13 originals. Earlier5/7/11 coordinates are Haar. The row13 forbidden set is empty or root3, so its density is at most13/12 below the retained PA cap3/2. Later17/19 coordinates are Haar and every row has mass one. Thus the actual old PA law satisfies

    R_Q(nu0)<=(13/12)·157435/165888.

On A=[1 mod K], no old-coordinate projection to phase3 matches, so the row is Haar and nu0(A)=1/K>0. All91 depth4 originals match A; their j mod81 ternary phases exhaust all81 cells. Hence the actual fibre is empty on A. No joint law supported on U can retain nu0.

Now select the periodic second slot b+2c mod3. The selected input still has only row13 originals, whose forbidden root set is a subset of{0,1,2,3}. Every row has good mass at least9/13, so its normalized density is at most13/9<3/2. No PA mass loss occurs. The new actual law has

    R_Q(nu)<=(13/9)·157435/165888.

The box-slice theorem leaves at most two active cofactors. In this finite example each contains only depths4,5,6, so c>=1−2(3^-4+3^-5+3^-6)=703/729. Using R3(H3)=1/2, the one fixed-u lift has the complete-query upper

    R_P <= (13/9)r_H+[729/(2·703)](1+(13/9)r_H)
        =5457999593/2099146752
        =2.60010386972697... .

These are density-based upper bounds, not optimum claims. The new marginal comes from rebuilding the selected actual PA input, not from retaining the old dead-fibre marginal.

Every original has a private witness. For its cofactor d_(a,b,c) and Q color t in{0,1,2,3}, choose x_Q=t+d_(a,b,c) modulo K. Its valuations at5,7,11 truncated at12 are(a,b,c). Any same-color matching cofactor has exponents componentwise at most(a,b,c) with the same total12, hence equals that cofactor. Different colors are separated modulo13. Choose the required ternary residue by CRT. This witnesses only the chosen original, including when several depth4 originals share a ternary residue.

## Verification

Program: [three_coordinate_periodic_selector.py](../../frontier/cover-geometry/three_coordinate_periodic_selector.py).
Data: [three_coordinate_periodic_selector.json](../../frontier/cover-geometry/three_coordinate_periodic_selector.json).

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/three_coordinate_periodic_selector.py

Exit0;14 named checks. Exhaustive diagnostics cover23409 box slices for N=0,...,16 and702 local feasible-transfer cases. The actual example has364 independently phased labels; all364 private witnesses were tested against every original, totaling132496 congruence comparisons. The PA row bounds, dead source mass, finite fibre reserve and complete-query arithmetic are retained. The general proof supplies the arbitrary-N quantifier; no huge period or infinite original family is enumerated.

The ordinary graph argument supplies the general selector theorem. No new Lean verification or external novelty claim is made.

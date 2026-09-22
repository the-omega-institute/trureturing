[Index](../../marked_head_profile.md) · [Complete-chain blockers](376-complete-prime-chain-transport-and-joint-prefix-laws.md) · [Saturated fibres](378-saturated-prime-fibres-and-mixed-tail-incidence.md) · [Root forests](379-root-forest-disintegration-and-residue-costs.md) · [One three-prime source](389-saturated-chain-source-has-small-complete-layout-second-moment.md)

# Normalized two-prime root blockers admit a common second-moment law

Let `R` be a subset of the nonzero roots in `Z/5 x Z/7`. Assume that
its first projection has at least three roots, its second has at least
five, and it meets every product of three roots at 5 and five roots
at 7. Then there is **one probability supported on R** for which

\[
 \Gamma_{35}(\nu)
 :=\max_{(b_d)_{d\mid35}}
   \mathbb E_\nu\left(\sum_{d\mid35}
                    \mathbf1_{x=b_d\bmod d}\right)^2
 \le4.                                                   \tag{TB1}
\]

Every divisor residue in TB1 is a freely chosen fixed residue. The
law is fixed before this entire maximum is taken. A layout need not
have a common centre. The proof constructs the law by classifying
five minimal bipartite supports in the four-root case; the three-root
case has a direct saturated construction.

The same root laws, when extended by **independent uniform higher
digits**, satisfy a complete-layout second-moment bound at all finite
heights, bounded by the independent auxiliary comparison with bases `(3,3)`.
That extension concerns full uniform tails. An arbitrary source that
meets full-height product trees need not contain those tails, so no
all-height source theorem follows. In particular this does not close
the unrestricted Erdős #7 problem. These are ordinary mathematical
proofs and exact controls, not new Lean theorems.

## 1. Root conditions and arbitrary-layout costs

Regard the first roots as rows and the second roots as columns. The
nonzero-root hypothesis leaves at most four rows and six columns.
Write `N_i` for the column neighborhood of row `i`.

If exactly three rows are active, the product condition forces
`|N_i|>=3` for each: a three-row set can select `i` and the two missing
rows, and a row with at most two neighbors misses some five-column set.

If four rows are active, the product condition is equivalent to

\[
 |N_i\cup N_j|\ge3\quad(i\ne j).                       \tag{TB2}
\]

Necessity follows by selecting these two rows and the missing fifth
row. For sufficiency, any three-row set contains at least two active
rows, whose three or more neighbors meet every five-column set.
The separate one-coordinate condition gives

\[
 \left|\bigcup_iN_i\right|\ge5.                         \tag{TB3}
\]

For a supported law, let `w_ij` be its point masses and `r_i,c_j`
its row and column masses. An arbitrary complete layout chooses a
row `a`, a column `b`, and a point `(u,v)`, independently; divisor one
contributes the constant one. Its load is

\[
 L=1+\mathbf1_{i=a}+\mathbf1_{j=b}+\mathbf1_{(i,j)=(u,v)}.
\]

Expanding under this same law gives the exact identity

\[
 \mathbb EL^2
 =1+3r_a+3c_b+2w_{ab}
       +(3+2\mathbf1_{u=a}+2\mathbf1_{v=b})w_{uv}.        \tag{TB4}
\]

Consequently row, column and atom caps `alpha,beta,gamma` imply the
useful sufficient bound

\[
 \Gamma_{35}(\nu)\le1+3\alpha+3\beta+9\gamma.           \tag{TB5}
\]

TB5 will handle four of the five minimal types. The remaining type
uses TB4 itself, since the relative positions of the largest masses
matter. Absent rows, columns and point cells have zero mass and are
included in both formulas.

## 2. Three active rows

Choose any three neighbors in each active row and assign mass `1/9`
to each of the nine chosen points. Row masses are `1/3`, column
masses are at most `1/3`, and atom masses are `1/9`. TB5 gives TB1.
There is no requirement that the three chosen neighbor sets agree.

## 3. Five minimal types for four active rows

Delete edges while preserving nonempty rows, TB2 and TB3, until the
support is edge-minimal. A law on this smaller support is also a law
on the original support. The following classification is up to
independent permutations of rows and columns:

| Type | The four row neighborhoods | Edges |
| --- | --- | ---: |
| A | `{a}`, `{b,c}`, `{a,b,c}`, `{d,e}` | 8 |
| B | `{a}`, `{b,c}`, `{b,d}`, `{b,e}` | 7 |
| C | `{a}`, `{b,c}`, `{b,d}`, `{c,e}` | 7 |
| D | `{a}`, `{b,c}`, `{b,d}`, `{e,f}` | 7 |
| E | `{a,b}`, `{a,c}`, `{b,c}`, `{d,e}` | 8 |

The letters in each row of the table denote distinct columns. Here
is a combinatorial proof that the table is exhaustive.

**Degrees at most three.** Deleting an edge from a row of degree at
least four preserves every pair union. If at least six columns occur,
it also preserves TB3. If exactly five columns occur, that row has
a shared neighbor: four or more private columns would confine the
other three nonempty rows to at most one column, contradicting TB2.
Deleting the edge to a shared neighbor again preserves TB3. Thus
minimality excludes every row degree at least four.

**A triple must contain the neighbor of a singleton.** There is at
most one singleton row, by TB2. Suppose a degree-three neighborhood
`S` contains no singleton neighbor. If a vertex `v` of `S` also
occurs in another row, deleting its edge leaves all columns present.
The only possible new TB2 violation is that `S\{v}` equals another
degree-two row. Such a row makes both other vertices of `S` shared.
Hence existence of one shared vertex forces all three to be shared,
and minimality requires all three complementary pairs as the other
three rows. The entire projection would then be `S`, contrary to TB3.
If no vertex of `S` is shared, deletion forces the total projection
to have exactly five columns; otherwise one could delete an edge.
The other three rows would then all lie in the two columns outside
`S`, again contradicting TB2. This proves the assertion.

**No singleton.** All four rows must now have degree two. Their
neighborhoods are four distinct edges of a simple graph on the five
or six active column vertices. A graph edge joining a leaf to a
vertex of degree at least two would allow deletion of the latter's
incidence. Its column remains present, and the new singleton leaf
is absent from every other row, so every row-pair union still has
at least three elements. Minimality rules this out. Thus components
are isolated edges or have minimum degree at least two. Four edges
on five or six vertices can only be a triangle and an isolated edge:
four isolated edges would require eight vertices, and a four-cycle
has only four. This is type E.

**A singleton `{a}` and a triple.** Every triple contains `a` by the
previous argument. Deleting `a` from a triple loses no column, so
minimality forces its other two entries to equal a degree-two row.
Two triples would need the same remaining degree-two row, hence both
would be `{a,b,c}` and the whole projection would have only three
columns. Therefore there is exactly one triple, its matching double,
and one other double. TB3 forces the last double to use two new
columns. This is type A.

**A singleton and no triple.** The other three rows are distinct
pairs avoiding `a`. They form a simple graph with three edges on
four or five column vertices. It is a forest: a triangle would use
only three vertices. The possibilities are a three-edge star, a
three-edge path, or a two-edge path and an isolated edge. These are
types B, C and D. Three isolated edges would need six columns in
addition to `a`, exceeding the available six.

This proves the classification without relying on numerical LPs or
the finite enumeration in section 7.

## 4. One explicit law for each type

For type A use the uniform law on its eight points. Its maximum row
degree is three and maximum column degree is two. TB5 gives

\[
 1+3(3/8+2/8)+9/8=4.                                 \tag{TB6}
\]

For types C and D, use the uniform law on seven points. Both maximum
degrees are two, so TB5 gives `1+3(2/7+2/7)+9/7=4`. For type E,
the uniform law on eight points gives `1+3(2/8+2/8)+9/8=29/8`.

For type B give the isolated point mass `1/6`, each of the three
edges in the common column mass `1/9`, and each of the three private
leaf points mass `1/6`. These masses sum to one. In units of `1/18`,
the row masses are `(3,5,5,5)`, the common-column mass is six, every
other active column has mass three, the common-column atom masses
are two and all other atom masses are three.

To check every layout in TB4, separate four cases. If the chosen
column is the common column and the chosen row is a spoke row, the
first three nonconstant terms have numerator `15+18+4=37`; the
remaining point term has numerator at most 15. If the column is
common and the row isolated, these bounds are 27 and 15. If the
column is not common and `(a,b)` is a supported point, the bounds
are 30 and 21. If it is not a supported point, the bounds are 24
and 15. Absent row or column choices cannot increase the maximum:
replacing an identically zero indicator by any supported one can
only increase the nonnegative load pointwise. The same argument
handles an absent point choice. Therefore

\[
 \Gamma_{35}(\nu_B)=1+\frac{52}{18}=\frac{35}{9}<4.      \tag{TB7}
\]

Equality is attained by selecting a spoke row, the common column,
and that row's private leaf point. Those residues are incompatible
with one common centre. In particular, restricting the maximum to
centred layouts would omit a maximizing layout even in this small
case.

All constructed laws, including section 2, also satisfy the common
caps

\[
 \max_i r_i\le\frac38,\qquad
 \max_j c_j\le\frac13,\qquad
 \max_{i,j}w_{ij}\le\frac16.                            \tag{TB8}
\]

The caps and TB1 refer to the same selected law. They are not pooled
from separately optimized probabilities. The displayed laws are
witnesses for TB1, not claims of minimax optimality over all laws.

## 5. Full uniform tails: a separate all-height consequence

Let `H_5,H_7>=1`, `Q_H=5^H_5 7^H_7`, and lift the selected root law
by independent uniform higher digits in both coordinates. This law
is supported on the full inverse image of its root support. Put

\[
 A_p(H)=\sum_{a=1}^H(2a+1)p^{-(a-1)},\qquad
 A_5(\infty)=\frac{35}{8},\quad A_7(\infty)=\frac{35}{9}.
                                                               \tag{TB9}
\]

In the complete-load square expansion, retain the terms from pairs
of divisors in `{1,5,7,35}` as one squarefree layout. Their total is
at most four by TB1. For every other pair, the congruence intersection
is empty or one cylinder at the lcm. TB8 and the independent uniform
tails bound this cylinder by `alpha*5^(1-a)`, `beta*7^(1-b)` or
`gamma*5^(1-a)7^(1-b)`, according to its positive coordinates,
where `(alpha,beta,gamma)=(3/8,1/3,1/6)`.

There are `2a+1` ordered exponent pairs with maximum `a`. Summing
only the terms beyond the squarefree block gives, for arbitrary
independent divisor residues,

\[
 \Gamma_{Q_H}(\nu_H)\le F_H
 :=4+\frac38(A_5-3)+\frac13(A_7-3)
                  +\frac16(A_5A_7-9).                 \tag{TB10}
\]

Consequently `F_H` increases to `3541/576<7`. This is an upper
bound, not an exact formula for the lifted maximum.

For independent auxiliary variables with finite tails
`Pr(K_p>=a)=3^(-a)`, `1<=a<=H_p`, the complete second moment is

\[
 T_H=\prod_{p\in\{5,7\}}
       \left(1+\sum_{a=1}^{H_p}(2a+1)3^{-a}\right).    \tag{TB11}
\]

At `(H_5,H_7)=(1,1)`, `F_H=T_H=4`. Increasing the 5-height to
`a>=2` changes TB10 by at most
`(221/216)(2a+1)5^(1-a)`, whereas TB11 increases by at least
`2(2a+1)3^(-a)`. Their ratio is at most

\[
 \frac{221}{240}\left(\frac35\right)^{a-2}<1.          \tag{TB12}
\]

Increasing the 7-height similarly gives a ratio at most
`(153/224)(3/7)^(a-2)<1`; here the slope bound in TB10 is
`1/3+(1/6)(35/8)=17/16`. Taking any finite path of height increments
from `(1,1)` proves

\[
 \Gamma_{Q_H}(\nu_H)\le F_H\le T_H,                    \tag{TB13}
\]

with the second inequality strict away from `(1,1)`. This proof
retains the original unequal heights. It assumes full uniform tails
throughout; arbitrary conditional or missing tails do not satisfy
the cylinder formulas used in TB10.

## 6. Interface to actual arithmetic sources

The theorem's nonzero-root condition is an explicit premise. In the
already normalized extremal model of 350 and 378, the actual 3-free
residual avoids the present pure classes `0 mod5` and `0 mod7`.
Report 375 supplies the separate projection bounds, and 376 supplies
the three-by-five root-product obstruction. When those established
model hypotheses apply, the actual root projection meets precisely
the conditions above. No additional normalization or assumption of
minimum-cardinality preservation is being introduced here.

A root law can be lifted to an actual full residual by selecting one
actual witness above each of its supported root points. This preserves
TB1 for the four squarefree divisors and uses one actual supported
law. It does **not** establish TB10 for that lift: actual higher
digits may be restricted and correlated. Nor does it automatically
control other primes or all original repeated-prime labels. The
missing continuation is a bound for the complete original divisor
layout under one law on the actual full source.

## 7. Exact controls and scope of reuse

The [standard-library checker](../../frontier/cover-geometry/two_prime_root_second_moment.py)
checks all five template laws using all `5*7*35=1225` independent
layouts per law, including absent residues. It compares direct
integration of the squared load with TB4 and confirms the exact
maxima `(4,35/9,4,4,29/8)`. It separately enumerates all 135751
row-unordered multisets of four nonempty neighbor sets of size at
most three in six columns. Of these, 83210 satisfy the conditions;
900 are edge-minimal and lie in exactly the five displayed orbits,
with counts `(180,120,360,180,60)`. This is an independent complete
control of the reduced classification, not a substitute for its
combinatorial proof. Fifteen full uniform-tail controls reconstruct
1739 source points and 105 divisor-cylinder tables, check the exact
tail scaling and the root/deeper-pair decomposition, and compare its
bound with TB10--TB11. Exact rational checks also verify TB10's
limiting constant and the two initial slope ratios in TB12.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_prime_root_second_moment.py
```

The lcm-square estimate uses the existing technique in Chapter 08,
`finite_head_geometry.md` and report 389. Reports 376, 378 and 379
provide the source obstructions and the saturated/forest probability
constructions. The common-law bound above concerns normalized root
sources and their specified uniform lifts.

[Index](../../marked_head_profile.md) · [Sharp source structure](403-root-structure-of-sharp-minimum-sources.md) · [Balanced selection](408-a-balanced-five-tree-selection-controls-all-heights.md) · [Asynchronous gluing](410-an-initial-ternary-budget-allows-asynchronous-stopping.md)

# A sharper full-five criterion and a sharp minimum source boundary

Ordinary analytic proof and exact research construction; no Lean claim.
This is a source-family theorem and a universal obstruction to one
probability architecture, not a counterexample to the source conjecture.

Use the source class and original finite game of [report 400](400-literal-layout-mixtures-and-exact-tree-rank-duality.md).
A source lies in `{1,2,3,4} times Z/7^K`; admissibility requires a
complete ternary projection tree in each of the six row pairs and a
complete five-ary tree in the full projection. For one probability
`nu` supported on the source, write

    Gamma_(1,K)(nu) = max_a E_nu (sum_(d | 5*7^K) 1_(x=a_d mod d))^2,
    t_K = sum_(j=0)^K (2j+1)3^-j = 3-(K+2)3^-K.

CRT identifies `(r,y)` with `x mod 5*7^K`. Each original divisor has
its own independently chosen phase, including choices outside the
source. The law is chosen before those phases. The general selection
criterion below does not itself require source admissibility.

## A finite-height improvement of the balanced full-five criterion

Fix K>=2 and one actually supported labelled complete five-ary tree.
Give every selected leaf mass 5^-K. As in 408, let beta_r be its row
mass, q_(r,c) its row/root-cell mass, and M_r=max_c q_(r,c). Define

    b = max_r (beta_r+3M_r).

Suppose c>=8/9 and b<=c. Since there are exactly five root columns,
M_r>=beta_r/5, hence beta_r<=5c/8. The exact independent-phase root
square from 408 is

    1+3beta_a+3C_b+2q_(a,b)
      +(3+2[a=s]+2[b=d])q_(s,d).

The three exhaustive cases, retaining actual shared cell/column
constraints, give the following bounds:

* s=a: at most 8/5+3beta_a+9M_a <= 8/5+3c.
* s!=a, b=d: q_(a,b)+q_(s,b)<=1/5 implies the joint contribution
  2q_(a,b)+5q_(s,b)<=1. The result is <=13/5+15c/8.
* s!=a, b!=d: at most 11/5+3beta_a+2M_a
  <=11/5+2c/3+7beta_a/3 <=11/5+17c/8.

The first upper bound dominates the other two: the differences are
9c/8-1 and 7c/8-3/5, both nonnegative when c>=8/9. Row-zero phases
have zero indicators and may be replaced by actual-row phases without
decreasing the pointwise load, so they are also covered.

Every higher-depth pure or joint prefix mass is at most 5^-j under
the same actual law. The original-divisor LCM expansion, with all
phases still independently selected, gives

    Gamma_(1,K) <= V_K(c)
      := 8/5+3c+4 sum_(j=2)^K (2j+1)5^-j
       = 27/10+3c-(4K+7)/(2*5^K).

Consequently define

    c_K = 11/10-2(K+2)/3^(K+1)+(4K+7)/(6*5^K).

If b<=c_K, choose c=max(b,8/9), which is permitted because
c_K>=c_2=122/135>8/9. Then Gamma_(1,K)<=2t_K, with exact certified
margin 3(c_K-c). A strict b<c_K gives a strict margin.

The finite thresholds increase to 11/10. Indeed

    c_(K+1)-c_K
      = [2(2K+3)/3] [3^-(K+1)-2*5^-(K+1)] > 0

for K>=1. A simpler height-independent criterion is b<=9/10. Taking
c=9/10 yields

    Gamma_(1,K) <= 27/5-(2K+7/2)5^-K,
    2t_K-Gamma_(1,K) >= 1/90  (K>=2).

The margin equals 1/90 at K=2. Its next-height increase equals
2(2K+3)[3^-(K+1)-2*5^-(K+1)]>0. This improves 408's sufficient
22/25 criterion for arbitrary actual selections; it does not infer
such a selection from arbitrary source admissibility.

## Two one-surplus tails, with exact pair capabilities

Let F_h be the standard complete five-ary seven-adic tree of height h,
using digits 0,...,4 from lowest to highest. For a two-element row set
A, define

    Q_0^A = {(r,0): r in {1,2,3,4}\A},
    Q_h^A = {(r,7y):(r,y) in Q_(h-1)^A}
             union union_(r=1)^4 {(r,r+7y):y in F_(h-1)}.

Then |Q_h^A|=5^h+1, its projection is exactly F_h, and a row pair B
has a complete ternary projection tree exactly when B!=A. At height
zero, B meets the two complementary rows exactly when B!=A. At every
higher node, B gets exactly its two private root columns, and must
obtain its third good child from the continuing column. This proves
the exact capability statement by induction, not merely sufficiency.

For K>=1 put h=K-1 and define R_K by five root children:

| Column | Actual child source |
|---|---|
| 0 | Q_h^{12} |
| 1 | Q_h^{13} |
| 2 | row 1 above F_h |
| 3 | row 2 above F_h |
| 4 | row 3 above F_h |

Its cardinality is 2(5^h+1)+3*5^h=5^K+2 and its projection is exactly
F_K. The root good-child counts for row pairs 12,13,14,23,24,34 are
respectively 3,3,3,4,3,3. Therefore R_K is admissible and, by the
existing size lower bound in 400, sharp minimum.

For K>=2 this is exactly the second root pattern of 403: two
one-surplus children and three clean children. The exceptional
double-good partition sets are {pi_2,pi_3} and {pi_1,pi_3}. In their
one-surplus recursions these same sets persist along the exceptional
path. Thus the example meets the full stated capability constraints.

## A uniform ternary root forces an actual forbidden cost

Let any actual supported probability nu on R_K be concentrated on
exactly three root columns, each having mass 1/3. Its conditional laws
within those columns are arbitrary. Only columns zero and one can
be nonmonochromatic, so a selected column c is monochromatic in a
row r. Choose the original phases at labels 1,5,7,35 to select 1,
row r, column c, and cell (r,c), respectively. On that column all four
indicators are one; elsewhere the divisor-one indicator remains one.
Consequently

    E_nu[L_root^2] >= 16*(1/3)+1*(2/3) = 6.

All other original-divisor indicators are nonnegative, so Gamma_(1,K)
is at least six for every such nu, whereas 2t_K=6-2(K+2)3^-K<6.
For this actual source the remaining phases can even all be made empty:
choose pure phase 6 at every depth >=2 and row-zero mixed phases.

The exact root identity gives more detail. If a monochromatic cell has
mass w and its row has total mass beta_r, the aligned four-label root
cost is 1+3beta_r+12w >= 1+15w. A law meeting the target therefore
requires w <= (2t_K-1)/15 < 1/3. This is an actual shared-law inequality.

Thus every 409 law with positive synchronized prefix depth, and every
410 law with positive minimum stopping depth, fails on this source,
regardless of its chosen ternary subtree or terminal probabilities.
This is stronger than failure of a tail-profile sufficient inequality.
The q=0 constructor in 409 is explicitly outside this obstruction.
Nonuniform root weights and laws using more than three root columns
are also outside it.

## A successful law on the same source

Both exceptional Q_0 bases contain row four. At both duplicated
projection leaves choose row four; every other projection leaf has
one available row. Give each of the resulting 5^K labelled leaves
mass 5^-K. This is one actual uniform full-five-tree law, fixed before
all original phases are chosen.

Within either Q_h, the selected row-four distribution at height zero
and the one-continuing-plus-four-private recursion yield

    q_h(r)=(1-5^-h)/4  for r=1,2,3,
    q_h(4)=(1+3*5^-h)/4.

Hence in the full law on R_K,

    beta_1=beta_2=beta_3=3/10-(1/10)5^{-(K-1)},
    beta_4=1/10+(3/10)5^{-(K-1)}.

For K>=2 the first three are maximal. Every root column has mass 1/5;
every root cell has mass at most 1/5. For independent phases at 5,7,35,
the actual root-square identity from 398/408 is

    1+3beta_a+3C_b+2q_(a,b)
      +(3+2[a=s]+2[b=d])q_(s,d).

It is at most 1+3beta_max+12/5, attained by taking a private column
and its corresponding row. Therefore its exact maximum is

    g_K=43/10-(3/2)5^-K.

At every deeper depth j the pure and joint prefix masses are at most
5^-j. Apply the existing literal-LCM shell count to the same law,
leaving every phase independent:

    Gamma_(1,K) <= U_K
       := g_K+4 sum_(j=2)^K (2j+1)5^-j
        = 27/5-(2K+5)5^-K.

At K=2, U_2=126/25 and 2t_2-U_2=16/225. The target increment is
(4K+6)3^-(K+1), while U_(K+1)-U_K=(8K+18)5^-(K+1). For K>=2,
(5/3)^(K+1)>3>(8K+18)/(4K+6), so the target margin strictly increases.
Thus this law has uniform margin at least 16/225 for every K>=2,
and U_K tends to 27/5. K=1 is not included in this positive theorem.

## Every 408 balanced selection still fails once K>=3

This conclusion concerns all supported uniform full-five selections,
not only the successful one just chosen. Both missing row pairs contain
row one. Consequently neither Q_0 contains row one, and every uniform
selection in Q_h has row-one mass (1-5^-h)/4, independently of how its
duplicated leaf is labelled. In R_K every such selection therefore has

    beta_1=3/10-(1/10)5^{-(K-1)},   M_1=1/5.

The maximum root-cell value is exactly 1/5 because the private row-one
column is present, and no column is heavier. Thus

    beta_1+3M_1=9/10-(1/10)5^{-(K-1)}>22/25  (K>=3).

Every balanced-selection certificate of 408 fails. At K=2 equality
is possible, and no exclusion is claimed. The explicit full-five law
above succeeds by its actual root bound despite that criterion's failure.

## What this resolves, and the remaining bridge

The 403 root classification does not imply extraction of a qualifying
uniform ternary stopping frontier, even on sharp minimum sources and
even after allowing arbitrary terminal laws or weakening their row
caps. The obstruction is already an actual cost at the first root.

A complete recursive approach must permit other mass allocations,
such as the full-five probability proved here. This particular positive
construction uses one explicit recursively specified pair of tails;
it does not supply a law for arbitrary one-surplus tails with the same
capability sets. The remaining general bridge is still actual coupled
row/prefix control for those arbitrary tails.

The squared-root identity, LCM shell count, and sharp size bound are
reused. The new content is the larger finite-height selection threshold,
this two-one-surplus all-height family,
the all-laws obstruction to uniform ternary extraction on it, and its
explicit successful full-five law. No literature originality claim.

## Reusable exact checks

[refined_five_tree_common_law.py](../../frontier/cover-geometry/refined_five_tree_common_law.py)
provides `test_selection`, `make_common_law`, and `verify_common_law`
for arbitrary supplied actual labelled full-five selections. It also
constructs the recursive family, verifies its pair capabilities, and
checks the structural obstruction for every three-root equal-mass law.
The finite controls include all 1,225 original root phase assignments,
30 tail capability cases, sharp sources at heights 2 through 5, a row
permutation, all ten three-root selections at those heights, and 21
malformed inputs. Runtime input validation remains enabled under `-O`.

Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined_five_tree_common_law.py
```

These finite controls check the reusable program and examples. The
all-height claims use the proofs above; they are not finite-enumeration
claims or Lean certification.

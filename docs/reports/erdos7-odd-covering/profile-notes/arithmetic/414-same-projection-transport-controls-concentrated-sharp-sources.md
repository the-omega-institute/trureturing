[Index](../../marked_head_profile.md) · [Literal phase game](400-literal-layout-mixtures-and-exact-tree-rank-duality.md) · [Sharp source patterns](403-root-structure-of-sharp-minimum-sources.md)

# A same-projection transport bound and a common law on concentrated sharp sources

Ordinary analytic proof; exact rational checks below support the arithmetic.
No Lean certification is claimed. This treats an explicit unbounded family
of sharp minimum sources, not all one-surplus tails or all admissible sources.

Work in the original independent-phase game of report 400. For K>=1 let
X={1,2,3,4} times Z/7^K, identify a point with its CRT residue modulo 5*7^K,
and let ell_lambda be the sum of the 2(K+1) original-divisor indicators.
Each divisor d|5*7^K has an independent residue a_d, including inactive row
and column choices. For a probability nu on X put

    Gamma_K(nu)=max_lambda E_nu[ell_lambda^2],
    t_K=3-(K+2)3^-K.

Every law constructed below is selected before lambda.

## Same-projection relabelling lemma

Let nu and nu_bar have a coupling (R,R_bar,Y) which preserves the entire
seven-adic coordinate Y. Suppose P(R!=R_bar)<=delta and every depth-j
seven-adic cylinder has probability at most b^-j for 0<=j<=K. Then

    |E_nu ell_lambda^2-E_nu_bar ell_lambda^2|
       <= 3 sum_(j=0)^K (2j+1) min(delta,b^-j)             (T1)

for every original layout lambda, and hence the same right side bounds
|Gamma_K(nu)-Gamma_K(nu_bar)|.

Proof. Expand the square as ordered pairs of original divisor labels.
A pair of pure labels 7^u,7^v depends only on Y and contributes zero
difference. A pair containing a mixed label 5*7^u either has inconsistent
phase conditions (so its event is empty) or selects one row and one
seven-adic cylinder of depth j=max(u,v). Its two indicators can differ
only on {R!=R_bar} within that cylinder. The absolute expectation difference
is therefore at most min(delta,b^-j). There are 4(2j+1) ordered label pairs
with maximal seven-adic depth j, of which 2j+1 are pure-pure. The remaining
3(2j+1) pairs give T1. Triangle inequality is applied to one fixed layout;
no coupling between independently selected original phases is introduced.
Taking maxima preserves the uniform difference bound.

This lemma does not require nu_bar to be supported on the original
source. Both laws and the coupling must live on the same ambient carrier;
nu itself remains an actually supported probability throughout.

## Actual sharp source with concentrated clean tails

Seven-adic digits are read lowest first. Let F_h be the full five-ary tree
using digits 0,...,4, with F_0={0}. For i in {1,2,3,4}, define C_(i,0)
as the one point labelled i, and C_(i,1) as all five leaves labelled i.
For h>=2, let C_(i,h) have C_(i,h-1) in root columns 0,1,2 and pure
row-1 copies of F_(h-1) in columns 3,4.

Thus C_(i,h) has exactly one row label on each leaf of F_h and has star
signature i: a row pair B has a ternary projection tree iff i belongs to B.
This follows by induction. If i is in B the first three children work;
if i is absent only the last two children can work. For h>=1 its number
of row-i leaves when i!=1 is 5*3^(h-1), and every other leaf has row 1.
The uniform full-five law therefore concentrates at row 1 as h increases.

For a two-row set A put

    Q_0^A={(r,0): r in {1,2,3,4}\A},
    Q_h^A= column 0 containing Q_(h-1)^A
             plus column i containing C_(i,h-1), i=1,2,3,4.

These are actual labelled sources, not row-capability summaries. Their
projection is F_h, their size is 5^h+1, and a pair B has a complete ternary
projection tree iff B!=A. At height zero this is the nonempty intersection
of two row pairs. At positive height B gets exactly two good clean
children (the two i in B), and needs the continuing child for its third.
This proves the iff recursively.

For K>=2, h=K-1, define R_K by these five root children:

| Root column | Source |
|---|---|
| 0 | Q_h^{12} |
| 1 | Q_h^{13} |
| 2 | C_(1,h) |
| 3 | C_(2,h) |
| 4 | C_(3,h) |

The good-child counts for pairs 12,13,14,23,24,34 are 3,3,3,4,3,3.
Thus all six pair trees exist. The full projection is F_K and
|R_K|=5^K+2, so report 400's size bound makes this a sharp minimum source.
It has precisely the two-one-surplus/three-clean root pattern of 403.

## Actual component laws, fixed for all layouts

Let mu_K select the smaller row at each duplicated projection leaf and
the sole row elsewhere; give the selected 5^K leaves equal mass 5^-K.
For B=23,24,34, let eta_(B,K) be the following actual uniform ternary law:
recursively select the three least good child columns, and at a terminal
leaf select the smaller available row in B. Each selected leaf has mass
3^-K. This deterministic rule depends only on R_K and B.

Inside C_(i,h), whenever B is one of 23,24,34 and i is in B, the first
three good children recurse until the base; all selected leaves have
row i. Inside a Q tail, eta_B uses the continuing child and the two clean
children indexed by B. At the global root, eta_23 and eta_24 use columns
0,1,3; eta_34 uses columns 0,1,4.

Choose the single actual common law

    nu_K=(5/13)mu_K+(8/39)(eta_(23,K)+eta_(24,K)+eta_(34,K)).       (T2)

It is a mixture of one full-five law and three of the six actual pair
ternary laws; the other three permitted pair coefficients are zero.
All component choices and coefficients are fixed before the layout.

## Comparison probabilities used only in the estimate

Define mu_bar_K by keeping mu_K's Y projection and replacing every row by 1.
For each eta_B, alter only the two leaves y=0 and y=1 reached by taking
one exceptional root column and then only continuing Q columns. At each
such leaf replace the deterministic row by a uniform choice between the
two rows of B. Keep Y unchanged and call the resulting probability eta_bar_B.

The comparison probabilities can put mass outside R_K. They are never
claimed to be successful source laws; T1 transfers their bounds to the
actual law T2. Each eta_bar_B retains its uniform ternary Y marginal.
Its conditional row law in either global Q child is exactly uniform
on B: this holds at the newly balanced terminal point, and induction
preserves it because the two clean children have the two distinct rows
of B, with each of the three children carrying probability 1/3.

Put nu_bar_K=(5/13)mu_bar_K+(8/39)sum_B eta_bar_B. Its row/root-cell
matrix is independent of K (entries displayed after multiplication by 117):

             col 0   col 1   col 2   col 3   col 4
    row 1       9       9       9       9       9
    row 2       8       8       0      16       0
    row 3       8       8       0       0       8
    row 4       8       8       0       0       0

All entries sum to 117. Its row masses are (45,32,24,16)/117 and column
masses are (33,33,9,25,17)/117.

For independent root phases a at 5, b at 7, and (s,d) at 35, the exact
root square is

    1+3 beta_a+3 C_b+2 q_(a,b)
      +(3+2[a=s]+2[b=d]) q_(s,d).                         (T3)

The maxima over b,d for each (a,s), multiplied by 117, form the table

       s=1  s=2  s=3  s=4
    a=1 432  425  409  409
    a=2 373  432  368  368
    a=3 349  352  360  344
    a=4 325  328  320  336

Consequently the exact root maximum is 432/117=48/13. It is attained
only at (a,b,s,d)=(1,0,1,0),(1,1,1,1),(2,3,2,3) among active phases.
Inactive row or column choices can be replaced by active choices without
decreasing the pointwise load, so this maximum covers every original
phase. Independent enumeration directly of the squared load, including
all inactive choices, yields the same value and these three attainers.

At any positive depth j the pure cylinder mass satisfies

    m_j <= (5/13)5^-j+(8/13)3^-j.

Row 1 joint cylinders receive only mu_bar; any other row lies in at most
two of the three pair laws. Thus

    c_j <= max((5/13)5^-j,(16/39)3^-j)=(16/39)3^-j.

The original-divisor LCM expansion now bounds every remaining shell:

    Gamma_K(nu_bar_K)
      <= 48/13 + sum_(j=2)^K (2j+1)[(5/13)5^-j+(24/13)3^-j]
      < 587/104.                                        (T4)

Here sum_(j=2)^infty (2j+1)5^-j=11/40 and the corresponding ternary
sum is 1. No coherent-layout or common-prefix restriction was imposed.

## Actual-to-comparison coupling

For mu_K use its very same Y and change only the label. Its row-1 mass is

    1-(3/5)^(K-2)+7/5^K,

so the mismatch probability is exactly

    delta_K=(3/5)^(K-2)-7/5^K <= (3/5)^(K-2).             (T5)

For completeness the actual full-five row counts are

    (5^K-25*3^(K-2)+7,
     10*3^(K-2)-2,
     10*3^(K-2)-2,
      5*3^(K-2)-3).

They follow by the clean-tail count 5*3^(h-1) and the continuing Q
recursion. Within Q_h, the contribution to each non-row-1 row, before
the chosen exceptional terminal row, is

    A_h=(5*3^(h-1)-3)/(2*5^h), h>=1;

the chosen terminal row receives another 5^-h. Q^{12} chooses row 3,
Q^{13} chooses row 2. Adding the five actual root children gives T5.
The entire Y marginal of both mu laws is the uniform full-five law,
so every depth-j cylinder has mass at most 5^-j.

For each eta_B, each of the two altered leaves has mass 3^-K. Coupling
the balanced terminal choice to the original deterministic row changes
that label with probability 1/2. Hence the total mismatch is exactly
3^-K, with Y unchanged. All other points retain their actual row.
Every depth-j cylinder has mass at most 3^-j.

Apply T1 to the full-five pair and to each actual/comparison ternary
pair, and combine them using the actual mixture coefficients:

    Gamma_K(nu_K)
      <= 587/104
       +(15/13) sum_(j=0)^K (2j+1) min(delta_K,5^-j)
       +(24/13)(K+1)^2 3^-K.                            (T6)

This is a bound for the actually supported law T2 against all independent
original-divisor phases. The comparison laws are only an intermediate
estimate, and no law is chosen after seeing a layout.

## An explicit result at every height K>=10

For a simple bound without a changing cutoff, use delta_K for j=0,1,2
and 5^-j for j>=3. Since sum_(j=0)^2(2j+1)=9 and
sum_(j=3)^infty(2j+1)5^-j=3/40, T6 yields

    Gamma_K(nu_K)
      <= 149/26+(135/13)(3/5)^(K-2)
                  +(24/13)(K+1)^2 3^-K.                (T7)

Therefore

    2t_K-Gamma_K(nu_K)
      >= 7/26-(135/13)(3/5)^(K-2)
         -[(24/13)(K+1)^2+2(K+2)]3^-K.                 (T8)

Each subtracted term strictly decreases for K>=10. For (K+1)^2 3^-K
its next/current ratio is (K+2)^2/[3(K+1)^2]<1; for (K+2)3^-K it is
(K+3)/[3(K+2)]<1. The geometric term has ratio 3/5.
At K=10 the exact T8 value is

    3623071823/39981093750 > 9/100.

Thus, for every integer K>=10, the fixed actual law T2 satisfies

    Gamma_K(nu_K) <= 2t_K-9/100.                         (T9)

The stronger changing-cutoff bound T6 has K=10 margin
27872286023/307546875000, but that improvement is unnecessary for T9.
The result is genuinely unbounded in height. This fixed law actually fails
at K=2: the literal original-divisor phases

    (a_1,a_5,a_7,a_35,a_49,a_245)=(0,2,3,17,3,52)

have actual squared-load expectation 10483/1755, exceeding 2t_2=46/9
by 1513/1755. This is failure of the fixed recipe, not of the source:
at K=2 the clean tails are monochromatic, and the source is the already
successful family of 412. [Exact separation](416-exact-independent-layout-tree-separation-and-actual-laws.md)
also proves that T2 fails at K=3,4. [Prefix-local transport](417-prefix-local-disagreement-extends-the-same-law-to-height-seven.md)
and the [finite completion](418-concentrated-sharp-sources-admit-a-common-law-at-every-height.md)
prove that T2 succeeds at every K>=5. Different actual laws close K=2,3,4.
Arbitrary one-surplus tails, the full sharp-minimum source class, and
unrestricted Erdős #7 remain unresolved here.

## Reproduction and scope

The independent-phase root maximum, exact threshold arithmetic, actual
finite source counts, same-Y coupling identities, and ideal root table
are checked by
[`concentrated_sharp_source_relabel_transport.py`](../../frontier/cover-geometry/concentrated_sharp_source_relabel_transport.py).
Its parameterized constructors provide `source(K)`, the actual full-five
and three pair laws, `common_law(K)`, and explicit same-Y couplings.
The generic coupling checker validates both marginals and all prefix
caps before returning the row-relabel shell bound. The program also
checks the K=2 literal failure witness and rejects named malformed
inputs. Runtime validation uses explicit exceptions and remains active
with `python3 -O`.

From the repository root, run:

    python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/concentrated_sharp_source_relabel_transport.py
    python3 -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/concentrated_sharp_source_relabel_transport.py

The general induction and all-height inequalities above are analytic,
not inferred from finitely many source enumerations.

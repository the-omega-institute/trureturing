[Index](../../marked_head_profile.md) · [Tree duality](375-deep-prime-prefix-projections-and-tree-contraction.md) · [Root laws](395-root-rectangle-blockers-need-no-standalone-projection-condition.md) · [Heavy-row laws](396-a-heavy-row-controls-all-seven-adic-depths.md)

# Stationary row mixtures control all seven-adic depths

Suppose a source is supported on the four nonzero 5-rows and the union of every
three rows contains a complete five-ary 7-tree of depth `K`. There
is one probability on the actual source whose full independent-divisor
second moment at modulus `5*7^K` is at most

\[
 U_K=4+4\sum_{j=2}^K(2j+1)5^{-j}
 \le 2\left(1+\sum_{j=1}^K(2j+1)3^{-j}\right).
 \tag{SM1}
\]

The comparison is equality at `K=1` and strict for `K>=2`. The
upper bounds increase to `51/10`, below the comparison limit `6`.
The selected trees and their row labels can differ and can vary with
every prefix. No repeated or Cartesian source structure is required.

The three-row premise is additional: this report does not derive it
from a five-ary tree in the full union, from pair-union ternary trees,
or from the known obstructions for a general odd-cover residual.
Pair-union hypotheses are not used in the result. These are ordinary
mathematical proofs and exact rational checks, not Lean certification.
Unrestricted Erdős #7 remains open.

## 1. Source and row-avoiding component laws

Fix `K>=1`, and write

\[
 R\subseteq\{1,2,3,4\}\times\mathbb Z/7^K,
 \qquad N_i=\{y:(i,y)\in R\}.
 \tag{SM2}
\]

Digits are read from lowest to highest. A complete five-ary tree of
depth `K` selects exactly five children at every selected nonleaf.
Assume that for each `i` the set

\[
 \bigcup_{r\ne i}N_r
 \tag{SM3}
\]

contains such a tree. Choose one of these trees for each `i` and
assign each selected leaf to one actual available row other than
`i`. Uniform weight `5^-K` on its labelled leaves gives a probability
`nu_i` on the actual source `R`. It has zero mass in row `i` and
satisfies, simultaneously for every prefix `u mod 7^j`,

\[
 \nu_i(C_u)\le5^{-j},\qquad
 C_u=\{(r,y)\in R:y\equiv u\pmod{7^j}\},
 \qquad 0\le j\le K.
 \tag{SM4}
\]

A selected depth-`j` node has exactly `5^(K-j)` selected descendants;
an unselected prefix has none. Assigning leaves to rows does not
change these plain-prefix masses. The four component trees need
not coincide.

More generally, the argument below only requires four actual
probabilities on `R`, each avoiding its indexed row and satisfying
SM4. The tree premise is a sufficient construction of those laws.

## 2. Stationarity produces a single common law

Define the row-stochastic matrix

\[
 M_{ir}=\nu_i(\text{row }r).
 \tag{SM5}
\]

Its diagonal is zero. A finite stochastic matrix has a stationary
probability `lambda`; irreducibility is not needed. For example,
Cesàro averages of successive distributions have a convergent
subsequence, and their difference after one matrix step tends to
zero. When the entries are rational, choosing a closed irreducible
communicating class and solving its normalized stationary equations
gives rational weights, extended by zero outside that class.

Take any such probability and set

\[
 \lambda M=\lambda,\qquad
 \nu=\sum_{i=1}^4\lambda_i\nu_i.
 \tag{SM6}
\]

Then `nu` is one probability on the actual source, and

\[
 \begin{aligned}
 \nu(\text{row }r)&=\lambda_r\le\tfrac12,\\
 \nu(C_u)&\le5^{-j},\\
 \nu(\text{row }r\cap C_u)&\le(1-\lambda_r)5^{-j}.
 \end{aligned}
 \tag{SM7}
\]

The first equality is stationarity. Since `M_rr=0` and `M_ir<=1`,
`lambda_r=sum_(i!=r) lambda_i M_ir<=1-lambda_r`, giving the half
bound. The plain-prefix inequality follows by averaging SM4. For
the joint inequality the component `nu_r` contributes zero, so
only coefficients of total mass `1-lambda_r` remain.

All three bounds hold under this same `nu`, at every prefix and
every required depth. No marginal optimizer is substituted for
another. Some stationary weights and some source-point masses may
be zero.

## 3. The entire independent root layout

At the first 7-digit write `w_rc` for the joint root masses, `R_r`
for the row masses, and `C_c` for the column masses under `nu`.
Include the absent 5-row zero with mass zero. SM7 gives

\[
 R_r\le\tfrac12,\quad C_c\le\tfrac15,\quad
 w_{rc}\le\frac{1-R_r}{5},\quad
 w_{rc}\le\min\left(R_r,\frac{1-R_r}{5}\right)\le\tfrac16.
 \tag{SM8}
\]

A complete root layout chooses a row `r`, a column `c`, and a point
`(s,d)` independently, for labels `5`, `7`, and `35`. Label `1`
contributes one. Put `R=R_r`, `C=C_c`, `x=w_rc`, `z=w_sd`.
Expanding the load square yields exactly

\[
 1+3R+3C+2x+
       \bigl(3+2\mathbf1_{r=s}+2\mathbf1_{c=d}\bigr)z.
 \tag{SM9}
\]

There are four cases; none imposes compatibility on the chosen phases.

1. **Same row and column.** Here `z=x<=(1-R)/5`, so SM9 is at most
   `17/5+(6/5)R<=4`.
2. **Same row, different columns.** Both `x,z<=(1-R)/5`; the two
   point coefficients sum to seven. Thus SM9 is at most
   `3+(8/5)R<=19/5`.
3. **Different rows, same column.** The two distinct cells satisfy
   `x+z<=C`. Consequently `2x+5z<=2C+3z`, and SM9 is at most
   `1+3R+5C+3z<=5/2+3R<=4`.
4. **Different rows and columns.** Use `x<=(1-R)/5` and `z<=1/6`
   to get `5/2+(13/5)R<=19/5`.

These inequalities also hold when an independently selected phase
has zero mass. Therefore the full root maximum is at most four.
The constant is attained by an actual source consisting of two
rows with the same five columns, with probability `1/10` on each
of its ten points. Every three-row union contains those five
columns, and this law is a stationary mixture of row-avoiding laws.

## 4. Original labels at every depth

CRT identifies SM2 with residues modulo `Q=5*7^K`. For independently
chosen residues at every original divisor, define

\[
 \Gamma_Q(\nu)=\max_{(a_d)_{d\mid Q}}
  \mathbb E_\nu\left(\sum_{d\mid Q}
                   \mathbf1_{x\equiv a_d\pmod d}\right)^2.
 \tag{SM10}
\]

Write `P_j` for the chosen `7^j`-event and `Q_j` for the chosen
`5*7^j`-event, `0<=j<=K`. Thus `P_0=1`, while `Q_0` selects a
row. Retain all ordered-pair terms with both depths at most one
as the single root square from SM9; their sum is at most four.

At each later LCM 7-depth `j>=2` there are exactly `2j+1` ordered
depth pairs `(a,b)` with `max(a,b)=j`. Each pair has four choices
of labels: `P_a P_b`, `P_a Q_b`, `Q_a P_b`, `Q_a Q_b`. A nonempty
congruence intersection is contained in one depth-`j` 7-prefix,
so SM7 bounds each term by `5^-j`. Incompatible intersections
contribute zero. Summing gives the first inequality in SM1.

Define

\[
 t_p(K)=1+\sum_{j=1}^K(2j+1)p^{-j}.
 \tag{SM11}
\]

Then `U_K=4t_5(K)-12/5`, while the exact comparison difference is

\[
 2t_3(K)-U_K
 =\sum_{j=2}^K(2j+1)\bigl(2\,3^{-j}-4\,5^{-j}\bigr).
 \tag{SM12}
\]

Every summand is positive, since `2(3/5)^j<=18/25<1` for `j>=2`.
Hence the comparison is equality at height one and strict at every
larger finite height. In particular,

\[
 U_2=\frac{24}{5},\qquad
 2t_3(2)-U_2=\frac{14}{45}.
 \tag{SM13}
\]

The geometric-series identity gives `t_5(infinity)=15/8` and
`t_3(infinity)=3`. Therefore

\[
 U_\infty=\frac{51}{10}<6,
 \qquad 6-U_\infty=\frac9{10}.
 \tag{SM14}
\]

The proof concerns every finite `K`; it does not infer the theorem
from checks over a finite range. Laws selected for different heights
are not asserted to form a projectively compatible process.

## 5. Exact checker and scope

The [stationary-mixture checker](../../frontier/cover-geometry/stationary_row_mixture_bound.py)
contains two reusable functions. `stationary_distribution` accepts
an exact rational zero-diagonal stochastic matrix of any order at
least two, chooses a closed communicating class, solves its rational
stationary equations, and verifies the answer against the original
matrix. Periodicity and reducibility are permitted.
`mix_row_avoiding_laws` accepts four probability dictionaries on
actual `(row,y)` coordinates and a height. It checks normalization,
row exclusions, and every prefix cap, constructs the stationary
mixture, and checks SM7 for that one resulting probability. A user
applying it to a specified source must supply dictionaries supported
on that source; the function uses their union as its source.

Its depth-two fixture has four different complete five-ary trees
with 25 leaves each, and varying assignments of leaves to the
available rows. Their union has 100 source points. The matrix is

\[
 \begin{pmatrix}
 0&7/25&9/25&9/25\\
 9/25&0&7/25&9/25\\
 9/25&9/25&0&7/25\\
 9/25&8/25&8/25&0
 \end{pmatrix},
 \tag{SM15}
\]

with stationary row masses

\[
 (9/34,\;448/1853,\;53/218,\;464/1853).
 \tag{SM16}
\]

Literal integration over all `5*7*5*7=1225` independent root
layouts gives exact maximum `279217/92650`. The fixture is a
control for the construction, not an optimizer or an actual odd
covering residual. A separate two-row fixture attains the root
constant four. Further controls check periodic and reducible
matrices, reject invalid matrices and component laws, and verify
SM12 at heights one through six and the infinite constants.
Every root layout also compares literal integration with SM9;
enumeration of 556 ordered original-label pairs across heights
one through six verifies the retained root block and the later
LCM multiplicities.
All arithmetic is rational and checks remain active under `-O`.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/stationary_row_mixture_bound.py
```

The new conclusion supplies a common probability for the stated
three-row tree class at every 7-depth while preserving arbitrary
independent residues at all original labels. It does not establish
that a general source admits those row-avoiding component laws,
does not cover higher powers of 5 or additional primes, and does
not settle existence or nonexistence of an unrestricted distinct
odd covering.

[Index](../../marked_head_profile.md) · [Joint source trees](376-complete-prime-chain-transport-and-joint-prefix-laws.md) · [Exact root classes](398-six-exact-root-types-control-arbitrary-seven-adic-tails.md) · [Larger supports](399-sparse-second-digits-control-sources-outside-fixed-subclasses.md)

# Literal layout mixtures, sharp source size, and exact tree-rank duality

At 5-height one, the universal supported-law problem has an exact dual
formulation with no source variable: maximize a tree order statistic of
one mixture of literal squared-layout costs. This formulation preserves
independent residues at every original divisor and the requirement that
one actual probability work against all layouts. It also yields a
constructive source certificate whenever the proposed bound is exceeded.

The same source class has sharp minimum cardinality `5^K+2` at every
7-height `K`, proved by a complementary-pair induction and attained by
a type-C construction. This determines the exact tree-rank maximum in
the affine simplex of layout mixtures constructed in section 8. The
general finite-height comparison for this four-row source class is
established by [report 427](427-shared-row-cap-mixtures-break-the-six-barrier.md)
and [report 429](429-phase-conflict-cap-flow-closes-the-height-two-bound.md),
together with the separate root comparison.

The order statistic cannot be averaged over layouts. Already at height
one, 28 actual layouts each have tree rank one, while their uniform
mixture has tree rank `5/2`. A separate exact transport criterion below
characterizes which pure and mixed tail marginals, together with their
coincidences, arise from one layout mixture. Local overlap bounds alone
are insufficient.

These are finite minimax and transport deductions and exact research
programs, not Lean-certified theorems. The later common-law bounds settle
`Gamma_(1,K)<=2t_K` on this source class; they do not supply the joint
transport through arbitrary five-adic heights and prime supports.
Unrestricted Erdős #7 remains open.

## 1. Source class and the original finite game

Fix `K>=1`, let `Y=Z/7^K`, and use the carrier

\[
 X=\{1,2,3,4\}\times Y.
 \tag{LD1}
\]

Seven-adic trees read the lowest digit first. Call a source `R subset X`
admissible when:

- for every pair `A` of the four rows, the projection of
  `R intersect (A x Y)` contains a complete ternary tree of depth `K`;
- the full `Y` projection contains a complete five-ary tree of depth `K`.

These are the pair and standalone conditions from report 376, after
omitting row zero. The definition permits three active rows; requiring
all four is a separate restriction addressed in section 4.

Put `Q=5*7^K`. A literal layout chooses one residue `a_d mod d`
independently for every `d|Q`, including divisor one. For the CRT point
`x=(r,y)` let

\[
 \ell_\lambda(x)=\sum_{d\mid Q}{\bf1}_{x\equiv a_d\pmod d},
 \qquad c_\lambda(x)=\ell_\lambda(x)^2.
 \tag{LD2}
\]

All five choices of the 5-coordinate are allowed in a phase, including
row zero. No compatibility between phases is imposed. Define

\[
 \Gamma(R)=\min_{\nu\in\Delta(R)}\max_\lambda
                  \sum_{x\in R}\nu_xc_\lambda(x),
 \qquad
 f_\theta(x)=\sum_\lambda\theta_\lambda c_\lambda(x),
 \tag{LD3}
\]

where `theta` is a probability on the finite set of layouts. Finite
minimax gives

\[
 \Gamma(R)=\max_\theta\min_{x\in R}f_\theta(x).
 \tag{LD4}
\]

The maximum on the right uses one whole-layout mixture. Replacing it by
unrelated pairwise phase distributions would change the game.

## 2. An order statistic replaces the source search

For a real function `g` on `Y`, define

\[
 U_b(g)=\max_{T\text{ complete }b\text{-ary}}\min_{y\in T}g(y).
 \tag{LD5}
\]

At a leaf the value is `g(y)`; at an internal node it is the `b`-th
largest of its seven child values. Induction proves this recursion and
constructs an attaining tree by keeping the `b` largest children and
recursing. Ties may be settled arbitrarily.

For `f:X -> R`, put

\[
 B(f)=\min\left\{
    \min_{|A|=2}U_3\left(y\mapsto\max_{r\in A}f(r,y)\right),
    U_5\left(y\mapsto\max_{1\le r\le4}f(r,y)\right)
                \right\}.
 \tag{LD6}
\]

Then, exactly,

\[
 \max_{R\text{ admissible}}\min_{x\in R}f(x)=B(f).
 \tag{LD7}
\]

For the upper bound let `m=min_R f`. Every pair-tree witness in `R`
is also a witness that the corresponding row maximum is at least `m`
on a complete ternary tree; the full five-tree gives the last term.
Thus each term in LD6 is at least `m`.

For the reverse bound use the actual superlevel source

\[
 R_f=\{x\in X:f(x)\ge B(f)\}.
 \tag{LD8}
\]

Every rank in LD6 is at least `B(f)`. Select an attaining tree for each
rank, and at each selected leaf choose a row attaining its row maximum.
All selected points lie in `R_f`, so it is admissible. The union of these
seven finite witness sets is itself an admissible subsource of `R_f`.
LD7 follows. Finiteness also gives the strict version

\[
 \{f>c\}\text{ is admissible}\quad\Longleftrightarrow\quad B(f)>c.
 \tag{LD9}
\]

Combining LD4 and LD7, and exchanging two maxima, yields

\[
 \boxed{\max_{R\text{ admissible}}\Gamma(R)
       =\max_\theta B(f_\theta).}
 \tag{LD10}
\]

All maxima attain. Thus the desired source theorem is equivalent to

\[
 B(f_\theta)\le 2t_K\quad\text{for every literal layout mixture},
 \qquad t_K=3-\frac{K+2}{3^K}.
 \tag{LD11}
\]

A rational mixture with `B(f_theta)>2t_K` would certify failure of this
abstract source theorem: its seven tree witnesses construct a source,
and LD4 certifies that every law on that source violates the bound.
It would not by itself realize that source as an actual residual of an
odd distinct covering. Conversely, testing finitely many mixtures below
the threshold does not prove LD11.

## 3. The equivalent low-cost tree alternative

Define the opposite bottleneck

\[
 L_b(g)=\min_{T\text{ complete }b\text{-ary}}\max_{y\in T}g(y).
 \tag{LD12}
\]

Its recursion takes the `b`-th smallest child value. Since the `b`-th
largest of seven numbers is their `(8-b)`-th smallest, induction gives

\[
 U_b(g)=L_{8-b}(g).
 \tag{LD13}
\]

Consequently `B(f)<=c` holds if and only if at least one of the following
actual rectangles has cost at most `c` at every point:

- `A x T`, where `A` is a fixed pair of rows and `T` is a complete
  five-ary tree;
- all four rows times a complete ternary tree.

The inequality is non-strict on these low-cost rectangles. On the
opposite side LD9 uses the strict superlevel set. No limiting or generic
position assumption is needed.

## 4. Exactly four active rows

If the source must meet each of the four rows, replace LD6 by

\[
 B_4(f)=\min\left\{B(f),\ \min_r\max_y f(r,y)\right\}.
 \tag{LD14}
\]

Every such source has minimum cost at most each row maximum. Conversely
`{f>=B_4(f)}` has all seven required tree witnesses and meets every row.
Thus LD7, LD9 and LD10 remain valid with `B_4` and exactly four active
rows. For the constructive subsource, add one maximizing point from
each row if the seven tree witnesses omit it.

The low-cost alternative for `B_4(f)<=c` gains a third branch: one entire
row has cost at most `c`. Omitting this branch would incorrectly identify
the exactly-four-row problem with the larger source class. Three-row
sources are already controlled by report 379, RF19, which gives
`Gamma_(1,K)<=2t_K` at 5-height one.

## 5. Deterministic layout bounds do not average

At `K=1`, for each `r in {1,2,3,4}` and `c in Z/7`, choose

\[
 a_5=r,\qquad a_7=c,\qquad a_{35}=(r,c)\text{ by CRT}.
 \tag{LD15}
\]

Writing `I_r` and `I_c` for the matching row and column indicators,

\[
 \ell=(1+I_r)(1+I_c),\qquad c_\lambda=(1+3I_r)(1+3I_c).
 \tag{LD16}
\]

Each of these 28 layouts has `B(c_lambda)=1`: a pair excluding row `r`
has cost one on six columns, and no cost is below one. The same is true
of `B_4`. But the uniform mixture of all 28 has, at every actual point,

\[
 f_\theta=\left(1+\frac34\right)\left(1+\frac37\right)=\frac52,
 \qquad B(f_\theta)=B_4(f_\theta)=\frac52.
 \tag{LD17}
\]

This is a counterexample to convexity inside the literal-layout class.
Proving a low-cost tree for each deterministic layout and then averaging
those conclusions is invalid. The bound four at height one is not
refuted; LD17 is strictly below it.

## 6. Exact coupling of the next two original labels

The following criterion retains dependence between the new pure and
mixed phases. It applies at any one-step extension from 7-height `K-1`
to `K`, conditioning on each complete old layout `z`. Let its mixture
mass be `alpha_z`, and write its old load at a lifted point as `A_z(r,y)`.
The two new phases have labels `7^K` and `5*7^K`.

For a fixed `z`, suppress that index. Let `q_y` be the mass whose new
pure phase is `y`, let `v_(r,y)` be the mass whose new mixed phase is
`(r,y)`, and let `h_(r,y)` be the mass where these phases coincide in
the 7-coordinate and the mixed row is `r`. Here `r` ranges over all
five rows `0,...,4`, even though costs are tested only on rows `1,...,4`.
Put

\[
 V_y=\sum_r v_{r,y},\qquad H_y=\sum_r h_{r,y},\qquad H=\sum_yH_y.
 \tag{LD18}
\]

These arrays arise from one nonnegative joint phase distribution of
mass `alpha` if and only if

\[
 \begin{gathered}
 q,v,h\ge0,\qquad \sum_yq_y=\sum_{r,y}v_{r,y}=\alpha,\\
 h_{r,y}\le v_{r,y},\qquad H_y\le q_y,\\
 q_y+V_y-2H_y\le\alpha-H\quad\text{for every }y.
 \end{gathered}
 \tag{LD19}
\]

To prove sufficiency, reserve the coincidences `h`, leaving supplies
`a_y=q_y-H_y`, demands `b_y=V_y-H_y`, and total `M=alpha-H`. Residual
transport may join any two different 7-residues and may never join a
residue to itself. The weighted Hall conditions for this complete
bipartite graph minus its diagonal are exactly

\[
 a_y+b_y\le M\quad\text{for every }y.
 \tag{LD20}
\]

Indeed a singleton left residue sees every right residue except itself;
a set containing two different left residues sees every right residue.
These exhaust the nontrivial cuts. Finite max-flow therefore supplies
an off-diagonal transport. Split each arriving demand fibre among its
five rows according to `v_(r,y)-h_(r,y)`; a zero-demand fibre receives
zero residual mass. Then restore `h`. Necessity is
the same forbidden-diagonal cut argument. When `M=0`, all residual
supplies and demands vanish and the construction consists only of `h`.
Rational inputs admit rational transport.

The actual squared-cost function is now the linear expression

\[
 f(r,y)=\sum_z\left[
  \alpha_zA_z(r,y)^2+
  (2A_z(r,y)+1)\bigl(q_z(y)+v_z(r,y)\bigr)+2h_z(r,y)
                      \right],\qquad r=1,2,3,4.
 \tag{LD21}
\]

This follows by expanding `(A+U+V)^2` with binary new indicators `U,V`.
Conversely every collection satisfying LD19 for each `z`, with
`sum_z alpha_z=1`, constructs a whole-layout mixture and hence exactly
LD21. The formula keeps the old/new correlation by conditioning on the
entire old layout. Conditioning only on separate old phase marginals
would require an additional joint-realizability proof.

Local Fréchet overlap bounds do not imply LD19. On two residues take
`q=V=(1/2,1/2)`, all mixed mass in row one, and coincidences
`h=(1/2,0)`. Each individual overlap lies between zero and `1/2`, but
the remaining half of both marginals sits at the same second residue
and cannot be transported off-diagonal. LD20 detects `1>1/2`.

At height two there are 1,225 old root layouts and 49 new 7-residues.
The original extension has `1225*49*245=14,706,125` complete layouts.
The conditional description uses `1225*(1+49+245+245)=661,500`
nonnegative scalar variables before eliminations. This is an exact
finite description, not a polynomial-time solution: the tree-rank
objective remains nonconvex, and old-layout counts grow with height.

## 7. Research programs and remaining inequality

The [layout-mixture certificate program](../../frontier/cover-geometry/prime_layout_mixture_certificate.py)
evaluates rational whole-layout mixtures and builds actual tree witnesses.
It accepts an exact JSON mixture and an optional rational threshold;
without arguments it checks literal phase independence, the nonconvexity
example, the strict threshold boundary, and a three-row mixture for which
`B=20/7` but `B_4=10/7`. Its 14 malformed-input controls reject inexact
weights, invalid phases and incomplete carriers.

The [tail-coupling constructor](../../frontier/cover-geometry/joint_tail_coupling.py)
constructs or rejects rational tail couplings. Its finite controls compare
5,613 marginal/diagonal arrays with independently enumerated integer joint
tables, reconstruct all 1,692 feasible arrays, and check LD21 against a
literal height-two mixture on all 245 CRT cells, including row zero.
Ten malformed-input controls reject invalid dimensions and inexact masses;
integer-only inputs are normalized to exact fractions before construction.

They use the Python standard library and keep validation active under
`-O`. Their certificates concern the finite mathematical objects above;
no numerical optimizer result is accepted as an exact certificate.

The remaining inequality is LD11, or its exactly-four-row form using
LD14. The recursive tree ranks and the linear coupling cuts preserve
information that scalar row or column caps discard. Neither identity
alone bounds the rank by `2t_K`. Even a proof of that bound would still
need the other heights and source-realization arguments required by the
unrestricted covering problem.

## 8. Arbitrary superlevel geometry exists below the target scale

Literal layout costs impose quantitative constraints, but their origin
alone does not force a strict superlevel source into a more restricted
geometric class. In fact their convex hull contains the following
full-dimensional simplex. This construction is valid also for `K=0`.

For any nonnegative subprobability `p` on `X`, with `sum_x p(x)<=1`,
there is a literal layout mixture whose cost at every actual point is

\[
 f(x)=A_K+C_Kp(x),
 \quad
 A_K=\sum_{j=0}^K\frac{2j+1}{7^j},
 \quad
 C_K=1+2\sum_{j=0}^K7^{-j}.
 \tag{LD22}
\]

To construct it, choose `T` uniformly in `Z/7^K`. For every pure label
`7^j`, take phase `T mod 7^j`. Set every mixed label `5*7^j` with `j<K`
to row zero. Independently choose the deepest mixed phase at an actual
point with distribution `p`, and place its remaining mass at any
row-zero point. All choices are valid independent-label layouts;
using compatible pure phases in this particular mixture imposes no
restriction on the layout set tested in LD3.

At an actual point `(r,y)`, the shallow mixed indicators vanish. Write

\[
 P_T(y)=\sum_{j=0}^K{\bf1}_{y\equiv T\pmod{7^j}}.
 \tag{LD23}
\]

The deepest mixed indicator `J` is independent of `T`, with mean
`p(r,y)`. There are `2j+1` ordered exponent pairs with maximum `j`, so
`E P_T^2=A_K`, while `E P_T=sum_j 7^(-j)`. Expanding `(P_T+J)^2`
proves LD22, including the contribution of divisor one.

The closed forms and the total increment budget are

\[
 A_K=\frac{14}{9}-\frac{3K+5}{9\,7^K},\qquad
 C_K=\frac{10}{3}-\frac1{3\,7^K},\qquad
 \sum_{x\in X}\bigl(f(x)-A_K\bigr)\le C_K.
 \tag{LD24}
\]

Choosing `p=0` or a point mass gives the `|X|+1` vertices
`A_K 1` and `A_K 1+C_K e_x`. They are affinely independent. Thus no
nonzero polynomial in the `|X|` point-cost coordinates can vanish on
all literal layout mixtures: it would vanish on the nonempty interior
of this simplex. This statement concerns identities, not inequalities;
the budget in LD24 remains essential.

For any nonempty `R subset X`, use `p=1_R/|R|`. Every threshold strictly
between `A_K` and `A_K+C_K/|R|` has strict superlevel set exactly `R`.
In particular, take the 28-point source from report 399 at `K=2`.
Then

\[
 f_{\rm outside}=\frac{75}{49}
 <\frac85
 <\frac{2263}{1372}=f_{\rm inside},
 \qquad B(f)=B_4(f)=\frac{2263}{1372}.
 \tag{LD25}
\]

The gaps around `8/5` are `17/245` and `339/6860`. This is an actual
layout-mixture superlevel source satisfying all seven tree conditions
but containing no same-height literal-prefix subsource from reports
396, 397 or 398, by the source audit in report 399. It refutes a
threshold-independent extension of those geometric classifications to
all actual-mixture superlevels. It does not exclude conditioning and
reslicing, already distinguished in report 399.

The [affine-simplex constructor](../../frontier/cover-geometry/layout_mixture_affine_simplex.py)
returns the literal phases and rational probabilities in LD22. Its
controls recompute the squared loads directly, reuse the existing
28-point fixture and source audit, and verify the strict superlevel
identity in LD25 without copying the fixture into a second data source.

The displayed source has cost below `46/9`, and even the entire simplex
at `K=2` lies below that threshold pointwise:
`A_2+C_2=34/7<46/9`. More generally its maximum possible point cost is
`A_K+C_K<44/9`, below the target at every `K>=2`. At `K=1`, the
superlevel source LD8 needs at least five points, so LD24 gives
`B(f)<=A_1+C_1/5=73/35<4`. Thus this construction supplies no
high-threshold counterexample to LD11. A stronger classification at the target scale
would have to use its numerical cost threshold or another quantitative
constraint, rather than the bare fact that costs come from literal
layout mixtures.

## 9. The sharp minimum source size is \(5^K+2\)

For every `K>=0`, with depth-zero trees interpreted as one leaf,

\[
 \min_{R\text{ admissible at height }K}|R|=5^K+2.
 \tag{LD26}
\]

For exactly four active rows the same minimum holds when `K>=1`;
at `K=0` the minimum is four. Thus the first minima in the full
admissible class are `3,7,27,127,627,...`.

Here is a counting proof by induction. At height zero, at most two
row points leave a pair of rows empty. For positive height choose a
complete five-ary projection tree `T` inside the source. Call a chosen
child **clean** when its source consists of exactly one row-labelled
point above each leaf of the corresponding five-ary tail tree and no
other points in that child.

In a clean child, fix any partition of the four rows into two pairs.
The pair projections partition the leaves of its five-ary tail tree.
Exactly one of them contains a complete ternary tree. This is the
three-versus-three complement duality on a five-ary tree: two such
ternary trees must intersect, and a subset missing one has a ternary
tree in its complement, by the same child-order-statistic induction
as LD13 with five children.

Suppose now that `|R|<=5^K+1`. The chosen full tree accounts for at
least `5^K` points, leaving at most one extra point.

- With no extra point, all five selected children are clean. For a
  fixed complementary pair of row pairs they provide only five good
  child incidences in total. Both root ternary trees require six.
- If the extra point is inside one selected child, the other four
  children are clean. For every complementary row pairing they
  contribute four incidences. To reach six, the exceptional child
  must be good for both members. Hence that same child satisfies
  all six pair-tree conditions and the full five-tree condition,
  yet has at most `5^(K-1)+1` points, contradicting induction.
- If the extra point is outside the five selected children and
  `K>=2`, its singleton child cannot support a ternary tree of
  depth `K-1`. Again only five good incidences are available.
  If `K=1`, all six row-pair counts would have to be at least three
  among at most six points. Complementary pair counts force the
  total to be six and every pair sum to be three, which would make
  all four integer row counts equal to `3/2`. This is impossible.

These cases also cover an extra point outside `T` but inside a
selected child: it belongs to the second case. They prove the lower
bound in LD26, without assuming four active rows.

For sharpness at `K>=1`, use the type-C root pattern from report 398.
Set `h=K-1`, take root columns `a,b,c,d,e=0,1,2,3,4`, and let `F` be
the full five-ary tail tree with digits in `{0,1,2,3,4}`. Give each
private cell `(1,a),(3,d),(4,e)` all of `F`. Within `F`, the two
ternary trees

\[
 T_{\rm left}=\{0,1,2\}^h,\qquad
 T_{\rm right}=\{2,3,4\}^h
 \tag{LD27}
\]

intersect in the unique all-two leaf. In column `b`, give row 2 the
tails `(F minus T_right) union T_left` and row 3 the tails `T_right`.
In column `c` use the same two sets for rows 2 and 4. Each shared
column projects onto all of `F`, each incident row contains a
ternary tail tree, and exactly one tail point is duplicated between
its two rows. Their row-set sizes are `5^h-3^h+1` and `3^h`; they are
not asserted to both have size `3^h`.

The six row pairs therefore have `3,3,3,3,3,4` good root columns,
and the full projection has all five. The point count is
`3*5^h+2*(5^h+1)=5^K+2`. The construction uses all four rows, including
at `h=0`. At `K=0` separately choose three row points. This establishes
both the bound and its stated sharpness scopes.

As a consequence, the precise maximum within the affine simplex
LD22 is, for every `K>=1`,

\[
 \max_{p\ge0,\,\sum p\le1}B(A_K\mathbf1+C_Kp)
 =\max_{p\ge0,\,\sum p\le1}B_4(A_K\mathbf1+C_Kp)
 =A_K+\frac{C_K}{5^K+2}.
 \tag{LD28}
\]

LD8 constructs an admissible source of at least `5^K+2` points with
cost at least `B`. Summing their increments and using LD24 gives
`(5^K+2)*(B-A_K)<=C_K`. Uniform `p` on the sharp source attains
equality, including the four-active-row requirement. At height two,
this maximum is `2188/1323`; at height zero the two maxima are
respectively `2` and `7/4`.

The affine-simplex program constructs the actual sharp sources and
checks their seven tree conditions through height five. It directly
checks the 27-point source's literal mixture and rank at height two.
It also checks the local row-count obstruction at total mass five
and six. These finite checks support the implementation; the induction
above, rather than an enumeration cutoff, proves all heights.
LD28 optimizes only the simplex LD22. It is not an upper bound on the
full layout-mixture maximum in LD10.

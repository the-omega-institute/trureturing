# Rectangular overlap and all-height budgets

Sections 11–13 of [Complete event laws and first-hit costs](43-sharp-first-hit-ambiguity-with-identical-complete-event-laws.md), following [Stationary pair-label bounds](45-stationary-pair-label-bounds.md).

## 11. Rectangular overlap gives a sharp square-count bound

This is an independent ordinary mathematical result, not a Lean certificate.
It does not modify the separate three-label count argument. No oddness,
prime-power geometry, or distinct-cofactor hypothesis is needed for the
theorem below.

### 11.1. Statement and necessary nondegeneracy

Let `X,Y` be finite sets, and let there be `n >= 1` colors. Color `c` has
`N_c` original rectangular labels

\[
 R_{c,i}=A_{c,i}\times B_{c,i}\subseteq X\times Y,
 \qquad 1\le i\le N_c.
\]

Rectangles may overlap, including rectangles of the same color. Write

\[
 U_c=\bigcup_i R_{c,i},\qquad L=\sum_c N_c,
 \qquad K=\max_{(x,y)\in X\times Y}
          \#\{c:(x,y)\in U_c\}.
 \tag{FA63}
\]

Thus `K` counts colors at a point, not the number of labels there.

Let `W:X x Y -> [0,infinity)` be a common nonnegative weight, and define

\[
 M_c(x,y)=W(x,y)\mathbf1_{U_c}(x,y).
\]

Assume that the row marginals of `M_c` are the same for every color,
and that their column marginals are also the same for every color:

\[
 \sum_y M_c(x,y)=a'_x\quad\text{for every }c,x,
 \qquad
 \sum_x M_c(x,y)=b'_y\quad\text{for every }c,y.
 \tag{FA64}
\]

Require the common total mass to be strictly positive:

\[
 m:=\sum_xa'_x=\sum_yb'_y>0.
 \tag{FA65}
\]

In particular, `K >= 1`. Strict positivity of `W` on the nonempty union
of the color supports is sufficient for (FA65), but is stronger than what
this theorem requires.

Let `L_eff` be the number of original labels whose rectangles have positive
total `W` mass. Then

\[
 \boxed{L\ge L_{\mathrm{eff}}
       \ge\left\lceil\frac{n^2}{K}\right\rceil.}
 \tag{FA66}
\]

The conclusion concerns the number of original rectangles. Zero-mass,
empty, or redundant labels need not be removed from that count; retaining
them only weakens the resulting lower bound.

The positive-mass hypothesis is essential. For example, let `n>=2`, take
`X={1,...,n}`, let `Y` have one point, give color `c` the one rectangle
`{c} x Y`, and put `W=0` everywhere. All color marginals are zero, but
`L=n,K=1`, which would violate `L>=n^2`. There is no normalization in
this zero-common-mass case.

### 11.2. Normalize once and remove only zero marginal coordinates

By (FA64), every color has the same total mass `m`. Keep the original
definition of `M_c`; its normalized matrix is `M_c/m`. These normalized
matrices have row and column marginals

\[
 a_x=a'_x/m,\qquad b_y=b'_y/m,
 \qquad\sum_xa_x=\sum_yb_y=1.
\]

Let `X_+ = {x:a_x>0}` and `Y_+ = {y:b_y>0}`. Nonnegativity implies that
every normalized matrix `M_c/m` vanishes outside `X_+ x Y_+`. Restrict to these
sets. Each original rectangle restricts to the rectangle
`(A_{c,i} intersect X_+) x (B_{c,i} intersect Y_+)`; no new labels are
created. The original value of `K` remains an upper bound on color
multiplicity in the restricted grid. Alternatively, a stronger bound
uses the geometric maximum of `1_{U_c}` over the full product
`X_+ x Y_+`. It still includes its zero-`W` cells.

For the rest of the proof, use these restricted index sets, so every
`a_x,b_y` is strictly positive. The original counts `N_c,L` remain the
counts used in (FA66).

### 11.3. Split each color among its original rectangles

For each color, split its normalized matrix into nonnegative matrices
supported by the individual original rectangles:

\[
 M_c/m=\sum_{i=1}^{N_c}F_{c,i},\qquad
 \operatorname{supp}(F_{c,i})\subseteq R_{c,i}.
 \tag{FA67}
\]

Such a split always exists, even with same-color overlap. For example,
at a point in `U_c`, divide the normalized mass equally among all labels
of color `c` whose rectangles contain that point; use zero elsewhere.
This partitions mass, not necessarily the support into rectangles.

For each `F=F_{c,i}`, write its row sums as `r_x`, column sums as `s_y`,
and total mass as `m_i`. If `m_i=0`, then `F=0`; assign its replacement
matrix to be zero and perform no division. If `m_i>0`, define

\[
 G_{c,i}(x,y)=\frac{r_xs_y}{m_i}.
 \tag{FA68}
\]

This is a nonnegative rank-one matrix with exactly the same row and
column sums as `F`. Moreover, it is still supported inside the same
original rectangle. Indeed, `r_x>0` implies `x in A_{c,i}`, and `s_y>0`
implies `y in B_{c,i}`, so their Cartesian product lies in `R_{c,i}`.

Define

\[
 T_c=\sum_iG_{c,i}.
 \tag{FA69}
\]

Then each `T_c` has the common normalized row and column marginals
`a,b`, is supported inside `U_c`, and satisfies

\[
 \operatorname{rank}(T_c)
 \le\#\{i:m_i>0\}=N_c^{\mathrm{eff}}\le N_c.
 \tag{FA70}
\]

Here the equality with the original effective-label count uses the
equal-sharing split specified after (FA67): a component has positive mass
exactly when its original rectangle has positive `W` mass. Thus the
rank bound counts original labels without adding new rectangles.

The replacement may fill holes in `F_{c,i}` or cells where the original
`W` was zero. It does not leave the original rectangle. It is an
auxiliary matrix construction, not a claim that the original joint law
or an actual clipping history is unchanged or realizes `T_c`.

### 11.4. Whitened couplings are contractions

Let `D_a,D_b` be the positive diagonal matrices with entries `a_x,b_y`,
and put

\[
 A_c=D_a^{-1/2}T_cD_b^{-1/2}.
 \tag{FA71}
\]

The row and column marginal identities give

\[
 A_c\sqrt b=\sqrt a,\qquad A_c^{\mathsf T}\sqrt a=\sqrt b,
 \qquad \|\sqrt a\|_2=\|\sqrt b\|_2=1.
 \tag{FA72}
\]

For every real vector `v` on `Y_+`, weighted Cauchy–Schwarz in each row
gives

\[
 \begin{aligned}
 \|A_cv\|_2^2
 &=\sum_x\frac1{a_x}
       \left(\sum_yT_c(x,y)\frac{v_y}{\sqrt{b_y}}\right)^2\\
 &\le\sum_x\sum_yT_c(x,y)\frac{v_y^2}{b_y}\\
 &=\sum_yv_y^2.
 \end{aligned}
 \tag{FA73}
\]

Thus `||A_c||op <= 1`. Every nonzero singular value of `A_c` is at most
one. Invertible diagonal multiplication preserves rank, so its squared
Frobenius, or Hilbert–Schmidt, norm satisfies

\[
 \|A_c\|_{\mathrm{HS}}^2
 \le\operatorname{rank}(A_c)
 =\operatorname{rank}(T_c)
 \le N_c^{\mathrm{eff}}.
 \tag{FA74}
\]

### 11.5. Summing the colors uses the overlap cap

Let `A = sum_c A_c`. Equation (FA72) yields

\[
 A\sqrt b=n\sqrt a,
 \qquad \|A\|_{\mathrm{HS}}^2\ge n^2.
 \tag{FA75}
\]

At each matrix entry, at most `K` colors have a nonzero entry in `A_c`,
because `T_c` remains supported inside `U_c`, and the diagonal factors
in (FA71) do not enlarge support. Pointwise Cauchy–Schwarz therefore gives

\[
 \left(\sum_c A_c(x,y)\right)^2
 \le K\sum_c A_c(x,y)^2.
\]

Summing over the grid and applying (FA74),

\[
 n^2\le\left\|\sum_c A_c\right\|_{\mathrm{HS}}^2
 \le K\sum_c\|A_c\|_{\mathrm{HS}}^2
 \le K\sum_cN_c^{\mathrm{eff}}=K L_{\mathrm{eff}}.
 \tag{FA76}
\]

Since `L_eff` is an integer and `L>=L_eff`, this proves (FA66).

The value `K` in this argument is the geometric color multiplicity of
the unions in (FA63). If `W` has zero cells, it must not silently be replaced
by a smaller multiplicity measured only where the original weighted
matrices are positive: rank-one replacement can fill such zero cells
inside an original rectangle. The geometric `K` remains valid there.

### 11.6. Application to clipped-source pair balance

In the clipped-source model with an old law `rho` and threshold
`delta(x,y)`, the common actual weight is

\[
 W(x,y)=\rho(x,y)\frac{u(x,y)}{k(x,y)}
 \quad(k(x,y)>0),\qquad W(x,y)=0\quad(k(x,y)=0).
\]

Both full old–current pair marginals being product with the uniform
current law is exactly the common-row/common-column condition (FA64) for
`M_c=W 1_{U_c}`. Provided their common total mass is positive, (FA66)
therefore applies to the original rectangular labels. Unlike the
separate three-label geometric theorem, this argument does not require
`rho` to be positive on the full Cartesian carrier: additional holes
are allowed, subject to (FA64)--(FA65) and the geometric definition of `K`.
No claim of physical reachability for the auxiliary matrices `T_c` is
needed. This finite uniform-color application is not a conclusion for
arbitrary current heights or for the global covering problem.

In particular, if at most one bad color occurs at each old history in
the full geometric carrier, including zero-`rho` cells, then `K=1` and

\[
 L\ge n^2.
 \tag{FA77}
\]

Same-color overlapping labels are still allowed by this conclusion:
`K=1` counts colors, and the splitting step in Section 11.3 handles their
possibly multiple labels.

### 11.7. Sharpness at `K=1` with an allowed history-dependent policy

Abstractly, take an `n x n` grid, one singleton rectangle per cell, and
color it by a Latin square. With constant positive `W`, each color has
the same row and column marginals, `K=1`, and exactly `n^2` rectangles
occur. Hence (FA77) is sharp for the general rectangular theorem.

The same bound is attained within the positive-depth distinct-cofactor
arithmetic class when history-dependent thresholds are allowed, as in
the Latin construction of Section 8. Here
is an explicit realization of that mechanism.

Let `r<s<p` be odd primes and `n=p-1`, with old heights at least `n`.
Choose disjoint old cylinders `C_i` of depths `i`, for `1 <= i <= n`,
using residues

\[
 c_i=\frac{r^{i-1}+1}{2}\pmod{r^i},
\]

and cylinders `D_j` of depths `j` by the same formula with `s`. These
residues are nonzero modulo the corresponding prime. For `i<j`, the
`r`-adic valuation of `c_j-c_i` is exactly `i-1`, so the `C_i` are
pairwise disjoint; the `D_j` are likewise disjoint. Let their uniform
pure-survivor masses be

\[
 \sigma_i=\frac{r^{1-i}}{r-1},\qquad
 \tau_j=\frac{s^{1-j}}{s-1}.
\]

Use one original label `C_i x D_j` per cell and assign its current
color using any Latin square of order `n`, for example
`1 + ((i+j-2) mod n)`. The original moduli are `r^i s^j p`, all distinct.
Every active old history has exactly one bad color.

Choose a constant

\[
 0<\varepsilon<\frac{\min_{i,j}\sigma_i\tau_j}{n-1},
\]

and set, on the old cell `C_i x D_j`,

\[
 u_{ij}=\frac\varepsilon{\sigma_i\tau_j},\qquad
 \delta(x,y)=\frac{u_{ij}}{1+u_{ij}}<\frac1n.
 \tag{FA78}
\]

Assign any threshold in `(0,1)` outside the active cells. With a uniform
pure-product incoming old law, the actual clipped weight on an active
cell is `W=rho u_{ij}`, because `k=1`. Every cell has total `W` mass
`epsilon`.

More precisely, at each `x in C_i`, each color occurs in exactly one
column cell, and its row-weight sum is

\[
 \nu_r(\{x\})\tau_j u_{ij}
 =\nu_r(\{x\})\frac\varepsilon{\sigma_i},
\]

independent of that color. The column identity is symmetric. Outside
the active projections all these sums are zero. Thus both actual full
pair marginals are product, `K=1`, and `L=n^2` attains (FA77).

This establishes sharpness using a history-dependent threshold. It is
not a fixed-threshold attainability claim. The construction and the
rank bound are ordinary mathematics here; no Lean certification or
literature-priority claim is made.

### 11.8. A counterexample to measuring overlap only on positive-weight cells

For any `n>=3`, take `X=Y={0,1}^n` and define

\[
 U_c=\{(x,y):x_c=y_c\},\qquad 1\le c\le n.
\]

Each color has two original rectangles: both bits at coordinate `c`
are zero, or both are one. Thus `L=L_eff=2n`.

Put `W(x,y)=1` when `x,y` agree at exactly one coordinate, and zero
otherwise. For each fixed `x` and each color `c`, there is exactly one
such `y` belonging to `U_c`: keep coordinate `c` and complement every
other coordinate. The column statement is identical. Consequently
every `M_c=W 1_{U_c}` has row and column sums all equal to one and total
mass `2^n`. Each of its two original rectangles has positive mass
`2^(n-1)`.

Every positive-`W` point belongs to exactly one color, so a multiplicity
measured only there would give `K_support=1`. The resulting claimed bound
`L>=n^2` would be false, since `L=2n<n^2`. The geometric multiplicity is
instead `K=n`, attained when `x=y`, and the actual theorem is consistent.
All common row and column marginals are positive, so merely deleting
zero marginal rows and columns does not eliminate these interior holes.

For `n=3`, the carrier is an `8 x 8` grid, there are `24` positive-weight
cells and `6` effective rectangles, and each color has total mass `8`.
This example belongs to the general rectangle theorem; no claim is made
that it is a distinct-prime-prefix arithmetic source or is reachable
through a prescribed clipping history.

## 12. A quantitative rectangular certificate for actual pair-balance defects

This is an ordinary finite-dimensional mathematical derivation, without a
Lean certification or literature-priority claim. Its auxiliary matrices do
not replace the actual arithmetic source, preparation, or clipped law.

### 12.1. Finite geometric data

Let X and Y be finite nonempty sets and let c range over n >= 1 colors.
Each color has N_c original rectangles R_i x S_i; their union is U_c.
Let L = sum_c N_c and let

    K = max_{(x,y) in X x Y} #{c : (x,y) in U_c}.

This maximum is over the full geometric carrier, including points having
zero actual probability. Rectangles may overlap within and between colors.
No distinctness of shapes, arithmetic assumptions, or full-support source
is needed for the matrix result.

Let W >= 0 be any finite common weight on X x Y. Put

    M_c = W 1_{U_c},  H = sum_c M_c,  T = sum_{x,y} H(x,y).

Assume T > 0. Let r_c,s_c be the row and column sums of M_c. Define

    m = T/n,  a = H_X/T,  b = H_Y/T,
    e_X = (1/2) sum_c ||r_c - m a||_1,
    e_Y = (1/2) sum_c ||s_c - m b||_1.

Thus a,b are probability vectors. Individual colors may have zero mass;
their total masses need not equal m. The conclusion is

\[
 e_X+e_Y\ge T\left(1-\frac{\sqrt{KL}}n\right)_+.
 \tag{FA79}
\]

Here t_+ = max(t,0). T > 0 forces K,L > 0. When T = 0, all weights vanish
on all color supports and the defect is zero; no nontrivial count follows.

### 12.2. Trimming without increasing any geometric support

For one color write t_c = sum M_c and

    D_Xc = ||r_c - m a||_1,  D_Yc = ||s_c - m b||_1.

Scale each row of M_c down, if necessary, until its sum is at most m a(x).
The removed mass is exactly

    E_Xc = sum_x (r_c(x)-m a(x))_+
         = (D_Xc + t_c - m)/2.

Next scale columns down until their sums are at most m b(y). The columns
after row trimming are bounded by the original s_c, so this removes at
most

    E_Yc = sum_y (s_c(y)-m b(y))_+
         = (D_Yc + t_c - m)/2.

Call the resulting nonnegative matrix M'_c. Row bounds remain valid after
column trimming. Its mass satisfies

\[
 \sum M'_c\ge t_c-E_{Xc}-E_{Yc}
 =m-\frac{D_{Xc}+D_{Yc}}2.
 \tag{FA80}
\]

The right side can be negative; the lower bound is still valid. Summing
over all colors gives

\[
 \sum_c\sum M'_c\ge T-e_X-e_Y.
 \tag{FA81}
\]

All trimming occurs within the original support; it is a proof operation,
not an asserted implementation of a physical clipping stage.

### 12.3. Rectangular replacement preserving the trimmed marginals

For each color distribute every entry of M'_c among the original rectangles
of that color containing the entry, for example equally. This produces
nonnegative matrices F_i, each supported on its own R_i x S_i, with
sum_{i of color c} F_i = M'_c. A zero F_i is discarded.

For a remaining F_i with positive mass t_i and row and column sums f_i,g_i,
replace it by

    Q_i(x,y) = f_i(x) g_i(y) / t_i.

This matrix has rank one, the same two marginals as F_i, and support inside
the same original rectangle. Let B_c = sum_{i of color c} Q_i. Then B_c
has the same mass and marginals as M'_c, rank at most N_c, and support
inside U_c. The replacement may fill a zero-probability point; this is why
K must count full geometric support rather than only points where W > 0.

### 12.4. One common normalization and the norm bound

Delete the zero entries of a and b when forming inverse diagonal matrices;
the corresponding rows and columns of every B_c are zero. Equivalently,
extend all normalized matrices by zero on those coordinates. Set

    A_c = D_a^(-1/2) B_c D_b^(-1/2).

For any vectors f,g, weighted Cauchy--Schwarz and the marginal caps give

    |f^T A_c g|
      <= [sum_x (B_c)_X(x) f(x)^2/a(x)]^(1/2)
         [sum_y (B_c)_Y(y) g(y)^2/b(y)]^(1/2)
      <= m ||f||_2 ||g||_2.

Consequently ||A_c||_op <= m, rank A_c <= N_c, and

\[
 \|A_c\|_{\mathrm{HS}}^2\le m^2N_c.
 \tag{FA82}
\]

At each entry, at most K different colors are nonzero. Entrywise
Cauchy--Schwarz and (FA82) imply

\[
 \left\|\sum_c A_c\right\|_{\mathrm{HS}}^2
 \le K\sum_c\|A_c\|_{\mathrm{HS}}^2
 \le Km^2L.
 \tag{FA83}
\]

The vectors sqrt(a),sqrt(b) have Euclidean norm one and

    sqrt(a)^T (sum_c A_c) sqrt(b) = sum_c sum B_c
                                  >= T-e_X-e_Y.

Its left side is at most ||sum_c A_c||_op, hence at most its Hilbert--Schmidt
norm. Therefore T-e_X-e_Y <= (T/n) sqrt(KL), proving (FA79).

### 12.5. Exact-balance and weighted consequences

If e_X=e_Y=0 and T>0, then L >= ceil(n^2/K). This proof permits holes in W
and in the actual incoming source. It counts geometric color overlap.

There is also a stronger exact-balance profile inequality. Every color
then has mass m>0 and the same normalized marginals a,b. Apply the same
rectangle replacement without trimming and divide A_c by m to get matrices
C_c with operator norm at most one, rank at most N_c, and

    C_c sqrt(b) = sqrt(a).

For any nonnegative numbers v_c, the same entrywise estimate gives

\[
 \left(\sum_c v_c\right)^2\le K\sum_c v_c^2N_c.
 \tag{FA84}
\]

Every N_c is positive. Taking v_c=1/N_c yields

\[
 \sum_c\frac1{N_c}\le K.
 \tag{FA85}
\]

Cauchy--Schwarz, n^2 <= (sum_c N_c)(sum_c 1/N_c), recovers the label-count
bound. Applying the argument to any nonempty subset of colors gives the
corresponding bound with that subset's own geometric overlap. These are
necessary conditions, not claims that arbitrary count profiles occur.

### 12.6. Connection to the actual height-one clipped law

Let rho be any incoming probability on X x Y, possibly correlated and
with holes, and let the fresh current color be independent uniform on n
colors. For the original color unions U_c put k=sum_c 1_{U_c}. Given any
history-dependent delta(x,y) in (0,1), set

    u = min(k/n,delta)/(1-min(k/n,delta)),  w=u/k   if k>0,
    u=w=0                                                  if k=0.

The actual normalized clipped law is

    mu(x,y,c) = rho(x,y)/n [1+u(x,y)-n w(x,y)1_{U_c}(x,y)].

Choose W=rho w above. Then H=rho u, T=E_rho[u], and direct summation gives

    mu_XC(x,c) - rho_X(x)/n = H_X(x)/n - r_c(x),
    mu_YC(y,c) - rho_Y(y)/n = H_Y(y)/n - s_c(y).

Hence e_X and e_Y are exactly the total-variation distances

    e_X = TV(mu_XC, rho_X x uniform_n),
    e_Y = TV(mu_YC, rho_Y x uniform_n).

Equation (FA79) therefore controls the actual pair defects on the same
incoming source and same clipping operation:

\[
 \operatorname{TV}(\mu_{XC},\rho_X\otimes\operatorname{Unif}_n)
 +\operatorname{TV}(\mu_{YC},\rho_Y\otimes\operatorname{Unif}_n)
 \ge\mathbb E_\rho[u]\left(1-\frac{\sqrt{KL}}n\right)_+.
 \tag{FA86}
\]

The mass T is a specified clipping-activity weight. It is not asserted to
be first-hit loss, uncovered mass, or a new total-loss budget. The bound is
nonzero only when KL<n^2 and T>0. Arbitrarily many original labels can make
the right side zero. Thus (FA86) does not settle an unrestricted odd covering,
does not give a future-loss saving, and does not erase tail obligations.
On a fixed finite carrier, thresholds tending uniformly to zero also make
T tend to zero. Consequently this is not a positive defect bound uniform
over every allowed threshold.

For K=1, exact pair balance requires n^2 labels. The earlier Section 8
Latin construction attains n^2 in the height-one, history-dependent
threshold class. In particular n=6 requires and admits 36 mixed labels
(plus the three separate pure labels in that arithmetic construction).
This is not an attainment statement for constant thresholds.

## 13. Full current heights retain an original-label overlap budget

This is an application of the finite rectangular defect theorem, not a
claim of a new matrix theorem, a Lean certificate, or a resolution of
unrestricted Erdos #7. Expanding a current prefix into fine leaves is an
auxiliary counting operation. The original arithmetic moduli and residues
remain unchanged, and each original label is charged exactly once with
the weight specified below.

### 13.1. Finite interface with literal current subsets

Let X,Y,Z be finite nonempty sets, with |Z|=n and uniform law nu on Z.
The incoming old law rho on X x Y is any probability, including correlated
laws and laws with zero-mass holes. The current coordinate is fresh and
independent, with incoming joint law rho x nu.

Each original label i specifies

    A_i x B_i x J_i,  A_i subset X, B_i subset Y, J_i subset Z.

There is no assumption that the J_i form a partition or are disjoint.
Empty old rectangles or empty J_i can be omitted. The bad current set at
an old history, its current mass, and its geometric maximum are

    B(x,y) = union_{i : x in A_i, y in B_i} J_i,
    alpha(x,y) = nu(B(x,y)),
    alpha_* = max_{(x,y) in X x Y} alpha(x,y).

The maximum includes zero-rho cells. Define the original-label cost

\[
 S=\sum_{\text{original labels }i}\nu(J_i).
 \tag{FA87}
\]

It counts labels separately even when their current subsets coincide.
It is not the probability of the full arithmetic union: old-coordinate
conditions have not been integrated into S.

Let delta(x,y) lie in (0,1). Set

    u = min(alpha,delta)/(1-min(alpha,delta)),

and set u/alpha=0 when alpha=0. The actual clipped joint law is

    mu(x,y,c) = rho(x,y)/n
                [1+u(x,y)-(u(x,y)/alpha(x,y))1_{B(x,y)}(c)].

Its old marginal is rho. Put T=E_rho[u] and define the full-coordinate
pair defects

    e_X = TV(mu_XZ, rho_X x nu),
    e_Y = TV(mu_YZ, rho_Y x nu).

Then

\[
 e_X+e_Y\ge T\left(1-\sqrt{\alpha_*S}\right)_+.
 \tag{FA88}
\]

In particular, exact balance of both pairs and T>0 require

\[
 \alpha_*S\ge1.
 \tag{FA89}
\]

### 13.2. Proof by a counted expansion, without changing the actual source

For every original label i and every c in J_i, make one auxiliary
rectangular label A_i x B_i of color c. The resulting union U_c is
exactly {(x,y): c in B(x,y)}. If L_exp is the number of auxiliary labels
and K_exp their geometric color multiplicity, then

\[
 \begin{aligned}
 L_{\mathrm{exp}}&=\sum_i|J_i|=nS,\\
 K_{\mathrm{exp}}&=\max_{x,y}|B(x,y)|=n\alpha_*.
 \end{aligned}
 \tag{FA90}
\]

The actual bad mass is k(x,y)/n=alpha(x,y), exactly as in the finite
defect theorem. Its weight is

    W(x,y) = rho(x,y) u(x,y)/k(x,y)
           = rho(x,y) u(x,y)/(n alpha(x,y))

when alpha>0, and zero otherwise. Thus sum_c W 1_{U_c}=rho u and its
activity mass is the same T. No alternative incoming measure or clipping
history is introduced. Applying the finite theorem and substituting (FA90)
gives sqrt(K_exp L_exp)/n=sqrt(alpha_* S), proving (FA88). If T=0, the
actual law equals its incoming product and (FA88) reads 0>=0; (FA89) does not
follow. If T>0 and both defects vanish, (FA88) gives (FA89).

### 13.3. Arbitrary finite prime-power heights and old-coordinate blocks

For a fresh full p-coordinate Z=Z/p^H Z with Haar law, an original
current congruence c=b_i modulo p^(a_i), 1<=a_i<=H, has mass

\[
 \nu(J_i)=p^{-a_i},\qquad S=\sum_i p^{-a_i}.
 \tag{FA91}
\]

Thus the finite ambient height cancels from (FA88). The statement holds for
every finite H, with all digits retained. No bound on the number of
different heights, no current-height-one restriction, and no replacement
of a literal current prefix by an independent color are needed.

If the declared incoming current base is instead uniform on the pure
survivors {z : z is nonzero modulo p}, its size is
n=(p-1)p^(H-1). A nonempty original prefix with a_i>=1 has nonzero first
digit and

\[
 \nu(J_i)=\frac{p^{1-a_i}}{p-1}.
 \tag{FA92}
\]

Prefixes with zero first digit have empty intersection with this base.
This alternative requires that pure-survivor base as an actual incoming
contract. It does not justify replacing the incoming law of an arbitrary
whole process by a newly conditioned law.

For more than two old prime coordinates, partition them into two groups.
Let X and Y be the respective complete Cartesian blocks. By the original
prime-power coordinate representation, each old cofactor condition is
a product A_i x B_i, including unrestricted factors when the modulus
does not involve a coordinate. Its original residue is retained. The
same inequality applies with rho equal to the same actual old block law.

The measured pairs here are (the entire X block, current Z) and (the
entire Y block, current Z). Separate pairwise independence between Z and
each individual old prime does not imply either block independence.
Changing the grouping changes which full joint marginals must be
controlled. The theorem does not supply that stronger observation from
weaker single-coordinate data.

### 13.4. What the arithmetic application does and does not supply

S is a sum over the original numerical labels, with the literal current
prefix mass as its weight. Distinctness of original numerical moduli is
compatible with, but is not used by, the matrix inequality. Expansion can
produce repeated auxiliary shapes and does not assert that these are
additional distinct original moduli.

The result supplies an all-height necessary condition for exact pair
balance and a same-source quantitative pair-defect certificate. The right
side is positive only if alpha_* S<1 and T>0. Without a bound on old
cofactor diversity, S can be arbitrarily large, so no uniform positive
defect for unrestricted families follows. Small thresholds can also make
T arbitrarily small.

Neither T nor S is identified with first-hit loss. This inequality does
not itself convert a pair defect into uncovered mass, a future-loss
saving, or a telescoping budget along the whole prime sequence. Those
remain separate mathematical obligations, including all tail primes.

[Continue with section 14: finite original-label cores](47-finite-label-core-and-omitted-mass.md).

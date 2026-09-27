[Index](../../marked_head_profile.md) · [Pair-tree laws](376-complete-prime-chain-transport-and-joint-prefix-laws.md) · [Exact layout dual](400-literal-layout-mixtures-and-exact-tree-rank-duality.md) · [Recursive sources](401-a-recursive-minimum-source-has-one-law-at-every-height.md)

# One common law with a universal row-compatible bound

At 5-height one, every four-row source satisfying the six pairwise
ternary-tree conditions and the full five-ary projection condition
admits one actual probability for all independently phased original
divisor layouts. Its squared-load bound is

\[
 C_K=\frac{168}{25}-\frac{4K+7}{5^{K+1}}
              -\frac{39(K+2)}{25\,3^K}<\frac{168}{25}=6.72.
\]

The probability mixes a full-tree law with pair-tree laws, using the
full-tree row distribution to choose which row each pair mixture
avoids. Retaining the zero intersections between distinct row phases
improves its separate-prefix bound from `1698/245` to `168/25`.
No heavy row, three-row five-tree premise, fixed root graph or repeated
tail geometry is required.

The limit is still `18/25` above six. This is a general bound in the
stated source model, not the desired finite comparison `2t_K`, a
conditioning theorem for arbitrary prime fibres, or a solution of
unrestricted Erdős #7. The arguments and exact research checks are
not Lean-certified.

## Source, original labels, and an initial bound

Let `K>=0`, let `Y=Z/7^K`, and read seven-adic digits from lowest to highest. A complete `b`-ary tree of depth `K` selects exactly `b` children at every selected nonleaf; at depth zero its leaf set is a singleton. Let

\[
R\subseteq\{1,2,3,4\}\times Y.
\]

Assume that the union of every two row fibres contains a complete ternary tree of depth `K`, and that the full projection onto `Y` contains a complete five-ary tree of depth `K`. Three active rows are allowed.

Identify points with residues modulo `5*7^K` by CRT. For a supported probability `nu`, define the full original-divisor functional

\[
\Gamma_{1,K}(\nu)
=\max_{(a_d)_{d\mid5\cdot7^K}}
\mathbb E_\nu\left(\sum_{d\mid5\cdot7^K}
\mathbf1_{x\equiv a_d\pmod d}\right)^2.
\tag{GM1}
\]

Every residue is selected independently of the other labels, with no compatibility restriction. Divisor one contributes its constant indicator. Phases in row zero remain allowed, even though the source has no points there.

There is one probability on the given `R` such that

\[
\Gamma_{1,K}(\nu)\le B_K
:=\frac85 S_K(1/5)+\frac95 S_K(1/3)-\frac65 S_K(1/15)
<\frac{1698}{245},
\tag{GM2}
\]

where

\[
S_K(z)=\sum_{j=0}^K(2j+1)z^j
=\frac{1+z-(2K+3)z^{K+1}+(2K+1)z^{K+2}}{(1-z)^2}
\qquad(0\le z<1).
\tag{GM3}
\]

This is an ordinary mathematical proof, not Lean certification. Its limiting ceiling is `6+228/245`, so it does not establish the general target `Gamma_(1,K)<=2t_K`, where `t_K=S_K(1/3)`. It does not resolve unrestricted Erdős #7.

## A supported mixture using the full-tree row distribution

For each pair `{r,s}`, choose a complete ternary tree in that pair's actual projection. Give its `3^K` leaves equal mass and assign each leaf to one available row in the pair. This gives a probability `eta_rs` on the original source. For every literal seven-adic prefix `P` of depth `j`,

\[
\eta_{rs}(P)\le q_j:=3^{-j},\qquad
\eta_{rs}(\{u\}\times P)\le
\begin{cases}q_j,&u\in\{r,s\},\\0,&u\notin\{r,s\}.
\end{cases}
\tag{GM4}
\]

Choose a complete five-ary tree in the full projection, weight its leaves uniformly, and assign each leaf to an actual available row. Write `mu` for this probability and `beta_r=mu(row r)`. Then

\[
\sum_r\beta_r=1,\qquad
\mu(P)\le f_j:=5^{-j},\qquad
\mu(\{r\}\times P)\le\min(\beta_r,f_j).
\tag{GM5}
\]

For each omitted row `i`, average the three pair laws avoiding it, and then weight these four averages by the row distribution of `mu`:

\[
W_i=\frac13\sum_{\substack{r<s\\r,s\ne i}}\eta_{rs},\qquad
\omega=\sum_{i=1}^4\beta_iW_i,\qquad
\nu=\frac25\mu+\frac35\omega.
\tag{GM6}
\]

All components are supported on the same actual `R`. The choices in GM6 are made once, before any adversarial layout is selected.

Every `W_i` has prefix masses at most `q_j`. For a fixed row `r`, the law `W_r` assigns it zero mass. In each `W_i` with `i!=r`, exactly two of its three pair laws can contribute to row `r`. Consequently

\[
\omega(P)\le q_j,\qquad
\omega(\{r\}\times P)\le\frac23(1-\beta_r)q_j.
\tag{GM7}
\]

The resulting single law therefore satisfies, simultaneously at every prefix and every depth `0<=j<=K`,

\[
\begin{aligned}
m_j:=\max_P\nu(P)&\le\frac25f_j+\frac35q_j,\\
\nu(\{r\}\times P)&\le\frac25\bigl[\min(\beta_r,f_j)+(1-\beta_r)q_j\bigr].
\end{aligned}
\tag{GM8}
\]

For `0<=f,q<=1`, the function `min(beta,f)+(1-beta)q` increases up to `beta=f` and decreases afterwards, allowing zero slopes at the endpoints. Thus

\[
c_j:=\max_{r,P}\nu(\{r\}\times P)
\le\frac25\bigl[f_j+(1-f_j)q_j\bigr].
\tag{GM9}
\]

At `j=0`, these formulas give `m_0=1` and every row mass at most `2/5`. There is no missing depth-zero term.

## The independent original-label square

For a literal layout, write `P_j` for its selected class modulo `7^j` and `Q_j` for its selected class modulo `5*7^j`. The load is

\[
L=\sum_{j=0}^K(\mathbf1_{P_j}+\mathbf1_{Q_j}).
\tag{GM10}
\]

For an ordered pair of depths `(a,b)`, put `j=max(a,b)`. The intersection `P_a intersect P_b` is empty or a depth-`j` plain prefix. Each of `P_a intersect Q_b`, `Q_a intersect P_b`, and `Q_a intersect Q_b` is empty or a row-prefix of depth `j`. Distinct row choices in the last intersection make it empty. These statements do not require the selected phases to be compatible.

Exactly `2j+1` ordered depth pairs have maximum `j`. Expanding every term of `L^2` under the same `nu` gives

\[
\Gamma_{1,K}(\nu)\le\sum_{j=0}^K(2j+1)(m_j+3c_j).
\tag{GM11}
\]

Substitution of GM8 and GM9 yields

\[
m_j+3c_j\le\frac85f_j+\frac95q_j-\frac65f_jq_j,
\tag{GM12}
\]

which proves the finite expression in GM2. No separately optimized probabilities are combined, and no products of unrelated marginal bounds are used.

Each summand coefficient in GM12 is strictly positive:

\[
\frac85f_j+\frac95q_j-\frac65f_jq_j
=\frac85f_j+\frac35q_j(3-2f_j)>0.
\]

Hence `B_K` strictly increases with `K` and is strictly below its infinite sum. Using `S_infinity(z)=(1+z)/(1-z)^2`,

\[
\lim_{K\to\infty}B_K
=\frac85\frac{15}{8}+\frac95\,3-\frac65\frac{60}{49}
=3+\frac{27}{5}-\frac{72}{49}
=\frac{1698}{245}.
\tag{GM13}
\]

The first finite values are

| `K` | `B_K` |
| ---: | ---: |
| 0 | `11/5` |
| 1 | `118/25` |
| 2 | `451/75` |
| 3 | `7388/1125` |
| 4 | `190967/28125` |

## Comparison with the pair-only certificate

Uniformly averaging the six `eta_rs` gives one supported probability with plain-prefix caps `q_j` and row-prefix caps `q_j/2`. GM11 then gives the pair-only certificate `(5/2)t_K`, where `t_K=S_K(1/3)`.

The improvement in GM2 is strict at every finite height:

\[
\frac52t_K-B_K
=\sum_{j=0}^K(2j+1)
\left(\frac7{10}3^{-j}-\frac85 5^{-j}+\frac65 15^{-j}\right)>0.
\tag{GM14}
\]

The `j=0` contribution is `3/10`, and the `j=1` contribution is `-1/50`; their sum is `7/25`. For every `j>=2`, dividing the parenthesized coefficient by `3^-j` gives

\[
\frac7{10}-\frac85(3/5)^j+\frac65(1/5)^j
>\frac7{10}-\frac85\frac9{25}
=\frac{31}{250}>0.
\]

Thus GM14 is `3/10` at height zero, `7/25` at height one, and strictly increases thereafter. This compares two explicit general certificates; it does not assert optimality of either supported law.

## Keeping the mixed-label row sequence

Let `K>=0`, let `beta=(beta_1,...,beta_4)` be a probability vector, and put

\[
 f_j=5^{-j},\quad q_j=3^{-j},\quad
 m_j=\frac25f_j+\frac35q_j,\quad
 c_j(x)=\frac25\bigl[\min\{x,f_j\}+(1-x)q_j\bigr].
\]

For a row word `r_0,...,r_K` define `n_j=|{i<j:r_i=r_j}|`.
The upper functional obtained from these common-law caps, retaining
the incompatibility of different mixed-phase rows, is

\[
 \mathcal F_K(\beta,r)
 =\sum_{j=0}^K(2j+1)m_j
 +\sum_{j=0}^K\left[
 (2j+3+2n_j)c_j(\beta_{r_j})
 +2\sum_{i<j}c_j(\beta_{r_i})\right].
 \tag{RA1}
\]

Its maximum is attained by every constant row word whose selected row
has `beta_r=1/5`; at `K=0` the selected beta is immaterial. Every
nonconstant row word has strictly smaller value. The maximum is

\[
 C_K=\frac85S_K(1/5)+\frac{39}{25}S_K(1/3)-\frac{24}{25}
 =\frac{168}{25}-\frac{4K+7}{5^{K+1}}
       -\frac{39(K+2)}{25\,3^K},
 \quad S_K(z)=\sum_{j=0}^K(2j+1)z^j.
 \tag{RA2}
\]

In particular `C_K` increases to `168/25=6.72`. This is the sharp
maximum of RA1, not a sharpness claim for an actual layout expectation
or source minimax problem. It still exceeds the desired target
asymptotically.

### Why RA1 bounds every literal layout

Write `P_j` for its pure `7^j` event and `Q_j` for its mixed
`5*7^j` event, whose row is `r_j`. Keep all original labels and their
independent residue choices. The `P_a P_b` ordered products give
`(2j+1)m_j` when the larger depth is `j`.

The `Q_j^2` term gives one copy of `c_j(beta_rj)`; `P_a Q_j` and
`Q_j P_a` for `0<=a<=j` give `2j+2` copies. The opposite cross terms
with `P_j` and `Q_i`, `i<j`, give `2 sum_(i<j)c_j(beta_ri)`.
Finally `Q_i Q_j` is empty if their rows differ; the `n_j` matching
earlier rows give at most `2n_j*c_j(beta_rj)`. Incompatible residues
may make further intersections empty, which only decreases the bound.
This proves RA1 without aligning or identifying any literal phase.

If a mixed phase chooses absent row zero, its event vanishes.
Replacing its row label in the cap functional by an actual row only
adds nonnegative bounds. Thus optimizing RA1 over four rows also
bounds layouts containing any absent-row phases.

### A constant-row prefix is maximized at beta = 1/5

For a constant word through depth `N`, its row contribution is

\[
 A_N(x)=\sum_{j=0}^N(6j+3)c_j(x).
\]

Each summand is concave and piecewise linear. Since `f_0=q_0=1`,
`c_0(x)=2/5` is constant. For `N>=1`, the left derivative at `x=1/5` is

\[
 \frac{12}{5}-\frac65\sum_{j=2}^N(2j+1)3^{-j}
 \ \ge\ \frac{12}{5}-\frac65=\frac65>0.
\]

The infinite sum beginning at depth two equals one. The right
derivative is strictly negative, since each nonconstant summand has
slope `-(2/5)q_j` to the right of `1/5`. Concavity proves that `1/5`
is the unique maximum for `N>=1`; for `N=0` all `x` give the same value.

Put

\[
 u_j=\max_{0\le x\le1}c_j(x)
     =\frac25\bigl[f_j+(1-f_j)q_j\bigr],\qquad
 v_j=c_j(1/5).
\]

The depth-zero value is separate: `v_0=u_0=2/5`. For `j>=1`,

\[
 v_j=\frac25\bigl[f_j+\tfrac45q_j\bigr],\qquad
 u_j-v_j=\frac{2}{25}3^{-j}-\frac25\,15^{-j}.
 \tag{RA3}
\]

### Charge the first row change and every later depth

Suppose the word first changes at depth `h>=1`. Its prefix through
`h-1` is bounded by the constant-row optimum just proved. At depth
`h`, `n_h=0`, so its nonnegative row-cap coefficients sum to `4h+3`,
losing `2h` relative to the aligned coefficient `6h+3`.

At every later depth `j>h`, previous rows are not all equal.
Consequently `n_j<=j-1`, and the coefficient sum is at most `6j+1`,
losing at least two. Bounding each cap by `u_j`, the excess over
the aligned row contribution is at most

\[
 D_{h,K}=(6h+3)(u_h-v_h)-2h\,u_h
 +\sum_{j=h+1}^K a_j,
 \quad
 a_j=(6j+3)(u_j-v_j)-2u_j.
 \tag{RA4}
\]

The pure-prefix term in RA1 is identical for both words. The tail
terms have the exact expression

\[
 a_j=\frac25\left[
 \frac{6j-7}{5}3^{-j}-2\,5^{-j}-(6j+1)15^{-j}
 \right].
 \tag{RA5}
\]

In particular `a_2=-4/375<0`. For `j>=3`, multiplying the bracket
by `15^j` gives

\[
 (6j-7)5^{j-1}-2\,3^j-(6j+1)
 \ge (6j-13)3^{j-1}-(6j+1)
 \ge 48j-118>0.
\]

Thus `a_j>0` at every depth `j>=3`. This sign check is essential
when replacing the finite sum in RA4 by an infinite upper bound.

### The infinite upper bound is strictly negative

Summing the geometric series in RA4 gives

\[
 D_h:=\lim_{K\to\infty}D_{h,K}
 =\frac{8-2h}{25}\,3^{-h}
  -\frac{4h+1}{5}\,5^{-h}
  -\frac{434h+346}{245}\,15^{-h}.
 \tag{RA6}
\]

The series identities used here are

\[
 \sum_{j=h}^{\infty}(2j+1)3^{-j}=3(h+1)3^{-h},\qquad
 \sum_{j=h}^{\infty}(2j+1)15^{-j}
    =\frac{105h+60}{49}\,15^{-h},
\]

and

\[
 2\sum_{j>h}u_j=\frac15\,5^{-h}
       +\frac25\,3^{-h}-\frac{2}{35}\,15^{-h}.
\]

For `h>=4`, the first coefficient in RA6 is nonpositive and the
other terms are strictly negative. The initial exact values are

\[
 D_1=-\frac{407}{1225},\qquad
 D_2=-\frac{467}{6125},\qquad
 D_3=-\frac{16397}{826875}.
 \tag{RA7}
\]

For `h>=2`, all terms after the initial term in RA4 have index at
least three, so `D_(h,K)<=D_h<0`. For `h=1,K>=2`, the negative
`a_2` is included and the omitted tail again consists only of positive
terms, giving the same conclusion. The remaining case `h=K=1` has
`D_(1,1)=-2u_1=-28/75<0`.

Every row change is strictly worse than the aligned `beta=1/5`
profile. For a constant word that beta is feasible: distribute the
remaining `4/5` among unused rows. Substituting RA3, with its separate
depth-zero value, proves RA2.

## A limit of changing the mixture coefficient


The alignment theorem fixes the mixture coefficient at `2/5`. Allowing a different coefficient does not by itself make the retained row-cap method reach six.

For `nu_lambda=lambda*mu+(1-lambda)*omega`, with the same supported component laws as GM6, retain the row-mass parameter in the cap:

\[
c_j^{\lambda}(b)
=\lambda\min(b,5^{-j})+\frac23(1-\lambda)(1-b)3^{-j},
\qquad
m_j^{\lambda}=\lambda5^{-j}+(1-\lambda)3^{-j}.
\tag{GM22}
\]

Let `r_j` be the actual row selected by label `5*7^j`, and let
`n_j=|{i<j:r_i=r_j}|`. If a mixed phase selects row zero, replacing it by an arbitrary active-row phase with the same seven-adic prefix cannot decrease the load on the source: the original indicator vanishes there. Thus the maximum may be bounded using row sequences in `{1,2,3,4}`.

An ordered mixed/mixed pair with different rows has empty intersection. Retaining this fact and the row parameters gives

\[
\begin{aligned}
G_K(\lambda;\beta,\mathbf r)
=\sum_{j=0}^K\bigg[&(2j+1)m_j^{\lambda}
 +(2j+3+2n_j)c_j^{\lambda}(\beta_{r_j})\\
&+2\sum_{i<j}c_j^{\lambda}(\beta_{r_i})\bigg].
\end{aligned}
\tag{GM23}
\]

The terms are respectively pure/pure intersections; the mixed label at depth `j` paired with the pure labels through that depth, itself, and earlier mixed labels in its row; and the pure label at depth `j` paired with earlier mixed labels. It follows that

\[
\Gamma_{1,K}(\nu_\lambda)
\le \max_{\mathbf r}G_K(\lambda;\beta,\mathbf r)
\le \max_{\substack{\beta\ge0,\ \sum\beta=1\\\mathbf r}}G_K(\lambda;\beta,\mathbf r).
\tag{GM24}
\]

Even this stronger cap certificate cannot establish a uniform ceiling of six for any choice of `lambda`. Two explicit feasible profiles prove the limitation.

First, put every mixed label in one row whose `beta` mass is `1/5`, and assign the remaining `4/5` to another row. Since
`sum_j (2j+1)min(1/5,5^-j)=S_K(1/5)-4/5`, this profile has value

\[
A_K(\lambda)
=4\lambda S_K(1/5)+\frac{13}{5}(1-\lambda)S_K(1/3)-\frac{12}{5}\lambda,
\qquad
A_\infty(\lambda)=\frac{39}{5}-\frac{27}{10}\lambda.
\tag{GM25}
\]

Second, choose distinct rows `a,b`, put `r_0=a` and `r_j=b` for every `j>=1`, and take `beta_a=4/5`, `beta_b=1/5`. At depth zero the row contribution is `2/5+2lambda`. At each positive depth, row `b` has coefficient `6j-1` and row `a` has coefficient two. Hence this profile gives

\[
\begin{aligned}
D_K(\lambda)
={}&\lambda S_K(1/5)+(1-\lambda)S_K(1/3)+\frac25+2\lambda\\
&+\sum_{j=1}^K\left[
 \lambda(6j+1)5^{-j}
 +(1-\lambda)\frac{48j-4}{15}3^{-j}\right],\\
D_\infty(\lambda)={}&\frac{17}{3}+\frac{11}{15}\lambda.
\end{aligned}
\tag{GM26}
\]

For example, the positive-depth sums used here are
`sum_(j>=1)(6j+1)5^-j=17/8` and
`sum_(j>=1)(48j-4)3^-j/15=34/15`.

The first limiting line decreases and the second increases. They meet at

\[
\lambda=\frac{64}{103},\qquad
A_\infty(\lambda)=D_\infty(\lambda)=\frac{3153}{515}
=6+\frac{63}{515}.
\tag{GM27}
\]

Therefore

\[
\min_{0\le\lambda\le1}
\max\{A_\infty(\lambda),D_\infty(\lambda)\}
=\frac{3153}{515}>6.
\tag{GM28}
\]

The limitation already appears at a finite height. At `K=4`, the two profiles are
`A_4(lambda)=1027/135-(42623/16875)lambda` and
`D_4(lambda)=1333/243+(136202/151875)lambda`.
They intersect at `lambda=322250/519809`, and

\[
\min_{0\le\lambda\le1}\max\{A_4(\lambda),D_4(\lambda)\}
=\frac{15702287}{2599045}
=6+\frac{108017}{2599045}>6.
\tag{GM29}
\]

Thus allowing the mixing coefficient to depend on height does not remove this obstruction within GM22–GM24. The two limiting profiles also converge uniformly in `lambda`, since their finite expressions are affine with convergent coefficients.

GM28 and GM29 are lower bounds for the maximum of the cap expression, not for `Gamma` itself. The expression can overestimate mutually constrained prefix intersections. Neither profile is asserted to attain all its cap bounds under an actual layout. They therefore establish a limit of this proof method, not a counterexample to the target source theorem, a minimax lower bound for an actual source, or an obstruction to a stronger analysis of the same supported laws.

## Exact construction and verification

The standard-library program
[full_and_pair_tree_common_law.py](../../frontier/cover-geometry/full_and_pair_tree_common_law.py)
accepts an arbitrary finite source and height, selects the seven actual
tree witnesses, and returns their exact rational laws, the full-tree row
masses, the pair weights `(1-beta_r-beta_s)/3`, and the resulting `nu`.
Its verifier checks the selected trees, support, normalization, mixture
identities and every actual plain and joint prefix mass. Tree selection
and tree verification reuse the sibling original-layout certificate.

The verifier reports the separate-prefix bound `B_K`, the sharper
row-compatible bound `C_K`, and the minimum of `C_K` and the source's
measured prefix envelope. It does not assume that the measured prefix
envelope itself is at most `C_K`: the latter uses additional zero
mixed-row intersections. Neither quantity is labelled an exact
source minimax value.

With `--stdin`, the program reads a JSON object with `height` and
`source` (a list of `[row,residue]` pairs) and prints the full exact
certificate and verification. With no arguments it runs 12 source
controls, including three-row and four-row height-zero sources,
the eight-point type E, the report 399 source, a full carrier, and
the two report 401 families through height three. Its 26 rejection
controls cover invalid data, failed tree premises and altered
certificates. Separate controls compare the row-profile formula
against direct ordered-label intersections, check the closed finite
series, and check the first-change algebra and exceptional tail sign.

These checks are finite controls for the analytic argument. The
construction supplies a law on each source under the full-height
premises; it does not assert that those premises survive conditioning
on earlier coordinates or supply an iteration theorem for such fibres.

[Index](../../marked_head_profile.md) · [Root laws](390-two-prime-root-blockers-admit-a-common-second-moment-law.md) · [Two-digit layout oracle](392-root-optimal-laws-do-not-tensorize-the-full-layout-bound.md)

# A two-digit seed controls repeated type-B sources at all heights

One compatible probability law on repeated type-B digit sources satisfies
the full independent-divisor second-moment comparison at every pair of
positive heights, including unequal heights. The law uses a specified
two-digit seed, followed by independent copies of one root law. Its
complete second moment is bounded uniformly by
`67803771/7658816<9`; a finite set of exact comparisons proves the
stronger finite-height target.

This is a theorem about the structured sources defined below. It does
not extend to arbitrary sources meeting the same tree tests, identify
a minimax law, or realize these sources as residuals of an actual odd
cover. The proof and exact arithmetic checks are not Lean-certified.
Erdős #7 remains open.

## 1. Source, common law and full layout functional

Use the type-B root source

\[
 B=\{(1,1),(2,2),(2,3),(3,2),(3,4),(4,2),(4,5)\}
        \subset\mathbb Z/5\times\mathbb Z/7.
 \tag{BT1}
\]

Its types `I,H,P` consist respectively of `(1,1)`, the three points in
column 2, and the three remaining points. For positive heights `H,K`,
define `R_{H,K}` by projecting paired digit words in `B^max(H,K)`:

\[
 R_{H,K}=\left\{\left(\sum_{j<H}r_j5^j,\sum_{j<K}c_j7^j\right):
                  (r_j,c_j)\in B\right\}.
 \tag{BT2}
\]

The source excludes the zero first root in both coordinates. The tree
intersection argument of report 392 applies at unequal heights by
extending each shorter complete tree to the larger depth and then
projecting an intersection point. In particular this construction keeps
the full tree conditions, not just marginal cardinality conditions.

For digit positions 0 and 1 jointly, assign each ordered pair of root
points a probability determined by its ordered pair of types:

\[
 \sigma(u,v)=\frac{W_{\operatorname{type}(u),\operatorname{type}(v)}}{989},
 \qquad
 W=\begin{pmatrix}35&16&30\\24&10&21\\32&14&27\end{pmatrix}.
 \tag{BT3}
\]

These are per-point-pair masses. With type sizes `(1,3,3)`,
`(1,3,3)W(1,3,3)^T=989`, so the law normalizes. At every digit position
`j>=2`, independently of the seed and all other later positions, use
the per-point root law

\[
 \tau(I)=\frac15,\qquad \tau(H)=\frac1{15},\qquad
 \tau(P)=\frac15.
 \tag{BT4}
\]

Let `nu_{H,K}` be the corresponding coordinate projection, with masses
summed when projection identifies points. Thus all heights and all
layout tests use marginals of the same seed-plus-tail law; there is
no choice of a separate optimizing probability for each divisor.

Set `Q=5^H7^K`. For one independently chosen residue `a_d mod d` at
each divisor `d|Q`, including `a_1=0`, define

\[
 \Gamma_{H,K}(\nu)=
 \max_{(a_d)_{d\mid Q}}
 \mathbb E_\nu\left(\sum_{d\mid Q}1_{x\equiv a_d\pmod d}\right)^2.
 \tag{BT5}
\]

CRT identifies BT2 with residues modulo `Q`. No centering or mutual
compatibility of the chosen layout residues is imposed. The conclusion is

\[
 \boxed{\quad
 \Gamma_{H,K}(\nu_{H,K})<t_Ht_K,
 \qquad t_h=1+\sum_{a=1}^h\frac{2a+1}{3^a}
             =3-\frac{h+2}{3^h},\qquad H,K\ge1.
 \quad}
 \tag{BT6}
\]

## 2. The exact two-digit block and its prefix maxima

The full nine-divisor layout maximum of the seed is

\[
 \Gamma_{2,2}(\sigma)=\frac{5989}{989}.
 \tag{BT7}
\]

The exact separation formula in report 392 checks all `56,000`
baseline choices and maximizes the remaining three independent phases.
The attaining layout is evaluated literally:

| Divisor | 1 | 5 | 25 | 7 | 49 | 35 | 175 | 245 | 1225 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Residue | 0 | 2 | 12 | 2 | 16 | 2 | 37 | 212 | 562 |

For `0<=a,b<=2`, let `M_ab` be the maximum seed probability of a
joint prefix cell at depths `(a,b)`. Direct summation of the 49 seed
atoms gives, with rows indexed by `a` and columns by `b`,

\[
 (M_{ab})=\frac1{989}
 \begin{pmatrix}989&351&90\\272&173&48\\72&46&35\end{pmatrix}.
 \tag{BT8}
\]

Define

\[
 c_5=\sum_{b=0}^2(2b+1)M_{2b}=\frac{385}{989},\qquad
 c_7=\sum_{a=0}^2(2a+1)M_{a2}=\frac{409}{989},\qquad
 g=M_{22}=\frac{35}{989}.
 \tag{BT9}
\]

All these quantities concern the same law BT3. They are separate
upper bounds and need not be simultaneously attained by one prefix.

## 3. Later digits and the LCM expansion

Under BT4, a spoke row has mass `1/15+1/5=4/15`; the isolated row
has mass `1/5`. Column 2 has mass `3/15=1/5`, as does each other
occupied column, and the largest atom has mass `1/5`. Consequently
the row, column and atom caps are

\[
 \alpha=\frac4{15},\qquad\beta=\frac15,\qquad\gamma=\frac15.
 \tag{BT10}
\]

Independence after the first two paired digits now gives the following
prefix-cell upper bounds:

\[
 \begin{aligned}
 P_{2+i,b}&\le M_{2b}\alpha^i &&(i\ge1,\ 0\le b\le2),\\
 P_{a,2+j}&\le M_{a2}\beta^j &&(j\ge1,\ 0\le a\le2),\\
 P_{2+i,2+j}&\le
    g\gamma^{\min(i,j)}\alpha^{(i-j)_+}\beta^{(j-i)_+}
       &&(i,j\ge1).
 \end{aligned}
 \tag{BT11}
\]

In the last line each paired constrained tail position costs at most
`gamma`; the unmatched positions cost the appropriate marginal cap.
Replacing this factor by independent powers `alpha^i beta^j` would
discard the actual dependence between the two coordinates of one digit.

Expand the square in BT5 into ordered pairs of divisor indicators.
An intersection is empty or a single cylinder at the LCM. The number
of ordered pairs of exponents in `{0,...,a}` with maximum `a` is
`(a+1)^2-a^2=2a+1`. Therefore the number of ordered divisor pairs
whose LCM has exponents `(a,b)` is

\[
 (2a+1)(2b+1).
 \tag{BT12}
\]

When `a,b<=2`, retain the entire squared two-digit load and bound it
by BT7. Do not replace it by the sum of individual prefix caps.
Every remaining ordered pair has an LCM outside that square, so all
and only those remaining terms receive BT11 and BT12.

For `n=H-2,m=K-2>=0`, write

\[
 \begin{aligned}
 F_{n,m}={}&\frac{5989}{989}
 +c_5\sum_{i=1}^{n}(2i+5)\alpha^i
 +c_7\sum_{j=1}^{m}(2j+5)\beta^j\\
 &+g\sum_{i=1}^{n}\sum_{j=1}^{m}(2i+5)(2j+5)
        \gamma^{\min(i,j)}\alpha^{(i-j)_+}\beta^{(j-i)_+}.
 \end{aligned}
 \tag{BT13}
\]

This proves `Gamma_{H,K}(nu_{H,K})<=F_{H-2,K-2}` for all `H,K>=2`.
All summands are nonnegative, so finite bounds increase to their strip
and full limits. BT13 is an upper bound, not an asserted exact maximum.

## 4. Closed sums and equal heights

For `0<=z<1`, put

\[
 f(z)=\sum_{i\ge1}(2i+5)z^i
      =\frac{2z}{(1-z)^2}+\frac{5z}{1-z},
 \qquad
 U(z)=\sum_{i\ge1}(2i+5)^2z^i
      =\frac{4z(1+z)}{(1-z)^3}
       +\frac{20z}{(1-z)^2}+\frac{25z}{1-z}.
 \tag{BT14}
\]

Split the infinite double sum into `i=j=t`, `i=t+d,j=t`, and
`i=t,j=t+d`, with `t,d>=1` in the off-diagonal terms. Since
`(2t+5)(2t+2d+5)=(2t+5)^2+2d(2t+5)`, its value is

\[
 J=U(\gamma)\left(1+\frac\alpha{1-\alpha}+\frac\beta{1-\beta}\right)
 +2f(\gamma)\left(\frac\alpha{(1-\alpha)^2}
                       +\frac\beta{(1-\beta)^2}\right)
 =\frac{203105}{7744}.
 \tag{BT15}
\]

Thus

\[
 F_{\infty,\infty}
 =\frac{5989}{989}+c_5f(\alpha)+c_7f(\beta)+gJ
 =\frac{67803771}{7658816},\qquad
 9-F_{\infty,\infty}=\frac{1125573}{7658816}>0.
 \tag{BT16}
\]

For equal heights, the remaining finite comparisons are:

| Height `h` | `F_{h-2,h-2}` | `t_h²` | `t_h²-F_{h-2,h-2}` |
| --- | --- | --- | --- |
| 2 | `5989/989` | `529/81` | `38072/80109` |
| 3 | `114349/14835` | `5776/729` | `775513/3604905` |
| 4 | `625208/74175` | `6241/729` | `2383181/18024525` |
| 5 | `29061638/3337875` | `521284/59049` | `885932194/7299932625` |

The factors increase because
`t_{h+1}-t_h=(2h+3)/3^(h+1)>0`, and

\[
 t_6^2-F_{\infty,\infty}
 =\frac{330668515445}{4070208833856}>0.
 \tag{BT17}
\]

This proves every equal-height comparison with `h>=2`, and also every
unequal pair with both heights at least 6.

## 5. Unequal heights at least two

For a finite first tail depth `n`, sum the second tail geometrically:

\[
 \begin{aligned}
 J_{n,\infty}=\sum_{i=1}^n(2i+5)\bigg[
  &\sum_{j=1}^i(2j+5)\gamma^j\alpha^{i-j}\\
  &+\gamma^i\left((2i+5)\frac\beta{1-\beta}
                         +\frac{2\beta}{(1-\beta)^2}\right)\bigg],\\
 F_{n,\infty}={}&\frac{5989}{989}
     +c_5\sum_{i=1}^n(2i+5)\alpha^i+c_7f(\beta)+gJ_{n,\infty}.
 \end{aligned}
 \tag{BT18}
\]

Exchange `alpha,beta` and `c_5,c_7` for `F_{infinity,m}`. The eight
strip inequalities below use the common cutoff 5 for the other height:

| Finite coordinate | Height `h` | Strip bound | `t_h t_5` minus bound |
| --- | --- | --- | --- |
| 5-coordinate | 2 | `54047/7912` | `13185883/17303544` |
| 5-coordinate | 3 | `95207/11868` | `8855923/25955316` |
| 5-coordinate | 4 | `202741/23736` | `7890089/51910632` |
| 5-coordinate | 5 | `23348017/2670300` | `492874421/5839946100` |
| 7-coordinate | 2 | `77779/10879` | `10554001/23792373` |
| 7-coordinate | 3 | `4936643/598345` | `443072117/3925741545` |
| 7-coordinate | 4 | `2354636/271975` | `64143254/1784427975` |
| 7-coordinate | 5 | `11958154/1359875` | `2764043954/80299258875` |

These prove BT6 whenever one height is in `{2,3,4,5}` and the other
is at least 5. When both heights are in `{2,3,4}`, the nine differences
`t_H t_K-F_{H-2,K-2}` are all positive:

| `H` / `K` | 2 | 3 | 4 |
| --- | --- | --- | --- |
| 2 | `38072/80109` | `671516/1201635` | `4169122/6008175` |
| 3 | `98809/240327` | `775513/3604905` | `5223971/18024525` |
| 4 | `535874/1201635` | `576193/3604905` | `2383181/18024525` |

These nine cells, the eight strips and BT17 exhaust all `H,K>=2`.

## 6. Height-one boundaries use the same seed process

Project the same seed law onto the smaller divisor rectangles. Direct
enumeration over all occupied phases gives:

| Heights | Exact full layout maximum | Layouts examined | Finite target minus maximum |
| --- | --- | --- | --- |
| `(1,1)` | `3911/989` | 140 | `45/989` |
| `(1,2)` | `4811/989` | 122500 | `2195/8901` |
| `(2,1)` | `4740/989` | 62720 | `2834/8901` |

Unoccupied phases can be replaced by occupied phases without decreasing
the nonnegative squared load, so these are full independent-layout
maxima. The literal attaining layouts are:

| Heights | Divisor-to-residue assignment |
| --- | --- |
| `(1,1)` | `1:0, 5:2, 7:2, 35:2` |
| `(1,2)` | `1:0, 5:2, 7:2, 35:2, 49:16, 245:212` |
| `(2,1)` | `1:0, 5:2, 7:2, 25:12, 35:17, 175:87` |

For `K>=2`, retain the exact `(1,2)` block. The remaining LCM terms
have first-coordinate depth at most 1 and second-coordinate depth
greater than 2. BT8 gives their summed initial coefficient
`M_02+3M_12=234/989`. Similarly, for `H>=2` at second-coordinate
height 1, the coefficient is `M_20+3M_21=210/989`. Hence

\[
 \begin{aligned}
 \Gamma_{1,K}&\le\frac{4811}{989}
       +\frac{234}{989}\sum_{j=1}^{K-2}(2j+5)\beta^j
       \le\frac{913}{172}<2t_3,\\
 \Gamma_{H,1}&\le\frac{4740}{989}
       +\frac{210}{989}\sum_{i=1}^{H-2}(2i+5)\alpha^i
       \le\frac{644940}{119669}<2t_3.
 \end{aligned}
 \tag{BT19}
\]

The two strict margins against `2t_3=152/27` are respectively
`1493/4644` and `776308/3231063`. Since `t_1=2` and `t_h` increases,
BT19 proves all boundary comparisons with the other height at least
3. The three finite cases in the table complete BT6 for every pair
of positive heights, using the original common law throughout.

## 7. Reusable exact checks and scope

The [tail checker](../../frontier/cover-geometry/repeated_type_b_tail_bound.py)
recomputes the seed maximum using the existing nine-label oracle,
derives all nine prefix maxima directly from the seed atoms, and
checks the row, column and atom caps from the later-digit law. It
checks the exact infinite bound, nine finite cells, eight infinite
strips, the equal-height table, and the three projected seed maxima
and boundary limits. All checks remain enabled under `-O`.

```sh
python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/repeated_type_b_tail_bound.py
```

The public pure functions `finite_bound`, `strip_bound` and
`infinite_bound` accept exact nonnegative seed coefficients and caps
below one. They evaluate BT13, BT18 and BT16 for further candidate
laws. A new application must separately establish that its actual
source and common law satisfy the required seed and prefix bounds.

The all-height conclusion follows from the LCM expansion, convergent
series and the finite certificates covering all height pairs. It is
not an inference from bounded-height enumeration alone. The theorem
supplies one compatible law for BT2; it establishes neither an
all-source theorem nor the missing realization by an actual covering
system.

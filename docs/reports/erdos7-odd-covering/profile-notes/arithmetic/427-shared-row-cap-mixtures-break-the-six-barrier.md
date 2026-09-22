[Index](../../marked_head_profile.md) · [Exact architecture](425-full-six-pair-cap-mixtures-have-an-exact-laminar-dual.md) · [Previous common-law ceiling](426-retuned-tree-mixtures-give-a-smaller-general-ceiling.md)

# Shared row caps give a common-law ceiling below six

For every finite height `K>=0`, every actual source with one full
five-cap law and all six row-pair three-cap laws admits a convex
mixture of those seven laws whose complete original-divisor squared
load is at most

    C = 407237/70076 = 5.81136194988... < 6.                    (JC1)

The seven component laws may be chosen arbitrarily and fixed in
advance. The mixture weights depend on the source and these fixed
laws; they are fixed before every independently chosen layout phase.
No component is selected again in response to a layout. In
particular, the statement applies to every choice of the actual
full five-tree and six pair ternary-tree laws used in report 426.
The improvement uses free weights on all seven fixed components.

At height three the same exact certificates give the stronger bound
`146409/26585`. Consequently the required finite comparison holds
throughout the range `K>=3`:

    Gamma_(1,K) <= 2t_K = 6-2(K+2)/3^K.                       (JC2)

Indeed,

    2t_3-146409/26585 = 87877/717795 > 0,
    2t_4-C             = 76609/1892052 > 0,

and `2t_K` increases with `K`. This is an ordinary proof with exact
rational certificates, not Lean certification. The argument here
does not settle the height-two finite comparison. The height-zero
and height-one comparisons are separate low-height arguments, not
outputs of the certificates below.

## 1. Fixed actual components and the finite game

Let `S subset {1,2,3,4} times Z/7^K`. A full five-cap law `mu` is a
probability on `S` for which every depth-`j` seven-adic prefix has
mass at most `5^-j`, including the union over all four rows. For
each pair `B={r,s}`, let `eta_B` be a probability supported on the
actual points of `S` in those rows, with every depth-`j` prefix of
mass at most `3^-j`. Digits are read lowest first. All seven laws
are fixed throughout the argument. Write `beta_r=mu(row r)`.

A complete original layout `L` chooses independent phases for all
labels `7^j` and `5*7^j`, `0<=j<=K`. Divisor one is retained. Let
`f_L` be the square of the resulting indicator load. The layout
set and the seven-component game are finite. For any probability
`theta` on **whole layouts**, put

    c_i(theta)=E_(L~theta) E_(x~law_i) f_L(x).

Finite minimax gives

    min_(lambda in simplex_7) max_L sum_i lambda_i E_(law_i) f_L
       = max_theta min_i c_i(theta).                          (JC3)

Thus an upper bound on the right gives one mixture on the actual
source, fixed before all phases. This uses the finite minimax step
of report 425 but already works for any seven fixed legal laws;
it does not require minimizing separately over the cap families.
Replacing a mixed phase in absent row zero by a phase in an actual
row, at the same seven-adic prefix, only increases the pointwise
load. It therefore suffices to consider mixed rows in `{1,2,3,4}`.

## 2. Complete row words and a shared tail

Assume `K>=3` through section 3. Section 4 treats shorter words
separately when deriving the universal ceiling.

For the mixed-row word `r_0,...,r_K`, set

    n_j = #{i<j:r_i=r_j},
    w_(r,j) = (2j+3+2n_j) 1_(r_j=r) + 2 #{i<j:r_i=r}.        (JC4)

These coefficients follow by expanding the square over all ordered
pairs of original labels. Two mixed labels in different rows have
empty intersection. Every remaining intersection has depth equal
to the larger exponent; incompatible seven-adic phases only remove
terms. The pure-label coefficient is `2j+1`, and

    sum_r w_(r,j)=4j+3+2n_j <= 6j+3.                          (JC5)

The accompanying checker independently enumerates the ordered pairs
and verifies JC4 against the resulting coefficients for every
length-four word, including divisor one.

Write `S_b(K)=sum_(j=0)^K (2j+1)b^-j`. For a distribution on whole
layouts define

    rho_r = P_theta(r_0=r),
    z_r   = E_theta sum_(j=1)^3 w_(r,j)3^-j,
    T_r   = E_theta sum_(j=4)^K w_(r,j)3^-j.                  (JC6)

Simultaneously relabel rows so that `rho_1<=rho_2<=rho_3<=rho_4`.
All row words and all full-law mass vectors remain available under
this permutation. The four tail coordinates are nonnegative and
obey one shared budget:

    sum_r T_r <= 3(S_3(K)-S_3(3)).                            (JC7)

For a pair `{r,s}`, `r<s`, its two actual root row masses sum to
one. Its expected depth-zero mixed contribution is therefore at
most `3rho_s`. At positive depths each row prefix has mass at most
`3^-j`. The same actual pair law consequently satisfies

    c_rs(theta) <= S_3(K)+3rho_s+z_r+z_s+T_r+T_s.             (JC8)

The **same four `T_r`** occur in all six pair bounds. They come
from the same distribution on complete layouts. Assigning a new,
independent tail budget to each pair would discard this constraint.

For the full law, retain its actual row masses through depth two:

    F_beta(word)=sum_r sum_(j=0)^2
                       w_(r,j) min(beta_r,5^-j),
    C_F(K)=4S_5(K)-3S_5(2).

Using JC5 only on its remaining depths gives

    c_F(theta) <= C_F(K)+E_theta F_beta(word).                (JC9)

No row masses of different component laws have been identified.
JC8 uses each pair law's own normalization, whereas JC9 uses the
full law's own `beta`. All expectations still refer to one actual
source and one common `theta`.

## 3. A finite upper relaxation valid for every real beta

Retain the first four mixed rows. There are exactly `4^4=256`
possible words, and every whole-layout distribution induces a
probability on these words. Seven-adic phases have already been
bounded in JC8--JC9. For fixed `beta`, maximize `v` over this word
probability, four nonnegative `T_r`, and `v>=0`, subject to

    v <= C_F(K)+E_theta F_beta,
    v <= S_3(K)+3rho_s+z_r+z_s+T_r+T_s     (all six r<s),
    rho_1<=rho_2<=rho_3<=rho_4,
    sum_r T_r <= 3(S_3(K)-S_3(3)),
    sum_word theta_word=1.                                  (JC10)

Each actual layout distribution supplies feasible row and tail
data. Its minimum actual component price is bounded by the minimum
of these seven upper prices, hence by JC10's maximum. The tail
relaxation need not correspond to an actual layout distribution;
this only enlarges the upper bound.

To cover the entire real `beta` simplex, cut each coordinate at
`1/25` and `1/5`. On each resulting cell, `F_beta` is affine in
`beta` for fixed `theta`. The pair bounds do not depend on `beta`.
If `P` denotes their minimum, then for fixed `theta,T` and one cell,

    max_beta min(C_F+E_theta F_beta, P)
       = min(max_beta(C_F+E_theta F_beta), P).                (JC11)

The inner affine maximum occurs at a cell vertex. Maximizing also
over `theta,T` commutes with the resulting finite maximum over
vertices. This proves the reduction; it does not assume that the
optimized value of JC10 is convex in `beta`.

At a cell vertex at least three coordinates lie in
`{0,1/25,1/5,1}`. Exactly one coordinate is at least `2/5`; the
other three independently belong to `{0,1/25,1/5}`. Thus there are
exactly `4*3^3=108` vertices. The checker regenerates this complete
set rather than accepting a supplied list of vertices.

## 4. The same 108 exact duals at finite and infinite-tail bounds

The constraint coefficients in JC10 depend only on the 256 words
and a beta vertex. Height enters only through the three constants
`S_3(K)`, the shared tail budget, and `C_F(K)`. Their values are

| Bound used | `S_3` | Shared tail budget | `C_F` |
| --- | ---: | ---: | ---: |
| `K=3` | `76/27` | `0` | `253/125` |
| `K=4` | `79/27` | `1/3` | `1301/625` |
| Infinite series upper bound | `3` | `5/9` | `21/10` |

The last row is an upper bound for every finite `K>=3`, obtained
from `S_3(infinity)=3` and `S_5(infinity)=15/8`. It does not posit
an infinite source or an infinite minimax game.

For `K<3`, append arbitrary rows to each original word until its
length is four, and set every `T_r=0`. All added coefficients are
nonnegative. The infinite-series pair constant `3` dominates
`S_3(K)`, and its full-law constant `21/10` dominates
`S_5(K)<=S_5(2)=9/5`. Thus JC8--JC9 with the last table row still
upper-bound the original shorter-layout prices. This extends JC1
to these heights without adding any labels to the actual game;
the sharper low-height finite targets remain separate.

For each beta vertex, the checker retains six nonnegative pair
multipliers `p_rs`, three nonnegative root-order multipliers `a_r`,
a nonnegative tail multiplier `u`, a nonnegative full-law
multiplier `b`, and an unrestricted normalization multiplier `q`.
It checks all of the following exactly:

- For every word, `q+sum_r a_r(1_(r_0=r)-1_(r_0=r+1))` is at
  least the sum of its six pair price coefficients weighted by
  `p_rs`, plus `b F_beta(word)`.
- For each row `r`, `u>=sum_(pairs containing r) p_rs`.
- `sum_(r<s) p_rs+b>=1`.

These are all 256 word columns, four shared-tail columns, and the
value column of the dual inequality. They certify

    v <= q+S_3 sum_(r<s) p_rs
             +3(S_3-S_3(3))u+C_F b.                         (JC12)

All `108*261=28188` column inequalities are checked with exact
fractions. The same 108 duals give

| Bound used | Maximum of the 108 certified upper values |
| --- | ---: |
| `K=3` | `146409/26585` |
| `K=4` | `1716541/301925` |
| Infinite series upper bound | `407237/70076` |

For example, at an infinite-bound maximizing vertex
`beta=(1/5,0,1/5,3/5)`, in pair order
`12,13,14,23,24,34`, the complete certificate is

    (p_12,p_13,p_14,p_23,p_24,p_34)
          = (63963,0,0,37728,0,0)/245266,
    (a_1,a_2,a_3)=(16714,0,0)/245266,
    u=101691/245266, b=143575/245266,
    q=762254/245266.                                        (JC13)

The stored certificates establish upper bounds; no claim that JC1
is optimal, attained by an actual source, or sharp for the
seven-component architecture is made. Combining JC3, JC10 and
JC12 proves JC1 for all finite heights and JC2 for `K>=3`.

## 5. A precise height-two boundary of this price relaxation

Keeping the root row masses of a pair law coupled to its later
row caps gives the stronger pair upper price

    P_rs(theta)=S_3(2)+max_(0<=gamma<=1)
      sum_(j=0)^2 [E_theta w_(r,j) min(gamma,3^-j)
                  +E_theta w_(s,j) min(1-gamma,3^-j)].       (JC14)

The maximum is attained at one of
`0,1/9,1/3,2/3,8/9,1`. Even this refinement, together with the full
law's exact row-cap upper price through depth two, does not prove
the required `46/9`. Take

    beta=(1/25,1/5,1/5,14/25),
    theta(2,2,2)=5/16, theta(3,3,3)=5/16,
    theta(4,4,1)=3/8.

Its full relaxed price is `1029/200`. The six prices in JC14,
in pair order `12,13,14,23,24,34`, are

    185/36, 185/36, 185/36, 923/144, 917/144, 917/144.

Their minimum with the full price is

    185/36 = 46/9+1/36.                                     (JC15)

The checker verifies the stated distribution, all six breakpoints
for each pair, and every exact price. This is an obstruction to
this **upper-price relaxation**. It is not an actual source or a
lower bound on the actual seven-component game, and does not refute
the height-two target. That target requires additional information
beyond these separately bounded row-cap prices.

## 6. Reusable exact verification

The associated standard-library program is
[`joint_row_cap_common_law.py`](../../frontier/cover-geometry/joint_row_cap_common_law.py).
It regenerates all beta vertices and row words, reconstructs the
original-label coefficients, checks every rational dual column,
evaluates the three sets of constants, and verifies the height-two
relaxation boundary. It contains no numerical optimizer and writes
only its result to stdout. Its row indices `0,1,2,3` correspond to
the mathematical rows `1,2,3,4` above.

```sh
python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_row_cap_common_law.py --compact
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_row_cap_common_law.py --compact
```

Both modes verify the same exact results. The formal scope remains
an ordinary all-height analytic argument plus a complete rational
case split. Neither the finite enumeration alone nor the existence
of a numerical optimizer is used as an all-height proof.

The source comparison retains five-height one and arbitrary seven-height.
It does not bound the additional load and cross terms from deeper powers
of five, or supply the joint transport required for arbitrary prime
supports. Unrestricted Erdős #7 remains unresolved.

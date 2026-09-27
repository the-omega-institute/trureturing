[Index](../../marked_head_profile.md) · [Root theorem](390-two-prime-root-blockers-admit-a-common-second-moment-law.md) · [Product-tree condition](376-complete-prime-chain-transport-and-joint-prefix-laws.md)

# Diagonal prefix sources obstruct the finite-height moment comparison

The full-height product-tree and one-coordinate tree conditions do not,
by themselves, extend report 390's root bound to the proposed finite-height
independent comparison. An explicit source at heights `(2,2)` has optimal
complete-layout second moment `33/5`, exceeding the proposed `529/81`.
The lower bound holds for **every** probability on that source, with all
original divisor labels and freely assigned divisor residues retained.

This source uses all five first-5 roots. It therefore does not refute
the more restrictive excluded-root problem arising in the normalized
extremal-cover model. No realization as an actual minimum odd-cover
residual is asserted. These are ordinary proofs and exact rational
controls, not Lean-certified results or a resolution of Erdős #7.

## 1. Literal diagonal digits and both tree obstructions

For `h>=1` and `u=(u_0,...,u_(h-1))` in `{0,1,2,3,4}^h`, set

\[
 x(u)=\sum_{j=0}^{h-1}u_j5^j,\qquad
 y(u)=\sum_{j=0}^{h-1}u_j7^j,\qquad
 R_h=\{(x(u),y(u)):u\in\{0,\ldots,4\}^h\}.
 \tag{DM1}
\]

The carrier is `Z/5^h x Z/7^h`, identified with `Z/35^h` by CRT.
The source contains exactly `5^h` points. Trees and prefixes use
lowest digits first throughout.

Take any complete ternary subtree in the 5-coordinate and any complete
five-ary subtree in the 7-coordinate, both of depth `h`. At a pair of
nodes reached by the same digit prefix, their chosen next digits are
a three-element subset of `{0,...,4}` and a five-element subset of
`{0,...,6}`. They intersect, because `3+5>7`. Choose a common digit
and repeat. After `h` choices the two selected leaves form a point
of `R_h`. Thus `R_h` meets every required product of trees.

The 7-projection of `R_h` consists of all words with digits in
`{0,...,4}`. It meets every complete ternary 7-tree: at each node
the three chosen children intersect these five allowed children.
The 5-projection is the entire 5-tree, so the separate ternary
5-tree condition also holds. All of these are full-height statements,
not only cardinality tests on the roots.

## 2. An exact full-layout minimax value

Write `Q_h=5^h 7^h`. A layout independently chooses a residue `b_d mod d`
for every divisor `d|Q_h`, including one. Define

\[
 L_b(z)=\sum_{d\mid Q_h}\mathbf1_{z=b_d\bmod d},\qquad
 \Gamma_{Q_h}(\nu)=\max_b\mathbb E_\nu L_b^2.
\]

Then

\[
 \boxed{\inf_{\nu\text{ supported on }R_h}\Gamma_{Q_h}(\nu)
 =S_h:=\sum_{a,b=0}^h(2a+1)(2b+1)5^{-\max(a,b)}
 =\sum_{t=0}^h\frac{(t+1)^4-t^4}{5^t}.}
 \tag{DM2}
\]

**Upper bound under one law.** Give all `5^h` source points equal mass.
A cylinder of modulus `5^a 7^b` either has inconsistent digit demands,
uses a 7-digit outside `{0,...,4}`, or fixes exactly `max(a,b)` common
digits. Its mass is therefore zero or `5^(-max(a,b))`.

Expand a full layout square into ordered pairs of divisor indicators.
For exponents `(a,b)` and `(c,d)`, the intersection is empty or one
cylinder with exponents `(max(a,c),max(b,d))`. Its mass is at most
`5^(-max(a,b,c,d))`, regardless of phase compatibility. There are
`(t+1)^4-t^4` ordered exponent quadruples with maximum `t`. Summing
these bounds gives `Gamma<=S_h`. One layout centered at any point
of `R_h` makes every intersection consistent and attains all bounds.
Thus the uniform law has `Gamma=S_h` for the full independent maximum.

**Lower bound for every law.** For each center `v` in `R_h`, choose the
particular layout `b_d=v mod d` for every original divisor. For a fixed
source point `z`, average the squared load of these layouts over the
uniformly chosen center `v`. For each ordered pair of divisors, the
fraction of centers agreeing with `z` on both demands is exactly
`5^(-max(a,b,c,d))`. Hence this averaged squared load is `S_h` at
every `z`. For an arbitrary supported probability `nu`, finite summation
therefore gives

\[
 \frac1{5^h}\sum_{v\in R_h}\mathbb E_\nu L_v^2=S_h.
 \tag{DM3}
\]

At least one of these fixed layouts has expectation at least `S_h`.
It is an admissible layout in the full maximum, proving `Gamma>=S_h`
for every `nu`. Centered layouts are used as an exact lower certificate;
the upper bound already covers incompatible layouts. No restriction
of the definition of `Gamma` has been made.

The final identity in DM2 counts the same exponent quadruples in two
ways: `(2a+1)` ordered pairs have maximum `a`, and their combined
four-coordinate maximum is `max(a,b)`.

## 3. Finite-depth failure and its exact scope

The proposed independent comparison with prefix bases `(3,3)` is

\[
 T_h=\left(1+\sum_{a=1}^h(2a+1)3^{-a}\right)^2
     =\left(3-\frac{h+2}{3^h}\right)^2.
 \tag{DM4}
\]

Already at `h=2`, DM2 gives

\[
 S_2=1+\frac{15}{5}+\frac{65}{25}=\frac{33}{5},
 \qquad
 T_2=\left(1+1+\frac59\right)^2=\frac{529}{81},
 \qquad
 S_2-T_2=\frac{28}{405}>0.
 \tag{DM5}
\]

So no choice of probability can prove `Gamma<=T_2` for this source,
despite both full-height tree conditions. The next finite values are:

| Height | Optimal `S_h` | Comparison `T_h` | `S_h-T_h` |
| ---: | ---: | ---: | ---: |
| 1 | `4` | `4` | `0` |
| 2 | `33/5` | `529/81` | `28/405` |
| 3 | `8` | `5776/729` | `56/729` |
| 4 | `5369/625` | `6241/729` | `13376/455625` |

This failure is not monotone in height. At height five the difference
is `-4220216/184528125`. Moreover

\[
 \sup_h S_h=\frac{285}{32}=9-\frac3{32}<9=\lim_h T_h.
 \tag{DM6}
\]

DM6 is the existing Haar fourth-moment series `F4(5)` from
[report 18](../001-064/18-actual-bb-kernels-with-fixed-old-second-moment-need-not-be-uniformly-continuous.md#the-haar-fourth-moment-and-the-original-label-transfer).
Its application here comes from the exact two-coordinate diagonal
minimax identity DM2. The example does not refute a constant bound
of nine for all abstract sources.

At height one the source is the five-point matching already covered
by report 390. At greater heights the two coordinates' higher digits
are equal digit by digit and are strongly correlated. They are not
independent uniform higher digits, so report 390's uniform-tail bound
does not apply. Its valid root theorem remains unchanged.

The present refutation excludes one proposed inference from the stated
abstract tree tests alone. It neither rules out a stronger arithmetic
argument using actual original residues and minimum-cover structure,
nor settles the subclass with a missing first-5 root. In particular
no root permutation can remove a root from `R_h`: all five are active.

## 4. Exact controls

The [standard-library checker](../../frontier/cover-geometry/diagonal_prefix_second_moment.py)
checks all 210 local three-by-five child-set pairs and all 35 standalone
ternary 7-child sets. These local exhaustive checks support the recursive
proof in section 1; the program does not enumerate all full-height trees.
At heights one, two and three it constructs literal source points and
every original divisor, verifies all nonempty cylinder masses, and
checks the centered-load average independently at every source point.
The resulting constant vector is DM3's finite dual certificate for
all supported laws, not a test of one optimized probability.
Exact rational arithmetic also checks the table, the height-five reversal,
and the reused limiting series value.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/diagonal_prefix_second_moment.py
```

The general minimax statement and all-height tree intersection follow
from the proofs above. No finite enumeration is used to claim the
unrestricted Erdős problem or the excluded-root extension is decided.

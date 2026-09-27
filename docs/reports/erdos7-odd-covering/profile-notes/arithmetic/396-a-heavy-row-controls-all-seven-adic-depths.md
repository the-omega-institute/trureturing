[Index](../../marked_head_profile.md) · [Tree duality](375-deep-prime-prefix-projections-and-tree-contraction.md) · [Root laws](395-root-rectangle-blockers-need-no-standalone-projection-condition.md) · [Repeated sources](393-two-digit-seed-controls-repeated-type-b-sources-at-all-heights.md)

# A heavy row controls all seven-adic depths

Suppose a source has four available nonzero 5-rows, one row contains
a complete five-ary 7-tree, and the union of every pair of the other
three rows contains a complete ternary 7-tree. At every 7-depth
`K>=2`, an explicit single supported probability satisfies the full
independent-divisor second-moment comparison. The tree choices and
their leaf labels may vary arbitrarily with depth and prefix. No
Cartesian product or repeated root pattern is required.

The proof retains the incompatibility between events in the designated
row and events in the other rows. A finite dynamic program bounds the
first three depths; a geometric tail then handles all remaining depths.
These are ordinary mathematical proofs and exact rational checks, not
Lean-certified results. The designated-row premise is an additional
condition, not a consequence established for arbitrary residuals of an
odd covering. Unrestricted Erdős #7 remains open.

## 1. Source and one common probability

Fix `K>=2` and let

\[
 R\subseteq\{1,2,3,4\}\times\mathbb Z/7^K,\qquad
 N_i=\{y:(i,y)\in R\}.
 \tag{HR1}
\]

Use base-7 digits from lowest to highest. A complete `b`-ary tree of
depth `K` selects exactly `b` children at each selected nonleaf.
Assume:

1. `N_4` contains a complete five-ary tree of depth `K`.
2. Each `N_i union N_j`, for `1<=i<j<=3`, contains a complete ternary
   tree of depth `K`.

For a source meeting every ternary-5 by five-ary-7 product tree, the
second premise follows from tree duality: use the three 5-roots
`{0,i,j}`; since row zero is absent, `N_i union N_j` meets every
five-ary 7-tree and therefore contains a ternary tree. This implication
does not supply the first premise.

Choose one five-ary tree in `N_4` and give each of its `5^K` leaves
mass `5^-K` in row 4, obtaining `nu_F`. For each weak pair `{i,j}`,
choose a ternary tree in `N_i union N_j` and label each leaf by one
available row in that pair. Uniform mass on its `3^K` labelled leaves
is a probability on the actual source. Average the three pair laws
to obtain `nu_W`, and put

\[
 \nu=\tfrac12\nu_F+\tfrac12\nu_W.
 \tag{HR2}
\]

Every layout below is tested against this same probability. For all
`0<=j<=K` and every 7-prefix of depth `j`, simultaneously:

\[
 \begin{aligned}
 \nu(\text{prefix})&\le m_j=\tfrac12(3^{-j}+5^{-j}),\\
 \nu(\text{row }4,\text{ prefix})&\le f_j=\tfrac12 5^{-j},\\
 \nu(\text{row }i,\text{ prefix})&\le w_j=\tfrac13 3^{-j}
                      &&(i=1,2,3).
 \end{aligned}
 \tag{HR3}
\]

A selected tree prefix contains exactly the corresponding fraction of
the uniformly weighted leaves. Labeling leaves only decreases the mass
assigned to a particular row. Each weak row occurs in two of the three
pair laws, giving the factor `(1/2)(2/3)=1/3` in `w_j`.

CRT identifies HR1 with residues modulo `Q=5*7^K`. For independent
residues `a_d mod d` at **every** divisor `d|Q`, including `d=1`, set

\[
 \Gamma_{1,K}(\nu)=\max_{(a_d)_{d\mid Q}}
      \mathbb E_\nu\left(\sum_{d\mid Q}
                       1_{x\equiv a_d\pmod d}\right)^2.
 \tag{HR4}
\]

No compatibility between the selected residues is imposed. The result is

\[
 \Gamma_{1,K}(\nu)<2t_K,\qquad
 t_K=1+\sum_{j=1}^K(2j+1)3^{-j}
    =3-\frac{K+2}{3^K},\qquad K\ge2.
 \tag{HR5}
\]

## 2. Preserve row incompatibility in the layout bound

Write `P_j` for the chosen `7^j`-event and `Q_j` for the chosen
`5*7^j`-event, `0<=j<=K`; thus `P_0=1`. A `Q_j` whose 5-root is
absent may be replaced by any supported such event without decreasing
the nonnegative squared load. Classify its row as `F` (row 4) or `W`
(one of rows 1, 2, 3).

Two `Q` events of different classes have zero intersection. Two events
in different actual weak rows also have zero intersection; replacing
that zero by a weak-row bound only increases an upper estimate. No
literal modulus or independently chosen phase is removed by this step.

For a class word `c=(c_0,...,c_K)`, set `b_F,j=f_j` and `b_W,j=w_j`.
Expanding all ordered pairs of indicators, and bounding a nonempty
intersection at the larger prefix depth, gives the envelope

\[
 B(c)=\sum_{i,j=0}^K\left[
 m_{\max(i,j)}+b_{c_i,\max(i,j)}+b_{c_j,\max(i,j)}
 +1_{c_i=c_j}b_{c_i,\max(i,j)}\right].
 \tag{HR6}
\]

The four summands correspond respectively to `P_i P_j`, `Q_i P_j`,
`P_i Q_j`, and `Q_i Q_j`. In particular `Gamma<=max_c B(c)`.
This is an upper bound: its individual caps need not be attained
simultaneously by any actual layout.

The envelope has a dynamic program. Before assigning depth `j`, let
`u` be the number of earlier `F` choices and `v=j-u`. The common
increment from `P_i P_j` terms is `(2j+1)m_j`. The remaining increments
for the next choice are

\[
 \begin{aligned}
 D_F(j,u)&=(2j+3+4u)f_j+2v w_j,\\
 D_W(j,u)&=2u f_j+(2j+3+4v)w_j.
 \end{aligned}
 \tag{HR7}
\]

To verify the coefficients, the new diagonal contributes three
row-prefix terms. Each earlier `F` contributes two additional `f_j`
terms regardless of the new choice; the new `F` event contributes
`2j f_j`, plus `2u f_j` from its same-row intersections. The `W`
calculation is identical. Counts of earlier classes therefore suffice;
the earlier word still determines the accumulated score but not the
next increment.

## 3. The exact three-depth envelope

At depths `0,1,2`, HR6 or HR7 gives:

| Class word | Envelope |
| --- | --- |
| `FFF` | `439/90` |
| `FFW` | `3319/675` |
| `FWF` | `3191/675` |
| `FWW` | `6589/1350` |
| `WFF` | `2831/675` |
| `WFW` | `5869/1350` |
| `WWF` | `6029/1350` |
| `WWW` | `71/15` |

Thus the complete depth-at-most-two block, for the same law at any
`K>=2`, is bounded by

\[
 B_2=\frac{3319}{675}<2t_2=\frac{46}{9},\qquad
 2t_2-B_2=\frac{131}{675}.
 \tag{HR8}
\]

The maximizing class word is an envelope certificate, not a claim of
an attaining arithmetic layout or the minimax value of this source.

## 4. All later depths

For an LCM 7-depth `j`, there are `2j+1` ordered exponent pairs.
For each pair, one product is `P P` and three are `P Q`, `Q P`, `Q Q`.
For `j>=1`, `f_j<=w_j`. Consequently the total at LCM depth `j>=3`
is at most

\[
 (2j+1)(m_j+3w_j)
 =(2j+1)\left(\tfrac32 3^{-j}+\tfrac12 5^{-j}\right).
 \tag{HR9}
\]

Retain HR8 as a whole and add only these later terms:

\[
 \Gamma_{1,K}(\nu)\le U_K
 =\frac{3319}{675}
   +\sum_{j=3}^K(2j+1)
          \left(\tfrac32 3^{-j}+\tfrac12 5^{-j}\right).
 \tag{HR10}
\]

The comparison is exact at every finite height:

\[
 2t_K-U_K=\frac{131}{675}
   +\tfrac12\sum_{j=3}^K(2j+1)(3^{-j}-5^{-j})>0.
 \tag{HR11}
\]

This proves HR5 without inference from a finite range of heights.
For `0<z<1`, the tail identity

\[
 \sum_{j\ge n}(2j+1)z^j
 =z^n\left(\frac{2n+1}{1-z}+\frac{2z}{(1-z)^2}\right)
 \tag{HR12}
\]

also gives

\[
 U_\infty=\frac{60709}{10800}<6,\qquad
 6-U_\infty=\frac{4091}{10800}.
 \tag{HR13}
\]

## 5. Boundary and verification scope

At `K=1` the stated source conditions imply the rectangle-blocker
hypothesis: every weak pair has at least three neighbors, and every
pair using row 4 has at least five. The root theorem of report 395
supplies a law with `Gamma<=4=2t_1`. This need not be HR2: its root
envelope can be `21/5`. Thus the theorem supplies a law at every
positive height, but does not assert that those laws form a single
projectively compatible process. At each fixed height, HR2 is one
common law for all divisor labels and all layouts.

The [exact envelope checker](../../frontier/cover-geometry/row_class_layout_envelope.py)
provides a reusable dynamic program for arbitrary nonnegative rational
plain-prefix and two row-class cap arrays. It returns the maximum of
HR6 and a maximizing class word. Its independent checker enumerates
literal ordered `P/Q` label pairs rather than using the recurrence.
It checks all eight values above, the root boundary, finite tail
identities, and the infinite constants. Checks remain active under `-O`.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/row_class_layout_envelope.py
```

For other sources, cap arrays require a proof from one actual supported
law; the program supplies no such law. Nor does this result establish
the designated-row premise for a general blocker. It removes dependence
on a repeated source geometry while retaining that explicit premise.

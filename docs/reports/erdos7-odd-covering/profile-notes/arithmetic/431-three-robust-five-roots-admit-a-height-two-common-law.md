[Index](../../marked_head_profile.md) · [Root rectangle laws](395-root-rectangle-blockers-need-no-standalone-projection-condition.md) · [Root constructions](390-two-prime-root-blockers-admit-a-common-second-moment-law.md) · [The other height-two orientation](429-phase-conflict-cap-flow-closes-the-height-two-bound.md)

# Three robust five-roots admit a height-two common law

At heights `H5=2,K7=1`, an actual source with three robust first-five
root fibres admits one supported law controlling all six independent
original labels by `46/9`. A root fibre is robust when its child-by-seven
support meets every three-by-five rectangle. The construction selects
one law inside each of three such fibres, then mixes them with equal
weights. It does not require a standalone seven-projection condition.

The proof reuses the classification and supported laws of report 395,
changes the law on the transpose of type A, and checks a simultaneous
sixteen-entry local bound. This is a general source theorem for the
stated subclass, not a proof for every height-two product-tree blocker
or a claim that these sources arise from minimal odd covers. The proof
and exact arithmetic checks are not Lean-certified.

## 1. Source, labels and statement

Write a point as `(r,a,y)`, where `x=r+5a mod 25`, with
`r,a in Z/5` and `y in Z/7`. For a source `S`, put

\[
 R_r=\{(a,y):(r,a,y)\in S\}.
\]

Call `r` robust if `R_r` meets every `A x D` with `|A|=3,|D|=5`.
Equivalently, for every five-column set `D`, at least three child
rows of `R_r` meet `D`. No conditional law has yet been chosen in this
definition: it concerns the actual support.

The full load, with every displayed phase independent, is

\[
 \begin{aligned}
 L(r,a,y)={}&1+1_{r=r_1}+1_{(r,a)=(r_2,a_2)}+1_{y=b_0}\\
            &+1_{(r,y)=(r_3,b_1)}
             +1_{(r,a,y)=(r_4,a_4,b_2)}.
 \end{aligned}                                                    \tag{RF1}
\]

These are exactly the original labels `1,5,25,7,35,175`. Let
`Gamma(nu)=max E_nu L^2` over all of their phases. Then

\[
 \boxed{\quad
 \text{If three distinct roots are robust, some law supported on }S
 \text{ satisfies }\Gamma(\nu)\le\frac{46}{9}.
 \quad}                                                          \tag{RF2}
\]

The three roots can be any actual roots. In particular the theorem
applies when root zero has been excluded and three of the four allowed
roots are robust. Additional source points receive zero mass.

## 2. A local bound that retains the inherited seven label

In a selected root fibre, use the mask bits `(P1,M1,P2,M2)` for the
labels `(5,35,25,175)` whose root phases enter that fibre. The global
label `7` is present in every fibre. Set

\[
 c=1+P1,\qquad t=1+M1,\qquad e=P2,\qquad f=M2.
\]

For a supported law `mu`, the local maximum is

\[
 F_\mu(M)=\max_{b,u,v,d}
  \mathbb E_\mu\bigl(c+t1_{y=b}+e1_{a=u}
                              +f1_{(a,y)=(v,d)}\bigr)^2.           \tag{RF3}
\]

Combining the two column indicators when `M1=1` preserves the maximum;
it does not impose consistency on the original phases. To see this,
fix the rest of the load `A=c+e1_{a=u}+f1_{(a,y)=(v,d)}` and write
`g_b=E((2A+1)1_{y=b})`. Distinct column choices `b,b'` add
`g_b+g_b'` to `E A^2`. Taking both indicators at the column with the
larger `g` gives at least that increment, with the additional
nonnegative term `2 mu(y=b)`. Coincident choices were already allowed.
The maximization over `u,v,d` remains unrestricted.

For row masses `rho`, column masses `sigma` and atom masses `w`, the
literal expansion in (RF3) is

\[
 \begin{aligned}
 c^2+t(2c+t)\sigma_b+e(2c+1)\rho_u+2tew_{ub}
 +f(2c+1+2t1_{d=b}+2e1_{v=u})w_{vd}.
 \end{aligned}                                                    \tag{RF4}
\]

Consequently simultaneous row, column and atom caps `(alpha,beta,gamma)`
give the following bound under that same law, for every mask:

\[
 F_\mu(M)\le c^2+t(2c+t)\beta+e(2c+1)\alpha
                  +\bigl(2te+f(2c+1+2t+2e)\bigr)\gamma.           \tag{RF5}
\]

## 3. One local law for every robust fibre

Use the constructions of report 395. The following four families
suffice for all its generic cases; `(N,A,B)` denotes simultaneous
caps `alpha=A/N,beta=B/N,gamma=1/N`:

\[
 (9,3,3),\qquad(8,3,2),\qquad(7,2,2),\qquad(5,1,1).               \tag{RF6}
\]

Here is the complete coverage of that report's reductions.

| Actual fibre case | Supported law used here |
| --- | --- |
| Three active child rows | Nine selected points, family `(9,3,3)` |
| Four active rows: A or cycle4 | Uniform law, family `(8,3,2)` |
| Four active rows: C, D, F or singleton_triangle | Uniform law, family `(7,2,2)` |
| Four active rows: triangle_full or two_triples | Uniform law, family `(9,3,3)` |
| Four active rows: B or A_shared | The explicit weighted law of report 395 |
| Five active rows, at least five active columns | Report 390's matching or Hall-defect construction: `(5,1,1)`, `(7,2,2)`, B, or `(8,3,2)` |
| Five active rows, three active columns | Nine selected points, family `(9,3,3)` |
| Five active rows, four active columns | Transpose the four-row classification, as described below |

For the last case, only types with at most five active columns can
occur before transposing back. They are A, B, C, cycle4, triangle_full,
two_triples, singleton_triangle and A_shared. Transposing B and A_shared
gives two further explicit weighted laws. The remaining transposes fit
the symmetric cap families in (RF6), except A. The transposed cycle4
still fits `(8,3,2)` since both its row and column degrees are two.
Types D and F have six and seven active columns and cannot occur in
this reduction to five child rows.

For transposed A, use the following law, with point coordinates
`(child,column)` numbered from zero:

| Point | `(0,0)` | `(1,1)` | `(2,1)` | `(0,2)` | `(1,2)` | `(2,2)` | `(3,3)` | `(4,3)` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Mass times 36 | 6 | 3 | 3 | 4 | 4 | 4 | 6 | 6 |

All points belong to the transposed A support and the masses sum to
one. Its row-mass numerators are `(10,7,7,6,6)` and its column-mass
numerators are `(6,6,12,12)`. In particular its column cap is `1/3`.
The uniform eight-point transposed law would instead have column cap
`3/8` and fails the required common envelope; the changed weights
are necessary for this construction.

This failure is visible on an original layout. Take three aligned
copies of the transposed A support and their uniform 24-point law.
Concentrate the root phases of all four positive-five labels in the
first root, with both child phases zero and all seven phases equal
to column two. The selected root contributes `93/8` and each other
root contributes `17/8` before the outer factor `1/3`. Thus this law
has a layout price

\[
 \frac{93+17+17}{24}=\frac{127}{24}
                    =\frac{46}{9}+\frac{13}{72}.
\]

The weighted construction above supplies a successful law on the
same source. This example distinguishes the choice of law from the
existence of an admissible law.

Applying (RF5) to the four cap families, and (RF4) to B, A_shared,
their transposes and the changed transposed A law, gives one envelope
valid simultaneously for all these chosen laws. In increasing binary
mask order, with `P1` the least significant bit, it is

| Mask | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `B(M)` | 2 | 17/3 | 11/3 | 8 | 29/9 | 68/9 | 46/9 | 91/9 |

| Mask | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `B(M)` | 17/6 | 41/6 | 29/6 | 19/2 | 4 | 77/9 | 19/3 | 34/3 |

These are bounds for all sixteen masks under a single chosen fibre
law, rather than separately selected laws for different masks. The
exact checker evaluates the explicit laws by integer arithmetic and
also exhausts the independent, unmerged column phases.

## 4. Uniform mixing across the actual roots

Choose one of the preceding laws `mu_i` in each of three robust roots
and let `nu=(mu_1+mu_2+mu_3)/3`, with each law embedded in its actual
root. For any original complete layout, let `M_i` collect its four
positive-five labels whose root phases enter root `i`. These masks
are disjoint. If a label's root phase lies outside the three chosen
roots, its indicator vanishes on the law; adding that label to any
one selected mask can only increase the local maximum. Thus it
suffices to consider the `3^4=81` complete allocations.

For every partition `M_1 disjoint-union M_2 disjoint-union M_3={0,1,2,3}`,
the displayed table satisfies

\[
 B(M_1)+B(M_2)+B(M_3)\le\frac{46}{3}.                            \tag{RF7}
\]

Equality occurs only at the three permutations of `(15,0,0)`.
The local estimates then give, for every layout under the same `nu`,

\[
 \mathbb E_\nu L^2
 \le\frac{B(M_1)+B(M_2)+B(M_3)}3\le\frac{46}{9}.
\]

This proves (RF2). No axes have been exchanged, no independent
conditional tails have been postulated, and all phases in (RF1)
remain independent.

## 5. Consequence for product-tree sources and the remaining case

Suppose root zero is excluded and the source meets every complete
ternary depth-two five-tree times every five-element seven-root set.
For a deleted column pair `E`, put `D=(Z/7) minus E`. Call root `r`
bad for `E` if at most two of its child rows meet `D`, and write
`B_r` for its set of bad pairs. There are 21 pairs.

The product-tree condition is equivalent to at least three of the
four allowed roots being good for each pair. Indeed, for fixed `D`,
a root whose projection has at most two children can be avoided by
a ternary child choice; if two allowed roots are bad, root zero and
those two roots form an avoiding ternary root choice. Conversely,
with at least three good roots, every ternary root choice includes
a good root, and every ternary child choice there meets the projection.
Equivalently the four sets `B_r` are pairwise disjoint.

A robust root is exactly one with `B_r` empty. Thus (RF2) applies
whenever at least three of these sets are empty. In particular, if
one allowed root is bad for every pair, the other three sets must be
empty. An empty allowed root is one instance of this condition, so
every such source with only three active allowed roots is covered.

Pairwise disjointness alone does not say that three sets are empty.
Sources with fewer than three robust roots remain outside this
theorem, including configurations in which all four roots have
nonempty, disjoint bad sets. A standalone seven-projection condition
does not enter the proof above and has not been used to settle that
remaining case.

For an explicit boundary witness, in each allowed root `r=1,2,3,4`
give child zero the two neighbors `{0,r}`, give children one and two
the three neighbors `{0,1,2}`, and leave the other children empty.
This source has 32 points and five active seven columns. The bad set
of root `r` is precisely the singleton `{ {0,r} }`: each of the two
three-neighbor children meets every five-column set, while child zero
is missed exactly when its two neighbors are deleted. The four bad
sets are disjoint, so the source passes the product-tree and
standalone tests, but none of its roots is robust. This demonstrates
the scope gap, not a failure of the desired `46/9` bound or realization
as a minimal-cover residual.

## 6. Sharpness in the stated class and verification

The constant in (RF2) is sharp without a standalone seven condition.
Take

\[
 S=\{(r,a,y):r\in\{1,2,3\},\ a\in\{0,1,2\},\ y\in\{0,1,2\}\}.
\]

Every selected root fibre is a three-by-three complete rectangle,
hence robust. For each of the 27 source points choose the complete
layout whose six phases are all centered there. Averaging the squared
loads of these layouts, at any fixed source point, gives

\[
 \left(1+\frac33+\frac59\right)
 \left(1+\frac33\right)=\frac{46}{9}.
\]

Indeed the centered load factors as
`(1+1_{same root}+1_{same root and child})(1+1_{same column})`.
The layout average therefore bounds every supported law's worst
layout below by `46/9`, while (RF2) supplies the matching upper bound.
This example has only three seven columns, so it does not establish
sharpness in the narrower class requiring five seven columns.

The [standard-library checker](../../frontier/cover-geometry/three_robust_roots_common_law.py)
imports the ten support types from report 395's checker. It checks
the four generic cap families, all ten original laws and eight
admissible transposes, including the changed transposed A law. It
evaluates 435456 original independent local phase choices and 108864
merged choices, confirms equality of the two maxima for every law
and mask, and checks all 81 root allocations. It also checks the 21
deleted-column pairs for the boundary witness and all 729
point/layout entries in the sharpness certificate. Literal CRT
residues verify both the sharpness calculation and the failing
uniform transposed A control. Checks remain enabled under `-O`:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/three_robust_roots_common_law.py
```

The classification and Hall reductions are the existing theorems of
reports 395 and 390. The new conclusion is their strengthened local
functional construction and its height-two assembly under three
actual robust roots. It does not resolve the unrestricted height
bridge or Erdős #7.


## 7. The fixed terminal-law recipe does not extend unchanged to every height

The same terminal choices, uniformly mixed over a ternary prefix tree,
need not give the analogous target at arbitrary five height. This is
a failure of that prescribed law, not of free source-law existence.
Let

\[
 t_H=\sum_{j=0}^H\frac{2j+1}{3^j},\qquad H\ge2,\qquad h=H-1.
\]

Take prefix leaves in `{1,2,3} times {0,1,2}^{h-1}`, each with mass
`3^{-h}`. At each leaf except `f`, use the uniform nine-point terminal
law on children `{0,1,2}` and seven columns `{0,1,2}`. At `f` use
the section-3 transposed-A law with columns relabelled as follows:

| `(child,column)` | `(0,1)` | `(1,2)` | `(2,2)` | `(0,3)` | `(1,3)` | `(2,3)` | `(3,0)` | `(4,0)` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Mass times 36 | 6 | 3 | 3 | 4 | 4 | 4 | 6 | 6 |

Every terminal support still meets every three-by-five rectangle.
Let `e=(1,0,...,0)` and let `f` be its sibling obtained by replacing
the last prefix digit by one. For `H=2`, use `e=(1)` and `f=(2)`.
Initially center every original divisor label `5^j` and `7*5^j`,
`0<=j<=H`, at `e`'s child zero and seven column zero. With all
terminal laws uniform nine-point, the price is `2t_H`: the five
prefix load has second moment `t_H`, and the independent column
factor has second moment two.

Move only the deepest mixed label to `f`'s child three and column
zero. Under the original uniform terminal law this new point is
absent. Removing the old hit loses

\[
 (4H+3)3^{-(H+1)},
\]

since its mass is `3^{-(H+1)}` and its other-label load is `2H+1`.
Now change only the terminal law at `f` to the displayed A transpose.
Without the moved label its load there is
`(H-1)(1+1_{y=0})`. Both terminal laws give column zero mass `1/3`,
so that part of the second moment is unchanged. The new marked
atom has total mass `1/(6*3^{H-1})` and other-label load `2H-2`.
Thus the final literal layout has price

\[
 \boxed{\quad
 \mathbb E L^2=2t_H+
       \frac{4H-15}{18\cdot3^{H-1}}.
 \quad}
\]

This is greater than `2t_H` for every `H>=4`. At `H=4` the law has
242 positive-mass points and the original `(residue,modulus)` list is

\[
 (0,1),(1,5),(1,25),(1,125),(1,625),
 (0,7),(21,35),(126,175),(126,875),(4151,4375).
\]

Its price is `2845/486=2t_4+1/486`. These are distinct odd original
divisor labels, with the unit label serving the constant-load term.
The support uses four seven columns. If a standalone five-column
source projection is also required, add an actual source point in
column four and give it zero probability. This preserves the product
tree tests and the same failed law; it does not exclude other laws
on the enlarged source.

[`fixed_terminal_law_height_boundary.py`](../../frontier/cover-geometry/fixed_terminal_law_height_boundary.py)
checks the normalization, terminal rectangle tests, original CRT
phases and each separate contribution above exactly at heights two
through seven. The general-height formula follows from the preceding
calculation. The height-two theorem of this report is unchanged;
extension requires a law accounting for the inherited load, or a
stronger joint estimate.

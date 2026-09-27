[Index](../../marked_head_profile.md) · [Common chain law](376-complete-prime-chain-transport-and-joint-prefix-laws.md) · [Saturated fibres](378-saturated-prime-fibres-and-mixed-tail-incidence.md) · [Root forests](379-root-forest-disintegration-and-residue-costs.md)

# Saturated chain blockers do not supply full-history conditional caps

There is a 36-point source in the first-root product at primes 5, 7 and
11 which meets every product tree required by every increasing subchain
above 3. Its first-5 projection has the minimum size three. One uniform
law satisfies the marginal and saturated-prefix joint bounds of reports
376 and 378 for the complete chain `3<5<7<11`. Nevertheless **no law
supported on this source admits the corresponding full-history
conditional caps in any adaptive read-once coordinate order**.

There is also a direct finite-depth comparison obstruction. For every
supported law, one fixed complete squarefree divisor layout has
squared-load stop-loss at threshold 49 at least `5/12`; the independent
Bernoulli product with those caps gives only `1/3`. Thus even bypassing
the conditional-law construction cannot infer that full convex
comparison from the listed tree and saturated-prefix hypotheses alone.

This is an **abstract source**, not a claimed residual of any actual
distinct odd covering system. It does not refute reports 376, 378 or
379, which retain only the weaker caps they state. It refutes a proposed
bridge from their listed source properties to the full-history cap
interface in Chapters 54--55 or its finite-depth convex comparison.
The unrestricted Erdős #7 assertion remains unresolved. The result is
an ordinary proof with an exact standard-library checker, not Lean
verification or a literature-priority claim.

## 1. The source and the precise product-tree property

Use alphabets `F_5,F_7,F_11`, represented by their usual least
nonnegative residues. Put `s=(0,1,3)` and

\[
 R=\{(u+1,i+1,i+s_u+d+1):
       0\le u\le2,\ 0\le i\le5,\ d\in\{0,1\}\}.
 \tag{SC1}
\]

All coordinates are nonzero. There is no wraparound: the third
coordinate ranges from 1 to 10. Every pair `(u,i)` gives two distinct
points, so `|R|=36`. Its projection sizes at `5,7,11` are `3,6,10`.

For every nonempty increasing subchain
`p_1<...<p_t` drawn from `{5,7,11}`, put
`lambda_1=3` and `lambda_j=p_(j-1)` for `j>1`. The property being tested is

\[
 \text{for every }T_j\subseteq\mathbb F_{p_j},\quad
 |T_j|=\lambda_j,\qquad
 R\cap\bigcap_{j=1}^t\{x:x_{p_j}\in T_j\}\ne\varnothing.
 \tag{SC2}
\]

At height one these sets are exactly the leaf sets of complete trees
with the indicated branching numbers. The alphabets include root zero
even though `R` avoids it. The same `R` is used in every subchain test.

Here is a proof for all seven subchains. Single-coordinate projections
have the stated sizes, so they meet every selected three-root set.
For a fixed first-5 root, the first-7 projection is `{1,...,6}` and
the first-11 projection is a consecutive set of seven roots. These
facts prove the chains `(5,7)` and `(5,11)`. For each fixed first-7
root `i+1`, the first-11 roots available across all three first-5
roots are precisely

\[
 \{i+1,i+2,i+3,i+4,i+5\}.
 \tag{SC3}
\]

A selected three-root set at 7 contains a nonzero root in `{1,...,6}`.
The five roots in SC3 meet every seven-root subset of `F_11`, proving
the chain `(7,11)`.

For `(5,7,11)`, a three-root subset of `F_5` meets `{1,2,3}`; fix
one such `u+1`. A five-root subset of `F_7` contains at least four
members of `{1,...,6}`. At this fixed `u`, the six row pairs at 11
are the six edges of one path on seven consecutive vertices. Any
four of its edges have at least five incident vertices. Deleting
the four roots outside a seven-root subset of `F_11` therefore cannot
remove all these possibilities. This proves SC2 without enumeration.

The exact independent enumeration checks the following numbers of
tree products:

| Selected primes | Branching numbers | Products checked |
| --- | --- | ---: |
| 5 | 3 | 10 |
| 7 | 3 | 35 |
| 11 | 3 | 165 |
| 5,7 | 3,5 | 210 |
| 5,11 | 3,5 | 4620 |
| 7,11 | 3,7 | 11550 |
| 5,7,11 | 3,5,7 | 69300 |
| Total | | 85890 |

## 2. One law satisfies the stated saturated-source bounds

Let `nu` be uniform on `R`. The complete chain `3<5<7<11` has
complementary branching bases `(3,3,5)`. The actual maximum first-root
probabilities under this one law are

\[
 \max_a\nu(x_5=a)=\frac13,\quad
 \max_b\nu(x_7=b)=\frac16,\quad
 \max_c\nu(x_{11}=c)=\frac16.
 \tag{SC4}
\]

They obey the complete-chain marginal caps `(1/3,1/3,1/5)`. Each
first-5 fibre has twelve points. Conditional on that root, the maximum
first-7 and first-11 masses are both `1/6`, so

\[
 \nu(x_5=a,x_7=b)\le\frac1{18}\le\frac19,\qquad
 \nu(x_5=a,x_{11}=c)\le\frac1{18}\le\frac1{15}.
 \tag{SC5}
\]

These are stronger than the first-root saturated joint caps supplied
by report 378 for this chain. More generally, for every squarefree
query on a subset of these coordinates, `nu` satisfies its SC4
marginal cap and the report-378 bound: if the query fixes the first-5
root, multiply `1/3` by the minimum of the applicable other-coordinate
caps; otherwise use just their minimum. Triple atoms have probability
`1/36`, below the resulting `1/15` bound.

Even the pair `(7,11)` has maximum joint atom `1/18`, below the product
`(1/3)(1/5)=1/15`. Thus retaining all three pair-product upper bounds
would still not resolve the obstruction below.

SC4--SC5 concern **one complete-chain law**. Uniform `R` is not claimed
to meet the stronger first-11 cap `1/9` of the one-coordinate chain
`3<11`, or the `1/7` first-11 cap of `3<5<11`. Report 376 supplies a
possibly different law for each selected chain. SC2 keeps all chain
obstructions without combining their separately supplied laws.

## 3. No full-history law exists, even with adaptive order

Fixing any two coordinates in SC1 leaves at most two choices for
the third. For the first-7 or first-11 coordinate this follows from
the path edges in each fixed first-5 fibre. For the first-5 coordinate,
at a fixed first-7 root the three pairs at 11 are

\[
 \{i+1,i+2\},\quad\{i+2,i+3\},\quad\{i+4,i+5\}.
 \tag{SC6}
\]

Their maximum point multiplicity is two. The maximum fibre size is
exactly two in each of the three directions.

Suppose a normalized law supported on `R` could be generated by
reading every coordinate once, selecting the next unread coordinate
from the already observed transcript, and obeying the root caps

\[
 \Pr(X_p=a\mid\text{complete preceding transcript and selected }p)
 \le c_p,\qquad(c_5,c_7,c_{11})=(1/3,1/3,1/5).
 \tag{SC7}
\]

Randomized coordinate choices are permitted, with the selection
randomizer included in the conditioning. At every positive-probability
history immediately before the last coordinate, the first two
coordinates are fixed. Support on `R` leaves at most two roots for
the last coordinate. Their total allowed mass is at most `2/3` or
`2/5`, strictly below one. No normalized final row exists. This
contradiction covers every fixed, adaptive or randomized read-once
order, without enumerating policies.

A separate root-cell capacity certificate gives the same failure.
Successive conditioning, including adaptive selection, bounds the
probability of any prescribed root triple by `c_5 c_7 c_11=1/45`.
For adaptive selection, induction on the unread-coordinate set applies:
at the selected coordinate its prescribed root costs at most `c_p`,
and on every resulting history the remaining prescribed roots cost
at most the product of their caps. Averaging over the selected
coordinate preserves the bound. Since `R` has only 36 root triples,
its total permitted mass is at most `36/45=4/5<1`.

## 4. A sharp finite-depth stop-loss obstruction on the same source

Let `nu` now be **any** probability supported on `R`, with no marginal
or conditional cap assumption. For each fixed centre `c` in `R`,
choose its CRT residue modulo `385`. Give every divisor of `385`
the restriction of that same centre, including divisor one. This is
one legal complete squarefree divisor layout; its load is

\[
 L_c(x)=\sum_{d\mid385}\mathbf1_{x=c\bmod d}
       =\prod_{p\in\{5,7,11\}}(1+\mathbf1_{x_p=c_p}).
 \tag{SC8}
\]

It equals 8 at `c` and is at most 4 elsewhere. Consequently, for
every `16<=tau<64`,

\[
 \mathbb E_\nu(L_c^2-\tau)_+=(64-\tau)\nu(\{c\}).
 \tag{SC9}
\]

Summing SC9 over the 36 fixed centres gives exactly `64-tau` for
every such `nu`. Uniform `R` makes all these costs equal. Therefore

\[
 \inf_{\nu\text{ supported on }R}\ 
 \max_{c\in R}\mathbb E_\nu(L_c^2-\tau)_+
 =\frac{64-\tau}{36}.
 \tag{SC10}
\]

This is a minimax only over these 36 centred layouts, sufficient for
an obstruction to a bound required for every layout. No claim is made
that arbitrary layouts share a common centre. The centre witnessing
the maximum may depend on the chosen law, and is then fixed before
sampling `x`; it never changes with the sample.

For the **height-one** independent comparison variables `B_p`, with
`Pr(B_p=1)=c_p`, put `D=product_p(1+B_p)`. The event `D=8` has
probability `1/45`, and every other value is at most 4. Thus

\[
 \mathbb E(D^2-\tau)_+=\frac{64-\tau}{45}.
 \tag{SC11}
\]

At `tau=49`, SC10 is `5/12`, SC11 is `1/3`, and their strict
difference is `1/12`. Hence **no supported law**, including one with
all the marginal and saturated-prefix bounds above, can satisfy
this finite-depth independent-product stop-loss comparison for all
complete layouts.

This does not invalidate Chapter 63, whose conditional-cap hypotheses
are missing here. Nor does it show failure of a bound on the raw
second moment `Gamma`, or compare against a product with geometric
higher digits. Those higher digits increase the auxiliary right side;
SC11 is specifically the finite height-one Bernoulli product.

## 5. The source obstruction persists at arbitrary finite heights

For any positive integers `H_5,H_7,H_11`, let

\[
 R_H=\{x\in\prod_p\mathbb Z/p^{H_p}\mathbb Z:
                  (x_5\bmod5,x_7\bmod7,x_{11}\bmod11)\in R\}.
 \tag{SC12}
\]

Every higher digit is free. Each complete full-height chain tree
has the root branching numbers used in SC2. Choose a root witness
from that property, then choose any leaf below each selected root
inside its prescribed tree. The resulting full point lies in `R_H`.
Thus the full-height product-tree obstruction holds for every
increasing subchain and every choice of its complete trees.

The first-5 projection remains saturated at depth one. It is not
claimed saturated at greater depth: its size at depth `a>=1` is
`3*5^(a-1)`, whereas the minimum blocker size would be `3^a`.

Lift uniform `R` by independent uniform higher digits. A specified
depth-`a` cylinder at prime `p` has its root mass multiplied by
`p^(-(a-1))`. Since the three primes dominate their complete-chain
bases `(3,3,5)`, SC4 gives all the full-height marginal caps

\[
 \nu_H(x_p=b\bmod p^a)\le r_p^{-a},
 \qquad(r_5,r_7,r_{11})=(3,3,5).
 \tag{SC13}
\]

Conditional on a fixed first-5 root, its higher 5 digits are uniform
and independent of the remaining root law. The conditional 7 and 11
prefix caps are still `3^(-a)` and `5^(-a)`. Intersecting any query
events bounds its conditional mass by the minimum of those caps
and the corresponding 5-tail cap. Multiplying by `1/3` proves exactly
the depth-one saturated form of report 378, including its SF6 bound
on full cofactor APs at arbitrary heights. It does not multiply the
two unsaturated-coordinate caps.

Nevertheless the terminal-root argument of section 3 still rules out
every adaptive full-coordinate source law satisfying SC7. Fixing the
two complete earlier coordinates fixes their roots, and the last
coordinate still has at most two possible first roots. Extra digits
cannot make a normalized row out of first-root capacity below one.
The root-cell certificate also remains `36/45=4/5`, independently
of the heights. This is an all-height proof, not an extrapolation
from finitely many tested heights.

Only the source and conditional-law obstruction are lifted here.
No all-divisor, infinite-geometric stop-loss comparison at these
higher heights is asserted.

## 6. Reproduction and the remaining quantitative bridge

The [standalone checker](../../frontier/cover-geometry/saturated_chain_conditional_obstruction.py)
uses two constructions of `R`, checks all 85890 tree products, all
eight squarefree query types and all terminal fibres, and checks
SC8 on 13860 centre/ambient-point pairs using integer CRT and all
eight original squarefree divisor labels. Its pointwise identity
`sum_(c in R) (L_c(x)^2-49)_+=15` is the finite dual certificate
behind SC10 for arbitrary supported laws. All arithmetic is exact.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/saturated_chain_conditional_obstruction.py
```

Report 379 already warns that its remaining coordinates may be
correlated and explicitly retains a minimum rather than a product
of their caps. Its example demonstrates failure of multiplication
for a particular constructed law. The present source gives the
stronger existence obstruction: **no alternative supported law or
adaptive coordinate order repairs the desired caps**, although all
prime-chain product obstructions hold and the first coordinate is
saturated. Report 381 concerns multiplicity and repeated prime
exposure in actual missing-fibre quotients; it does not establish
this abstract conditional-law bridge.

To connect an actual minimum-cover residual to Chapters 54--55,
one must prove an additional property of its original congruence
realization that rules out this source behaviour. Alternatively,
the arbitrary-head interface of Chapter 08 permits a direct
same-law layout estimate without full-history caps. Such an estimate
must control `sup_b integral L_b^2 dnu` (or a justified stop-loss
functional) for one supported law, retaining the actual original
layout; separate prefix bounds do not supply it. Neither such a
uniform quantitative estimate nor arithmetic realizability of `R_H`
is established here.

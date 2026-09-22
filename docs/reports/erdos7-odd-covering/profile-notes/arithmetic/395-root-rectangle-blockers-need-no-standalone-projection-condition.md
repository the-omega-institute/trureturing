[Index](../../marked_head_profile.md) · [Root laws with the standalone hypothesis](390-two-prime-root-blockers-admit-a-common-second-moment-law.md) · [Failure of fibrewise inheritance](394-standalone-tree-blocking-need-not-pass-to-joint-prefix-fibres.md)

# Root rectangle blockers need no standalone projection condition

Every source in a five-by-seven carrier that meets every three-by-five
rectangle admits one supported probability law whose complete root-layout
second moment is at most 4. The separate hypothesis that at least five
7-columns occur, used in report 390, is unnecessary for this functional
conclusion.

The new step is a complete four-row classification without a lower bound
on the number of columns. Five additional minimal types admit explicit
laws; the remaining five are covered by the constructions of report 390.
The theorem controls arbitrary independent row, column and point choices
under the same law. It makes no claim about the auxiliary caps of report
390, deeper conditional laws, or realization by an actual odd-cover
residual. The combinatorial proof and exact checks are not Lean-certified.

## 1. Statement and the root functional

Let

\[
 R\subseteq\mathbb Z/5\times\mathbb Z/7,
 \qquad R\cap(A\times B)\ne\varnothing
 \quad\text{whenever }|A|=3,\ |B|=5.
 \tag{RB1}
\]

For a probability law `nu` supported on `R`, define

\[
 \Gamma_{35}(\nu)=
 \max_{a,b,u,v}
 \mathbb E_\nu\left(1+1_{i=a}+1_{j=b}
                         +1_{(i,j)=(u,v)}\right)^2.
 \tag{RB2}
\]

The four labels are all divisors `1,5,7,35`; the three nonconstant
residue choices are independent. In particular `(u,v)` need not equal
`(a,b)`. The theorem is

\[
 \boxed{\quad\text{RB1 implies that some supported law }\nu
                    \text{ satisfies }\Gamma_{35}(\nu)\le4.\quad}
 \tag{RB3}
\]

Write `N_i` for the columns occurring in row `i`. RB1 is equivalent
to every three rows having at least three columns in their union:
otherwise five columns avoid that union, and conversely any empty
three-by-five rectangle leaves at most two possible neighbor columns.
In particular at least three rows and at least three columns are active.

For point masses `w_ij` and their row and column sums `r_i,c_j`, the
same-law identity from report 390 is

\[
 \mathbb E L^2=1+3r_a+3c_b+2w_{ab}
       +(3+2\,1_{u=a}+2\,1_{v=b})w_{uv}.
 \tag{RB4}
\]

Thus maximum row, column and point masses `alpha,beta,gamma` give
`Gamma<=1+3alpha+3beta+9gamma`. We use this sufficient estimate only
where the displayed law supplies all three caps simultaneously.

## 2. The four-row classification

Suppose exactly four rows are active. The fifth row is empty, so RB1
is equivalent to

\[
 |N_i\cup N_j|\ge3\quad(i\ne j),\qquad N_i\ne\varnothing.
 \tag{RB5}
\]

Delete edges while preserving RB5 until the support is minimal. There
is no condition protecting the total number of columns during deletion.
Up to row and column permutations, exactly the following ten types
remain; distinct displayed letters denote distinct columns.

| Type | Four row neighborhoods | Edges |
| --- | --- | ---: |
| A | `{a}`, `{b,c}`, `{a,b,c}`, `{d,e}` | 8 |
| B | `{a}`, `{b,c}`, `{b,d}`, `{b,e}` | 7 |
| C | `{a}`, `{b,c}`, `{b,d}`, `{c,e}` | 7 |
| D | `{a}`, `{b,c}`, `{b,d}`, `{e,f}` | 7 |
| F | `{a}`, `{b,c}`, `{d,e}`, `{f,g}` | 7 |
| cycle4 | `{a,b}`, `{b,c}`, `{c,d}`, `{d,a}` | 8 |
| triangle_full | `{a,b}`, `{a,c}`, `{b,c}`, `{a,b,c}` | 9 |
| two_triples | `{a}`, `{b,c}`, `{a,b,c}`, `{a,b,c}` | 9 |
| singleton_triangle | `{a}`, `{b,c}`, `{b,d}`, `{c,d}` | 7 |
| A_shared | `{a}`, `{b,c}`, `{a,b,c}`, `{b,d}` | 8 |

Here is a proof of exhaustiveness independent of the finite checker.

**Degrees and singleton rows.** A row of degree at least four can lose
an edge and retain at least three neighbors, so deletion preserves every
pair union and nonemptiness. Minimality therefore bounds every degree
by three. Two singleton rows would have a union of size at most two,
so at most one singleton occurs. Two degree-two rows cannot be equal.

**No singleton, with a triple.** Deleting one element from a triple
leaves a double. The only way this can violate RB5 is for another row
to equal that double. Minimality for all three deletions forces the
other three rows to be the three complementary pairs of the triple.
This is `triangle_full` and permits no second triple.

**No singleton and no triple.** The four rows are distinct two-element
sets, regarded as four edges of a simple graph on column vertices. If
an edge has a degree-one endpoint, retain that endpoint alone in its
row. No other row contains it, so its union with every other double
still has size three. This contradicts minimality. Thus the graph has
minimum degree at least two on its active vertices. Four simple edges
then force the four-cycle: at most four vertices can occur, three
vertices support at most three distinct edges, and on four vertices
every degree is two. This gives `cycle4`.

**A singleton and a triple.** Denote the singleton by `{a}`. Every
double avoids `a`, by RB5. A triple not containing `a` would need all
three complementary doubles among the other rows to prevent its three
edge deletions. One other row is the singleton, so that is impossible.
Hence each triple is `{a,b,c}` for some `b,c`. Deleting `a` from that
triple can fail RB5 only if another row is precisely `{b,c}`. Every
triple therefore requires its matching double. If there are two triples,
there is only one remaining double, so the triples coincide: this is
`two_triples`. Three triples have no available matching double. With
exactly one triple, the other double avoids `a`, differs from `{b,c}`,
and either shares one element with it or is disjoint. These are
`A_shared` and A respectively.

**A singleton and no triple.** The other three rows are distinct
two-element sets avoiding `a`. The simple graph consisting of these
three edges is one of: a three-edge star, a three-edge path, a two-edge
path and a disjoint edge, three disjoint edges, or a triangle. They
give B, C, D, F and `singleton_triangle`.

This exhausts all cases, and direct edge deletion verifies minimality
of each displayed type. The old type E, a triangle plus an isolated
edge, is no longer minimal: deleting one endpoint of the isolated row
leaves `singleton_triangle`. The column-count premise in report 390
was what prevented that deletion.

## 3. Explicit laws for all ten types

The laws for A, B, C, D and F are the existing laws of report 390.
A, C, D and F use their uniform laws. Type B gives its singleton and
three private points mass `1/6` each, and its three common-column
points mass `1/9` each. Their exact full-layout maxima are respectively
`4,35/9,4,4,25/7`, so each is at most 4.

The uniform law on `cycle4` has row and column caps `1/4` and atom
cap `1/8`; RB4 bounds it by `29/8`. Each of `triangle_full` and
`two_triples` has nine edges, maximum row and column degrees three,
and therefore uniform caps `(1/3,1/3,1/9)`, giving 4. The uniform
seven-point law on `singleton_triangle` has row and column caps `2/7`
and point cap `1/7`, again giving 4.

For `A_shared`, order the eight points as

\[
 (1,a),(2,b),(2,c),(3,a),(3,b),(3,c),(4,b),(4,d).
\]

Give them the respective masses

\[
 \frac1{18}(3,2,2,2,2,2,2,3).
 \tag{RB6}
\]

The row-mass numerators are `(3,4,6,5)` and the column-mass numerators
are `(5,6,4,3)` in column order `a,b,c,d`. For each selected row and
column, maximizing the final point term in RB4 gives the following
numerators for the entire squared-load expectation:

| Selected row / column | a | b | c | d |
| --- | ---: | ---: | ---: | ---: |
| 1 | 69 | 60 | 54 | 51 |
| 2 | 60 | 66 | 60 | 54 |
| 3 | 70 | 72 | 66 | 60 |
| 4 | 63 | 70 | 60 | 69 |

All entries are at most `72=4*18`. The entry `(3,b)` is attained by
choosing the point `(3,b)`, so this law's exact maximum is 4. Choices
of absent rows, columns or point cells cannot increase the maximum:
their zero indicators may be replaced by any occupied choices, which
only increases the nonnegative load pointwise. This argument concerns
independent layout choices and does not require a common center.

A supported law on any minimal subgraph is also a supported law on
the original graph, by giving discarded edges zero probability. This
proves the four-row lemma under RB5, with no standalone projection
hypothesis.

## 4. Three and five active rows

**Three active rows.** The two empty rows can be paired with each
active row in the triple-row formulation of RB1. Thus every active
row has at least three neighbors. Choose three in each row and put
mass `1/9` on each of the nine selected points. Its row and column
caps are at most `1/3`, and its atom cap is `1/9`, so RB4 gives 4.
No lower bound on the total projection beyond what RB1 forces is used.

**Five active rows and at least five active columns.** These are
exactly the hypotheses already treated by the full root theorem of
report 390, which supplies a common law with `Gamma<=4`.

**Five active rows and three active columns.** Every active column
has at least three neighbors: if it had at most two, three rows would
avoid it and could have at most two columns in their union, contrary
to RB1. Choose three neighbors in each of the three columns and put
mass `1/9` on those nine points. Column and row caps are both at most
`1/3`, and the point cap is `1/9`, giving 4.

**Five active rows and four active columns.** Every pair of active
columns has at least three neighboring rows in its union. Otherwise
choose three rows avoiding that union, and take the two columns
together with the three inactive columns; this is an empty three-by-five
rectangle. Transpose the support. It now has four nonempty rows, on
a five-column carrier, satisfying RB5. Adjoin two unused columns and
one empty row to put it in the lemma's five-by-seven carrier. These
zero indicators do not change the maximum, as in section 3. The
four-row lemma supplies a law with root functional at most 4.
Transposing it back preserves
RB2, which is symmetric in its row and column indicators and transports
the independently selected point as well.

Fewer than three active columns contradict RB1. These cases, together
with the three-row and four-row arguments, prove RB3 for every source
in the five-by-seven carrier.

## 5. Relation to conditional fibres and exact verification

Report 394 proves that the standalone 7-tree condition can fail after
conditioning on a joint prefix, even when a root fibre retains the
product-rectangle condition. That loss is real. RB3 shows that it
does not by itself prevent the conclusion `Gamma_35<=4` at such a
root fibre: RB1 alone suffices.

This does not prove that arbitrary joint fibres retain RB1, that a
collection of independently chosen root laws combines into one global
law with the desired deeper bounds, or that root estimates tensorize.
Those are separate compatibility and functional obligations.

The [standard-library checker](../../frontier/cover-geometry/root_rectangle_second_moment.py)
uses each nonempty subset of four labelled rows as a column incidence
type. Every support with at most seven active columns is represented
by a multiset of these 15 types. It checks all
`binomial(22,7)-1=170543` nonempty multisets, with no degree cutoff,
then checks RB5 and every allowed edge deletion. There are `141133`
valid supports and `103` minimal supports before quotienting by row
permutations. They form exactly the ten types in section 2:

| Type | Minimal column multisets with labelled rows |
| --- | ---: |
| A | 24 |
| B | 4 |
| C | 12 |
| D | 12 |
| F | 4 |
| cycle4 | 3 |
| triangle_full | 4 |
| two_triples | 12 |
| singleton_triangle | 4 |
| A_shared | 24 |

For each of the ten explicit laws, the checker evaluates all `1225`
independent row, column and point choices on the full five-by-seven
carrier, including absent choices. Direct squared-load sums are compared
with RB4, and an attaining choice is returned. This gives `12250`
layout checks, the exact `A_shared` table, and a check that old type E
has the claimed strict reduction. Checks remain enabled under `-O`:

```sh
python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/root_rectangle_second_moment.py
```

The general theorem follows from the combinatorial classification,
explicit laws and the three-/five-row reductions. The exhaustive
classification and rational layout evaluations are independent finite
controls on that proof; they do not establish a higher-height theorem
or resolve Erdős #7.

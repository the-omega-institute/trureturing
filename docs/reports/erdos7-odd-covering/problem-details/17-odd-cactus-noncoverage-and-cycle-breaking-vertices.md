[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](06-block-saturation-and-the-actual-crossing-budget.md) · [Next](07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md)

<a id="arbitrary-odd-cactus-graphs-are-noncovering"></a>
#### Arbitrary odd cactus graphs are noncovering

Let \(D\) be a finite set of distinct odd integers greater than one, and choose
one residue class \(a_d\pmod d\) for every \(d\in D\). Let \(G_D\) have as vertices
the primes dividing \(Q=\operatorname{lcm}_{d\in D}d\), and join distinct primes
\(p,q\) exactly when \(pq\mid d\) for some \(d\in D\).

**Theorem.** If every nontrivial block of \(G_D\) is an edge or a simple
cycle, then the chosen residue classes do not cover the integers. Isolated
vertices are allowed.

Here a graph with this block property is a cactus. There is no bound on the
number of cycles, vertex degrees, prime powers in the moduli, or residues.
Triangles may carry all the original three-prime moduli; they are not replaced
by pairwise projections. Different connected components are allowed.

This existence conclusion is also a specialization of
[Schroeder, Theorem 1.1](../../../../Library/Arith/schroeder2026noncoverage.md):
a cactus has no clique larger than three, so each original modulus has at
most three distinct prime factors. The theorem permits arbitrary heights
and arbitrarily many primes in the family. We use this as the existing
noncoverage boundary, without adding a Lean wrapper or claiming a new
existence result.

The following argument extends the [preceding quantitative pseudoforest
analysis](06-block-saturation-and-the-actual-crossing-budget.md#arbitrary-odd-pseudoforests-are-noncovering) to arbitrarily many cycles joined at articulation primes. It
bounds entire blocked parent fibres, assigns summable fees to distinct
child primes, and certifies the actual recursively feasible coordinate
domains in (CA22)--(CA25). Those quantitative domains and their extension
counts are the additional objects established here. No literature priority
is claimed for the argument.

##### Exact block recursion on original prime-power coordinates

Work first in one connected component. Write
\[
 X_p=\mathbb Z/p^{h_p}\mathbb Z,
 \qquad h_p=v_p(Q),
\]
and let \(H_p\) be uniform measure on \(X_p\). The CRT identifies the full
component coordinate space with the product of these finite spaces. A class
whose modulus has \(p\)-adic exponent \(a\) imposes one cylinder in \(X_p\) of
measure \(p^{-a}\). The cylinders always refer to the original class residues.

Root the block-cut tree at prime \(3\) if it is present, and at any prime
otherwise. A block has one parent prime \(p\); all its other prime vertices are
its child vertices. All nonroot primes are at least \(5\). Child vertex sets of
distinct child blocks of a fixed prime are disjoint.

Every mixed original modulus belongs to exactly one block. Indeed its prime
support is a clique. A cactus has no clique of size four, and a three-vertex
clique is exactly a triangular block. Thus bridge and longer-cycle blocks have
only their edge-supported moduli, whereas a triangle has its three edge
families and its complete three-prime family. Pure powers are assigned to
their single prime.

Define \(V_p\subseteq X_p\) to be the set of words at \(p\) that extend to an
assignment avoiding every original class in the subtree below \(p\), including
the pure powers at \(p\), but excluding the incoming parent block. For a child
block \(B\) of \(p\), define
\[
 \mathcal B_{B\to p}=\{x_p:\text{every tuple in }
       \prod_{q\in B\setminus\{p\}}V_q
       \text{ is hit by a class of }B\}.
\]
If \(P_p\) is the union of the original pure-power cylinders at \(p\), then
\[
 V_p=X_p\setminus\left(P_p\cup
             \bigcup_{B\text{ child block of }p}\mathcal B_{B\to p}\right).
 \tag{CA1}
\]
This is equality, not a relaxation. Child block witnesses and then descendant
witnesses glue because the block-cut incidence graph is a tree. Also
\[
 H_p(P_p)\le\sum_{a\ge1}p^{-a}=\frac1{p-1}.
 \tag{CA2}
\]

We will close the bottom-up invariant
\[
 H_p(V_p)\ge\frac23\qquad(p\ne\text{root}).
 \tag{CA3}
\]
The argument below proves this invariant, rather than assuming it globally.

##### A bound on an entirely blocked parent fibre

Suppose all child domains of a block are nonempty. On this one block fix the
single product probability law
\[
 \nu_B=\bigotimes_{q\in B\setminus\{p\}}H_q(\cdot\mid V_q).
 \tag{CA4}
\]
Let \(K\) upper-bound the \(\nu_B\)-probability of the union of block classes
not involving \(p\). For every fixed positive parent exponent \(a\), suppose
the sum of the probabilities of the child-coordinate parts of all block
classes with parent exponent \(a\) is at most \(\lambda\). The same
\(\lambda\) is used for every exponent; no class residues are optimized
separately in defining the law (CA4).

For an integer \(r\ge1\), if
\[
 g=1-K-(r-1)\lambda>0,
\]
then
\[
 H_p(\mathcal B_{B\to p})\le
 F_{p,r}(\lambda,K):=
 \frac{p^{1-r}\lambda}{(p-1)[1-K-(r-1)\lambda]}.
 \tag{CA5}
\]

To prove this, for a parent word \(x_p\) let \(L_a(x_p)\) be the sum of
child-coordinate probabilities for the original block classes of parent
exponent \(a\) whose parent cylinders contain \(x_p\). On a blocked fibre,
the union bound gives
\[
 \sum_{a\ge1}L_a(x_p)\ge1-K.
\]
Since \(L_a(x_p)\le\lambda\), the sum with \(a\ge r\) is at least \(g\) on
that fibre. Each original parent cylinder of exponent \(a\) has \(H_p\)-mass
\(p^{-a}\); hence
\[
 \int\sum_{a\ge r}L_a\,dH_p
 \le\lambda\sum_{a\ge r}p^{-a}
 =\frac{p^{1-r}\lambda}{p-1}.
\]
Integrating the lower bound on blocked fibres proves (CA5). Finite original
exponent ranges are simply overcounted by the displayed infinite geometric
sums. Distinct original moduli ensure that each full positive exponent tuple
occurs at most once; no different original labels are merged.

Under the child density invariant (CA3), put
\[
 \beta_q=\frac{3}{2(q-1)}.
\]
For every exponent \(b\), a child cylinder has conditional probability at
most \(\tfrac32q^{-b}\). Summing these bounds over positive exponents gives
\(\beta_q\). Independence in the single law (CA4) therefore gives these
valid choices:

* A bridge with child \(q\): \(\lambda=\beta_q,\ K=0\).
* A triangle with children \(q,t\):
  \[
   \lambda=\beta_q+\beta_t+\beta_q\beta_t,
   \qquad K=\beta_q\beta_t.
   \tag{CA6}
  \]
  The product term in \(\lambda\) accounts for every original three-prime
  modulus, at its original parent exponent.
* A cycle of length at least four: deleting the parent leaves a path of
  children. If its endpoint weights are \(u,v\), then
  \(\lambda=u+v\), and \(K\) is at most the sum of the products of adjacent
  child weights along that path.

##### A valid relaxation for the longer-cycle path

Let \(z=u+v\), and suppose \(T\) bounds the sum of squares of all child
weights in a longer cycle. The elementary inequality \(2ab\le a^2+b^2\)
along its child path gives
\[
 K\le T-\frac{u^2+v^2}{2}\le T-\frac{z^2}{4}.
 \tag{CA7}
\]
At parent \(3\), substituting (CA7) into (CA5) gives the bound
\[
 G_r(z,T)=\frac{3^{1-r}z}
 {2[1-T+z^2/4-(r-1)z]},
 \tag{CA8}
\]
when the displayed denominator is positive.

Let \(s<t\) be the two smallest child primes, so
\(z\le\bar z=\beta_s+\beta_t\). They need not be the actual path endpoints.
The substitution \(z\mapsto\bar z\) in (CA8) is justified by monotonicity of
the complete fraction, not by asserting \(K\le T-\bar z^2/4\).

Specifically, throughout
\[
 0\le z\le5/8,\qquad 0\le T\le117/400,
 \tag{CA9}
\]
the derivative of \(z/[1-T+z^2/4-(r-1)z]\) has numerator
\(1-T-z^2/4>0\). The fraction is also increasing in \(T\) wherever its
denominator is positive. If \(r\ge2\), that denominator decreases as \(z\)
increases through (CA9), so positivity at \(\bar z\) implies positivity at
the actual \(z\). If \(r=1\), it is already positive because \(T<1\).
Consequently a positive certified value \(G_r(\bar z,T)\) bounds the actual
blocker. This preserves the direction of every inequality even when the two
smallest child primes are interior vertices.

##### A summable fee for each child prime

Define, on primes at least five,
\[
 f(5)=\frac14,\qquad f(7)=\frac16,\qquad
 f(q)=2^{-(q-1)/2}\quad(q\ge11).
 \tag{CA10}
\]
Overcounting the last primes by all odd integers at least eleven gives
\[
 \sum_{q\ge5\text{ prime}}f(q)
 \le\frac14+\frac16+\sum_{j\ge5}2^{-j}
 =\frac{23}{48}<\frac12.
 \tag{CA11}
\]

The local fee claim is as follows. With child densities at least \(2/3\), a
bridge with child \(s\) admits a cutoff \(r\) for which its parent-3 bound is
at most \(f(s)\). A cycle with two smallest child primes \(s<t\) admits a
cutoff for which its parent-3 bound is at most \(f(s)+f(t)\). Whenever
\(s\ge7\), such a cutoff may be chosen with \(r\ge2\). If \(s\ge97\), the
stronger fee \(f(s)\) suffices for every block type.

Here "parent-3 bound" means evaluation of the bound (CA5) at \(p=3\), for
later comparison with any actual parent. It does not change original classes,
child domains, or the law (CA4). The rest of this section proves the fee claim
by an exact finite certificate and two analytic infinite regimes.

###### Prime square sum and the finite certificate

An elementary upper bound sufficient here is
\[
 S_5:=\sum_{q\ge5\text{ prime}}\frac1{(q-1)^2}<\frac{13}{100}.
 \tag{CA12}
\]
List the primes between five and seventy-three, and overcount the rest by
the odd integers \(75,77,\ldots\). Monotone integration gives
\[
 S_5\le
 \sum_{5\le q\le73\text{ prime}}\frac1{(q-1)^2}
 +\frac1{74^2}+\frac1{148}
 =\frac{13668492439156530043}{105454959460135084800}
 <\frac{13}{100}.
 \tag{CA13}
\]
For two smallest child primes \(s<t\), define
\[
 T(s,t)=\frac94\left(\frac{13}{100}
 -\sum_{\substack{5\le q<t\text{ prime}\\q\ne s}}
       \frac1{(q-1)^2}\right).
 \tag{CA14}
\]
Every child prime belongs to \(\{s\}\cup\{q:q\ge t\}\), so (CA12) implies
that \(T(s,t)\) bounds its child square sum. In particular
\(0<T(s,t)\le117/400\), as required in (CA9).

The finite certificate checks every prime \(5\le s<t\le97\), and bridges
with prime \(5\le s<97\), using exact rational arithmetic. At each pair it
checks separately
\[
 \begin{array}{c|c|c}
 &\lambda&K\\\hline
 \text{long-cycle fraction}&\beta_s+\beta_t&
       T(s,t)-(\beta_s+\beta_t)^2/4\\
 \text{triangle}&\beta_s+\beta_t+\beta_s\beta_t&\beta_s\beta_t.
 \end{array}
 \tag{CA15}
\]
For the long cycle the first row represents exactly the monotone fraction
(CA8), justified by the long-cycle relaxation above; it is not a separate
assertion about the actual \(K\) at the artificial endpoints.

For every row the program enumerates integers \(r\) while
\(1-K-(r-1)\lambda>0\), starting at one if \(s=5\) and at two otherwise.
It verifies that at least one value of (CA5) is within the assigned fee.
Bridges are charged \(f(s)\). Pairs with \(t<97\) are charged
\(f(s)+f(t)\). At the boundary \(t=97\), it checks the stronger charge
\(f(s)\).

There are 528 rows: 22 bridge rows and twice the 253 pairs. Every assertion
passes. The largest cost/fee ratio is the long-cycle row \((s,t)=(5,11)\):
\[
 r=2,\quad\lambda=\frac{21}{40},\quad K=\frac{1031}{6400},\quad
 g=\frac{2009}{6400},\quad
 F_{3,2}=\frac{80}{287}<\frac9{32}=f(5)+f(11).
 \tag{CA16}
\]
Its exact fee surplus is \(23/9184\), and the ratio is \(2560/2583<1\).
The full certificate includes every chosen cutoff and all exact fractions.
It uses only the Python standard library and checks that assertions are
enabled. It can be rerun with

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/cactus_block_fees.py
```

These are scalar rational inequality checks over a closed finite box. They
do not enumerate cactus graphs and do not stand in for the infinite argument.

###### A small first child prime and an arbitrarily large second one

Fix prime \(s<97\), and suppose \(t\ge97\). For longer cycles,
\[
 T(s,t)\le T(s,97),\qquad
 \beta_s+\beta_t\le\beta_s+\beta_{97}.
\]
Use the cutoff certified at \((s,97)\). The long-cycle relaxation above
shows that decreasing both arguments preserves denominator positivity and
cannot increase (CA8).
The certified boundary value is at most \(f(s)\).

For triangles both \(\lambda\) and \(K\) from (CA6) decrease as \(t\)
increases. The fraction (CA5) increases in either parameter on its positive-gap
domain: differentiating with respect to \(\lambda\) gives a positive factor
\(1-K\), and differentiating with respect to \(K\) is positive. Thus the
same boundary cutoff again gives a bound at most \(f(s)\). The cutoffs are
at least two when \(s\ge7\). Bridges with \(s<97\) were already checked.

###### All child primes at least ninety-seven

Write the smallest child prime as \(s=2n+1\), with \(n\ge48\). For every
block type the estimates above imply the uniform bounds
\[
 K\le K_n:=\frac{9(n+1)}{16n^2},\qquad
 \lambda\le\lambda_n:=\frac{24n+21}{16n(n+1)}.
 \tag{CA17}
\]
For a longer cycle, its internal path sum is at most its child square sum,
which is at most
\[
 \frac9{16}\sum_{j\ge n}\frac1{j^2}
 \le\frac9{16}\left(\frac1{n^2}+\frac1n\right)=K_n.
\]
The two largest possible distinct child weights are at most
\(x=3/(4n)\) and \(y=3/[4(n+1)]\). Therefore all three block types have
\(\lambda\le x+y+xy=\lambda_n\). A triangle has
\(K\le xy\le K_n\), and a bridge has \(K=0\).

Choose
\[
 r=\lfloor2n/3\rfloor-1\ge31.
\]
Since \(r-1\le2n/3-2\), the gap is at least
\[
 1-K_n-(2n/3-2)\lambda_n
 =\frac{41n^2+24n-9}{16n^2(n+1)}>0.
 \tag{CA18}
\]
In particular
\[
 \frac{\lambda}{1-K-(r-1)\lambda}
 \le\frac{n(24n+21)}{41n^2+24n-9}\le\frac23.
 \tag{CA19}
\]
The last inequality is equivalent to \(10n^2-15n-18\ge0\), which holds
for \(n\ge3\): on writing \(n=k+3\), it becomes
\(10k^2+45k+27\ge0\).

It follows from (CA5) that
\[
 F_{3,r}(\lambda,K)\le3^{-r}\le2^{-n}=f(s).
 \tag{CA20}
\]
For completeness, write \(n=3m+j\), \(j\in\{0,1,2\}\), so \(m\ge16\).
The ratio \(3^r/2^n\) is respectively
\[
 (9/8)^m/3,\qquad(9/8)^m/6,\qquad(9/8)^m/4.
\]
All are greater than one because
\[
 9^{16}=1853020188851841
 >1688849860263936=6\cdot8^{16}.
\]
This proves the fee claim in every remaining infinite range.

##### Close the invariant for every actual parent prime

For fixed cutoff and fixed block parameters, there is the exact scaling
\[
 F_{p,r}(\lambda,K)=
 \frac2{p-1}\left(\frac3p\right)^{r-1}
 F_{3,r}(\lambda,K).
 \tag{CA21}
\]
Charge a bridge to its child prime, and a cycle to its two smallest child
primes. Distinct child blocks at a given parent have disjoint child vertex
sets. Thus these fees do not double count a prime, no matter how many child
blocks or descendants there are. The stronger one-prime charges in the
infinite regimes are optional savings.

Assume (CA3) for every child vertex. Equations (CA1), (CA2), and the fee claim give
the following bounds.

* At parent \(3\), (CA11) gives
  \[
    H_3(V_3)\ge1-\frac12-\frac{23}{48}=\frac1{48}>0.
    \tag{CA22}
  \]
  Prime \(3\), when present, is the root, so no \(2/3\) invariant is
  required there.
* At parent \(5\), all child primes are at least seven. All the certified
  cutoffs are consequently at least two, so the multiplier in (CA21) is at
  most \(3/10\). The available child fees sum to at most \(11/48\), giving
  \[
    H_5(V_5)\ge\frac34-\frac3{10}\frac{11}{48}
      =\frac{109}{160}>\frac23.
    \tag{CA23}
  \]
* At parent \(7\), the multiplier in (CA21) is at most \(1/3\), and prime
  seven itself is not a child. The available child fees sum to at most
  \(23/48-1/6=5/16\). Hence
  \[
    H_7(V_7)\ge\frac56-\frac13\frac5{16}
      =\frac{35}{48}>\frac23.
    \tag{CA24}
  \]
* At parent \(p\ge11\), even charging the full sum (CA11) gives
  \[
    H_p(V_p)\ge1-\frac1{p-1}-\frac2{p-1}\frac{23}{48}
     =1-\frac{47}{24(p-1)}
     \ge\frac{193}{240}>\frac23.
    \tag{CA25}
  \]

Leaves satisfy the invariant directly from (CA2). Induction up the finite
block-cut tree therefore proves (CA3) at every nonroot prime. The root has
positive density by (CA22) if it is three, or by (CA23)--(CA25) otherwise.

Choose a root word from its nonempty domain. Equation (CA1) supplies, for every
child block, a simultaneous tuple of words in the actual child domains that
avoids every original class of that block. Recursively choose the descendant
witnesses. Their consistency follows from the block-cut tree, and every
original label was assigned to exactly one vertex or block. Thus there is an
uncovered assignment for this entire connected component. An isolated vertex
is covered by the pure-power argument. Finally combine the component
assignments by CRT. The empty palette is trivially noncovering. This proves
the theorem.

##### What the theorem does and does not assert

The quantitative step is a uniform whole-fibre blocker estimate with a summable
child-prime fee. It permits arbitrarily many triangular or longer cycle
blocks sharing articulation primes, with unbounded heights and arbitrary
original residues. It uses one explicit product law per block, built from
the actual recursively feasible child domains. It never multiplies survival
fractions belonging to separately chosen cycle assignments.

The root-domain lower bound \(1/48\), and the nonroot lower bounds, are
marginal proportions of words admitting extensions. They are not asserted
to be lower bounds on the full original uncovered Haar density. Existence
of compatible witnesses is what the exact block recursion provides.

The supporting [finite rational certificate](../frontier/cover-geometry/cactus_block_fees.py)
retains all 528 cutoff inequalities and their [exact values](../frontier/cover-geometry/cactus_block_fees.json).
An independent [original-class control program](../frontier/cover-geometry/cactus_block_extension_controls.py)
retains full prime-power coordinates, derives blocks from the actual support
graph, and compares every conditional extension count with complete CRT
enumeration. Its [exact data](../frontier/cover-geometry/cactus_block_extension_controls.json)
include these controls:

| Original support geometry | Original period | Uncovered residues | Original Haar survival |
|---|---:|---:|---:|
| Two triangles sharing root 3, with higher powers and triple labels | 45045 | 8787 | 2929/15015 |
| Root 3 attached to 5, which joins two triangles | 255255 | 70210 | 118/429 |
| The path 3--5--7 attached to a triangle | 15015 | 4599 | 219/715 |

These finite controls test the exact recursion on original arithmetic data;
the universal theorem uses the proof and rational inequalities above. It is
an ordinary proof with finite exact computation, not a Lean certification.

The block-cut tree and the disjointness of child block interiors hold for
general graphs as well. The additional property used here is that deleting
the parent from a cycle leaves a path, whose internal cost obeys (CA7); a
triangle's extra three-prime labels are explicitly covered by (CA6).
A general biconnected block has no fee established by this argument. Already
a theta graph, consisting of three internally disjoint paths between the
same two endpoints, falls outside this fee argument. Its noncoverage already
follows from Schroeder's theorem because its cliques have size at most
three. Further work on such a graph therefore requires a specified stronger
quantitative target, such as a joint two-endpoint extension bound. The
current cycle fees establish no such bound for general blocks. Moduli with
four or more distinct prime factors, and their larger cliques, remain
outside both this cactus argument and the cited three-factor theorem.

<a id="a-bounded-number-of-cycle-breaking-vertices-in-each-component"></a>
#### A bounded number of cycle-breaking vertices in each component

The same [forest argument](06-block-saturation-and-the-actual-crossing-budget.md#arbitrary-forests-a-bound-independent-of-depth-and-degree) extends beyond forests. A feedback vertex set is a set
of vertices whose deletion leaves a forest. Its size is measured separately
in each connected component; the number of components remains unrestricted.
For a tail cutoff `q0` put `D=1+3/(q0-1)+2/(q0-1)^2` and define

\[
 C_0=\frac32D,\qquad
 z_k=C_kD,\qquad C_{k+1}=\frac{4z_k^2}{4z_k-1}.
 \tag{FV1}
\]

If every tail component has a feedback vertex set of size at most `k`,
then, for the same actual head law and original distinct moduli,

\[
 \mu\{x:\text{tail fibre is saturated}\}
 \le G C_k\sum_{q\text{ tail}}\frac1{(q-1)^2}.
 \tag{FV2}
\]

The case `k=0` is (AF2). For the induction step, choose a vertex `r` from
a nonempty feedback set in one component `J`, independently of the head
point. Let `alpha_r(x)` be the uniform fraction of its coordinate covered
by actual classes whose tail support is exactly `{r}`. Absorb the full
`r` prime power into the head with the unconditioned law `nu=mu times U_r`.
Each component `J_i` of `J-r` has a feedback set of size at most `k`.
Every remaining class belongs to exactly one `J_i` after this absorption:
its residual support is a clique and is therefore connected. In particular,
a triangle class containing `r` becomes a two-prime class in one residual
component. No such class is omitted or assigned twice.

Let `beta_i(x)` be the uniform probability over `r` that the family assigned
to `J_i` saturates its residual fibre. Saturation of `J` implies
`alpha_r+sum_i beta_i>=1`: otherwise some `r` value avoids its pure classes
and every residual component has an avoiding extension, which combine by
CRT. For any `B>1` and `A=B^2/(4(B-1))`, the identity

\[
 A t^2+B(1-t)-1=A\left(t-\frac{B}{2A}\right)^2
 \tag{FV3}
\]

gives `1[J saturated]<=A alpha_r^2+B sum_i beta_i`. The moment bound gives
`E_mu alpha_r^2<=G a_r^2`. The uniform transfer bounds `Gamma(nu)<=G D_r`,
where `D_r=1+3a_r+2a_r^2<=D`. The inductive forest-deletion estimate for all
the residual components therefore gives

\[
 \mu\{J\text{ saturated}\}
 \le G\left[A a_r^2+B C_kD_r
                        \sum_{q\in J\setminus\{r\}}a_q^2\right].
 \tag{FV4}
\]

There is no requirement that `nu` survive the pure-`r` classes: those were
separately charged through `alpha_r`. The subfamily assigned to each `J_i`
has no class wholly in its enlarged head. At each residual tail divisor
`t`, an enlarged head label `m r^f` determines the original modulus
`m r^f t`; thus distinctness is preserved even when projected moduli repeat.

Now set `z=C_kD`, `B=4z/(4z-1)` and `A=4z^2/(4z-1)=C_(k+1)`.
Here `z>=3/2`, so all denominators are positive, `A=Bz`, and (FV3) applies.
Both terms of (FV4) have coefficient at most `G C_(k+1)`.
Components already having a smaller feedback set obey the same bound,
because `C_(k+1)>=C_kD>=C_k`. Summation over all components proves (FV2).
The argument permits arbitrary degrees, exponents, component counts and
depths of attached trees. A feedback set of size one can break arbitrarily
many cycles sharing a vertex; this is more general than a single-cycle
component.

Two exact consequences of (FV2) and the prime-square bound (GS1) are:

| Head | Tail primes | Feedback vertices per component | Saturated-head mass upper bound |
|---|---|---:|---:|
| Arbitrary `{3,5,7}` head | `q>=23` | at most 1 | `<0.956460` |
| Complete star head | `q>73` | at most 2 | `<0.966288` |

For the first row, `D=138/121`, `C_1=3264065424/1458580343`, and

\[
 \frac{1889}{48}C_1S_{23}
 =\frac{1175604260732733206684398339119}
        {1229120627265994463000000000000}<1.            \tag{FV5}
\]

For the second row, `D=1580/1521`,
`C_2=387820588344395661352960000000000/170508100702446502707449794959279`,
and

\[
 177C_2S_{79}
 =\frac{16950596065609491264623331474432}
        {17541985668975977644799361621325}<1.           \tag{FV6}
\]

Every pseudoforest, meaning at most one cycle in each component, is covered
by the first row. Arbitrarily branching and deep trees may be attached to
each cycle, and a modulus may contain all three tail primes of a triangular
cycle. The second row implies that a full star completion must have a tail
component for which deleting any two vertices still leaves a cycle. Many
cycles in separate components do not suffice. These are ordinary proofs;
the exact recurrence values and inequalities are checked by the same
adjacent certificate as the forest constants.

Tree elimination has public antecedents in
[Csikvari--Nagy, *The Density Turan Problem*, Theorem 3.1 and Algorithm 3.3](https://arxiv.org/abs/1407.7873),
which use prescribed edge densities and a matching-polynomial criterion.
[He--Li--Liu--Wang--Xia, Theorem 6 and Corollary 38](https://arxiv.org/abs/1709.05143)
concern a tree event-dependency graph, a different hypothesis from a tree
of prime variables. Neither supplies the conditional square-energy and
cubic-potential estimate used here. No exact dominating theorem was found
in those searched scopes, and no global priority claim is made.
The verifier also checks all 16384 unary/binary constraint assignments on
a three-vertex binary path against its eight complete assignments, testing
exact-message completeness and the local cubic-potential inequality.
This finite regression checks the implementation against actual feasible
assignments; it does not replace the [arbitrary-tree proof](06-block-saturation-and-the-actual-crossing-budget.md#arbitrary-forests-a-bound-independent-of-depth-and-degree).

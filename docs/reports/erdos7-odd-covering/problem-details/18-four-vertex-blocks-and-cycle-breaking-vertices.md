[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](17-odd-cactus-noncoverage.md) · [Next](07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md)

<a id="four-vertex-blocks-with-a-common-descendant-budget"></a>
#### Four-vertex blocks with a common descendant budget

An ordinary proof extends the quantitative block recursion to arbitrary
four-vertex blocks. It permits original four-prime moduli and arbitrarily
many total primes, so the three-prime-divisors theorem does not directly
subsume its scope. The argument below covers all finite heights and every
prime range; the linked exact certificates supply only its finite
inequalities and original-arithmetic controls. No Lean certification or
literature-priority claim is made, and unrestricted Erdős #7 remains open.

##### Statement and the existing-result boundary

Let a finite family contain one residue class for each of a finite set of
distinct odd moduli greater than one. Its prime graph joins two primes when
some original modulus contains both. Suppose every nontrivial block of this graph is
either an edge, a simple cycle, or a block on four vertices. Then the family
does not cover the integers.
Isolated prime vertices are allowed and are handled by their pure-power classes.

Equivalently, it is enough to allow edge blocks, cycle blocks, and completed
four-vertex clique blocks: bounding all clique-supported labels on a
four-vertex block only overcounts its actual labels. The theorem allows
arbitrarily many such blocks, arbitrary original prime-power heights and
residues, and original moduli with four distinct prime factors.

The repository's audited source
[Schroeder source audit](../../../../Library/Arith/schroeder2026noncoverage.md) already supplies noncoverage when
every original modulus has at most three distinct prime factors, with no
bound on total prime support. Thus cactus or theta existence by itself is
not a new exclusion beyond that result. The result considered here retains
four-prime labels and allows arbitrarily many total primes. Consequently it
is not a direct specialization of that source theorem or of the separate
at-most-eight-total-primes exclusion recorded in
[total-support source audit](../../../../Library/Arith/schroeder2026nine.md). The latter source's local verification
boundary is recorded there and is not strengthened here.

The repository's four-prime-head theorem (P1) allows unrestricted interactions
above cutoff 67; it does not directly cover arbitrary smaller primes in
attached blocks. Its forest and feedback-set criteria have different
hypotheses. No global literature-priority claim is made. The present proof
uses quantitative cactus bounds as an ingredient and adds a common resource
budget for the three child domains of a four-vertex block.

##### Original coordinates and exact block recursion

Write \(Q\) for the original common period and
\(X_p=\mathbb Z/p^{h_p}\mathbb Z\), where \(h_p=v_p(Q)\). Let \(H_p\) be
uniform on \(X_p\). Root the block-cut tree of each component at prime three
when present and at any prime otherwise. All nonroot primes are at least
five.

For a prime \(p\), let \(D_p\) be the set of prime vertices strictly below
\(p\) in this rooted block-cut tree. Define \(V_p\subseteq X_p\) to consist
of the words admitting simultaneous avoidance in the entire descendant
subtree, including the pure-power classes at \(p\), and excluding its
incoming parent block. A child block \(B\) of \(p\) has child vertices
\(B\setminus\{p\}\). Its full-fibre blocker \(\mathcal B_{B\to p}\)
consists of parent words for which no tuple in
\(\prod_{q\in B\setminus\{p\}}V_q\) avoids the original classes of that
block. Then, with \(P_p\) the union of the pure-power classes at \(p\),
\[
 V_p=X_p\setminus\left(P_p\cup
                  \bigcup_{B\text{ child of }p}\mathcal B_{B\to p}\right),
 \qquad H_p(P_p)\le\frac1{p-1}.
 \tag{FB1}
\]

Every original mixed support is a clique and lies in exactly one block.
Every original class is therefore included once in this recursion. In
particular, a four-vertex block retains all its original pair, triple and
quadruple supports. Choices in different child blocks and subtrees glue
exactly through their common parent word.

For the three child vertices \(q_1,q_2,q_3\) of a four-vertex block, the sets
\(D_{q_1},D_{q_2},D_{q_3}\) are disjoint and avoid the entire block. This is
the joint structural information used below. Bounding three domains by
three independent copies of the same outside budget would discard it.

##### One original-label full-fibre estimate

For a block fix the single product law
\[
 \nu_B=\bigotimes_{q\in B\setminus\{p\}}H_q(\cdot\mid V_q).
 \tag{FB2}
\]
Let \(K\) bound the union probability of its original classes not involving
\(p\). Suppose the sum of child-coordinate probabilities of the classes
having each fixed positive parent exponent \(a\) is at most \(\lambda\).
For every integer \(r\ge1\) with
\(g=1-K-(r-1)\lambda>0\),
\[
 H_p(\mathcal B_{B\to p})\le
 F_{p,r}(\lambda,K)
 :=\frac{p^{1-r}\lambda}{(p-1)[1-K-(r-1)\lambda]}.
 \tag{FB3}
\]

Indeed a blocked fibre requires parent-touching load at least \(1-K\).
The exponents below \(r\) supply at most \((r-1)\lambda\). Integrating
the remaining load over the original parent coordinate gives at most
\(\lambda\sum_{a\ge r}p^{-a}\), since every original cylinder of exponent
\(a\) has parent measure \(p^{-a}\). Markov's inequality yields (FB3).
Distinct original moduli ensure at most one original class for a complete
exponent tuple. Heights are only overcounted by convergent geometric sums;
no projected labels are merged.

The exact parent comparison is
\[
 F_{p,r}(\lambda,K)
 =\frac2{p-1}\left(\frac3p\right)^{r-1}F_{3,r}(\lambda,K).
 \tag{FB4}
\]

##### Fees and the stronger induction statement

Use the following fees on primes at least five:
\[
 f(5)=\frac7{24},\quad f(7)=\frac18,\quad
 f(11)=\frac1{24},\quad f(13)=\frac1{48},\quad
 f(q)=2^{-(q-1)/2}\quad(q\ge17).
 \tag{FB5}
\]
Completing the last primes by all odd integers at least seventeen gives
\[
 \sum_{q\ge5\text{ prime}}f(q)
 \le\frac7{24}+\frac18+\frac1{24}+\frac1{48}
       +\sum_{j\ge8}2^{-j}
 =\frac{187}{384}=:F<\frac12.
 \tag{FB6}
\]
Put
\[
 a_p=\frac1{p-1},\qquad
 c_5=\frac3{10},\qquad c_p=\frac2{p-1}\quad(p\ge7).
\]
The induction statement for a nonroot prime is
\[
 \delta_p:=H_p(V_p)
 \ge1-a_p-c_p\sum_{q\in D_p}f(q).
 \tag{FB7}
\]
Since \(p\notin D_p\), (FB6) implies the uniform consequences
\[
 \delta_5\ge\frac{177}{256}>\frac23,\qquad
 \delta_7\ge\frac{821}{1152}>\frac23,
 \qquad
 \delta_p\ge1-\frac{379}{192(p-1)}
      \ge\frac{1541}{1920}>\frac23\quad(p\ge11).
 \tag{FB8}
\]

The local fee claims to be proved are:

* an edge is charged to its one child prime;
* a cycle is charged to its two smallest child primes;
* a four-vertex block is charged to its three child primes;
* each parent-three bound is at most its assigned fee; and the cutoff may
  always be chosen at least two when every child prime is at least seven.

Some infinite regimes use still smaller charges. For closing the induction,
these stronger bounds can always be weakened to the listed fee sums.

##### Edge and cycle fees under the revised fee schedule

The [preceding quantitative cactus proof (CA1)--(CA25)](17-odd-cactus-noncoverage.md#arbitrary-odd-cactus-graphs-are-noncovering) proves its edge and cycle bounds
assuming only the uniform child density \(2/3\), with
\(\beta_q=3/[2(q-1)]\). Its full-fibre estimate is exactly (FB3).
Its finite certificate contains 528 exact rational rows. Each of those
bounds remains below its revised charge in (FB5), including the rows with
second child prime 97 that charge only the first child. The new certificate
also checks a qualifying cutoff for every row. All these cutoffs have the
required lower bound two when the smallest child is at least seven.

For clarity, the infinite argument used there consists of two parts. With
one child prime below 97 and another above it, the certified boundary at 97
dominates by the proved monotonicity of the complete path fraction, not by
substituting artificial endpoints into a bound for the internal edge sum.
When all child primes are at least 97, the explicit cutoff
\(r=\lfloor2n/3\rfloor-1\), for smallest child \(2n+1\), gives a fee at
most \(2^{-n}\). These large-prime fees are unchanged in (FB5). Thus the
existing finite inequalities and their analytic tails establish the edge
and cycle claims for the present schedule. This is reuse of that quantitative
argument, not a claim of new cactus noncoverage.

##### Four-vertex block parameters from one joint outside budget

Let the child primes of a four-vertex block be \(s<t<u\). Put
\[
 e_i=\sum_{q\in D_{q_i}}f(q),\qquad (q_1,q_2,q_3)=(s,t,u).
\]
By disjointness of descendant sets,
\[
 e_i\ge0,\qquad \sum_i e_i\le F-f(s)-f(t)-f(u)=:E.
 \tag{FB9}
\]
If the parent is at least five, subtracting its fee would strengthen (FB9);
we do not need that saving.

The induction statement (FB7) gives the geometric coordinate caps
\[
 \frac{a_q}{\delta_q}\le b_q(e_q),\qquad
 b_5(e)=\frac1{3-(6/5)e},\qquad
 b_q(e)=\frac1{q-2-2e}\quad(q\ge7).
 \tag{FB10}
\]
The denominator is positive on \(0\le e\le F\). Under the single actual
law (FB2), summing the original exponent vectors gives valid block parameters
\[
 \lambda=\prod_{i=1}^3(1+b_{q_i}(e_i))-1,
 \qquad
 K=\sum_{i<j}b_{q_i}(e_i)b_{q_j}(e_j)
          +\prod_i b_{q_i}(e_i).
 \tag{FB11}
\]
In \(\lambda\), the product of all three child weights accounts for every
original four-prime label at that parent exponent. In \(K\), the triple
product accounts for original child-only triangle labels. Neither is removed.

###### A common cutoff can be certified at three budget vertices

Fix a positive fee \(C\) and an integer \(r\ge1\). Set
\(A=2C3^{r-1}>0\). With \(b_i=b_{q_i}(e_i)\), define
\[
 H_{A,r}(e)=
 [1+A(r-1)]\sum_i b_i
 +(1+Ar)\left(\sum_{i<j}b_ib_j+b_1b_2b_3\right).
 \tag{FB12}
\]
The inequality \(H_{A,r}(e)\le A\) is exactly
\[
 \lambda\le A[1-K-(r-1)\lambda].
 \tag{FB13}
\]
Because \(\lambda>0\), it implies positive gap and
\(F_{3,r}(\lambda,K)\le C\).

Every nonempty product of the \(b_i\) is log-convex in \(e\): its logarithm
is a sum of functions \(-\log(a-de_i)\) with positive second derivative.
It is therefore convex. All coefficients in (FB12) are positive, so \(H\)
is convex and coordinatewise increasing. On the simplex
\(e_i\ge0,\sum e_i\le E\), its maximum is attained at one of
\[
 (E,0,0),\qquad(0,E,0),\qquad(0,0,E).
 \tag{FB14}
\]
The remaining simplex vertex zero is dominated by these; the case \(E=0\)
is immediate. Thus it suffices to find **one common cutoff** that satisfies
(FB13) at all three vertices (FB14). Using a different cutoff at each vertex
would not justify this argument.

This convex test preserves the joint outside budget. In particular, it does
not let a small outside prime simultaneously consume the full descendant
budget in three disjoint child subtrees.

##### Closed finite box and its two boundary faces

The finite certificate evaluates (FB10)--(FB14) by exact rational arithmetic.
For each row it considers common cutoffs starting at one when \(s=5\), and
at two otherwise. It checks all three gaps and the maximum of their three
parent-three costs at that same cutoff. Its complete finite partition is:

1. **1540 interior rows:** primes \(5\le s<t<u<97\), fee
   \(C=f(s)+f(t)+f(u)\), budget \(E=F-C\).
2. **231 one-large-coordinate rows:** primes \(5\le s<t<97\), proxy child
   tuple \((s,t,97)\), fee \(C=f(s)+f(t)\), budget \(E=F-C\).
3. **22 two-large-coordinate rows:** prime \(5\le s<97\), proxy tuple
   \((s,97,99)\), fee \(C=f(s)\), budget \(E=F-C\).

The number 99 in the last line is an odd-integer upper-bound proxy, not an
assertion that 99 is prime. Distinct odd primes \(u>t\ge97\) satisfy
\(u\ge99\), which suffices. Formula (FB10) for this proxy has its ordinary
positive denominator.

All 1793 rows pass. For example, the interior row \((5,7,11)\) has common
cutoff one and gives
\[
 \max_{\text{three vertices}}F_{3,1}
   =\frac{33435}{73912}
   <\frac{11}{24},\qquad
 \frac{\text{cost}}{\text{fee}}=\frac{100305}{101629}<1.
 \tag{FB15}
\]
The certificate takes the first qualifying common cutoff in each row; it
does not need to optimize that cutoff. It recomputes the original support
sum by its seven nonempty subset masks and checks (FB13) by integer cross
multiplication as well as rational comparison. Its 528 edge and cycle rows
also pass under the revised fees.

The boundary rows cover infinite ranges as follows. When \(s<t<97\) and
\(u\ge97\), the actual budget is at most \(F-f(s)-f(t)\), and
\(b_u(e)\le b_{97}(e)\) for every nonnegative \(e\) in this larger simplex.
The polynomial (FB12) is increasing in all its coordinate caps. The certified
one-large row therefore applies, charging only \(f(s)+f(t)\). When
\(s<97\le t<u\), use budget \(F-f(s)\) and coordinate caps
\(b_t(e)\le b_{97}(e)\), \(b_u(e)\le b_{99}(e)\). This gives the two-large
row and fee \(f(s)\).

In particular, these boundary arguments do not incorrectly hold the exact
budget fixed while increasing a child prime: its fee decreases, so the
available outside budget can increase. The boundary simplex was deliberately
enlarged before applying coordinate monotonicity.

##### The fully infinite large-minimum range

Suppose the smallest child prime is \(s=2n+1\ge97\), so \(n\ge48\).
Since \(e_i\le F<1/2\), (FB10) gives
\(b_q(e_i)\le1/(q-3)\). The three distinct child weights are thus at most
\[
 x=\frac1{2(n-1)},\qquad y=\frac1{2n},\qquad
 z=\frac1{2(n+1)}.
\]
Consequently the two parameters in (FB11) satisfy
\[
 \lambda\le\lambda_n
 =\frac{12n^2+6n-3}{8n(n^2-1)},\qquad
 K\le K_n=\frac{6n+1}{8n(n^2-1)}.
 \tag{FB16}
\]
Choose \(r=\lfloor2n/3\rfloor-1\ge31\). Then
\[
 1-K-(r-1)\lambda
 \ge1-K_n-(2n/3-2)\lambda_n
 =\frac{20n^2-7}{8n(n^2-1)}>0,
 \tag{FB17}
\]
and
\[
 \frac{\lambda}{1-K-(r-1)\lambda}
 \le\frac{12n^2+6n-3}{20n^2-7}\le\frac23.
 \tag{FB18}
\]
The last inequality is equivalent to \(4n^2-18n-5\ge0\). At \(n=k+5\)
this is \(4k^2+22k+5\ge0\), so it holds in the required range.

It follows that
\[
 F_{3,r}\le3^{-r}\le2^{-n}=f(s).
 \tag{FB19}
\]
For the exponential comparison, writing \(n=3m+j\), \(j=0,1,2\), yields
the three ratios \((9/8)^m/3\), \((9/8)^m/6\), and \((9/8)^m/4\).
Here \(m\ge16\), and the exact integer inequality
\(9^{16}>6\cdot8^{16}\) proves all three ratios exceed one. This establishes
the four-vertex fee claim in the remaining infinite regime.

##### Close the induction and assemble an uncovered word

Assume (FB7) for all child domains. Then (FB8) permits the reused edge and cycle
estimates. For a four-vertex block, the actual disjoint descendant sets give
(FB9), and the common-budget, finite-boundary and infinite-tail arguments above give its fee. Each block cutoff is at least two if
every child prime is at least seven.

For an actual parent five, no child prime is three or five. Thus every
cutoff is at least two, and (FB4) is bounded by \(c_5=3/10\). For a parent
\(p\ge7\), (FB4) is bounded by \(c_p=2/(p-1)\). Distinct child blocks have
disjoint child vertex sets, and their charged primes lie inside \(D_p\).
Equation (FB1) now gives exactly (FB7). Leaves satisfy (FB7) directly with empty
descendant set. The finite bottom-up induction is therefore complete.

If the root is three, its child-block fees total at most \(F\), so
\[
 H_3(V_3)\ge1-\frac12-F=\frac5{384}>0.
 \tag{FB20}
\]
If the root is at least five, the same argument as for nonroots gives the
positive bounds (FB8). Choose a root word in its nonempty domain and then the
simultaneous block and descendant witnesses supplied by (FB1). All original
classes are avoided. Finally combine different connected components by CRT.
Isolated prime vertices and the empty family are immediate from (FB1).

This proves the stated noncoverage theorem for every finite block tree in
the specified class. Bounds (FB7) and (FB20) concern proportions of coordinate
words admitting extensions. They are not claimed to be proportions of all
uncovered words under the full original Haar law; extension multiplicities
must be retained when making that different calculation.

##### Remaining boundary

The proof allows any number of four-prime blocks, including blocks carrying
all their original four-prime labels, joined through articulation primes.
It does not treat an arbitrary larger block with interlocking four-prime
supports, or a five-prime support. The crucial new closure is the common
outside-prime budget of the actual disjoint child subtrees, followed by one
cutoff certified on its entire simplex. Neither an independent optimization
of its three domains nor a finite enumeration of graph shapes is used.


##### Exact certificates and original-arithmetic controls

The [fee certificate](../frontier/cover-geometry/four_vertex_block_fees.py)
retains [all exact rows](../frontier/cover-geometry/four_vertex_block_fees.json).
It checks 1793 four-vertex rows and 528 edge/cycle rows under the revised
fees. Its support sums use nonempty subset masks and rational arithmetic;
all three budget vertices in a row share one cutoff.

The [original-class control program](../frontier/cover-geometry/four_vertex_block_extension_controls.py)
retains full prime-power coordinates and every original residue and modulus.
Its [exact results](../frontier/cover-geometry/four_vertex_block_extension_controls.json)
compare all 18 vertex, block and whole-system conditional count vectors
against independent CRT enumeration:

| Original support geometry | Original period | Uncovered residues | Original Haar survival |
|---|---:|---:|---:|
| A complete four-prime block on 3, 5, 7, 11, higher powers of 3, and the hanging edge 5--13 | 45045 | 8544 | 2848/15015 |
| Two complete four-prime blocks sharing 3, with other primes 5, 7, 11 and 13, 17, 19 | 4849845 | 1001430 | 66762/323323 |

The first example includes original moduli 1155 and 3465. Its three child
subtrees have actual fee expenses `(1/48, 0, 0)`, whose sum is bounded by
`11/384`. The second example has block extension-count vectors
`(226, 162, 166)` and `(3410, 3000, 3105)` on the same root coordinate.
They are multiplied at the same root word before the pure-root exclusion;
separately averaged block counts would not give the correct joint count.

Both standard-library programs run with assertions enabled:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/four_vertex_block_fees.py
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/four_vertex_block_extension_controls.py
```

Their finite examples test the exact recursion and probability convention;
the ordinary proof above, rather than enumeration of these examples,
establishes the arbitrary-height and arbitrary-block-count assertion.

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

The case `k=0` is [(AF2)](06-block-saturation-and-the-actual-crossing-budget.md#arbitrary-forests-a-bound-independent-of-depth-and-degree). For the induction step, choose a vertex `r` from
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

Two exact consequences of (FV2) and the [prime-square bound (GS1)](07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#absorbing-a-finite-set-of-hub-primes) are:

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
[adjacent certificate](../certificates/star_block_obstruction_certificate.json) as the forest constants.

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

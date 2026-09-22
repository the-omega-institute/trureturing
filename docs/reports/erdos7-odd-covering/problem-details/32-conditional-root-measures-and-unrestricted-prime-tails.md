[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Conditional root measures and unrestricted prime tails

This chapter bounds the actual root words surviving both the original
pure-3 classes and a distinguished block. It gives a positive root
margin for six specified heads, including when that same block contains
an arbitrary finite set of additional primes greater than 10000. There
is no bound on the number of those additional primes or on the support
arity of a class. Original prime powers and residues remain unrestricted.

Sections 1–5 give an avoiding word for the connected prime-interaction
component containing 3. Noncoverage of the whole family additionally
requires avoiding words for its other components. Section 6 supplies
those obligations for a specified graph class.

The conclusions are ordinary mathematical results with exact rational
arithmetic checks. The analytic prime-product estimate is a separately
stated external premise. No new Lean theorem or unrestricted solution of
Erdős #7 is asserted.

## 1. Actual domains and the root-survivor statement

Restrict the original finite family of numerically distinct odd moduli
greater than one to its prime-interaction component containing 3, keeping
the original full prime-power coordinates. Avoidance of the other
components remains a separate obligation. Write $H_p$ for uniform
measure on the original finite $p$-coordinate. Let $A_3$ be the
complement of the actual original pure-3 classes. Distinctness gives

\[
 \delta_3:=H_3(A_3)\ge1-\sum_{a\ge1}3^{-a}=\tfrac12.
 \tag{JR1}
\]

The distinguished root block has child primes $J=(q_1,\ldots,q_k)$.
For each child use its actual extension domain $V_{q_i}$, including
avoidance of its pure classes, and the actual fee sum $e_i$ of its
strict descendant prime set. Assume the established descendant invariant

\[
 H_{q_i}(V_{q_i})\ge1-\frac1{q_i-1}-c_{q_i}e_i
       =\frac{d_i}{q_i-1}>0,
 \quad d_i=q_i-2-\gamma_i e_i,
 \tag{JR2}
\]

where $c_5=3/10$, $c_q=2/(q-1)$ for $q\ge7$, and

\[
 \gamma_i=(q_i-1)c_{q_i}=
 \begin{cases}6/5,&q_i=5,\\2,&q_i\ge7.\end{cases}
\]

Choose $0\le t_i<d_i$, put $a_i=d_i-t_i$, and assume

\[
 \kappa_i=\frac{q_i-1}{a_i}\le q_i.
 \tag{JR3}
\]

Define independent auxiliary nonnegative integer runs by

\[
 \Pr(K_0\ge a)=\frac2{3^a},\qquad
 \Pr(K_i\ge a)=\frac{\kappa_i}{q_i^a}\quad(a\ge1),
\]

and set

\[
 Y_i=\prod_{0\le j<i}(1+K_j),\qquad
 S_J(e;t)=\sum_{i=1}^k\frac{\mathbb E(Y_i-1-t_i)_+}{a_i}.
 \tag{JR4}
\]

Keep the fees of Chapters 25–31:

\[
 F_* =\frac{1493}{3072},\quad
 f(5)=\frac7{24},\ f(7)=\frac18,\ f(11)=\frac1{24},
 f(13)=\frac1{48},\quad f(q)=2^{-(q-1)/2}\ (q\ge17).
\]

Let $E=F_* -\sum_{q\in J}f(q)$ and $x=\sum_i e_i$.
The descendant sets are disjoint actual prime sets, so $0\le x\le E$.
Assume the union of all other root blockers has original $H_3$-mass
at most $E-x$. This hypothesis concerns those same original blocks
and domains; it is not a charge for arbitrary unproved outside blocks.

**Root-survivor bound.** If $S_J(e;t)\le1$, the actual root extension
domain satisfies

\[
 H_3(V_3)\ge\frac{1-S_J(e;t)}2-E+x.
 \tag{JR5}
\]

The next two sections prove this bound, preserving the full original
labels until the conditional comparison has been completed.

## 2. One actual law and a conditional label comparison

Begin with the actual bases

\[
 U_3=H_3(\cdot\mid A_3),\qquad
 U_i=H_{q_i}(\cdot\mid V_{q_i}).
\]

Every original depth-$a$ prefix in child coordinate $i$ has base
mass at most $(q_i-1)/(d_iq_i^a)$. No symmetry or prefix-closure
assumption on $V_{q_i}$ is used.

Assign each original mixed class of the block to its last child
coordinate. For a full earlier word $z$, let $B_i(z)$ be the union
of its matching current-coordinate prefixes, let

\[
 \alpha_i(z)=U_i(B_i(z)),\qquad \theta_i=t_i/d_i,
\]

and use the following density relative to $U_i$:

\[
 k_i(z,u)=
 \begin{cases}
 [1-\min(\alpha_i(z),\theta_i)]^{-1},&u\notin B_i(z),\\[2pt]
 (\alpha_i(z)-\theta_i)_+/[\alpha_i(z)(1-\theta_i)],&u\in B_i(z).
 \end{cases}
 \tag{JR6}
\]

The second value is taken as zero when $\alpha_i=0$. Separating the
cases $\alpha_i\le\theta_i$ and $\alpha_i>\theta_i$ shows that
the density integrates to one for every complete earlier word. Both
values are at most $1/(1-\theta_i)$. Thus each stage preserves the
whole previous joint law, and every depth-$a$ prefix has conditional
mass at most $\kappa_i/q_i^a$, conditional on that entire past.
The final actual law $\mu$ retains root marginal $U_3$.

The final probability of the stage-$i$ mixed union is

\[
 \frac{\mathbb E(\alpha_i-\theta_i)_+}{1-\theta_i}.
 \tag{JR7}
\]

For an original ending label with numerical modulus $nq_i^a$, retain
its own earlier-coordinate cylinder $A_{n,a}$. Here $n>1$, since
pure child classes are absent from the base domain. Labels with equal
$n$ but different $a$ can have different earlier residues. Put

\[
 R_i(z)=\sum_{\text{original ending labels }(n,a)}
          \frac{q_i-1}{q_i^a}\mathbf1_{A_{n,a}}(z).
\]

The base union bound gives $\alpha_i\le R_i/d_i$, so (JR7) is at
most $\mathbb E(R_i-t_i)_+/a_i$.

The conditional comparison used to bound this hinge has an elementary
proof. For a finite set of labels, suppose their indicator probabilities
are bounded, conditional on the entire earlier past, by deterministic
numbers $r_1\ge\cdots\ge r_m$. Put $I_j=\{1,\ldots,j\}$.
For any increasing supermodular set function $F$, increasing
increments imply

\[
 F(S)\le F(\varnothing)+
       \sum_{j\in S}\bigl(F(I_j)-F(I_{j-1})\bigr).
 \tag{JR8}
\]

Indeed, telescope over the members of $S$; the predecessors already
present in $S$ form a subset of $I_{j-1}$, so each increment is
bounded by the displayed full-chain increment. The increments are
nonnegative. Taking conditional expectations in (JR8) therefore bounds
the result by the expectation of $F(\{j:U\le r_j\})$, for a fresh
uniform $U$.

Apply this replacement first to the last earlier coordinate and then
work backwards. For fixed earlier indicators and already replaced
auxiliary coordinates, the function is the hinge of a modular load
with nonnegative label weights; it is increasing and supermodular.
Averaging preserves those properties. Each replacement retains the
untouched actual earlier law. Consequently fresh independent uniforms
are justified in the comparison law, without asserting independence of
the actual coordinates or labels.

After all replacements, a label's activity depends only on its complete
earlier exponent vector: a required exponent $b$ at coordinate $j$
is active when $K_j\ge b$. A coordinate absent from the label is
always active. Only now may labels with the same complete numerical
cofactor $n$ be grouped. Numerical distinctness permits at most one
label for each pair $(n,a)$, whence its total aligned weight is at most

\[
 \sum_{a\ge1}\frac{q_i-1}{q_i^a}=1.
 \tag{JR9}
\]

The completed auxiliary exponent box has exactly $Y_i-1$ nonempty
complete cofactors. It includes every support arity and every earlier
prime power. Thus the stage bound is the $i$-th summand of (JR4).
The original inventory is finite; completing it enlarges a nonnegative
load, and the geometric first moments are finite. There is no finite
height truncation of the original problem.

## 3. Return to the actual root intersection

Let $B_{\rm core}$ be the original root words for which the mixed
core classes cover every tuple in $\prod_i V_{q_i}$. For each root
word in $A_3\cap B_{\rm core}$, the constructed law gives conditional
probability one to the mixed core union. The union bound on the same
final law and the unchanged root marginal therefore give

\[
 \frac{H_3(A_3\cap B_{\rm core})}{\delta_3}\le S_J(e;t).
\]

For $S_J\le1$,

\[
 H_3(A_3\setminus B_{\rm core})
       \ge\delta_3(1-S_J)\ge\frac{1-S_J}{2}.
\]

Subtract the actual other-root union bound $E-x$, proving (JR5).
At a surviving root word the core has an avoiding child tuple, and
each other block has its avoiding extension. The disjoint actual
descendant subtrees permit block-cut gluing as in Chapters 23 and 28.
Positive original Haar mass therefore gives an original avoiding word
for the component containing 3. Combining it into an avoiding word for
the whole family requires avoiding words for every other component.

This estimates the joint pure-3/core survivor. It does not prove the
previous untrimmed-blocker inequality by changing that inequality's
parent measure.

## 4. Six heads and expense sensitivity

Take the reference children and fixed thresholds

\[
 J_*=(5,7,11,13,17),\qquad t=(0,1,3,5,7),\qquad
 E_{\max}=\frac{67}{3072}.
 \tag{JR10}
\]

All six heads in the table below dominate $J_*$ coordinatewise.
For a fixed position and expense, both $\kappa/q^a$ and the reciprocal
current denominator decrease as that prime increases. The first prime
is always 5; all other positions have the same $\gamma=2$.
Stochastic domination therefore gives $S_J(e;t)\le S_{J_*}(e;t)$.
This is a comparison of bounds, not a replacement of original moduli.

The exact arithmetic certificate gives

\[
 S_{J_*}(0;t)=
 \frac{2379346060993228562427403831}
      {2659278071347311162498750000}<\frac{179}{200},
 \tag{JR11}
\]

and at the full box corner $e_i=E_{\max}$,

\[
 S_{J_*}<\frac{909}{1000},\qquad
 \nabla S_{J_*}<\frac1{1000}(288,215,73,54,25)
                 <(1/3,\ldots,1/3).
 \tag{JR12}
\]

The corner derivative bounds apply throughout the box. To justify this,
write $X=1+K$ for a run with cap $\kappa$. Its law is affine:

\[
 \Pr(X=1)=1-\kappa/p,\qquad
 \Pr(X=n)=\kappa(p-1)/p^n\quad(n\ge2).
 \tag{JR13}
\]

Its derivative in $\kappa$ is $(G_p-\delta_1)/p$, where $G_p$
is a probability law supported on integers at least 2. The function
$(\prod_j x_j-T)_+$ is increasing and has increasing differences
in every pair of coordinates on $x_j\ge1$. Integrating one or two
such differences proves nonnegative first and mixed second derivatives
of its expectation with respect to the independent caps. Each cap is
increasing and convex in its own expense. The stage denominator
reciprocal is likewise increasing and convex and depends only on the
current expense, while its numerator depends only on earlier expenses.
Every pure and mixed second expense derivative is consequently
nonnegative. Integrating the corner gradient bound along the segment
from zero to the actual expense vector yields

\[
 S_J(e;t)\le S_{J_*}(0;t)+\sum_i L_i e_i
              <\frac{179}{200}+\frac{x}{3},\quad
 L=\frac1{1000}(288,215,73,54,25).
 \tag{JR14}
\]

The box supplies derivative bounds; it is not charged as five actual
copies of $E_{\max}$. Each actual descendant fee has one owner.
Combining (JR5) and (JR14) gives

\[
 H_3(V_3)\ge\frac{1-S_{J_*}(0;t)}2-E
                 +\sum_i(1-L_i/2)e_i
       >\frac{21}{400}-E+\frac56x.
 \tag{JR15}
\]

The six exact margins are as follows. The last column also subtracts
the tail allowance established in the next section.

| Head children $J_0$ | $E_0=F_* -\sum_{q\in J_0}f(q)$ | Head constant $21/400-E_0$ | Dense-tail constant $81/2000-E_0$ |
| --- | --- | --- | --- |
| $5,7,11,13,17$ | $3/1024$ | $1269/25600$ | $4809/128000$ |
| $5,7,11,13,19$ | $5/1024$ | $1219/25600$ | $4559/128000$ |
| $5,7,11,13,23$ | $13/2048$ | $2363/51200$ | $8743/256000$ |
| $5,7,11,13,29$ | $111/16384$ | $18729/409600$ | $69069/2048000$ |
| $5,7,11,13,31$ | $223/32768$ | $37433/819200$ | $138013/4096000$ |
| $5,7,11,17,19$ | $67/3072$ | $2357/76800$ | $7177/384000$ |

Every row has the additional term $5x/6$. In particular the uniform
head bound is $H_3(V_3)>2357/76800+5x/6$. Even the rectangular
corner estimate in (JR12) gives a positive constant margin; ownership
improves it. The effective change is the conditioned actual root law
and its complete-label comparison. These heads already lie within the
finite-block conclusion of Chapter 31; the next result permits an
unbounded number of vertices in the distinguished block itself.

## 5. Arbitrarily many additional primes above 10000

Let the distinguished block have vertices

\[
 \{3\}\cup J_0\cup T,
\]

where $J_0$ is one of the six heads and $T$ is any finite set of
primes greater than $B=10000$. Keep the actual descendant invariant
(JR2) and actual other-root charges. Expose the five head children
first using (JR10), then the tail primes in increasing order. Every
original class is still assigned to its last coordinate; classes may
mix arbitrary head and tail supports and powers.

For a tail prime $q$, choose

\[
 d_q=q-2-2e_q\ge q-3,\qquad
 t_q=d_q/2,\qquad \kappa_q=2(q-1)/d_q.
 \tag{JR16}
\]

Here $e_q\le E\le E_0\le E_{\max}<1/2$, so the denominators are
positive and $\kappa_q\le q$. The elementary bound
$(u-t)_+\le u^2/(4t)$ gives a tail ending charge at most

\[
 \frac{\mathbb E(Y_q-1)^2}{d_q^2}
       \le\frac{\mathbb E Y_q^2}{d_q^2}.
 \tag{JR17}
\]

For any auxiliary run,

\[
 \mathbb E(1+K_p)^2=1+\kappa_p\frac{3p-1}{(p-1)^2}.
\]

For tail primes $p\ge19$,

\[
 \mathbb E(1+K_p)^2
 \le1+\frac{2(3p-1)}{(p-1)(p-3)}
 \le1+\frac7{p-1}
 \le\left(\frac p{p-1}\right)^7.
 \tag{JR18}
\]

The middle inequality is equivalent to $p\ge19$, and the last is
the binomial inequality. Including the root coordinate, the reference
head moment at the expense corner is

\[
 M_2=\frac{3112461874161011540673}{47325920018794268621}<66.
 \tag{JR19}
\]

Monotonicity in expenses and the preceding prime comparison give this
same upper bound for every actual head under consideration.

Use the explicit prime-product premise

\[
 \prod_{B<p\le z}\frac p{p-1}
 \le c_\ell\frac{\log z}{\log B},\qquad
 c_\ell=\frac{2\ell^2+1}{2\ell^2-1},
 \tag{JR20}
\]

valid for $B\ge286$, integer $\ell\ge3$, $3^\ell\le B$, and
$z\ge B$. The inspected pinned source is Schroeder's *Noncoverage
for Distinct Odd Moduli with at Most Three Prime Divisors*, Lemma 8.2,
TeX label `lem:mertens`. It derives (JR20) from Rosser–Schoenfeld,
*Approximate formulas for some functions of prime numbers*, Illinois
Journal of Mathematics 6 (1962), Theorem 8, equations (3.28)–(3.29).
The pinned source statement and ratio derivation were inspected; the
original Rosser–Schoenfeld PDF was not independently retrieved. This
analytic premise is not certified by the rational program below.

The archive SHA-256 is
`5956327277ac47dd6e98a0a38f2a785cd61e647560c7f6ab5c73a63cf49faa51`.
Its member `three-prime-factors-complete/publication/three_factors/paper/main.tex`
has SHA-256
`291020863f5fbb4f2d98aa0a1d5ac63349bd8c565d4ab07422aee83d23825451`.
No source attachment or geometry computation is imported by this chapter's
checker.

For integer $\ell\ge4$, the premise implies $\log B>\ell>7/2$.
Independence of the auxiliary runs, (JR18), and (JR20) give

\[
 S_{\rm tail}\le
 66c_\ell^7\left(\frac B{B-3}\right)^2
 \sum_{q>B}\frac{(\log q/\log B)^7}{q^2},
\]

where extending the actual finite prime set to all primes only enlarges
the bound. The product bound may include the current prime even though
the original $Y_q$ uses only earlier primes. Also,
$(q-3)^{-2}\le[B/(B-3)]^2q^{-2}$.

The function $(\log z)^7/z^2$ decreases on $[B,\infty)$.
Enlarge the prime sum to integers and use the integral from integer
$B$:

\[
 \sum_{q>B}\frac{(\log q/\log B)^7}{q^2}
 \le\int_B^\infty\frac{(\log z/\log B)^7}{z^2}\,dz
 =\frac1B\sum_{h=0}^7
       \frac{7!}{(7-h)!(\log B)^h}.
\]

The substitution $z=Be^u$, followed by the binomial expansion and
$\int_0^\infty u^he^{-u}\,du=h!$, proves the equality. Replacing
$\log B$ by its lower bound $\ell$ in the positive sum gives

\[
 S_{\rm tail}\le66\tau_7(B,\ell),\qquad
 \tau_7(B,\ell)=\frac{c_\ell^7}{B}
       \left(\frac B{B-3}\right)^2
       \sum_{h=0}^7\frac{7!}{(7-h)!\ell^h}.
 \tag{JR21}
\]

For $B=10000$, $\ell=8$, all hypotheses hold and the exact value is

\[
 66\tau_7(10000,8)=
 \frac{5214935802363444072691875}{218135012396331463923822592}
 <\frac3{125}.
 \tag{JR22}
\]

Let $x_{\rm head}$ be the expense owned by head children and let
$x$ include all head and tail descendants. The estimates concern
one full normalized-kernel schedule, so

\[
 S_J<\frac{179}{200}+\frac{x_{\rm head}}3+\frac3{125}<1.
\]

Use $E\le E_0\le67/3072$ and $x_{\rm head}\le x$ in (JR5):

\[
 H_3(V_3)>
 \frac{1-179/200-3/125}{2}-E+x-\frac{x_{\rm head}}6
 \ge\frac{7177}{384000}+\frac56x>0.
 \tag{JR23}
\]

Thus the component containing 3 has an avoiding word. If each other
prime-interaction component is also avoidable, the Chinese remainder
theorem combines those words into noncoverage of the whole family.
The tail may contain every prime between 10000 and an arbitrarily large
endpoint; there is no reciprocal-sparsity hypothesis.

## 6. A graph class fulfilling the external block obligations

One concrete application allows a distinguished block of the preceding
head-plus-tail form and requires every other graph block to have at
most seven vertices. The non-3 descendant fees of Chapter 31 supply
(JR2). Every head contains 5 and 7. A different root block shares only
the root 3 with the distinguished block and therefore contains neither
5 nor 7. The exceptional root classes of Chapters 28–31 each contain
at least two of $\{5,7,11\}$, so no other root block is exceptional.
Their direct fee bounds and the actual disjoint ownership accounting
supply the other-root charge $E-x$.

The existing block-cut gluing supplies an avoiding word in the component
containing 3. Every block in every other component also has at most
seven vertices, so Chapter 31 supplies an avoiding word for each of
those components. Their prime sets are disjoint, and the Chinese
remainder theorem combines all these words into an avoiding residue
for the original family. This permits an arbitrarily large dense block,
with arbitrary classes across its head and tail, while keeping the
remaining blocks in a proved recursive class. It does not grant a
fee bound to a second arbitrary large block. The distinguished block
also cannot contain an additional prime at most 10000 outside its
specified head. Removing that restriction remains open for this route.

## 7. Exact arithmetic and its boundary

The standalone
[certificate program](../frontier/cover-geometry/joint_root_dense_tail_certificate.py)
and [rational results](../frontier/cover-geometry/joint_root_dense_tail_certificate.json)
use the identity, for integer $T\ge1$,

\[
 \mathbb E(Y-T)_+=\mathbb EY-T+
      \sum_{m=1}^{T-1}(T-m)\Pr(Y=m).
 \tag{JR24}
\]

The full infinite tail is retained in the exact mean. Direct enumeration
of the low-product tuples for $T=1,2,4,6,8$ has respective counts
$0,1,7,23,61$. Five-variable rational automatic differentiation
computes the exact expense gradient. The program checks (JR11)–(JR12),
(JR19), (JR22), all six table rows, and all numerical applicability
conditions. It uses only the Python standard library, accepts no oracle
attachment, and refuses execution with assertions disabled.

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_root_dense_tail_certificate.py \
  --output /tmp/joint-root-dense-tail.json
```

The rational zero/corner charges, every derivative, the head second
moment, and the tail fraction also agree with a separate scalar
multiplicative-convolution implementation. These checks certify the
finite arithmetic. The normalized-law construction, conditional label
comparison, expense monotonicity, prime-product premise, and graph
gluing are ordinary mathematical arguments, not outputs of a Lean
kernel. The result provides neither an arithmetic covering counterexample
nor an unrestricted noncoverage theorem.

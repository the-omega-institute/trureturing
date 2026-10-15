# Recursive relational observation: native graph-cover and Bethe boundaries

The constructor-network representation is equality-aware and admits arbitrary
whole-block potentials. This volume gives exact native cycle families showing
why two proposed upper substitutions fail: unrestricted graph-cover domination
and an optimized Bethe value used as a per-template upper bound. The examples
are finite, positive-rational and amplify by disjoint products. They do not
rule out a different sound cofinal verifier.

## 1. A native binary-potential embedding

**Definition 1.1 (perfect binary leaves).** Fix $h\ge1$, put $d=h+1$ and
$m=2^h$. For a bit string $b\in\{0,1\}^m$, let $u_b$ be the actual perfect
height-$h$ tree whose leaves, in left-to-right order, are $\alpha$ for $0$ and
$\beta$ for $1$. These are elements of the unchanged canonical interface
$S_d$. Let $f:\{0,1\}^m\to\mathbb Q_{>0}$ and give every other state of
$S_d$ a fixed positive rational weight $\eta$. Write

$$
W=\sum_{x\in S_d}w(x),
\qquad w(u_b)=f(b),
\qquad \mu(x)=w(x)/W.
\tag{GCB.1}
$$

For every internal target $q$ with $|q|<h$, impose the constant factor
$\Gamma_q=(0,0)$. For every terminal target $q$ of length $h$, choose the
successor slot of that terminal in a cyclic partition of all terminal slots and
use one native donor literal at that successor slot, decoding

$$
\alpha\mapsto(2,1),
\qquad \beta\mapsto(1,0),
\qquad \mathsf{branch},\mathsf{absent}\mapsto(2,1).
\tag{GCB.2}
$$

The donor indices are arbitrary original block indices and may form cycles.
Every equation is a complete native target equation; no new query port is
introduced.

**Theorem 1.2 (exact binary incidence realization).** The solutions of this
complete native template are in bijection with assignments of one bit to each
terminal-slot class. In particular, for a binary potential incidence pattern
on the slots, the native mass is

$$
W^{-n}\sum_y\prod_i f(y|_{\text{slots of block }i}).
\tag{GCB.3}
$$

Each whole-block potential occurs once.

**Proof.** The internal equations force every strict internal target to be a
branch endpoint, hence the prescribed perfect shape. The terminal equations
force a labelled leaf and identify the donor leaf bit with the terminal bit.
Along a successor cycle all bits are equal, so one class bit remains. Restricting
to the classes and assembling the ordered perfect trees are inverse maps. The
product weight in (GCB.3) is therefore the native whole-block product, with no
replica multiplicity. $\square$

The equality and constructor conditions in this proof are exactly those of
[CBN, Theorems 2.2, 4.2 and 6.2]. In particular, the representation does not
replace a repeated reply by independent replicas and does not factor an
arbitrary block weight into pairwise constructor weights.

## 2. The two-state cycle calculation

For $h=1$ write $u_{ab}=\langle\operatorname{bit}(a),
\operatorname{bit}(b)\rangle$ and let $F=(f(a,b))_{a,b\in\{0,1\}}$. Choose the
successor pattern in which block $i$ has state $u_{b_i b_{i+1}}$ on a cycle of
length $\ell$. Then

$$
Z_\ell(F)=\frac{\operatorname{tr}(F^\ell)}{W^\ell}.
\tag{GCB.4}
$$

Take the positive rational matrices

$$
F_-=\begin{pmatrix}1&3\\3&1\end{pmatrix},
\qquad
F_+=\begin{pmatrix}3&1\\1&3\end{pmatrix},
$$

and give each of the other seven states of $S_2$ weight $1/10$. In both cases
$W=87/10$. The eigenvalues are $4,-2$ for $F_-$ and $4,2$ for $F_+$, so

$$
Z_\ell(F_-)=\frac{4^\ell+(-2)^\ell}{W^\ell},
\qquad
Z_\ell(F_+)=\frac{4^\ell+2^\ell}{W^\ell}.
\tag{GCB.5}
$$

This is an actual complete native template, not a factor-graph analogy. The
single source and the one original-root late Read remain as in (JTC.2); a
terminal target uses the chosen actual literal before the authentic count, and
all later counts use the credited $\Gamma$ decoder.

## 3. Failure of unrestricted graph-cover domination

**Proposition 3.1 (a connected two-sheet lift increases native mass).** For
$F_-$, a triangle has raw mass

$$
4^3+(-2)^3=56.
$$

Its connected two-sheet crossed lift is a six-cycle and has raw mass

$$
4^6+(-2)^6=4160>56^2=3136,
\qquad \frac{4160}{56^2}=\frac{65}{49}.
\tag{GCB.6}
$$

**Proof.** The cycle formula (GCB.5) gives both traces. The crossed matching
is a connected two-sheet lift of the triangle and preserves the same native
terminal donor/decoder equations. $\square$

Pad the base by one fixed $u_{00}$ block and the lift by its two fixed copies.
The base and lift then have four and eight blocks, respectively, while their
raw masses remain $56$ and $4160$. After normalization the ratio is still
$65/49$. Taking $r$ disjoint padded gadgets multiplies the ratio to
$(65/49)^r$. Therefore the proposed unrestricted comparison

$$
Z(\text{connected }k\text{-cover})\le Z(\text{base})^k
\tag{GCB.7}
$$

is false even for positive rational native weights, and no correction with
logarithm $o(n)$ can repair this rule on the displayed family. The obstruction
is scoped to the rule itself; Ruozzi's graph-cover inequality has a
log-supermodularity hypothesis that the anti matrix does not satisfy.

A consistent relabelling of the three triangle bits cannot remove the example:
each anti edge would require opposite flip choices, whose xor around the
triangle is impossible. This is a native cycle obstruction, not a claim that
all reblocking or all global certificates fail.

## 4. Failure of an optimized Bethe upper substitution

For either displayed matrix put $P=F/4$. It is doubly stochastic. On an
$\ell$-cycle, a locally consistent edge law $\tau$ gives the Bethe objective

$$
\sum_i\left[H(B_{i+1}\mid B_i)+
\mathbb E\log_2\frac{F(B_i,B_{i+1})}{W}\right]
\le \ell\log_2\frac4W.
\tag{GCB.8}
$$

Indeed, each summand equals $\log_2(4/W)$ minus a nonnegative conditional
relative entropy against $P$. Uniform vertex marginals and edge law $P/2$
achieve equality, so the optimized Bethe mass is $(4/W)^\ell$.

For $F_+$ at length four, the exact native mass is
$272/W^4$, while Bethe gives $256/W^4$. The rational inequalities

$$
\left(\frac{40}{87}\right)^4
<\left(\frac{23}{50}\right)^4
<\frac{272}{(87/10)^4}
\tag{GCB.9}
$$

show that a cap chosen from the optimized Bethe value can be false on an
actual complete native template. Disjoint four-cycles amplify the ratio to
$(17/16)^r$. Consequently a correction whose logarithm is $o(n)$ cannot turn
this per-template upper substitution into a sound universal cap.

This does not say that every Bethe method is invalid: a theorem with explicit
loop or support hypotheses may have a different direction. It says that the
optimized Bethe value alone is an average-style quantity and is not an upper
bound for every arbitrary native template with owned joint weights.

**Convention 4.1 (the precise literature hypotheses).** Vontobel's graph-cover
identity identifies the optimized Bethe partition value with a limsup of
averaged finite-cover partition functions; it is not domination of each
individual cover. Ruozzi's upper comparison requires binary
log-supermodular factors, a hypothesis violated by $F_-$. Bounds for
permanents with a girth correction require a permanent support graph and a
specified girth, neither of which is a native all-template hypothesis. These
conditions explain why (GCB.7)--(GCB.9) are counterexamples to the proposed
unrestricted substitutions only.

[Vontobel]: https://arxiv.org/html/1012.0065v2
[Ruozzi]: https://arxiv.org/html/1202.6035
[DJPR]: https://arxiv.org/html/2609.02017v1

## 5. Paid full-family realizations of the counterexamples

The counterexamples can be embedded in the original finite source family. For
$n=2^H$ blocks, put the height-one states $u_{ab}$ at the frontier of the
public perfect height-$H$ scaffold in the right subtree and take $D=H+2$.
Every block literal is the full original-root word obtained by prefixing its
public scaffold address. Internal scaffold targets are constants and terminal
targets are the actual leaf literals used in (GCB.2).

For the padded anti base use $n=4,D=4$ and merge exactly the eight native
solutions into one canonical code name; all other canonical states receive
separate names. Since $|S_4|=15131$, the attained alphabet is
$15131-8+1=15124$. For its connected lift use $n=8,D=5$ and merge its
$64$ solutions; since $|S_5|=228947163$, the attained alphabet is
$228947163-64+1=228947100$. The preparation scans all $Rq$, $q\in W_D$, before
the request, using at most $2^D-1$ charged Reads, maximum literal length $D$
and $(D-1)2^D+1$ submitted letters. The merged name is isolated by the paid
handoff; the reader chooses at most one fresh original-root Read before any
authentic count and then uses the all-count decoder. These codes are attained
constructions, deliberately nonoptimal, and carry no free source identity,
subtree or navigation descriptor.

## 6. Boundary of the negative result

The cycle calculations reject the two stated comparison mechanisms on actual
native instances while preserving equality, correlations, cycles and whole
block weights. They do not establish a universal obstruction to finer cuts,
global recolouring, effective approximation, computability, or a different
finite proof language. They also do not change the credited interval
$\log_2(33/13)/8\le\lambda<3/16$.

A successful original solution still needs a sound cap for every complete
native template and accepted endpoints cofinal in the same unrestricted
$\sigma_d$, or a uniform effective finite-length error. The exact general
$M_1(D)$ and the broader space-time mutual-recovery programme remain open.

[CBN]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[JTC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_TARGET_CERTIFICATES.md
[FMR]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NCE]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md

## 追加锚（本行以下为增补区）

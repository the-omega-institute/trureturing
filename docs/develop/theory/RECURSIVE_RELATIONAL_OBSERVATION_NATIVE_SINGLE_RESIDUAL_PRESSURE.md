# Recursive relational observation: single-residual pressure and a certificate boundary

This volume isolates a native certificate class whose pressure can be computed
exactly. Its failure at depth two is a quantified method boundary, not a claim
about all possible certificates or about noncomputability of the native rate.
The source, one-read late target, complete alphabet and arbitrary correlations
are those fixed in [JTC, §1].

## 1. One residual target on a support

**Definition 1.1 (residual support).** Fix a finite native interface $S_d$ with
maps $g_q=\Gamma_q$ and replies $r_a$. Let $S\subseteq S_d$ be nonempty. Say
that $q_*$ is a residual target on $S$ when every $q\ne q_*$ is determined on
$S$ by one own-coordinate reply or is constant. The residual target itself may
also be determined on a particular subset of $S$. For a nonnegative whole-block
weight $w$ put

```math
R_S(w)=\max_{a}
\sum_y\max_z
\sum_{\substack{x\in S:r_a(x)=y\\g_{q_*}(x)=z}}w(x),
\tag{SRP.1}
```

where the constant experiment is included among the choices of $a$. The set
obtained by choosing, for each attained reply $y$, one maximizing residual
value $z$ is locally admissible: the residual target is decoded from $r_a$ and
all other targets retain their own witnesses.

**Theorem 1.2 (exact inhomogeneous residual pressure).** Let $S_i$ be residual
supports with residual targets $q_i$ and weights $w_i$. The maximum of

$$
\sum_{x\in B}\prod_iw_i(x_i)
$$

over every jointly admissible $B\subseteq\prod_iS_i$ is exactly

$$
\prod_iR_{S_i}(w_i).
\tag{SRP.2}
$$

Thus for one support, $A_n(w)=R_S(w)^n$ and
$\beta(w)=R_S(w)$ at every length. Donors may be off-target, cyclic and
coordinate-dependent; no independent-child restriction is used.

**Proof.** Choose, for each coordinate, one actual witness for its residual
target and discard the other target equations. This enlarges the relation,
so it suffices to bound the mass of the chosen equations' full solution set
inside $\prod_iS_i$. Draw one arrow to its donor, allowing a self-loop;
a constant equation has no outgoing arrow. Each component is a tree ending
at a constant terminal or a directed cycle with incoming trees.

Eliminate a vertex with no incoming arrows. Conditional on its donor state,
its residual value is fixed. That target cell is locally admissible, since
all other targets retain their global own witnesses on $S_i$. Summing the
vertex therefore costs at most $R_{S_i}(w_i)$ uniformly in the donor state.
No other remaining equation depends on the eliminated state. A constant
terminal, after its incoming trees have been eliminated, obeys the same
bound. Continue until only directed cycles remain.

It remains to consider a directed cycle. Write the residual equation at $i$
as $g_{q_i}(x_i)=f_i(x_{i+1})$, with indices cyclic, where each $f_i$
factors through one own reply. Define

```math
M_i(u,v)=\sum_{\substack{x_i:g_{q_i}(x_i)=u\\f_{i-1}(x_i)=v}}w_i(x_i),
\qquad h_i(v)=\max_uM_i(u,v).
```

The cycle mass is
$\sum_{z_1,\ldots,z_\ell}\prod_iM_i(z_i,z_{i-1})$. Entrywise domination by
$h_i(z_{i-1})$ bounds it by $\prod_i\sum_vh_i(v)$, including the diagonal
sum for a self-loop. Choosing, for every attained $f_{i-1}$ value $v$, a
maximizing $u$ gives one own-reply decoder for the residual
target, so the union of those cells is locally admissible and
$\sum_vh_i(v)\le R_{S_i}(w_i)$. Multiplying the eliminated and cyclic bounds
proves the upper inequality. Conversely, the product of local maximizing
sets is jointly admissible and has exactly the product mass. $\square$

**Corollary 1.3 (restricted fractional covers at every length).** Let
$Z_S(n)$ be the fractional cover optimum of $S^n$ by all native jointly
admissible subsets of that universe, and put $z_S=Z_S(1)$. For every
one-residual support $S$ and every $n\ge1$,

$$
Z_S(n)=z_S^n.
$$

If $K_S(n)$ is the corresponding integral optimum, then

$$
\log_2z_S\le\frac{\log_2K_S(n)}n
\le\log_2z_S+\frac{\log_2(1+n\ln|S|)}n.
$$

**Proof.** Products of local fractional cover members are jointly admissible
and give the upper $z_S^n$. Let $y$ be a local optimal nonnegative LP dual,
of total $z_S$, with every locally admissible set having $y$-mass at most
one. Formula (SRP.1) is exactly that largest local mass, so $R_S(y)=1$.
Theorem 1.2 makes $\prod_i y(x_i)$ a feasible joint dual of total $z_S^n$.
This proves equality. Finite harmonic set-cover rounding, as used in
[FMR, Lemma 4.4], gives
$Z_S(n)\le K_S(n)\le H_{|S|^n}Z_S(n)$ and
$H_{|S|^n}\le1+n\ln|S|$. These covers concern the restricted universe
$S^n$. They are not upper covers of $S_d^n$ unless $S=S_d$. $\square$

## 2. A total sound verifier for this class

**Definition 2.1 (single-residual verifier).** A certificate for
$V_{\mathrm{SR}}(d,\mu,C,\pi)$ is a finite rational decomposition
$\mu=\sum_\ell w_\ell$ together with, for each $\ell$, a support
$S_\ell$, residual target $q_\ell$, reply map $a_\ell$ and the maximizing cell
values used in (SRP.1). The verifier checks the decomposition, the native reply
and target tables, the residual condition for every other target, and the exact
inequality

$$
C\ge\sum_\ell R_{S_\ell}(w_\ell).
\tag{SRP.3}
$$

It rejects malformed or incomplete data. All checks are finite rational
calculations, so the predicate is total.

**Proposition 2.2 (soundness for the full native family).** If
$V_{\mathrm{SR}}$ accepts, every complete arbitrary-donor native template of
length $n$ has $\mu$-mass at most $C^n$.

**Proof.** Expand the product $\prod_i\mu(x_i)$ by the component index at
each coordinate. For a fixed index tuple, restrict the same native relation to
$\prod_iS_{\ell_i}$. Theorem 1.2 bounds its mass by
$\prod_iR_{S_{\ell_i}}(w_{\ell_i})$. Summing the index tuples gives
$(\sum_\ell R_{S_\ell}(w_\ell))^n\le C^n$. The summation indices are an
analytical expansion, not a component label supplied to the reader and not a
new Read. Whole-block weights remain whole-block weights. $\square$

An accepted cap therefore gives the usual original-task consequence from
[NPC, Theorem 7.1] and [FMR, §6]:
$M_1(D)\ge\lceil C^{-2^{D-d}}\rceil$ for $D\ge d$ and
$\lambda\ge-2^{-d}\log_2C$, with the original perfect scaffold and paid literal
acquisition. This is a lower witness, not an upper cover implementation.
No separate code construction is claimed here; whenever a canonical fiber is
realized, the cited [FMR] implementation charges its full original-root scan
and exports only the complete first-membership name.

## 3. Exact pressure on the five-state cyclic motif

**Definition 3.1 (the motif).** Put

$$
A=\alpha,\quad B=\beta,\quad C=\langle A,A\rangle,
\quad J=\langle B,A\rangle,
\quad Q=\langle C,A\rangle,
$$

$$
(u_0,u_1,u_2,u_3,u_4)=
(C,J,\langle C,C\rangle,\langle J,J\rangle,\langle A,Q\rangle).
$$

Let $P=\{u_0,u_1,u_2,u_3,u_4\}\subseteq S_3$. The six targets other
than $LL$ have own-coordinate witnesses on $P$; $LL$ is the sole residual
target. The four core states $u_0,u_1,u_2,u_3$ have distinct $LL$ factors,
while every native reply has at most three values on that core.

**Theorem 3.2 (all-weight motif pressure).** A nonempty subset of $P$ is
locally admissible exactly when it omits at least one of
$u_0,u_1,u_2,u_3$. Hence, for every nonnegative weight vector
$(w_0,\ldots,w_4)$,

$$
\beta_P(w)=A_n(w)^{1/n}
=\sum_{s=0}^4w_s-\min\{w_0,w_1,w_2,w_3\}
\quad(n\ge1).
\tag{SRP.4}
$$

Here $A_n(w)$ is the maximum product weight of a jointly admissible
subset of $P^n$.

The unrestricted joint fractional cover optimum on $P^n$ is exactly

$$
Z_P(n)=(4/3)^n\qquad(n\ge1).
\tag{SRP.7}
$$

At length one, the four supports
$P\setminus\{u_j\}$, $j=0,1,2,3$, with coefficient $1/3$ give the upper
cover, and the dual weights $1/3$ on the four core states give the matching
lower bound. This equality is for the motif universe $P^n$ with every
correlated native competitor retained, and does not identify $Z_3(n)$.

**Proof.** No local reply separates all four distinct $LL$ values on the
core, so a set containing the core is not admissible. If $u_0$ or $u_1$ is
omitted, the $RL$ reply determines $LL$; if $u_2$ or $u_3$ is omitted, the
$L$ reply does. All other targets already have their own witnesses. This
classifies the local sets. The largest local weight therefore omits the
least-weight core state, and Theorem 1.2 gives (SRP.4). The displayed cover
and dual weights prove $z_P=4/3$. More explicitly, the dual
$y=(1/3,1/3,1/3,1/3,0)$ has $R_P(y)=1$ by (SRP.4), so Theorem 1.2
bounds its product mass by one on every admissible subset of $P^n$.
Its total mass is $(4/3)^n$. Products of the four displayed local cover
members give the reverse inequality, proving (SRP.7). $\square$

This result is stronger than the existence of the credited cyclic fiber: it
holds for every weight vector and every length, while it remains confined to
this support and does not identify the full $\sigma_3$.

**Proposition 3.3 (paid realization of the restricted covers).** Place
$n=2^H$ actual motif blocks at the public depth-$H$ frontier in the right
subtree, with $D=H+3$. Any finite cover of $P^n$ by native admissible sets
can be implemented on this slice by first-membership names, using
$7n$ preparation Reads of maximum length $H+3$ and $n(7H+17)$ submitted
letters. A request on the slice uses at most one original-root Read of
length at most $H+3$, chosen before the authentic count.

**Proof.** Acquire each block boundary through the actual words $Ra_iq$,
$q\in W_3$, where $|a_i|=H$. The seven suffix lengths sum to ten, giving
$7(H+1)+10=7H+17$ letters per block. Compute the joint canonical tuple
and its first containing member, then export only that fixed-width name.
All other acquired distinctions are isolated under the paid service in
[JTC, §1]. Constant scaffold targets need no Read; every other target uses
its cover member's one constituent donor at the actual literal $Ra_ja$.
The factor decoder handles every later authentic count. Installed cover
tables, membership work, padded control/allocation, temporary storage,
predictor, isolation and authentication are separate resources.

For a full-family construction, scan the entire $W_D$ boundary using
$2^D-1$ Reads and $(D-1)2^D+1$ letters, use these names on the canonical
slice and a separate name for every other canonical state. This counts
exactly $m_*+|S_D|-5^n$ attained names, where $m_*$ is the number of
first-membership names actually used on $P^n$, and extends by
canonicalization to every variable shape. No unused cover member is
counted as retained source information. It does not make the restricted cover an optimal full-family
cover. $\square$

For a general restricted-support joint block menu at $n$ public prefix-free
actual occurrences $Ra_i$, $|a_i|\le H$, the credited [FMR, Lemma 6.2]
scan instead has bounds

$$
n(2^d-1)\text{ Reads},\qquad Q\le H+d,\qquad
A\le n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr).
$$

The submitted words are exactly $Ra_iq$, $q\in W_d$; a donor uses the
corresponding one original-root word. At $d=3$ these are the motif bounds
$7n$ and $n(7H+17)$. Presence and the declared joint menu are the
supplier's premises; Proposition 3.3's fixed full-depth scaffold is what
also covers every original permitted target in its full-family extension.

## 4. A sharp depth-two noncofinality result

**Definition 4.1 (depth-two coordinates).** At depth two write
$S_2=\{A,B\}\sqcup\{\langle x,y\rangle:x,y\in\{A,B,C\}\}$. For a residual
component containing both root leaves, write $a=w(A)$, $b=w(B)$, let $T$ be
the total branch weight and let $c_{\max}$ be the largest branch weight.

**Lemma 4.2 (row-column classification).** If a one-residual support contains
both $A$ and $B$, its branch states lie in one row or one column of the
$3\times3$ child grid, and its residual optimum is

$$
R=\max\{a+T,\ b+T,\ a+b+c_{\max}\}.
\tag{SRP.5}
$$

**Proof.** At least one side target, $L$ or $R$, is not the designated
residual target. Its factors on $A,B$ differ, whereas every nonempty
experiment gives absent on both leaves. Its own witness must therefore be
the root reply. That reply merges all branch states, so the selected side's
child must be fixed across them. This gives one row or one column, with at
most three branches. The root target itself is always own-determined, so
this argument also covers designation of the root as the residual target.

By the credited depth-two local-set classification [NCM, (NCM.15)], a
locally admissible subset either omits $B$, omits $A$, or retains both and
at most one branch. Their maximum weights are the three terms in (SRP.5).
If the designated residual is also own-determined, the whole support is
locally admissible and the same formula gives its total weight. An empty
branch part has $T=c_{\max}=0$. $\square$

**Theorem 4.3 (the static single-residual class has a strict gap).** Every
finite nonnegative decomposition accepted by $V_{\mathrm{SR}}$ at depth two
has $C\ge5/7$ when $\mu$ is a probability. This is sharp for the class. Since
the credited value is
$\sigma_2=\log_2(25/17)$, every such endpoint obeys

$$
-\log_2C\le\log_2(7/5)
<\log_2(25/17)-1/100.
\tag{SRP.6}
$$

**Proof.** If a component support omits one root leaf, it is locally
admissible and $R=W$, so $7R=7W\ge5W$. Otherwise at most three branch
states lie in one row or column, hence $c_{\max}\ge T/3$. From (SRP.5),

$$
2R\ge a+b+2T,
\qquad 3R\ge3a+3b+T.
$$
Twice the first inequality plus the second gives
$7R\ge5(a+b+T)=5W$. Summing over a decomposition with
$\sum_\ell W_\ell=1$ and using (SRP.3) yields
$1\le(7/5)C$. Sharpness is attained by the support
$\{A,B,\langle A,A\rangle,\langle A,B\rangle,\langle A,C\rangle\}$ with
weights $(2,2,1,1,1)/7$, for which $R=5/7$. Finally
$125^{100}>2\,119^{100}$, so $\log_2(125/119)>1/100$, and
$\log_2(25/17)-\log_2(7/5)=\log_2(125/119)$. $\square$

The obstruction is exact for the defined static-support, one-residual-target
and finite-superposition mechanism. It does not exclude multiple residual
targets, projection-dependent target selection, the joint certificate of
[JTC, §2], global recoloring, lawful finer cuts, or a different effective
proof system. In particular it is not a universal impossibility theorem.
Failure of the required endpoint coverage at $d=2$ also does not prove
that this class's endpoints over increasing depths fail to approach
$\lambda$; that is a different approximation question.

## 5. Original-task boundary

The theorem supplies a genuine all-correlated pressure calculation and a
sound cap family for the unchanged native competitors. Its finite depth-two
gap shows that increasing the number of static residual pieces cannot by
itself establish the required cofinality. A complete solution still needs a
sound verifier whose accepted endpoints approach the same unrestricted
$\sigma_d$, or a uniform effective bound on the finite-length tail. The exact
lambda interval, general $M_1(D)$, and the broader mutual-recovery programme
remain open.

[JTC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_TARGET_CERTIFICATES.md
[NPC]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[FMR]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NCM]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md

## 追加锚（本行以下为增补区）

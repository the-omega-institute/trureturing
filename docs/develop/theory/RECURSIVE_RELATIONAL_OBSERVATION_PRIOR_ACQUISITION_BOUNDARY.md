# Recursive relational observation: prior laws at an acquired boundary

This volume studies the stationary native acquisition contract of AAR13.1.
The source is sampled once, the source remains unchanged during acquisition,
and every finite original-root word is a legal four-reply `Read`. The question
is about the expected number of initial Reads under a public rational law on
the full family. Installation, local computation, retained memory, operand
length, validation and physical time remain separate resources.

The result separates two relations. The acquired first-leaf descriptor is
sufficient for passive prediction at the declared target, as in AAR13.3. Its
marginal law need not determine the conditional law of off-boundary replies,
and therefore need not determine the best active acquisition policy. A native
counterexample gives two full-support laws with the same boundary pushforward
and strictly separated optimal-cost bounds. A second theorem gives a useful
sufficient condition under which a boundary law does determine the optimum:
all potential off-boundary decorations must be representable by one persistent
joint forest independent of the descriptor. The forest coordinates may be
correlated.

## 1. Contract, boundary and two objectives

**Definition 1.1 (stationary native family and all-word objective).** Let
$\alpha,\beta$ be leaves and let $\langle x,y\rangle$ be a branch. The height
of a leaf is $0$ and

$$
\operatorname{height}(\langle x,y\rangle)
 =1+\max(\operatorname{height}(x),\operatorname{height}(y)).
$$

For $D\ge1$, use exactly the published family

$$
\mathcal F_D
 =\{\langle\alpha,v\rangle:
       \operatorname{height}(v)\le D\},
\tag{1.1}
$$

Fix a public word $p$ beginning with $R$, with $1\le n:=|p|\le D$, and write
$p_j$ for its length-$j$ prefix. A `Read` of an original-root word $w$
returns `absent`, $\alpha$, $\beta$ or `branch` according to the one actual
tree. A deterministic encoder starts from the same source-blind state on
every member of $\mathcal F_D$, may choose arbitrary finite words adaptively,
and must terminate and be correct on every member of $\mathcal F_D$. Its
exported state must support one decoder for every authentic supplied count
$k$ and the target future at $p$, with no new Reads. The source is sampled
once and is unchanged throughout acquisition.

For a public rational full-support law $\mu$ on $\mathcal F_D$, define

$$
V_{\rm all}(\mu)
 :=\inf_A\sum_{t\in\mathcal F_D}\mu(t)T_A(t),
\tag{1.2}
$$

where the infimum ranges over these globally correct all-word encoders and
$T_A(t)$ counts every actual Read, including repeated and absent Reads.

**Definition 1.2 (first-leaf boundary).** The native descriptor is

$$
\partial_p(t)=
\begin{cases}
 B,&p\text{ is branch in }t,\\
 (j,e),&p_j\text{ is the first leaf on the path to }p,\quad
       t|_{p_j}=\lambda_e,
\end{cases}
\tag{1.3}
$$

where $\lambda_0=\alpha$ and $\lambda_1=\beta$. A source with descriptor
$(j,e)$ has branches on the strict path prefixes, the label $\lambda_e$ at
$p_j$, and no descendants below that leaf. A source with descriptor $B$ has
branches through $p$.

The published AAR13.3 factor $\Gamma_p(\partial_p(t))$ determines the complete
future reply trajectory at $p$ for every authentic supplied count. It is a
passive prediction factor, not an acquisition operation. The source family,
the all-word encoder class, and the distinction between an acquired
descriptor and its decoder are exactly those of AAR13.1--AAR13.8.

**Proposition 1.3 (passive sufficiency does not price an action).** The law
of $\partial_p(t)$ determines the law of the passive target trajectory, but
the law of the next useful Read generally requires the conditional experiment

$$
K_c(w,y)=
\Pr_\mu\bigl(\operatorname{Read}_t(w)=y\mid\partial_p(t)=c\bigr)
\tag{1.4}
$$

for all legal words $w$, together with the joint compatibility of replies at
different words. A boundary marginal alone contains neither (1.4) nor its
same-source updates after a reply.

**Proof.** AAR13.3 gives the first assertion. An active encoder chooses its
next word from the current transcript. Two source laws can have the same
descriptor marginal while assigning different off-boundary replies inside
one descriptor fibre. The next-word reply and the posterior after that reply
then differ. A single marginal of the descriptor cannot determine either
quantity. The explicit native separation in Sections 2--3 supplies the
strict cost consequence. $\square$

## 2. A same-boundary full-support separation at $D=8$

Take

$$
D=8,\qquad p=RLLLLLLL,\qquad n=8.
\tag{2.1}
$$

For a word $a$ and a tree $u$, let $C_a[u]$ be the tree with branches on
the strict prefixes of $a$, the tree $u$ at $a$, and $\alpha$ at every
off-path sibling. This is the published AAR13.6 comb construction.

**Definition 2.1 (canonical and correlated representatives).** Put

$$
t_{j,e}=C_{p_j}[\lambda_e],
\qquad 1\le j\le8,\quad e\in\{0,1\}.
\tag{2.2}
$$

For $j=1$, set $s_{1,e}=t_{1,e}$. For $j\ge2$, alter only the subtree at
$RR$ in $t_{j,e}$ and call the result $s_{j,e}$, using

$$
\begin{array}{c|c}
 j& s_{j,e}|_{RR}\\ \hline
 2,3&\alpha\\
 4,5,6&\beta\\
 7,8&\langle\alpha,\alpha\rangle.
\end{array}
\tag{2.3}
$$

The alteration is made only where $RR$ is an existing off-path sibling. The
path to $p_j$ and its label are unchanged.

**Lemma 2.2 (legality and equal boundary fibres).** All sixteen $t_{j,e}$
and all sixteen $s_{j,e}$ are distinct members of $\mathcal F_8$. Moreover

$$
\partial_p(t_{j,e})=\partial_p(s_{j,e})=(j,e).
\tag{2.4}
$$

**Proof.** Every strict prefix of $p_j$ is a branch and the path label is
unchanged by (2.3), so (2.4) holds. The canonical right-subtree height is
at most $7$. The inserted trees in (2.3) have height at most $1$, and the
longest path still has right-subtree height at most $7$. The fixed left root
child is $\alpha$, so every representative satisfies (1.1). $\square$

**Definition 2.3 (one legal guided encoder).** First Read $RR$.

* If the reply is `absent`, Read $R$ and return its actual leaf descriptor.
* If the reply is $\alpha$, use the ordered prefix search tree

  $$
  S_\alpha=(3,\ (2,\varnothing,\varnothing),\ S[4,8]),
  \tag{2.5}
  $$
  where $S[a,b]$ is the ordinary median ordered tree on keys $a,\ldots,b$.
* If the reply is $\beta$, use

  $$
  S_\beta=(5,\ (4,S[2,3],\varnothing),\ (6,\varnothing,S[7,8])).
  \tag{2.6}
  $$
* If the reply is `branch`, use

  $$
  S_B=(7,\ S[2,6],\ (8,\varnothing,\varnothing)).
  \tag{2.7}
  $$

At key $i$, the encoder Reads $p_i$. A leaf reply returns $(i,e)$; a branch
reply at $p_8=p$ returns $B$; `absent` moves to the lower child and `branch`
moves to the upper child. A candidate return is accepted only on that actual
leaf or branch evidence. If the selected tree fails to produce such evidence,
the encoder discards the candidate and runs the published source-blind
prefix search of AAR13.4. The fallback has at most
$h(8)=\lceil\log_2(9)\rceil=4$ Reads.

**Lemma 2.4 (global correctness and core costs).** Definition 2.3 is one
common source-blind encoder correct on every member of $\mathcal F_8$. Its
cost is at most $9$ on every source. On the correlated representatives its
costs, in order $j=1,\ldots,8$, are

$$
(2,3,2,3,2,3,2,3),
\tag{2.8}
$$

independently of $e$.

**Proof.** If $RR$ is absent, $R$ is a leaf in a full tree and the second
Read supplies its actual label. Otherwise $R$ is branch. On a representative
$s_{j,e}$, (2.3) selects exactly the search tree containing key $j$, and
the reply at a queried prefix $p_i$ is `branch` for $i<j$, the actual leaf
label $\lambda_e$ for $i=j$, and `absent` for $i>j$. The key depths in
(2.5)--(2.7) give (2.8).

For an arbitrary source, a selected tree can only return on actual evidence.
If it does not, the fallback is the all-source AAR13.4 search, so the same
program terminates and is correct on the whole family. Each selected tree
has height at most four; hence the initial `RR`, at most four candidate Reads,
and at most four fallback Reads give the uniform bound $9$. No source name,
subtree port, advice, clock or supplied target count is used during
acquisition. $\square$

**Lemma 2.5 (all-word lower bound on the canonical core).** For every
globally correct all-word encoder $A$,

$$
\frac1{16}\sum_{j=1}^{8}\sum_{e=0}^{1}T_A(t_{j,e})
\ge \frac{21}{8}.
\tag{2.9}
$$

**Proof.** AAR Lemma 13.5 says that $A$ must Read $p_j$ on each $t_{j,e}$:
flipping only that leaf label gives another member of $\mathcal F_8$ with
the same replies at every other word and a different future trajectory.
This obligation applies even if the source has zero mass in a later law.

Apply the all-word projection theorem AAR14.1 to $A$. On the canonical
representatives the projection is the representative itself, so the theorem
produces a prefix-only encoder whose cost on each $t_{j,e}$ is no larger.
By AAR Lemma 13.7, every prefix query $p_i$ gives absent for $j<i$, the
actual label for $j=i$, and branch for $j>i$; both labels at a key therefore
have the same successful-search depth $d_j$. An ordered search tree on eight
keys has at most one key at depth one, two at depth two and four at depth
three. The remaining key is at depth at least four, so

$$
\sum_{j=1}^{8}d_j\ge1+2\cdot2+4\cdot3+4=21.
\tag{2.10}
$$

The prefix encoder's mean on the sixteen canonical sources is at least
$21/8$, and the projection cost is no larger than $A$'s cost there. The
argument began with arbitrary legal words, so it is not a restriction to
prefix competitors. $\square$

**Definition 2.6 (two rational full-support laws).** Let

$$
N_0=2,\qquad N_{h+1}=2+N_h^2,
\tag{2.11}
$$

so $N_8=|\mathcal F_8|$. Let $U$ be the uniform law on the entire
$\mathcal F_8$, and define the two core laws

$$
\nu_0(t)=\frac1{16}\mathbf 1_{\{t=t_{j,e}\text{ for some }j,e\}},
\qquad
\nu_1(t)=\frac1{16}\mathbf 1_{\{t=s_{j,e}\text{ for some }j,e\}}.
\tag{2.12}
$$

Set

$$
\mu_0=\frac{99}{100}\nu_0+\frac1{100}U,
\qquad
\mu_1=\frac{99}{100}\nu_1+\frac1{100}U.
\tag{2.13}
$$

Both are public rational laws on the same full family, and every source has
positive mass.

**Lemma 2.7 (exact equal boundary pushforwards).**

$$
(\partial_p)_*\mu_0=(\partial_p)_*\mu_1.
\tag{2.14}
$$

**Proof.** Each core law assigns $1/16$ to each of the sixteen descriptors
$(j,e)$ and zero to $B$. The uniform component is identical in (2.13), so
its boundary pushforward cancels in the comparison. $\square$

**Theorem 2.8 (strict mean-cost separation).** With $V_i=V_{\rm all}(\mu_i)$,

$$
\boxed{
V_1\le\frac{513}{200}=2.565
<
\frac{2087}{800}=2.60875\le V_0
}.
\tag{2.15}
$$

Consequently

$$
V_0-V_1\ge\frac7{160}>0.
\tag{2.16}
$$

These are separated bounds, not exact values of either optimum.

**Proof.** By (2.8), Definition 2.3 has mean $5/2$ under $\nu_1$ and
cost at most $9$ under every source, hence

$$
V_1\le\frac{99}{100}\frac52+\frac1{100}9
 =\frac{513}{200}.
\tag{2.17}
$$

For any encoder, Lemma 2.5 gives mean at least $21/8$ under $\nu_0$.
Every globally correct encoder makes at least one Read on every source: a
zero-Read termination has the same output on two sources with different
target trajectories. Therefore

$$
V_0\ge\frac{99}{100}\frac{21}{8}+\frac1{100}
 =\frac{2087}{800}.
\tag{2.18}
$$

The displayed rational gap is positive. The core lower bound uses arbitrary
word competitors through AAR14.1 and AAR13.7; correctness is still required
on the whole full-support family. $\square$

Theorem 2.8 answers the boundary-marginal invariance question negatively at
the stated native scope. It does not change AAR14.1's worst-case normalization
or AAR14.2's pointwise non-domination result. It concerns only expected
initial Read count under a declared actual-source law.

## 3. A growing native separation

The finite construction scales without changing the source contract. This
section records a family of separated bounds rather than an optimum ratio.

**Definition 3.1 (base-four off-path guide).** Fix $r\ge2$, put

$$
n=D=4^r,\qquad p=RL^{n-1}.
\tag{3.1}
$$

Let $d=\lceil\log_2 r\rceil$. Choose $r$ distinct leaves $s_0,\ldots,s_{r-1}$
of a fixed binary skeleton of height $d$ and replace the selected skeleton
leaves by the four trees

$$
G_0=\alpha,\quad G_1=\langle\alpha,\alpha\rangle,\quad
G_2=\langle\beta,\alpha\rangle,\quad
G_3=\langle\langle\alpha,\alpha\rangle,\alpha\rangle.
\tag{3.2}
$$

Call the resulting subtree $Z(c)$ when the selected leaf $s_i$ receives
$G_{d_i}$, where $(d_0,\ldots,d_{r-1})$ are the base-four digits of
$c\in\{0,\ldots,4^r-1\}$. A Read at $s_iL$ returns respectively
`absent`, $\alpha$, $\beta$, or `branch` for $G_0,G_1,G_2,G_3$.

For $j=1$, use the canonical $t_{1,e}$. For $j\ge2$, replace the existing
$RR$ subtree of $t_{j,e}$ by $Z(j-1)$ and call the result $g_{j,e}$. The
height added at $RR$ is at most $d+2$, so the right-subtree height is at
most $D$; no source is padded above the family bound.

**Theorem 3.2 (scalable separated bounds).** Let $\nu_0^{(r)}$ be uniform
on the $2n$ canonical witnesses $t_{j,e}$ and let $\nu_1^{(r)}$ be uniform
on the $2n$ guided witnesses $g_{j,e}$. With $U_r$ uniform on the same full
$\mathcal F_D$ and $\varepsilon=n^{-2}$, set

$$
\mu_i^{(r)}=(1-\varepsilon)\nu_i^{(r)}+\varepsilon U_r.
\tag{3.3}
$$

Then both laws are rational, full-support, and have identical
$\partial_p$ pushforwards. If $L_r$ is the canonical lower bound

$$
L_r=2r-1+\frac{2r+2}{4^r},
\tag{3.4}
$$

then

$$
V_{\rm all}(\mu_0^{(r)})
 \ge(1-\varepsilon)L_r+\varepsilon,
\qquad
V_{\rm all}(\mu_1^{(r)})
 \le(1-\varepsilon)(r+1)+\varepsilon(3r+2).
\tag{3.5}
$$

The difference between the displayed lower and upper bounds is

$$
\Delta_r
 =(1-\varepsilon)\left(r-2+\frac{2r+2}{4^r}\right)
   -\varepsilon(3r+1)>0,
\tag{3.6}
$$

for every $r\ge2$, and grows asymptotically like $r-2$.

**Proof.** Read the $r$ words $RRs_iL$ and interpret their four replies as
the base-four digits. On a guided witness this recovers $j=1+c$; read $p_j$
and return only on the actual leaf label or branch at $p$. On any source for
which the guide is misleading, use the AAR13.4 prefix fallback. The core
cost is $r+1$, and the worst cost is at most

$$
r+1+\lceil\log_2(n+1)\rceil\le3r+2.
$$

The canonical lower argument is the same mandatory-label and all-word
projection argument as Lemma 2.5. A binary search tree with $n=4^r$ keys
has minimum mean key depth (3.4): fill levels successively, leaving one
key at depth $2r+1$. Mixing with the common uniform law gives (3.5), using
one Read as the universal lower bound on the uniform component. Direct
substitution of $\varepsilon=4^{-2r}$ gives (3.6); its value at $r=2$ is
$709/2048$. For $r\ge3$, use $\varepsilon\le1/4096$ to bound its numerator
by $4095(r-2)-(3r+1)=4092r-8191>0$. All guide coordinates
are installed in one fixed off-path forest, so this is a same-source native
construction, not a sequence of independently redrawn nuisance replies.
$\square$

The family in Theorem 3.2 proves an increasing mean-cost gap in the stated
bounds. It does not assert exact Bayes optima, a sharp ratio, or a universal
asymptotic law for all native priors.

## 4. Joint-completion criterion and prefix reduction

The separation disappears under a law-faithful completion condition. The
condition is stronger than equality of one-query marginals and is designed
to preserve one actual source throughout an adaptive run.

**Definition 4.1 (potential completion forest).** Fix arbitrary admissible
$D,p$ and $n=|p|$. For $2\le i\le n$, let

$$
a_i=p_{i-1}\,\overline{p[i]}
\tag{4.1}
$$

be the sibling where a word first leaves the target path, and let

$$
\mathcal Z_i=\mathcal T_{D+1-i},
\qquad
\mathcal Z_* =\mathcal T_{D-n}\times\mathcal T_{D-n},
\tag{4.2}
$$

where $\mathcal T_h$ denotes all finite trees of height at most $h$.
A completion forest is

$$
z=(z_2,\ldots,z_n,z_*),
\qquad z_i\in\mathcal Z_i,\quad z_*\in\mathcal Z_*.
\tag{4.3}
$$

Define $T(b,z)$ by following $p$ to the first leaf specified by
$b=(j,e)$, installing $\lambda_e$ at $p_j$ and $z_i$ at every exposed
$a_i$ with $i\le j$; for $b=B$, follow the whole path, install every
$z_i$, and install the two components of $z_*$ below $p$. The fixed left
root child is $\alpha$. Coordinates not exposed by $b$ are ignored.

The height caps in (4.2) make every $T(b,z)$ a member of $\mathcal F_D$.
The map is a single-source realization: once $(b,z)$ is chosen, all words
are answered by that one finite tree.

**Definition 4.2 (joint-completion condition).** Let

$$
q=(\partial_p)_*\mu
\tag{4.4}
$$

and let $\nu$ be the conditional joint law of the entire forest $z$ under
$\mu$ given $\partial_p=B$. Require that, for every leaf descriptor
$b=(j,e)$, the conditional joint law of the exposed tuple

$$
(z_2,\ldots,z_j)\mid\partial_p=b
\tag{4.5}
$$

equals the corresponding coordinate projection of $\nu$. No independence
among the coordinates of $\nu$ is required. The sole independence is that
the one persistent forest $z$ is independent of $b$ in the representation

$$
\mu=T_*(q\times\nu).
\tag{4.6}
$$

Condition (4.5) is equivalent to (4.6) for the realization map above. If
$\mu$ has full support, $q$ is positive on every descriptor and $\nu$ is
positive on every legal forest. For a rational finite law, all these masses
are rational.

**Definition 4.3 (prefix optimum).** Let $V_{\rm pref}(q)$ be the minimum
expected Read count among ordered prefix search trees on keys $1,\ldots,n$
and the final branch outcome $B$, with key mass

$$
a_j=q(j,0)+q(j,1).
\tag{4.7}
$$

The $B$ outcome follows the rightmost key path and stops at the branch Read
at $p_n$.

By the ordered pruning in AAR14.1, any prefix-only encoder can be reduced to
one of these ordered search trees without increasing its Read count. Thus
$V_{\rm pref}(q)$ is the full prefix-only optimum for this objective.

**Theorem 4.4 (persistent joint completion implies exact prefix reduction).**
Under the joint-completion condition (4.5),

$$
\boxed{V_{\rm all}(\mu)=V_{\rm pref}(q).}
\tag{4.8}
$$

This is a sufficient condition. It allows arbitrary correlations inside the
completion forest and does not assert necessity.

**Proof.** The inequality $V_{\rm all}(\mu)\le V_{\rm pref}(q)$ is immediate,
because prefix encoders are legal all-word encoders. For the converse, fix
an arbitrary globally correct all-word encoder $A$ and a fixed public forest
$z$.

Construct a prefix encoder $B_z$ that simulates $A$ on the virtual source
$T(\partial_p(t),z)$ while the actual register remains the unchanged source
$t$. The notation $\partial_p(t)$ is only a mathematical abbreviation:
$B_z$ discovers the descriptor lazily through the prefix Reads below and
never receives a free boundary value. A simulated query $p_i$ is answered by
the actual prefix Read $p_i$.
For a word first diverging at $a_i$, the actual Read $p_{i-1}$ tells whether
the sibling exists. On a branch reply, return the local reply of the fixed
subtree $z_i$ at the residual word; on a leaf or absence, return `absent`.
For a strict extension of $p$, Read $p$ once; on a branch, answer locally
from $z_*$, and otherwise return `absent`. The empty word, the root, and all
words entering the fixed left child have public replies. These cases exhaust
all finite words.

The same $z$ is retained for the entire simulation. It is never resampled
after a reply, so repeated and adaptive virtual Reads are replies of one
stationary virtual source. Each simulated Read uses at most one actual
prefix Read. The height guards ensure that the virtual source is in the same
full family, so the global correctness and termination contract for $A$
applies to it. The virtual descriptor equals the actual descriptor, hence
the returned future decoder is correct for the actual source. Write
$C_z(b)$ for the resulting cost; it depends on $b$ and $z$, not on the
unexposed decorations of $t$.

By induction on the simulated transcript,

$$
C_z(b)\le T_A(T(b,z)).
\tag{4.9}
$$

Average (4.9) first over $b\sim q$ and then over the one forest
$z\sim\nu$. The exact law correspondence (4.6) gives

$$
\sum_z\nu(z)\sum_bq(b)C_z(b)
\le
\sum_{t\in\mathcal F_D}\mu(t)T_A(t).
\tag{4.10}
$$

The forest space is finite, so one public $z_0$ has $q$-mean cost no greater
than the left side of (4.10). Hardwire that $z_0$ into the deterministic
prefix encoder. This is a public installation choice, not the actual source
and not a runtime source answer. Thus $V_{\rm pref}(q)\le V_{\rm all}(\mu)$.
Together with the first inequality, (4.8) follows. $\square$

The proof uses one complete joint forest and the unchanged actual law. It
does not replace a conditional source by a fresh draw after each query, and
it does not infer a law from one-query marginals. The condition is sufficient,
not necessary: a law can violate (4.5) while an ordinary prefix strategy is
still optimal.

## 5. Small cases and the nonnecessity check

**Proposition 5.1 (degenerate target).** If $n=1$ and $p=R$, then for every
full-support law on every admissible $\mathcal F_D$,

$$
V_{\rm all}(\mu)=1.
\tag{5.1}
$$

**Proof.** One Read at $R$ returns alpha, beta or branch, exactly the three
descriptor cases. Zero Reads cannot distinguish two different target
trajectories. $\square$

**Proposition 5.2 (a positive law violating joint completion).** Let
$D=2$ and $p=RL$. There are $38$ sources in $\mathcal F_2$. Give each of
the five descriptors

$$
(1,0),(1,1),(2,0),(2,1),B
\tag{5.2}
$$

mass $1/5$. Conditional on $(2,0)$, let the $RR$ subtree be the mixture
$\tfrac12\operatorname{Unif}(\mathcal T_1)+\tfrac12\delta_\alpha$; conditional
on $(2,1)$ use
$\tfrac12\operatorname{Unif}(\mathcal T_1)+\tfrac12\delta_\beta$. Conditional
on $B$, take $RR$ uniform on $\mathcal T_1$ and take the two children of
$RL$ independently uniform on $\{\alpha,\beta\}$. The two $(1,e)$ sources
have no $RR$ subtree. This is a rational full-support law on all $38$ sources.

It violates (4.5), since

$$
\Pr(RR=\alpha\mid(2,0))=\frac7{12},\qquad
\Pr(RR=\alpha\mid B)=\frac16.
\tag{5.3}
$$

Nevertheless

$$
V_{\rm all}(\mu)=\frac75.
\tag{5.4}
$$

**Proof.** Read $RL$ first. A leaf gives $(2,e)$ and a branch gives $B$;
on an absent reply, Read $R$ to obtain $(1,e)$. The mean is
$1+2/5=7/5$. Conversely, a one-Read termination on either $(1,e)$ source
requires $R$, and a one-Read termination on either $(2,e)$ source requires
$RL$, by the label-flip argument. A word different from both cannot finish
on any leaf-label pair in one Read; it cannot lower the displayed mean.
Thus every strategy has mean at least $1+2/5$, proving (5.4). $\square$

This example shows that the joint-completion criterion is only sufficient.
Its failure does not by itself imply a mean-cost separation.

**Lemma 5.3 (single-query marginals do not preserve an adaptive law).** At
$D=5$ and $p=RLLLL$, consider canonical sources with first-leaf positions
$j=4$ and $j=5$. Put a fair bit $X$ into the leaf label of the off-path
subtree at $RR$, put a fair bit

$$
Y=X\oplus\mathbf 1_{\{j=5\}}
\tag{5.5}
$$

into the off-path subtree at $RLR$, and put $\alpha$ at the other siblings.
Vary the target leaf label independently. Every individual coordinate $X$
and $Y$ is fair conditional on the position, but the pair $(X,Y)$ identifies
whether $j=4$ or $j=5$. All these sources satisfy the same height bound.

Thus replacing the persistent source by independently redrawn replies with
the same one-word marginals changes the legal joint experiment. This is a
joint-law obstruction, not an additional expected-optimum separation.

## 6. Observer consequence: prediction versus choosing a Read

After a truthful transcript $h$, the actual posterior is

$$
\mu_h(t)=
\frac{\mu(t)\mathbf 1_{\{t\text{ is consistent with }h\}}
      }{\mu(\{u:u\text{ is consistent with }h\})}.
\tag{6.1}
$$

For a proposed word $w$, the action kernel is

$$
K_h(w,y)=\sum_t\mu_h(t)\mathbf1_{\{\operatorname{Read}_t(w)=y\}}.
\tag{6.2}
$$

The next posterior is obtained by conditioning this same $\mu_h$ on the
actual reply. A fresh nuisance draw is not an execution of the stationary
source: repeated Reads of one word return the same reply, and cross-word
correlations such as (5.5) persist.

For a finite family, a sufficient action-state is the conditional joint law

$$
\mathcal L_\mu\left(
\Gamma_p(\partial_p(t)),
\bigl(\operatorname{Read}_t(w)\bigr)_{|w|\le D+1}
\ \middle|\ h\right).
\tag{6.3}
$$

Words longer than $D+1$ are constant absent on the initial bounded family.
The vector in (6.3) is one response vector of one actual source and supports
every finite adaptive continuation. It is sufficient, not claimed minimal.

The relation retained for passive prediction is therefore
$\Gamma_p(\partial_p(t))$. The relation needed for active acquisition is the
boundary together with its conditional joint response experiment, or a
law-faithful reduction such as Theorem 4.4. Neither relation recovers a full
source, an unknown future task, physical time, or all retained memory for
free.

## 7. Coverage, literature and limits

The nearest published source is the [Adaptive Acquired Reference Frontier](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md),
whose AAR12--AAR15 sections fix the predictive factor, the native family,
the all-word acquisition contract, worst-case projection, the pointwise
off-path obstruction and the remaining recovery limits. In particular,
AAR13.3 supplies passive future decoding, Theorem 13.4 supplies prefix
attainment, Lemma 13.5 supplies actual-label evidence, Lemma 13.7 classifies
every original-root word on the canonical witnesses, Theorem 13.8 gives the
all-word worst-case price, Theorem 14.1 gives projection normalization, and
Proposition 14.2 records pointwise off-path non-domination. AAR15.2--AAR15.4
separate an acquired boundary factor from a full source and the wider
recovery programme. The present volume adds a source law and an expected
initial-Read objective; it does not reinterpret the worst-case claims as
Bayes claims.

Sparse Literal History Transport §§35--43 supplies the first-leaf future
semantics and the actual-label evidence pattern, while Literal Query Frontier
§2.3 and Acquired Orbit Resource Frontier §§1--2 supply joint-history and
finite decision-tree correspondences. Their source domains, menus and
consumer contracts differ, so none supplies the full-support separation or
joint-completion theorem here.

The exact source/operation correspondence is also supplied by
`NativeLiteralPathConstraints.compile_exact`,
`NativeIndependentExecution.native_history_correspondence` and
`NativeDepthPatterns.original_present_transport`. Those declarations account
for one unchanged source, literal four-reply semantics, absence and present
subtree transport. They do not certify the new ordinary optimization bounds.

Four primary decision-tree sources give methodological correspondences:

* Cicalese, Laber and Saettler, *Diagnosis determination: decision trees
  optimizing simultaneously worst and expected testing cost*, PMLR 32 (2014),
  §§1--2, [paper](https://proceedings.mlr.press/v32/cicalese14.pdf).
  Their DFEP model has a finite object class, tests, a prior, target classes
  and expected decision-tree cost. Here the objects are $\mathcal F_D$, tests
  are native words with four replies, and the target classes are the
  AAR13.3 trajectories. Their generic framework does not supply the native
  all-word classification or the strict same-boundary separation.
* Golovin, Krause and Ray, *Near-Optimal Bayesian Active Learning with Noisy
  Observations*, NIPS 2010, §§2--3,
  [arXiv](https://arxiv.org/abs/1010.3091). Their hypothesis and response
  variables form one joint law, including correlated observations. That is
  the relevant probabilistic interface for (6.3); their approximation
  theorem is not used as a native exact optimum result.
* Nowak, *The Geometry of Generalized Binary Search*, IEEE TIT (2011),
  §§I--II, [arXiv](https://arxiv.org/abs/0910.4397). Its fixed unknown
  hypothesis and noiseless query partitions explain the search-tree
  correspondence. Its binary response and coherence assumptions do not
  supply the native four-reply height-bounded proof.
* Bruno, De Prisco, De Santis and Vaccaro, *Bounds and Algorithms for
  Alphabetic Codes and Binary Search Trees*, 2024,
  [arXiv](https://arxiv.org/abs/2407.16443). Its successful/unsuccessful
  ordered-search cost is the ordinary structure behind (2.10) and (4.7).
  The native equality label, branch outcome and arbitrary-word reduction are
  proved here from AAR13.5--AAR13.7.

The new result is worth retaining as a focused ordinary-theory volume: it
fills the interface between passive boundary sufficiency and prior-dependent
active acquisition with a rational full-support native separation, a scalable
gap, and a law-faithful prefix-reduction theorem. The bounds are not exact
Bayes optima. A necessary-and-sufficient criterion for boundary-law
invariance, a total-resource optimum, an all-memory minimum, physical
spacetime recovery, worldwide originality, kernel certification and
completion of the broader programme remain open.

## 追加锚（本行以下为增补区）

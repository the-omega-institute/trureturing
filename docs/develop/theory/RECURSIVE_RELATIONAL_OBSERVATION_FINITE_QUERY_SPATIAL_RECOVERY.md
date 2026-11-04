# Recursive relational observation: finite-query spatial recovery under a shared hidden parameter

This companion fixes the source and permissions of Process Geometry §27 and adds
the hard-cap root-risk frontier. The same parameter $Q$ is used on both outward
arms and on every fresh edge. The result concerns the root and the coherent
labels on the actually exposed connected interval; it does not infer an
unacquired source law or a parameter readout.

## 1. The fixed PG27 source and the cap objective

**Definition 1.1 (PG27 source).** Fix $a,b>0$ with $a+b=1$. Draw
$Q\sim\mu$ once, where $\mu$ is a probability measure on $(0,1)$, and draw
$X_0\sim\operatorname{Bernoulli}(b)$ independently of $Q$. Conditional on
$(Q,X_0)$, generate independent left and right outward Markov arms with
transition matrix
$$
P_Q=
\begin{pmatrix}
1-Q&Q\\
1&0
\end{pmatrix}.
\tag{FR.1}
$$
A fresh boundary-edge query on either arm returns $1$ exactly when the two
newly exposed endpoint bits are both $0$, and otherwise returns $0$. A $1$ is
the first marker and terminates the experiment. All queries are fresh boundary
edges of the one connected interval containing the root.

The observer has an independent seed $U\sim\nu$. Its next side, stopping time
before a marker, and decoder are measurable functions of $U$ and the complete
ordered action/reply journal. It may stop at any time $\sigma\le n$, or stop
automatically at the first marker. It has no $Q$ port, no source-law table,
and no free old clock. A terminal root guess determines coherent labels on the
exposed interval by propagating the acquired edge relations. The loss is the
prior-average $0$-$1$ loss of the root guess (equivalently, the coherent-label
loss on that interval).

Write
$$
M_j=\int_{(0,1)}q^j\,\mu(dq),\qquad M_0=1,\qquad
A_j=M_j-M_{j+1}\quad(j\ge0).
\tag{FR.2}
$$
Because $\mu$ is supported on $(0,1)$, $M_{j+1}<M_j$ and $M_j>0$ for every
finite $j$. Let $R_n^*$ be the infimum of the above prior-average error over
all causal policies and decoders with cap $n$.

The full-history posterior and the zero-response transition used below are
exactly the PG27 identities: for arm lengths $(\ell,r)$ put
$$
\eta=(\ell\bmod2,r\bmod2),\qquad
s=\eta_L+\eta_R,\qquad
k=\lfloor\ell/2\rfloor+\lfloor r/2\rfloor.
\tag{FR.3}
$$
The all-zero journal has joint masses
$$
\Pr(X_0=0,\text{journal})=aM_{k+s},\qquad
\Pr(X_0=1,\text{journal})=bM_k.
\tag{FR.4}
$$
These are prior joint masses, already integrated over the same actual $Q$.
They are not conditional-on-survival seed weights.

## 2. The all-zero journal is the only uncured error leaf

**Lemma 2.1 (Marker leaves are exact).** On every journal containing a
marker, the connected exposed interval contains a $00$ edge. Its endpoint
value is therefore known, and the acquired relations propagate that value to
the root. A decoder can have zero loss on that leaf.

**Proof.** The transition $1\mapsto1$ is forbidden, so a reply $1$ identifies
the exposed pair as $00$. The journal records the ordered side and every
reply, hence the path from the marked edge to the root is known. Propagation
recovers the root and all labels in the exposed interval. $\square$

**Lemma 2.2 (Leafwise Bayes lower bound with an independent seed).** Fix a
seed value $u$ and follow the policy on the hypothetical journal consisting
only of zero replies until it stops at lengths $(\ell,r)$, with
$\ell+r\le n$. If the decoder sees no marker, its error contribution on this
seed is at least
$$
e(\ell,r)=\min\{aM_{k+s},\,bM_k\}.
\tag{FR.5}
$$
For a general seed law, the total error is the $\nu$-average of these
leafwise contributions, with marker leaves contributing zero.

**Proof.** With the zero journal fixed, the action sequence and the stopping
decision are fixed functions of $u$; the seed is independent of the source.
Conditional on $Q=q$, a left arm of length $\ell$ and a right arm of length
$r$ have alternating absolute bits. Under root $0$ there are $k+s$ transitions
$0\to1$, and under root $1$ there are $k$ such transitions. Integrating the
two root cases against $\mu$ gives (FR.4). A decoder that does not observe
$Q$ chooses one root label on this journal, so its correct joint mass is at
most the larger of the two masses and its error is at least their minimum.
The zero journal is the only possible non-marker journal. Integrating over the
original seed law gives the last assertion; replacing $\nu$ by its
survival-conditioned law would change the experiment and is not allowed.
$\square$

**Lemma 2.3 (The cap index bounds).** If $\ell+r\le n$ and
$m=\lfloor n/2\rfloor$, then
$$
k\le m,\qquad k+s=\left\lceil\frac{\ell}{2}\right\rceil+
\left\lceil\frac r2\right\rceil\le m+1.
\tag{FR.6}
$$
Consequently
$$
e(\ell,r)\ge \min\{aM_{m+1},\,bM_m\}.
\tag{FR.7}
$$

**Proof.** The first inequality follows by summing the two floor terms.
For the second, use $\lceil t/2\rceil+\lceil u/2\rceil\le
\lfloor(t+u)/2\rfloor+1$ when $t+u\le n$. Since the moment sequence is
decreasing, each mass in (FR.5) is at least the corresponding mass in
(FR.7). The minimum is monotone in both coordinates. $\square$

## 3. Exact attained hard-cap frontier

**Theorem 3.1 (Finite-query spatial recovery risk).** For $n=0$,
$$
\boxed{R_0^*=\min(a,b).}
\tag{FR.8}
$$
For $n\ge1$, with $m=\lfloor n/2\rfloor$,
$$
\boxed{R_n^*=\min\{aM_{m+1},\,bM_m\}.}
\tag{FR.9}
$$
The infimum is attained by a deterministic lawful control and a
prior-integrated MAP decoder. In particular every finite cap has strictly
positive risk, while
$$
\lim_{n\to\infty}R_n^*=0.
\tag{FR.10}
$$

**Proof.** For $n=0$ the observer stops immediately and the best root label
has mass $\max(a,b)$, giving (FR.8). For $n\ge1$, Lemmas 2.1--2.3 give the
lower bound (FR.9) for every causal policy, including early stopping,
random seeds, randomized side choices, and decoders that output a complete
coherent interval labeling.

It remains to attain the bound. If $n=2m+1$, query one side repeatedly until
a marker or the cap. On the all-zero journal the lengths are $(2m+1,0)$, so
$(k,s)=(m,1)$ and the two joint root masses are exactly
$(aM_{m+1},bM_m)$. MAP on that journal and exact propagation on a marker give
(FR.9).

Let $n=2m$ with $m\ge1$. Route E queries one side $2m$ times unless a marker
appears; its all-zero masses are $(aM_m,bM_m)$, so its error is
$$
E_{\rm E}=\min(a,b)M_m.
\tag{FR.11}
$$
Route O queries one side $2m-1$ times and then the other side once, again
stopping on a marker. Its all-zero masses are $(aM_{m+1},bM_{m-1})$, and
$$
E_{\rm O}=\min(aM_{m+1},bM_{m-1}).
\tag{FR.12}
$$
Both routes use only fresh boundary edges and are therefore lawful. Put
$A=aM_{m+1}$ and $B=bM_m$. If $A\le B$, then
$E_{\rm O}=A$ because $bM_{m-1}\ge B$. If $B<A$, then necessarily $b\le a$:
$b>a$ would imply $B\ge aM_m>A$. Hence $E_{\rm E}=B$. Thus
$\min(E_{\rm E},E_{\rm O})=\min(A,B)$, proving attainability.

Finally $M_j\downarrow0$ by dominated convergence, since $q^j\to0$ on
$(0,1)$. Positivity of $a,b,M_j$ gives strict positivity at each finite cap,
and (FR.10) follows. $\square$

**Corollary 3.2 (What the hard cap does and does not measure).** The value
$R_n^*$ is an unconditional prior-average root error. It is not a worst-$Q$
risk, a risk conditional on surviving to the cap, a Hamming loss for all
unexposed sites, or a free-abstention value. The proof integrates $Q$ before
the decoder acts and averages over the original independent seed law.
It gives no recovery of the unacquired law table, no parameter estimate, and
no statement about total storage, CPU time, physical time, or a four-view
reconstruction.

## 4. Comparison with the PG27 mean controller

Assume now
$$
I_\mu=\int\frac{\mu(dq)}{1-q}<\infty.
\tag{FR.13}
$$
PG27.17 gives the exact mean objective for all first-marker waiting
strategies. Its canonical PG27.18a representative uses
$$
v_j=bA_{j-1}-aA_j,\qquad
N_*=\inf\{j\ge1:v_j<0\},
\tag{FR.14}
$$
with $N_*=\infty$ for an empty set. It reads one side, switches to the other
side once at query $2N_*$ when $N_*<\infty$, then returns to the first side.
At a zero coefficient it keeps the even/even convention; another
zero-tie representative is still a mean optimizer but is a different
controller. The untruncated mean is
$$
\mathbb E_{\pi^{\rm can}}\tau
=2I_\mu-a+w_{N_*},\qquad
w_j=bM_{j-1}-aM_j,\quad w_\infty=0.
\tag{FR.15}
$$

For $m\ge1$ define
$$
T_m=\frac{A_m}{A_{m-1}},\qquad
U_m=\frac{M_{m+1}}{M_m},\qquad
\theta=\frac ba.
\tag{FR.16}
$$
The quantities are well defined because all displayed denominators are
positive.

**Lemma 4.1 (The two comparison ratios are ordered).**
$$
T_m\le U_m.
\tag{FR.17}
$$

**Proof.** Log-convexity of the moment sequence gives
$M_{m-1}M_{m+1}\ge M_m^2$. Multiplying out $T_m\le U_m$ leaves exactly
$$
A_mM_m\le A_{m-1}M_{m+1}
\Longleftrightarrow
M_m^2\le M_{m-1}M_{m+1}.
$$
$\square$

**Theorem 4.2 (Mean-optimal does not mean cap-risk-optimal).** Truncate the
canonical PG27.18a controller at cap $2m$ and use its best permitted
prior-integrated decoder. It attains the hard-cap frontier (FR.9) if and
only if
$$
\boxed{T_m\le\theta\le U_m.}
\tag{FR.18}
$$
At every odd cap $2m+1$, every one-switch representative of the PG27.18a
mean-optimal class has risk $R_{2m+1}^*$.

**Proof.** Since
$v_m=A_{m-1}(b-aT_m)$, the canonical controller has no switch by cap $2m$
when $T_m\le\theta$ (including equality), and has switched when
$T_m>\theta$. In the first case its zero journal has the even/even shape and
$$
C_m^{\rm can}=\min(a,b)M_m.
\tag{FR.19}
$$
If also $\theta\le U_m$, then $U_m<1$ forces $b<a$ and
$bM_m\le aM_{m+1}$, so (FR.19) equals (FR.9). If $\theta>U_m$, then
$aM_{m+1}<bM_m$; (FR.19) is strictly larger than the frontier, whether
$b\le a$ or $b>a$.

In the second case, Lemma 4.1 gives $\theta<U_m$ and $T_m<1$, hence
$b<a$. The zero journal has odd/odd shape and
$$
C_m^{\rm can}=\min(aM_{m+1},bM_{m-1}).
\tag{FR.20}
$$
Here $bM_m<aM_{m+1}$, while $bM_{m-1}>bM_m$; both entries in (FR.20) are
therefore strictly larger than the frontier $bM_m$. This proves the even-cap
iff statement.

At cap $2m+1$, if the switch has not occurred the zero journal has lengths
$(2m+1,0)$; if it has occurred it has lengths $(2m,1)$. Both have
$(k,s)=(m,1)$, hence both have the two masses in (FR.9). MAP and marker
decoding therefore attain $R_{2m+1}^*$. A zero-coefficient tie can choose
either one-switch placement, but this does not identify that tie choice with
the canonical even/even convention. $\square$

## 5. Strict same-source separations and resource boundaries

**Proposition 5.1 (A strict $b\ge\tfrac12$ counterfamily).** Fix one source
measure $\mu$ on $(0,1)$ and any $b\in[1/2,1)$, with $a=1-b$. For every
$m\ge1$, the canonical mean controller has $N_*=\infty$ and its cap-$2m$
risk is $aM_m$, whereas
$$
R_{2m}^*\le aM_{m+1}<aM_m.
\tag{FR.21}
$$
Thus the same hidden-$Q$ source gives a strict mean/cap-risk separation at
every positive even cap. No resampling of $Q$ is used.

**Proof.** Here $b\ge a$ and $A_m<A_{m-1}$, so
$v_m=bA_{m-1}-aA_m>0$ for every $m$. Hence the canonical controller never
switches. Its even-cap all-zero masses are $aM_m,bM_m$, whose minimum is
$aM_m$. The hard-cap theorem and strict moment decrease give (FR.21).
$\square$

**Example 5.2 (A genuinely hidden nondegenerate parameter).** Let $\mu$ be
uniform on $(0,\rho)$ with $\rho=3/4$, and take $a=3/5$, $b=2/5$. Then
$$
M_j=\frac{\rho^j}{j+1},\qquad
I_\mu=\frac{-\log(1-\rho)}{\rho}=\frac43\log4<\infty.
\tag{FR.22}
$$
The parameter $Q$ is nondegenerate and remains hidden. At $m=10$,
$$
T_{10}=\rho\,\frac{10\cdot15}{12\cdot14}=\frac{75}{112}>
\frac23=\theta,
\qquad
U_{10}=\rho\,\frac{11}{12}=\frac{11}{16}>\theta.
\tag{FR.23}
$$
The canonical mean controller has switched by cap $20$, so its risk is
$\min(aM_{11},bM_9)$; the frontier is
$$
R_{20}^*=\min(aM_{11},bM_{10})=bM_{10},
$$
and both $aM_{11}$ and $bM_9$ are strictly larger than $bM_{10}$. This is
a strict cap-risk failure on the same realization whose mean objective the
controller minimizes.

A capped policy pays at most its declared $n$ fresh-edge queries. The
untruncated first-marker cost is instead (FR.15), and is a separate
expectation. For example, the uniform law on $(0,1)$ has
$M_j=1/(j+1)$ and $I_\mu=\infty$: every untruncated waiting strategy has
infinite mean, while every finite cap has cost at most $n$ and its risk still
tends to zero by (FR.10). The finite correction in (FR.15) is not an
improvement comparison between two infinite expectations.

## 6. Relation to existing results and exact limits

The source and posterior formulas in (FR.1)--(FR.4), the all-policy waiting
tails, the finite-mean criterion, and the one-switch mean controller are the
PG27.1--PG27.3 and PG27.14--PG27.18c results in
[Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
The stopping-tail and replay interfaces are also supplied by
D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.lean,
including stopped_execution_replay_bridge,
conditional_no_marker_cylinder_mass, and adaptive_marker_stopping_tails; the
mixed-source mean suppliers are BeneficialMarkerDeflection.lean and
SingleDeflectionOptimalController.lean with their owning Blueprint Scribes.
Private helpers in FiniteAtomLinearRealization.lean and
RawFiniteAtomLinearRealization.lean are reused where applicable, without
treating private visibility as missing mathematics.

Controlled sensing is discussed in Nitinawarat--Atia--Veeravalli,
*Controlled Sensing for Multihypothesis Testing*, arXiv:1205.0858v6,
§§II--IV, https://arxiv.org/pdf/1205.0858v6. Active sequential testing is
discussed in Naghshvar--Javidi, *Active Sequential Hypothesis Testing*,
arXiv:1203.4626v4, §2.1, https://arxiv.org/abs/1203.4626v4. Those sources
use conditional-memoryless or asymptotic testing models; they do not supply
the shared latent-$Q$ integration, first-marker stopping, or the present
finite-cap formula.

The theorem does not add a hidden-parameter query, reset, copy, erased
journal, unacquired law table, arbitrary posterior preparation, or a new
source port. It separates fresh-edge count from prior description, archive
and output storage, local arithmetic and precision, and any physical
resource. A fixed-prior mathematical controller does not provide uniform
effective synthesis from arbitrary approximate descriptions of $\mu$.
No total-memory optimum, CPU bound, physical-time bound, whole-source
recovery theorem, or four-view recovery theorem follows.

## 99. 追加锚（本行以下为增补区）

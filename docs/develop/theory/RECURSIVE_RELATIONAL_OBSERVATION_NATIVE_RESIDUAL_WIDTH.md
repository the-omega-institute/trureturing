# Native residual width after chronological block observability

This continuation repairs the source-specific residual argument attached to
[Atomic substitution sources: acquisition of a persistent global port orientation](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md), §§27--39. The old volume is an immutable supplier. In particular, its Definition 27.1 fixes one actual source, one persistent physical order $a<b$, lexicographic beta-leaf births, and an all-index binary recurrence law. Its Proposition 39.2 is the only birth-index calculation used below. No semantic port, phase register, rank field, or irregular chronology is supplied to an evaluator.

The result below is deliberately split into an unconditional integer residual theorem and a fixed-threshold bridge. The former is proved for one actual source and one cut. The latter uses a logarithmic threshold menu to obtain one fixed threshold; a generic integer-to-threshold shortcut is false. This separation preserves the original unknown-law, unknown-cut and exact-output obligations.

## 1. Residuals, horizons, and the common physical layer

**Definition 1.1 (complete physical residual).** Fix a source $s$ of GPO Definition 27.1 and a completed cut $n$. Let $H_n=2n-1$. For a present branch $p$ at cut $n$, write

$$
 D_{s,n,p}(u)\in\{0,\ldots,H_n\},\qquad u\in\{0,1\}^{H_n},
$$

for the exact depth returned by ACR Definition 13.1: the initial paid word is $pa$, the tape bit $0$ chooses $a$, bit $1$ chooses $b$, every literal is submitted to the original root, and the final absent-child test is paid. The tape is restarted at the cone. Put $\mathcal R_{s,n}(p)=D_{s,n,p}$.

A prefix $p$ is a proof address only. It is not an acquired coordinate. Equality of two residuals means equality on the complete common tape cube, including tapes that terminate early.

**Lemma 1.2 (prefix offset).** Let $p$ be a present branch at a cut $n$ and let $v$ be a direction suffix that is legal after the physical prefix $p$. If the root evaluator has already consumed $h=|p|$ direction bits and its remaining horizon is at least $H_n-h$, then

$$
 D_{s,n,\varepsilon}(pv)=h+D_{s,n,p}(v).
 \tag{NRW.1}
$$

The right side is interpreted on the suffix domain; unused tape coordinates are ignored after the first terminal test.

*Proof.* The root walk pays exactly the $h$ edges of $p$ before starting the local walk in the $p$-cone. The local procedure, including its terminal test, is then identical. The common additive $h$ is independent of $v$ and therefore preserves equality and inequality of residuals. $\square$

**Definition 1.3 (same-rank layer).** At cut $n$ let $\kappa_n(p)$ be ACR Definition 10.1's rank. For a depth $h$ layer write

$$
 \mathcal P(n,h,q)=\{p\in\{a,b\}^h:\ p\text{ is a branch at }n,\ \kappa_n(p)=q\}.
$$

At a fixed $h$, every edge decreases rank by one or two. Hence the ranks of present words in that layer lie in at most $h+1$ consecutive values.

## 2. A valid chronological bridge

The failed argument in the unmerged draft read the first $d$ beta-spine births of a cone as $d$ consecutive global outputs. They need not be consecutive. The replacement uses one actual update and a contiguous lexicographic block of beta births.

**Definition 2.1 (a block exposed inside a cone).** Let $p$ be a branch at cut $n$. Choose an earlier update $e<n$. Immediately before update $e+1$, the beta leaves below $p$ form a lexicographic interval in the global beta-leaf list. If that interval has at least $m$ leaves, let

$$
 J(p,e,m),J(p,e,m)+1,\ldots,J(p,e,m)+m-1
 \tag{NRW.2}
$$

be the global birth numbers of the first $m$ such leaves when update $e+1$ is performed.

**Lemma 2.2 (one actual interval, not a sampled subsequence).** The indices in (NRW.2) are consecutive global birth numbers in the single source of Definition 27.1. If $p\ne p'$ are prefix-incomparable, then the two intervals at the same update are disjoint and have different first indices.

*Proof.* At one update the actuator enumerates all old beta leaves in physical lexicographic order and consumes the stream once per leaf. A fixed prefix selects a contiguous interval of that list. Prefix-incomparable cones select disjoint intervals. This is the actual chronology, including all sibling intervals before the selected block; no local reindexing has been made. $\square$

**Lemma 2.3 (orientation is recoverable from a complete residual).** Suppose $v$ is a branch of rank $r\ge3$ at cut $n$. The complete residual $D_{s,n,v}$ determines which physical child has rank $r-1$ and which has rank $r-2$.

*Proof.* Restrict the residual to tapes beginning with $a$ and with $b$, subtract the common first edge, and take the uniform mean of the two resulting suffix functions. A rank-$j$ cone has mean

$$
 \mu_0=\mu_1=0,\qquad
 \mu_j=\frac{2j}{3}-\frac49+\frac49(-1/2)^j\quad(j\ge2),
 \tag{NRW.3}
$$

by the ACR 13.2 recurrence. Thus $\mu_{r-1}\ne\mu_{r-2}$ for every $r\ge3$, including the terminal pair $2,1$. The larger-mean child is the rank-$r-1$ child. This is a mathematical decoder from the complete function; it is not a free physical observation. $\square$

**Lemma 2.4 (a short local update supplies a consecutive observable block).** Let $d\ge32$ and set

$$
 s_d=\min\{s\ge4:F_s\ge d\}.
 \tag{NRW.4}
$$

Suppose the ACR descriptor of $p$ has birth update $b_p$ and $\kappa_n(p)\ge d+4$. Put $e_p=b_p+s_d$. Then, immediately before update $e_p+1$, the $p$-cone contains at least $d$ beta leaves. Every branch born from the first $d$ of them has rank at least $3$ at cut $n$.

*Proof.* Use ACR Definition 10.1 and its two mass formulas $\lambda_\alpha(r)=F_r$ and $\lambda_\beta(r)=F_{r+1}$. At age $s_d$ the smaller beta mass is $\lambda_\alpha(s_d)=F_{s_d}\ge d$; the beta-initial case has the larger mass. Since $\kappa_n(p)\ge d+4$, the update $e_p+1$ is at least three updates before the final cut. The branches born there therefore have rank at least $3$, and Lemma 2.3 applies. $\square$

The numerical inequality in Lemma 2.4 is intentionally slack. Replacing $s_d$ by any larger logarithmic Fibonacci index only shortens the available horizon and does not change the argument.

**Lemma 2.5 (block observability of a complete residual).** Let $p$ satisfy the hypotheses of Lemma 2.4. From the complete function $D_{s,n,p}$ one can recover the $d$ consecutive stream bits

$$
 z_{J(p,e,d)},\ldots,z_{J(p,e,d)+d-1}.
 \tag{NRW.5}
$$

*Proof.* A direction prefix reaches any selected beta-leaf parent in the $p$-cone. Restricting $D_{s,n,p}$ to that prefix and subtracting its known edge length gives the residual of the branch born there. The branch rank is at least five, so Lemma 2.3 recovers its orientation bit. The bit saying which child has rank $r-1$ is exactly the birth bit $z_j$ in GPO Definition 27.1. Iterate over the first $d$ beta leaves in their lexicographic order. The proof uses all sibling intervals in the actual source only to identify the indices in (NRW.2); it never replaces them by local consecutive samples. $\square$

**Theorem 2.6 (same-source phase separation).** Let $g$ be a primitive binary polynomial of degree $d$, let $z$ be any nonzero maximum-length stream of period $T_d=2^d-1$, and let $p,p'$ be prefix-incomparable branches at the same cut with

$$
 \kappa_n(p)=\kappa_n(p')\ge d+4,\qquad
 J(p,e_p,d),J(p',e_{p'},d)<T_d.
 \tag{NRW.6}
$$

If the two first indices in (NRW.6) are different, then

$$
 \mathcal R_{z,n}(p)\ne\mathcal R_{z,n}(p').
 \tag{NRW.7}
$$

*Proof.* If the residuals were equal, Lemma 2.5 would give equal length-$d$ consecutive output blocks at the two first indices. The standard companion-state observability theorem for a degree-$d$ LFSR says that a length-$d$ consecutive output block determines the state. A primitive stream visits each nonzero state once per period, so equal blocks have equal indices modulo $T_d$. Both indices lie in $[1,T_d-1]$, contradicting Lemma 2.2; if the two local updates differ, their global birth intervals are disjoint by chronology. This is the only use of LFSR observability, and its supplier hypotheses are now literally satisfied. $\square$

Theorem 2.6 is source-specific and unconditional for complete integer residuals. It does not assert that an irregular beta spine is observable, and it does not use a fixed-tail probe. Terminal ranks zero and one are handled by the rank-five margin before the decoder is invoked.

## 3. One actual cut with exponentially many integer residuals

**Theorem 3.1 (one source and one common layer).** For every $d\ge32$, choose a primitive binary polynomial and a nonzero maximum-length seed. Put

$$
 h_d=\left\lfloor d/8\right\rfloor,\qquad
 n_d=d+2h_d+4,\qquad H_d=2n_d-1.
 \tag{NRW.8}
$$

At the one actual cut $n_d$, one rank $q_d\ge d+4$ has a set $\mathcal P_d=\mathcal P(n_d,h_d,q_d)$ with

$$
 |\mathcal P_d|\ge\left\lceil\frac{2^{h_d}}{h_d+1}\right\rceil,\qquad
 \mathcal R_{z,n_d}(p)\ne\mathcal R_{z,n_d}(p')\quad(p\ne p').
 \tag{NRW.9}
$$

All selected cones coexist in this one chronological source.

*Proof.* At cut $n_d$, all length-$h_d$ words are present branches. Their ranks lie between $n_d-2h_d=d+4$ and $n_d-h_d$, so there are at most $h_d+1$ rank values. Pigeonhole gives (NRW.9)'s cardinality. Every selected cone satisfies Lemma 2.4 with its own $e_p=b_p+s_d$. The first $d$ beta leaves at that update form a physical lexicographic interval. Distinct selected prefixes are prefix-incomparable; intervals at one update are disjoint, and intervals at different updates are disjoint in chronological order, so their first indices are distinct. Finally

$$
 B_{n_d}=F_{n_d+1}-1<
 \left(\frac{13}{8}\right)^{n_d+1}<2^d-1=T_d,
 \tag{NRW.10}
$$

by $F_m<\varphi^m$ and $\varphi<13/8$, with the displayed parameters and $d\ge32$. Hence all block starts are below one period and Theorem 2.6 applies. Maturity follows from $F_{n_d}-1\ge2d$. No source, cut, phase or rank is supplied to an acquisition controller. $\square$

The lower bound in (NRW.9) is $2^{\Omega(d)}$. It is a state-count statement about complete integer residuals. By Lemma 1.2, the root residual at a length-$h_d$ prefix is $h_d+D_{z,n_d,p}$ on the remaining suffix horizon; the common offset preserves the same width conclusion.

**Proposition 3.2 (uniform depth law is rank-only).** For a fair length-$H_d$ tape, the probability generating polynomial of a rank-$q$ cone is

$$
 G_0(x)=G_1(x)=1,\qquad
 G_q(x)=\frac{x}{2}(G_{q-1}(x)+G_{q-2}(x))\quad(q\ge2).
 \tag{NRW.11}
$$

Thus all $p\in\mathcal P_d$ have the same uniform depth law, although their pointwise residual functions differ.

*Proof.* The first direction chooses the two unordered child ranks with equal probability. Physical orientation only swaps the two summands. The terminal convention $G_0=G_1=1$ is essential. Induction on $q$ gives (NRW.11). $\square$

## 4. One fixed threshold, obtained without a threshold input

**Definition 4.1 (a fixed-threshold profile).** For $t\in\{0,\ldots,H_d\}$ put

$$
 \Theta_{p,t}(u)=\mathbf1\{D_{z,n_d,p}(u)\ge t\}.
 \tag{NRW.12}
$$

The threshold is chosen once for the instance $(d,z,n_d,q_d)$ and is not a suffix input. A representation that reads a threshold before the direction prefix is a different contract.

**Lemma 4.2 (first orientation difference has a bounded deficit).** Let $p,p'$ be two selected prefixes from Theorem 3.1 with the same descriptor birth update $b_p=b_{p'}$. If their complete residuals differ, there are an integer $c$ with $0\le c\le s_d$ and a tape $u$ such that

$$
 D_{z,n_d,p}(u)\ge q_d-1-c,\qquad
 D_{z,n_d,p'}(u)<q_d-1-c,
 \tag{NRW.13}
$$

or the same inequalities with $p,p'$ exchanged.

*Proof.* The two consecutive output blocks in Lemma 2.5 differ because their first indices are distinct within one primitive period. If all physical orientations in the two cones agreed through the first $s_d$ descendant updates, the actual lexicographic beta lists and their first $d$ birth bits would agree by induction on the updates. Hence there is a first common physical address at which the two orientation-labelled rank trees differ, and it lies at depth at most $s_d$. Before that address, the two rank trees and all physical child choices agree. Let $c$ be the number of smaller-rank child choices on this common prefix; then $c\le s_d$. At the differing branch, choose the physical child that has rank $r-1$ in the first cone and then continue along its larger-rank child at every later branch. The resulting path has total depth $q_d-1-c$. In the other cone the same first child has rank $r-2$, so no continuation can reach depth $q_d-1-c$. This is a fixed-threshold separation at $t=q_d-1-c$. The terminal ranks zero and one are below the selected rank-three decoder margin, so the first difference is an orientation difference rather than an omitted terminal test. $\square$

**Lemma 4.3 (the integer family is separated by a logarithmic threshold menu).** For the set $\mathcal P_d$ of Theorem 3.1, put

$$
 T_d^{\mathrm{menu}}=\{q_d-1-k:0\le k\le s_d\}.
 \tag{NRW.14}
$$

The tuple of profiles

$$
 p\longmapsto\bigl(\Theta_{p,t}\bigr)_{t\in T_d^{\mathrm{menu}}}
 \tag{NRW.15}
$$

is injective on $\mathcal P_d$ after splitting $\mathcal P_d$ into at most two classes according to the descriptor birth update.

*Proof.* At one fixed rank $q_d$, the relation $q_d=n_d-b_p+\mathbf1_{\{\sigma_p=\beta\}}$ permits at most two values of $b_p$. Within one class, Lemma 4.2 gives a threshold in $T_d^{\mathrm{menu}}$ separating every pair with unequal residuals. Theorem 3.1 says every pair is unequal. Thus equality of all menu profiles forces equality of the prefix. $\square$

**Theorem 4.4 (one fixed threshold has superpolynomial width).** There are a threshold $t_d\in T_d^{\mathrm{menu}}$ and a subset $\mathcal Q_d\subseteq\mathcal P_d$ such that

$$
 |\mathcal Q_d|\ge
 \left(\frac{1}{2}
 \left\lceil\frac{2^{h_d}}{h_d+1}\right\rceil\right)^{1/(s_d+1)}
 =2^{\Omega(d/\log d)},
 \qquad
 \Theta_{p,t_d}\ne\Theta_{p',t_d}\quad(p\ne p').
 \tag{NRW.16}
$$

The threshold $t_d$ is fixed across all prefixes and continuations in this one instance. Consequently it is a genuine single-threshold, direction-first width lower bound; it is not a family with a free threshold coordinate.

*Proof.* One of the two birth-update classes has size at least $N_d/2$, where $N_d$ is the cardinality in (NRW.9). For each $k\in\{0,\ldots,s_d\}$ let $M_k$ be the number of distinct profiles at threshold $q_d-1-k$ in that class. Lemma 4.3 gives

$$
 \frac{N_d}{2}\le\prod_{k=0}^{s_d}M_k.
 \tag{NRW.17}
$$

Some $M_k$ is therefore at least $(N_d/2)^{1/(s_d+1)}$. Choose $t_d=q_d-1-k$ and one representative prefix from every distinct profile; call the set $\mathcal Q_d$. Since $s_d=O(\log d)$ and $N_d=2^{\Omega(d)}$, the displayed size is $2^{\Omega(d/\log d)}$, which dominates every polynomial in $d$. The threshold is chosen after the source and cut are fixed but is not provided as an input to the evaluator. $\square$

**Proposition 4.5 (why the menu argument is necessary).** Pairwise inequality of integer functions alone does not imply one threshold with exponential width. For $m\ge1$ let

$$
 D_x(j,c)=2j+(c\mathbin{\mathsf{xor}}x_j),\qquad
 x\in\{0,1\}^m,\quad 1\le j\le m,\ c\in\{0,1\}.
 \tag{NRW.18}
$$

All $2^m$ integer functions are distinct, and every $D_x$ has the same uniform distribution. For each fixed threshold $t$, the threshold profile depends only on the unique coordinate $j$ for which $t\in\{2j,2j+1\}$; hence it has at most two profiles. This generic countermodel is not an FIB source. The native proof above succeeds because the first differing physical branch has only $O(\log d)$ possible depth deficits.

*Proof.* Distinct $x$ differ at a coordinate $j$, and the two values at $(j,0)$ and $(j,1)$ are interchanged. For fixed $t$, only one $j$ can straddle $t$; all other coordinates give a constant answer. $\square$

## 5. Sequential representation and resource boundaries

**Definition 5.1 (direction-first sequential machine).** A machine receives the physical direction bits in order. At a prefix layer it retains every control field, source-free work bit, prefix summary and resource counter that can affect a later answer. It has no source reply, semantic relabeling, threshold input, or reordering operation. The output is the root depth after the consumed prefix and the remaining suffix.

**Theorem 5.2 (fixed-threshold state and bit consequence).** Under Theorem 4.4's fixed threshold $t_d$, a direction-first exact or strict pointwise-$<1/2$ approximate machine has

$$
 w_{h_d}\ge|\mathcal Q_d|=2^{\Omega(d/\log d)},\qquad
 \log_2 w_{h_d}=\Omega(d/\log d).
 \tag{NRW.19}
$$

The statement counts all retained memory. It proves a linear bit lower bound, not exponentially many bits.

*Proof.* At the common layer, merging two states would give identical continuation profiles, contradicting Theorem 4.4. Strict pointwise error below $1/2$ rounds to the same exact Boolean profile, and taking binary logarithms gives the second inequality. $\square$

The root residual has the common $h_d$ offset in (NRW.1), and the remaining suffix horizon is at least $H_{n_d}-h_d$. Consequently a width result transfers to the root only after that offset and horizon are included. State merging is a representation argument; it grants no free complete-function access to an implementation.

For the root formulation, the same instance uses the single threshold $h_d+t_d$ on every selected prefix continuation. The shift is common to the layer and does not introduce a threshold input.

**Proposition 5.3 (what is and is not settled).** Theorems 2.6, 3.1 and 4.4 prove an unconditional same-source, same-layer integer obstruction and a superpolynomial consequence for one fixed threshold. Proposition 3.2 proves equal-rank uniform laws. Arbitrary adaptive acquisition lower bounds, alternate variable orders, weighted or sign-only samplers, exponential memory-bit lower bounds, necessity of the $4^d$ catalogue, and the original canonical $K_d(P)$ output order remain open.

In particular, the strict pointwise Boolean approximation claim is meaningful only under the exact direction-first contract with the fixed $t_d$. Sign-correct comparison probes, mean guarantees, average error, and approximation of the integer depth do not imply that contract. The original unknown-law/unknown-cut polynomial TOTAL acquisition question therefore remains unchanged.

## 6. Finite certificates and supplier boundaries

The following small certificates test the repaired chronology and the native limits. For each row, use the primitive recurrence displayed by its characteristic polynomial, seed $1,0,\ldots,0$, the actual lexicographic update rule of GPO Definition 27.1, and the stated mature cut. Enumerating the complete direction cube at the shown horizon gives the listed distinct integer residuals and equal rank law. These are mathematical finite certificates, not evidence for the all-$d$ theorem.

| $d$ | characteristic polynomial | cut $n$ | layer $h$ | selected rank | cones | distinct integer residuals | largest menu profile | common uniform law |
|---:|---|---:|---:|---:|---:|---:|---:|---|
| 4 | $X^4+X+1$ | 14 | 4 | 8 | 6 | 6 | 6 | yes |
| 5 | $X^5+X^2+1$ | 16 | 5 | 9 | 10 | 10 | 10 | yes |
| 6 | $X^6+X+1$ | 18 | 6 | 9 | 20 | 20 | 20 | yes |
| 7 | $X^7+X+1$ | 20 | 7 | 10 | 35 | 35 | 35 | yes |
| 8 | $X^8+X^6+X^5+X^4+1$ | 22 | 8 | 10 | 70 | 70 | 70 | yes |
| 9 | $X^9+X^5+1$ | 24 | 9 | 11 | 126 | 126 | 126 | yes |

The $d=5$ pair $p=\mathrm{aabbb}$ and $p'=\mathrm{abaaa}$ has equal first five beta-spine samples $10101$ at global indices $(23,38,61,100,161)$ and $(24,39,63,103,166)$, while their consecutive output blocks differ. Thus the old irregular-sample inference is false even though the complete residuals are distinct. The $d=32$ source with $X^{32}+X^{22}+X^2+X+1$ and seed $1,0,\ldots,0$ gives the same chronology failure in the advertised asymptotic range; no fixed-tail witness is used here.

HAC, [*Handbook of Applied Cryptography*](https://cacr.uwaterloo.ca/hac/about/chap6.pdf), Chapter 6, Definitions 6.7--6.13 and Facts 6.12--6.14, supplies companion-state observability from $d$ consecutive outputs and maximum period for primitive feedback. Bryant, [*Graph-Based Algorithms for Boolean Function Manipulation*](https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf), §§1.1--2 and Theorem 1, supplies fixed-order residual merging. Boundary Dynamics §79 supplies the finite-message residual principle. ACR §§10 and 13 supplies ranks, terminal conventions, paid depth and means; GPO §§27--29 and 39 supplies the actual source, lexicographic chronology and index recurrence. The common-update block bridge and the logarithmic threshold-menu argument are the repository claims recorded here.

The volume establishes a real source-faithful integer and fixed-threshold repair. It does not claim Lean verification, worldwide novelty, arbitrary acquisition hardness, or a polynomial TOTAL impossibility.

## 追加锚（本行以下为增补区）

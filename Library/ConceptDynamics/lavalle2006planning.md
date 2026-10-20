---
bibkey: lavalle2006planning
authors: Steven M. LaValle
year: 2006
title: Planning Algorithms
doi: null
url: https://lavalle.pl/planning/ch11.pdf
claim: History information states can be compressed to recursively updated sets of possible states, with action propagation followed by observation filtering.
strata_touched: []
license: citation-only
triage: anchor
---

# Information states with a frozen original target

**Definition 1 (Source and joint state).** Chapter 11 at https://lavalle.pl/planning/ch11.pdf, especially §§11.1, 11.2.1–11.2.2, supplies history information states, information mappings and recursive nondeterministic information-state propagation. The joint labels and finite-horizon arguments below are elementary applications of that method. They do not assert a newly discovered general theory of belief states.

Let $\Omega$ be original worlds, $\theta_0:\Omega\to\Theta$ a fixed target, and $S$ the current execution-state space. Current state includes all protocol memory and control that can affect subsequent observations. After accessible history $h$, let $\Omega_h$ be its nonempty compatible original-world set and $\Phi_h:\Omega_h\to S$ the actual transported state. Define

$$
B_h=\{(\Phi_h(\omega),\theta_0(\omega)):\omega\in\Omega_h\}
\subseteq S\times\Theta.
\tag{1}
$$

The target coordinate refers to the original world; it is not recomputed from the current source after motion. Accessible observer records are themselves part of the overall system. Subsequent assertions concern nonempty compatible beliefs, not impossible histories.

**Definition 2 (Action and receipt).** For action $a$ let $D_a\subseteq S$ be its legal domain, $\delta_a:D_a\to S$ its deterministic transport and $\lambda_a:D_a\to O_a$ the complete visible receipt. Receipts may combine the entire ordered transaction. Action $a$ is common legal at $B$ when $\operatorname{pr}_SB\subseteq D_a$. Put

$$
\operatorname{Post}(B,a,o)
=\{(\delta_a(s),\theta):(s,\theta)\in B,\ \lambda_a(s)=o\}.
\tag{2}
$$

The interpretation of a finite record is a function $\gamma:z\mapsto B$. Record correctness is $\gamma(U(z,a,o))=\operatorname{Post}(\gamma(z),a,o)$ on actual, nonempty successors.

**Proposition 1 (Exact update retains the original target).** Under Definition 2's current-state sufficiency,

$$
B_{hao}=\operatorname{Post}(B_h,a,o).
\tag{3}
$$

An initially exact record with the stated interpretation/update identity remains exact at every finite observed history.

Proof. A compatible original world remains compatible precisely when its actual current state yields receipt $o$. Its new current state is $\delta_a(\Phi_h(\omega))$, while its label remains $\theta_0(\omega)$. This gives both inclusions in (3), including distinct worlds with the same pair. Induction proves the record claim. An omitted private state affecting receipts would violate Definition 2's sufficiency; (3) is not a license to omit that state. $\square$

**Proposition 2 (Two marginals do not replace their joint relation).** Equal current-state and target projections do not guarantee the same posterior target after an observation.

Proof. Let $B_+=\{(0,0),(1,1)\}$ and $B_-=\{(0,1),(1,0)\}$. Both projections are $\{0,1\}$ in both cases. A legal read with identity transport and receipt $\lambda(s)=s$ gives, after receipt zero, target zero from $B_+$ and target one from $B_-$. Thus the missing data can be pairing information rather than an additional marginal value. $\square$

## 1. Reliable finite-horizon completion

**Definition 3 (Target completion table).** Set

$$
\mathcal G=\{B\ne\varnothing:|\operatorname{pr}_\Theta B|=1\},
\qquad\mathcal W_0=\mathcal G,
$$

$$
\mathcal W_{n+1}=\mathcal G\cup
\{B\ne\varnothing:\exists a\text{ common legal at }B,\
\forall o,\ \operatorname{Post}(B,a,o)\ne\varnothing
\Rightarrow\operatorname{Post}(B,a,o)\in\mathcal W_n\}.
\tag{4}
$$

A depth-bounded contingent strategy chooses actions from the actual observed history, may stop with an answer, and must be correct for every compatible world. A finite-node receipt-indexed tree is a stronger representation requirement when receipt alphabets are infinite.

**Proposition 3 (Reliable completion and strategy depth).** $B\in\mathcal W_n$ if and only if there is a contingent strategy determining the target in at most $n$ actions in every candidate world. In general its tree can have infinitely many branches. If every reachable common action has finitely many possible nonempty receipt successors, it has a finite-node tree. Semantic existence of such a tree does not assert a finite effective program when states and actions lack an effective representation.

Proof. At depth zero, reliability is exactly one possible target. For a depth at most $n+1$ strategy not already stopping, its first action must be common legal and every possible receipt must allow depth at most $n$ continuation. Induction gives (4). Conversely select a witnessing common action and, for each nonempty receipt successor, attach the depth-$n$ strategy supplied inductively. In set-theoretic models arbitrary choices of these subtrees use the usual choice principle. Finite branching plus finite depth makes the total number of vertices finite by induction. Without finite branching take $B=\{(k,k):k\in\mathbb N\}$ and one action reporting $k$. Every posterior is a singleton, so $B\in\mathcal W_1$, but its literal receipt-indexed tree has one leaf for every natural number. This separates finite depth, finite tree size and finite-program realizability. $\square$

**Proposition 4 (Finite-model minimax distance).** If $S,\Theta$, the available action set and receipt alphabets are finite, define $D(B)=\min\{n:B\in\mathcal W_n\}$, infinity if absent. For nonempty beliefs,

$$
D(B)=\begin{cases}
0,&B\in\mathcal G,\\
1+\displaystyle\min_{a\text{ common legal}}
\max_{o:\operatorname{Post}(B,a,o)\ne\varnothing}
D(\operatorname{Post}(B,a,o)),&B\notin\mathcal G.
\end{cases}
\tag{5}
$$

The empty action minimum is infinity. If $D(B)<\infty$, a minimizing action lowers $D$ on every actual branch and yields a reliable terminating strategy.

Proof. At any common legal action there is at least one possible receipt, since $B$ is nonempty. The finite maximum is the required worst continuation depth. Proposition 3 gives the least horizon as exactly one plus the minimum such maximum. If it is finite, choose a minimizing action; each child distance is at most $D(B)-1$. Iteration reaches distance zero in at most $D(B)$ steps. The finitely many beliefs also allow explicit monotone computation of (4) until stabilization, but that computation can be exponential in the original state description. The quantifiers are $\exists a\forall o$, different from choosing one existential witness in a fully supplied verifier input. $\square$

## 2. Coupled indistinguishability and the source-specific budget result

**Proposition 5 (Shared-tape indicator bound).** Suppose two worlds have different correct targets and use one probability law for a tape independent of the world. If on a measurable event $E$ their entire available histories and resulting outputs agree, and $\Pr(E)\ge1-\varepsilon$, their success probabilities satisfy

$$
p_A+p_B\le1+\varepsilon.
\tag{6}
$$

Proof. Let $I_A,I_B$ be success indicators on this common probability space. On $E$, the same answer cannot equal two different targets, so $I_A+I_B\le1$. Off $E$ the sum is at most two. Hence $I_A+I_B\le1+\mathbf1_{E^c}$, and expectation gives (6). Independence of successive tape symbols is unnecessary. Selecting a different world after observing each tape would not establish this premise for one fixed pair. $\square$

**Proposition 6 (Application of the existing randomized Reference result).** Use exactly the world class, fixed programs, public $q_0>0$, offset interval with no denominator-height bound, full source-blind floor ports, serial protocol and world-independent tape law in [randomized Reference risk][RISK] §§1–4. If pre-first-Step completed primitive References have a uniform finite almost-sure cap and the receiver is almost surely total in each world, then

$$
\inf_W s_D(W)\le\tfrac12.
\tag{7}
$$

Under that source's no-result-sink-feedback contract, a per-world almost-surely total receiver with uniform success $s_D(W)\ge p>1/2$ instead satisfies

$$
\sup_W\mathbb E[B_D(W)]=\infty.
\tag{8}
$$

These are the existing source-specific Theorems 4.2–4.3, not consequences of marginal equality alone.

Proof. RISK Theorem 4.2 supplies, for any $\varepsilon>0$, two genuine initialized worlds with one common allowed offset, distinct original owned boundaries and a measurable event of mass at least $1-\varepsilon$ on which the entire predecision histories agree. If Step occurs, its events and all later observations also agree. The worlds are chosen before tape revelation, using finitely many actual carriers. Proposition 5 then gives the sum bound, and hence a world with success at most $(1+\varepsilon)/2$. Taking the infimum and then $\varepsilon\downarrow0$ gives (7), without asserting an attained minimizing world or a bound for every fixed offset.

For (8), suppose a uniform finite expectation bound $C$ exists. Choose a completed-reference cap $M$ with $C/M<p-1/2$. Emulate the receiver, but upon the $M$-th pre-Step completed Reference frame terminate the emulation and give a fixed boundary answer before making a further request. Serial completion makes this a legal stop, and the no-result-feedback hypothesis allows the emulation of any tentative result writes. Markov's inequality bounds the probability of truncating the original receiver by $C/M$, so the capped receiver remains uniformly successful with probability at least $p-C/M>1/2$. It is per-world almost surely total and has a uniform finite cap, contradicting (7). This is the stopping argument of RISK §10. The crucial fixed-pair initialized construction remains supplied by that source, not by this elementary reduction.

The positive exact-unlocking construction uses a height-bounded paid calibration input and a known original boundary after first acquisition; the hypotheses of (7) deliberately omit those resources. Both results preserve the original label while current executions can merge. Neither implies arbitrary-source nonrecoverability with additional advice or a whole-system cost theorem. $\square$

[RISK]: ../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_REFERENCE_RISK.md

## 追加锚（本行以下为增补区）

## 3. Finite query menus and weighted randomized certificates

**Definition 4 (Finite query menu).** Let $\mathcal X$ be a finite nonempty input set, let $J$ be a finite set of query coordinates, let $W_r(x)$ be the complete reply at coordinate $r\in J$, and let $F:\mathcal X\to\Theta$ be the target. For $x,y\in\mathcal X$ put

$$
D(x,y)=\{r\in J:W_r(x)\ne W_r(y)\}.
\tag{8}
$$

Require the complete menu to jointly determine $F$: for all $x,y\in\mathcal X$, equality $W_r(x)=W_r(y)$ for every $r\in J$ implies $F(x)=F(y)$. For a fixed $x$, write $\mathcal Y_x=\{y:F(y)\ne F(x)\}$. Thus $D(x,y)\ne\varnothing$ for every $y\in\mathcal Y_x$. A queried set $S\subseteq J$ certifies $F(x)$ exactly when

$$
S\cap D(x,y)\ne\varnothing
\qquad\text{for every }y\in\mathcal Y_x.
\tag{9}
$$

Fix finite nonnegative coordinate prices $c_r$. Define the fractional certificate price

$$
\tau_c^*(x)=
\min\left\{
\sum_{r\in J}c_rz_r:
z_r\ge0,
\sum_{r\in D(x,y)}z_r\ge1
\text{ for every }y\in\mathcal Y_x
\right\}.
\tag{10}
$$

The minimum is finite and attained: the all-ones vector is feasible, and replacing each coordinate of any feasible vector by $\min(z_r,1)$ preserves feasibility and cannot increase its nonnegative price. The feasible set intersected with $[0,1]^J$ is nonempty and compact, so the continuous objective attains its minimum there. If $\mathcal Y_x=\varnothing$, the zero vector is feasible and $\tau_c^*(x)=0$.

**Proposition 7 (Certificate criterion).** Equation (9) is necessary and sufficient for exact certification on $x$.

Proof. If (9) fails, choose $y\in\mathcal Y_x$ with $S\cap D(x,y)=\varnothing$. The two inputs have different targets and identical replies at every queried coordinate, so a decoder receiving only those replies cannot be correct on both. Conversely, if (9) holds, every target-different candidate is excluded by at least one read coordinate; the common target among the remaining candidates is $F(x)$. The required joint determinacy in Definition 4 makes every difference set in (10) nonempty; its compact restriction described there proves finite attainment. Zero-price coordinates and the no-opposite-target case cause no exception. $\square$

**Theorem 8 (Weighted per-input randomized lower bound).** Use the finite menu of Definition 4, including the requirement that its complete replies jointly determine $F$, and finite nonnegative prices. Let a randomized adaptive algorithm use a seed independent of the unknown input. Assume it stops almost surely on every $x\in\mathcal X$ and has error probability at most $0\le\epsilon\le1/2$ on every input. Repeated and irrelevant queries are allowed and are charged at their coordinate prices. If $C_c(x)$ is its total price, then

$$
\boxed{
\mathbb E C_c(x)\ge(1-2\epsilon)\tau_c^*(x).
}
\tag{11}
$$

Proof. Fix $y\in\mathcal Y_x$ and couple the two executions with one seed. Let $H_{x,y}$ be the event that the run on $x$ queries at least one coordinate in $D(x,y)$. On the event $H_{x,y}^c$ where the run on $x$ is finite, induction over its complete adaptive transcript gives identical replies, subsequent queries, stopping point and output in the run on $y$: every queried coordinate has the same reply. Since $F(x)\ne F(y)$, at least one of the two finite runs is wrong. Almost-sure termination therefore gives

$$
\Pr(H_{x,y})\ge1-2\epsilon.
\tag{12}
$$

Let $p_r(x)$ be the probability that the run on $x$ queries $r$ at least once. The union bound and (12) give

$$
\sum_{r\in D(x,y)}p_r(x)\ge1-2\epsilon
\qquad(y\in\mathcal Y_x).
\tag{13}
$$

For $\epsilon<1/2$, set $z_r=p_r(x)/(1-2\epsilon)$. These $z_r$ satisfy every constraint in (10), so

$$
\sum_rc_rp_r(x)\ge(1-2\epsilon)\tau_c^*(x).
\tag{14}
$$

The actual number of reads dominates its at-least-once indicator, hence

$$
\mathbb E C_c(x)
\ge\sum_rc_rp_r(x),
$$

which proves (11). If $\epsilon=1/2$, the finite value $\tau_c^*(x)$ makes the right-hand side zero, and nonnegativity of the price proves the same statement. If $\mathcal Y_x$ is empty, only the right-hand side is forced to be zero by Definition 4; unnecessary paid reads may still give positive actual cost, and nonnegativity again proves (11). The proof uses one fixed pair $(x,y)$ at a time and does not assume independent query outcomes or a distribution on inputs. $\square$

**Convention 9 (What the primary methods supply).** Tal, *Properties and Applications of Boolean Function Composition*, ECCC Report TR12-163, §5.1 and Definition 5.3, supplies the fractional certificate/fractionally disjoint-block linear constraints in its Boolean-function setting. Ben-David and Kothari, *Randomized query complexity of sabotaged and composed functions*, arXiv:1605.09071v2, Lemma 8, supplies the disagreement-hit probability $1-2\epsilon$ used in the same-seed argument; Corollary 20 and Theorem 21 give the related direct-sum and composition results. The weighted per-input statement (11) is the finite-menu priced extension proved above; it is not attributed verbatim to either source. LaValle, *Planning Algorithms*, Chapter 11, supplies the information-state and recursive contingent-planning setting used by Definitions 1–3. $\square$

## 追加锚（本行以下为增补区）

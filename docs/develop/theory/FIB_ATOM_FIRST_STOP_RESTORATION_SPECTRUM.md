# FIB atom first-stop acquisition and restoration spectrum

**定义 78.0（Relation to the first-stop whitebox source）。** The source model is a continuation of the [finite state-changing read/restoration interface, Chapter 77](FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md#77-有限状态变动接口的全历史读恢复前沿). Numbers 78.1–78.18 below belong to this volume; references to Chapters 73–77 belong to that parent volume. The fixed transition table, original roots, first-stop reports and SAMEoriginal action are specified below, and no representation quotient alone supplies that action. Intermediate results 78.3–78.4 use finite response congruence and refinement as in Berstel, Boasson, Carton and Fagnot, [Minimization of automata](https://arxiv.org/abs/1010.5318); their role is the bounded probe construction within the restoration theorem, rather than a separate minimization objective.

## 78. First-stop identification, paid selectors and the restoration spectrum

The acquisition target is a once-chosen original identity. A recursive five-class description, a machine's future-response quotient, and a controller's partition of possible originals concern different objects. Their correspondence requires a specified transition table and observation interface. This chapter fixes that interface, proves an exact acquisition criterion, and gives a complete paid binary family whose original-indexed frontier is explicit. A response representation and permission to restore an unknown original are separate resources.

**定义 78.1（Finite first-stop contract）。** Let $A,Q$ be finite nonempty sets, let $T$ be a finite set of distinct terminal colours disjoint from $Q$, and let

$$
n=|A|,\qquad N=|Q|,\qquad
\delta:Q\times\{0,1\}\longrightarrow Q\sqcup T,\qquad j:A\longrightarrow Q.
$$

The stationary deterministic table and $j$ are known. One $a\in A$ is chosen once; the initial state is $j(a)$ and its only initial report is active. Injectivity of $j$ is not assumed.

From an active state a chosen bit executes one transition and costs one paid read. The report is active, or the first terminal colour together with the number of bits executed in this run. A terminal transition costs one read and stops the run immediately. No further bit is legal until restoration. From either active or stopped, SAMEoriginal restoration returns this same $a$ to $j(a)$, costs one restore, and gives no identifying output. It neither resamples $a$ nor reveals it. Restoration is unrestricted unless a budget is stated.

A deterministic controller has original-independent initial data, sees only its actual action/report history and the known table, and chooses a legal bit, restoration, or return. Its computation is uncharged and adds no information. An exact policy must return the actual original after finitely many actions for every $a$, including originals with zero weight or zero prior probability. Partial-run restorations, repeated tests, nonseparating bits, extra restorations, and actions after identity becomes inferable are admitted. Word ends and pauses add no sensor: without restoration, subsequent bits continue the current state. There is no external deadline, prehistory access, hidden clock or state sensor.

For a finite binary word $w$, define $R(q,w)=\mathsf{act}$ if its entire word is executed without reaching a terminal; otherwise $R(q,w)=(t,d)$, where $t$ is the first terminal colour and $d$ its executed-bit position. In particular $R(q,\varepsilon)=\mathsf{act}$. Unexecuted suffixes are neither read nor billed. An active word end is a censored finite report, not evidence of infinite nontermination. Write

$$
q\sim q'\quad\Longleftrightarrow\quad
R(q,w)=R(q',w)\text{ for every finite binary word }w.
$$

For an exact policy $P$, write $c_P(a),r_P(a)$ for its actual read and restore counts. All cost comparisons below retain the $2n$ original coordinates.

**命题 78.2（Originals and current response states）。** At a feasible history $h$, retain the set $B_h\subseteq A$ of originals producing that history and each survivor's current active state or stopped location $x_h(a)$. A bit applies $\delta$ and removes only originals whose actual report disagrees. Restoration replaces $x_h(a)$ by its own $j(a)$ and leaves $B_h$ unchanged. A correct return is possible only when $B_h$ is a singleton.

Proof. Induct on the actual actions. The initial set is $A$ and the initial counterfactual state is $j(a)$. Determinism gives precisely the stated filtering and successor update; restoration gives no new report and preserves the original. Two surviving originals share the entire controller history and its next decision, so one returned label cannot be correct for both. At a singleton, immediate return is correct. Thus currently coalesced successors do not authorize deleting or reweighting originals. Their distinct roots may again have different responses after restoration. The fixed relation $\sim$ belongs to the table and observer; $B_h$ belongs to the information actually acquired by this controller. $\square$

**数学引文 78.3（Finite separation used in the acquisition proof）。** Let $K$ be the number of $\sim$-classes in $Q$. Every inequivalent active pair has a separating word of length at most $K-1\le N-1$. The bound $N-1$ is sharp for $N\ge2$.

Proof. For proof notation only, extend the table to $X=Q\sqcup T$ by making every terminal self-loop on both bits. Give all active states one colour and each terminal its own distinct colour. This extension grants no post-stop action. Let $E_0$ be equality of colours and recursively put

$$
xE_{k+1}y
\quad\Longleftrightarrow\quad
xE_ky\quad\text{and}\quad
\delta(x,b)E_k\delta(y,b)\text{ for both }b\in\{0,1\}.
$$

These are refining equivalence relations. Induction shows that $E_k$ means equality of the resulting colours after every word of length at most $k$: the empty word supplies the initial colour, and a word $bv$ supplies the successor condition for $b$ and $v$. Conversely agreement on all such words gives both the shorter-word condition and the two successor conditions.

For active starts, these colour conditions are equivalent to equal first-stop responses for every word of length at most $k$. The colours at all successive prefixes determine the first terminal, its first depth, or the active word end. Comparing all prefixes preserves differences of stopping depth even when terminal colours agree.

If $E_{k+1}=E_k$, successor compatibility makes every later refinement equal. Terminal classes are singletons from $E_0$ and never split; only the initial active block splits. Each strict refinement increases the number of active blocks, so there are at most $N-1$ strict stages, and more precisely at most $K-1$ before the final $K$ active blocks. An equality cannot precede a later strict stage. The stable relation consequently agrees with responses to all finite words, proving the bounds and identifying its active restriction with $\sim$.

For sharpness take $Q=\{q_0,\ldots,q_{N-1}\}$ and one terminal $t$, with

$$
\delta(q_0,0)=t,\qquad
\delta(q_i,0)=q_{i-1}\ (i>0),\qquad
\delta(q_i,1)=q_i\ (0\le i<N).
$$

Every word of length at most $N-2$ leaves both $q_{N-2}$ and $q_{N-1}$ active. The word $0^{N-1}$ stops the former on its last bit and leaves the latter active. Both transitions exist at every state. When $N=1$ there is no inequivalent active pair. $\square$

**数学引文 78.4（Future-response representation used in acquisition）。** The stable quotient is a stationary deterministic response machine with exactly $K$ active states, and $K$ is the minimum under the convention that reached terminal colours remain distinct outputs. For the family of original roots, first restrict to active states reachable from $j(A)$ before stop and use the number $K_A$ of classes in that restriction.

Proof. The stable successor condition makes the transition on classes well defined. Induction along a word, stopping at its first terminal, preserves all active reports, terminal colour and executed depth. A finite stop in only one of two corresponding executions on an infinite input would contradict this finite-prefix induction; infinite nonstopping is preserved as well. Distinct quotient classes have a finite separating word by 78.3. A stationary deterministic representation using only its represented current state and the next bit cannot assign both classes the same represented state, since that assignment would force identical futures. Hence at least $K$ active represented states are required and the quotient attains the bound. The reachable restriction is transition-closed up to terminals, so the same argument applies to it.

This is a count of response states under a specified interface. It constructs no executable unknown-original checkpoint, counts no storage bits, and supplies no neural realization. In particular, a representation of a coalesced successor alone need not determine the original-dependent restoration target. $\square$

**定理 78.5（Exact acquisition criterion and a bounded representative）。** Under 78.1, an exact deterministic policy exists if and only if

$$
a\ne b\quad\Longrightarrow\quad j(a)\not\sim j(b).
$$

For $n=1$ immediate return uses zero reads and restores. For $n\ge2$ satisfying the condition there is one policy valid for every original using at most $n-1$ probes, $n-2$ restores and $(n-1)(N-1)$ paid reads. The read bound can be sharpened to $(n-1)(K_A-1)$.

Proof. If two roots are equivalent, couple both executions using the same deterministic controller history. At every common history the next action agrees. Successor compatibility gives the same immediate bit report and equivalent active successors. The chosen-bit counts agree, so terminal-depth reports agree. A restoration produces equivalent roots again and no identifying report. Induction preserves identical histories through all partial-run restorations and terminal/restart episodes. Any finite return is the same label on both originals and cannot be correct for both; failure to return also violates exactness.

For sufficiency partition $A$ initially into one block. With a chosen finite word family $W$, group originals by their vectors $(R(j(a),w))_{w\in W}$. If a block is nonsingleton, choose two of its members and add a separating word supplied by 78.3. This strictly splits at least one block and never merges blocks. After at most $n-1$ additions all blocks are singletons. Each word is nonempty and has length at most $N-1$, or $K_A-1$ on the reachable quotient.

Execute the first word from the supplied initial root and each later word after one SAMEoriginal restoration, stopping each run at its first terminal. The reports form the signature of that one chosen original, not reports from separately sampled originals. Its signature is injective, so decoding returns the actual $a$. A family of $k\le n-1$ words costs at most $k-1$ restores and $k(N-1)$ reads. Early singleton return can reduce these costs.

This is a sufficient representative bound, not a bound on every padded policy, a minimum read law for every machine, or a claim that it preserves each policy's own tradeoff. The criterion implies $n\le K_A\le N$. For $n=2$ one word and no restoration suffice. If $T$ is empty all reports stay active and exact acquisition is possible only for $n=1$. Duplicate $j$ values and distinct but response-equivalent roots both fail the criterion. $\square$

**定义 78.6（Complete paid onto selector）。** For $n\ge2$, list $A=\{a_1,\ldots,a_n\}$ and let $L=\lceil\log_2 n\rceil$. Choose a surjection $\sigma:\{0,1\}^L\to A$. For example, if $\operatorname{rank}(w)$ is its zero-based binary rank, take $\sigma(w)=a_{\min(\operatorname{rank}(w)+1,n)}$. Define

$$
Q_\sigma=\{(a,u):a\in A,\ u\text{ binary},\ |u|<L\},
\qquad j(a)=(a,\varepsilon),\qquad T=\{\mathsf{hit},\mathsf{miss}\},
$$

with distinct terminal colours, and for every active state and both bits define

$$
\delta((a,u),b)=
\begin{cases}
(a,ub),&|u|+1<L,\\
\mathsf{hit},&|u|+1=L\text{ and }\sigma(ub)=a,\\
\mathsf{miss},&|u|+1=L\text{ and }\sigma(ub)\ne a.
\end{cases}
$$

These exhaustive cases give a finite complete stationary deterministic table with $n(2^L-1)$ raw active states. No report reveals $a,u$ or a selector label. From a root the first $L-1$ reports are active, and the $L$th bit stops with hit exactly on the named original. All $L$ bits, including known selection bits and the terminal bit, are paid. A shorter prefix conveys no original information; restoration discards it. A declared word end without restoration does not start a new experiment.

Surjectivity separates every two roots by a word naming one of them. Every proper prefix state and both terminal colours are reachable from the family roots. Thus the family is response-identifiable and its singleton-membership tests are actual bit executions.

**命题 78.7（Common permutation attainers）。** For a permutation $\pi=(x_1,\ldots,x_n)$ of the originals put $t_i=\min(i,n-1)$. There is an exact policy in this same machine with

$$
c_\pi(x_i)=Lt_i,\qquad r_\pi(x_i)=t_i-1.
$$

Proof. Fix a length-$L$ preimage under $\sigma$ for each original. Test $x_1,x_2,\ldots$ in order. Return on a hit; after a miss return the sole remaining original if one remains, otherwise restore once and run the next complete test. An original in position $i<n$ has $i-1$ misses followed by its hit. The final original is inferred from $n-1$ misses without another query or restoration. Hence the displayed counts follow from the actual transitions, simultaneously for all originals. For $n=2$, $L=1$ and both cost pairs are $(L,0)$. $\square$

**定理 78.8（One simultaneous all-policy domination witness）。** Every deterministic exact full-history selector policy $P$ is componentwise above one vector from 78.7:

$$
\exists\pi\ \forall a\in A,\qquad
c_\pi(a)\le c_P(a),\quad r_\pi(a)\le r_P(a).
$$

Proof. Follow the chronological branch reporting miss after every completed selector run, only until its survivor set first becomes a singleton. Let $D$ be the distinct labels named by completed runs and $C=A\setminus D$. Every member of $C$ realizes that whole history: all completed tests miss, all partial prefixes report active, and restorations return that same member to its own root. This invariant includes discarded prefixes, repeated eliminated-label tests and extra restorations. If $|C|\ge2$, exactness forbids return.

This branch must reach a singleton after finitely many actions. Otherwise at most $n-2$ distinct originals are ever eliminated. The finite decreasing survivor sets have an eventual intersection of size at least two, every member of which realizes the entire infinite history. Finite exact return for such a member contradicts the impossibility of returning while at least two survive. This also excludes infinite useless tests or restorations. No impossible all-miss history after elimination of every original is used.

Order the first newly eliminated labels as $x_1,\ldots,x_{n-1}$ and let $x_n$ be the remaining original at the first singleton time. For $x_i$, $i<n$, its actual history agrees with the miss branch until the first completed test naming it, which reports hit on its own execution. Before that moment at least two originals were compatible, so $P$ could not already have returned. At least $i$ complete runs have then executed, costing $Li$ bits and at least $i-1$ restorations between terminal stops. Partial discarded runs, repetitions and extra restorations add nonnegative cost. Later actions cannot reduce either count.

For $x_n$, the miss spine through its first singleton is an actual prefix of its execution. It includes at least $n-1$ complete runs and $n-2$ restorations, with no earlier legal return. These bounds are precisely one permutation vector, and 78.7 realizes the entire vector in the fixed machine. The argument never replaces original coordinates by successors and retains zero-weight originals. $\square$

**定理 78.9（Exact deterministic frontier and upward closure）。** In the selector of 78.6, let $\mathcal D$ be the set of actual deterministic exact cost vectors and

$$
F_\sigma=\{(c_\pi,r_\pi):\pi\text{ a permutation of }A\},
$$

discarding duplicate vectors. Then $F_\sigma$ is exactly the Pareto-minimal subset of $\mathcal D$, and $|F_\sigma|=n!/2$.

Proof. Attainment and 78.8 give

$$
F_\sigma\subseteq\mathcal D\subseteq\uparrow F_\sigma,\qquad
\uparrow\mathcal D=\uparrow F_\sigma.
$$

Here $\uparrow S=\{z\in\mathbb R_{\ge0}^{2n}:\exists s\in S,\ s\le z\}$ is the upper closure in the nonnegative real coordinate space. The raw set $\mathcal D$ consists of actual integer count vectors; upper closure grants no policy realizing each larger vector. Prepending arbitrarily many restorations already gives infinitely many feasible padded vectors, whereas $F_\sigma$ is finite.

Every permutation has the same sums

$$
\sum_a c_\pi(a)=\frac{L(n-1)(n+2)}2,\qquad
\sum_a r_\pi(a)=\frac{(n-2)(n+1)}2.
$$

If one permutation vector is below another, equality of these sums forces equality of every coordinate. Thus distinct members are incomparable. A feasible vector strictly below an $F_\sigma$ member would, by 78.8, place another $F_\sigma$ member strictly below it, a contradiction. A feasible vector outside $F_\sigma$ has a distinct member below it and is not minimal. Costs distinguish positions $1,\ldots,n-2$, while the final two positions have the same pair. Exactly the exchange of those last two leaves a permutation vector unchanged; hence there are $n!/2$ distinct vectors, including one for $n=2$. This finite frontier does not make the set of all padded policies finite. $\square$

**推论 78.10（Sharp selector budgets and uniform laws）。** In the selector, every deterministic exact policy satisfies

$$
\max_a c_P(a)\ge L(n-1),\qquad
\max_a r_P(a)\ge n-2.
$$

Both lower bounds are attained by every permutation policy. A common restore budget $R<n-2$ is infeasible; for every integer $R\ge n-2$ the minimum worst read count is $L(n-1)$. Under the uniform law on all $n$ originals, the simultaneous minimum expected counts are

$$
\min_P\mathbb E[c_P]=\frac{L(n-1)(n+2)}{2n},\qquad
\min_P\mathbb E[r_P]=\frac{(n-2)(n+1)}{2n}.
$$

Proof. Domination in 78.8 supplies the maximum bounds. Dividing the two sums in 78.9 by $n$ supplies both expectation bounds. Every permutation policy attains both together. These equalities describe frontier optima, not every policy's costs. More restorations cannot improve a vector below this frontier. For $n=1$, immediate return instead gives $(0,0)$; the displayed $n\ge2$ restore formula is not used there. Combined with 78.5, this proves that $n-2$ is the sharp universal deterministic worst-restoration guarantee. $\square$

**定理 78.11（All nonnegative original weights）。** In the selector of 78.6, with $n\ge2$, for arbitrary $u_a,v_a\ge0$, let $s_a=Lu_a+v_a$ and arrange the scores as $s_{[1]}\ge\cdots\ge s_{[n]}$. Then

$$
\min_P\sum_a\bigl(u_ac_P(a)+v_ar_P(a)\bigr)
=\sum_{i=1}^n s_{[i]}\min(i,n-1)-\sum_a v_a.
$$

A descending-score permutation policy attains the value.

Proof. Nonnegative weights and 78.8 reduce the minimum to the attained finite frontier. On a permutation its value is $\sum_i s_{x_i}t_i-\sum_a v_a$. For $i<j$, exchanging the originals changes the nonconstant term by

$$
(s_{x_j}-s_{x_i})(t_i-t_j).
$$

Moving a larger score to a smaller $t$ never increases the objective and decreases it when both inequalities are strict. Removing inversions yields the formula. A frontier permutation is optimal exactly when it has no score inversion across distinct $t$ values. Tied scores and the equal final two positions allow either order. A dominated policy can also minimize if all its excess costs have zero corresponding weights; it cannot lower the value. Correctness still quantifies over every original.

For a prior $p_a$ and restore price $\lambda\ge0$, take $u_a=p_a,v_a=\lambda p_a$ and order by $p_a$. Since $\sum_a p_a=1$, the same formula is $(L+\lambda)\sum_i p_{[i]}t_i-\lambda$, attained by that one permutation for these parameters. This specialization does not erase originals outside the prior's support. $\square$

**定理 78.12（Entire deterministic restoration spectrum）。** For a response-identifiable machine define

$$
\rho=\min_{P\text{ exact}}\max_{a\in A}r_P(a).
$$

For $n=1$, $\rho=0$. Across the general machines of 78.1 with fixed $n\ge2$ the attainable values are exactly $\{0,1,\ldots,n-2\}$.

Proof. The representative in 78.5 gives a finite integer upper value, so the nonempty set of integer worst counts has a minimum and lies in this interval. Fix $r$ in it, put $m=r+2$, and choose $B\subseteq A$ of size $m$. On $B$ use the complete selector with length $L_m=\lceil\log_2m\rceil$ and onto map to $B$. For every outside original add a state $o_a$ whose two transitions both go to its own distinct terminal colour $t_a$, different from hit and miss, and set $j(a)=o_a$.

Begin the selector permutation policy on $B$. An outside original is identified by its first bit and uses no restoration. An inside original has exactly the selector history: when $L_m>1$ the first active report excludes the outside originals; when $L_m=1$ hit or miss excludes them. Thus the same policy acquires all originals and has worst restore count $m-2=r$. Conversely restrict any exact full policy to the actual inside originals. It remains a legal exact selector policy, so 78.8 forces a worst restore count of at least $m-2$. Hence $\rho=r$. The largest value needs only hit and miss; the intermediate constructions use the extra distinct colours permitted by the general model. No two-colour restriction is imposed on the entire spectrum statement. $\square$

**命题 78.13（Exact selector response representation）。** For $|u|=d<L$, define

$$
H_{a,u}=\{v\in\{0,1\}^{L-d}:\sigma(uv)=a\}.
$$

The minimum active response-state count of the selector is

$$
K_\sigma=\sum_{d=0}^{L-1}
\left|\{H_{a,u}:a\in A,\ |u|=d\}\right|\ge n.
$$

Proof. At the same depth, words shorter than $L-d$ report active; a word of that length reports hit exactly on $H_{a,u}$; longer words truncate at the same stop. Thus two such states are equivalent precisely when their $H$ sets agree. Different depths are inequivalent: a word just long enough to stop the state with shorter remaining depth leaves the other active. These are exactly all equivalence classes, and 78.4 attains the count. At depth zero the $n$ nonempty disjoint preimages of the onto map are distinct. All states are reachable, so there is no unreachable-state subtraction. The acquisition formulas depend only on $n,L$ for every surjection, while the residual-predicate count can depend on $\sigma$. $\square$

**命题 78.14（Equal representation size with different acquisition cost）。** For $n\ge3$, a selector and another machine can have the same $n$, the same minimum active response-state count $K_\sigma$, binary inputs and two terminal colours, yet respectively have $\rho=n-2$ and $\rho=0$.

Proof. Put $K=K_\sigma\ge n$. Construct a chain $q_0,\ldots,q_{K-1}$ in which both bits from $q_i$, $i>0$, go to $q_{i-1}$, while bit zero from $q_0$ gives hit and bit one gives miss. Choose $n$ distinct original roots, including $q_{K-1}$. Their first-stop delays are distinct, and the uninterrupted word $0^K$ identifies each original without restoration. All $K$ active states are reachable; their distinct delays separate every pair, so the representation minimum is $K$. The selector has $\rho=n-2$ by 78.10. Thus a response-state count does not determine restoration complexity. This compares minimum representation counts, not equal raw-state counts, and constructs no mechanism for implementing restoration. $\square$

**定义 78.15（Original-independent measurable random resource）。** In addition to 78.1, a randomized controller may use a seed $\omega$ on a declared probability space $(\Omega,\mathscr F,\mathbb P)$, with the same law for every original. For each finite legal action/report history, its next action as a function of $\omega$ is measurable; actual costs are measurable nonnegative extended random variables. The controller must return finitely and correctly with probability one separately for every $a\in A$. Fixing a seed fixes all history-dependent choices. The seed and controller initialization provide no original-dependent information, and every zero-prior original remains in correctness.

A further, explicit resource property is needed for unrestricted convex-hull attainment: for every finite probability vector $(p_1,\ldots,p_m)$, the declared random resource supports an original-independent pre-action choice with precisely these probabilities. Equivalently, it supplies an appropriate measurable finite lottery. A probability space by itself need not have this property; a one-point seed space permits only deterministic choices. No lottery channel is supplied by the transition table or response quotient. The two charged resources remain executed bits and restorations.

**定理 78.16（Random expected frontier and lottery qualification）。** Under the measurable seed and all-original correctness conditions of 78.15, every randomized expected cost vector is componentwise above some member of $\operatorname{conv}(F_\sigma)$. If the declared resource also supports the finite lotteries in 78.15, this convex hull is exactly the expected original-coordinate Pareto frontier. Weighted linear minima and optimal uniform-prior means remain those of 78.10–78.11 even without arbitrary lottery access, since their deterministic attainers remain available. Weighted expected cost means $\mathbb E[\sum_a(u_ac_P(a)+v_ar_P(a))]$ for nonnegative finite weights, with zero-coefficient terms contributing zero; this nonnegative integral is defined even when some unweighted expectations are infinite. A single deterministic frontier vector need not dominate a randomized expected vector.

Proof. For each original its good-seed set has probability one. Their finite intersection also has probability one. Fixing any seed in that intersection gives a deterministic controller exact for all originals, so 78.8 applies on that seed with one simultaneous permutation witness.

The common good-seed set is measurable: for each original, finite correct return is a countable union of measurable finite-history events. The finite-valued domination witness is measurable too. Prescribed finite action/report prefixes give finite intersections of measurable action events. Actions and return labels range over finite sets, and terminal depths over integers, so finite histories form a countable set. An extracted ordering is determined at a finite first-singleton time; its event is a countable union of these prefix events. Use a fixed convention for the equal last pair and assign any fixed frontier member on the null complement of the common good set. There are finitely many witnesses. Their expected vector $f$ belongs to $\operatorname{conv}(F_\sigma)$ and satisfies $f\le\mathbb E[z_P]$ componentwise. This inequality holds also when a cost expectation is infinite.

Conversely, choose a frontier permutation before acting with the probabilities of any given finite convex combination. Original-independent finite-lottery access makes its expected vector that combination. Every hull vector has the same total read sum and total restore sum from 78.9, so distinct hull vectors cannot dominate each other. If a random feasible expected vector strictly dominated a hull vector, its measurable witness expectation would be a hull vector below it, contradicting the fixed sums. Every feasible finite expected vector outside the hull is dominated by its witness expectation. Vectors with an infinite coordinate are also dominated by a finite hull vector. This proves the expected frontier.

Writing $\mathcal E$ for the raw set of finite expected feasible vectors, the precise relationship is

$$
\operatorname{conv}(F_\sigma)\subseteq\mathcal E
\subseteq\uparrow\operatorname{conv}(F_\sigma),\qquad
\uparrow\mathcal E=\uparrow\operatorname{conv}(F_\sigma).
$$

These inclusions and equality of upper closures use the finite-lottery hypothesis for the first inclusion. They do not identify the raw expected feasible set $\mathcal E$ with its upper closure. Without that hypothesis, the measurable-witness domination $\mathcal E\subseteq\uparrow\operatorname{conv}(F_\sigma)$ still holds, but arbitrary hull attainment and exact hull-frontier equality have not been established.

For $n=3$, when the declared random resource supports the corresponding uniform finite lottery, mixing all permutations uniformly gives every original expected costs $(5L/3,2/3)$, with $L=2$. Each deterministic frontier assigns two originals $(2L,1)$, so no deterministic frontier vector is below that expected vector. Finally, a convex combination cannot reduce a linear objective below its smallest deterministic value. The weighted formula and uniform means therefore remain exact. The necessity part of 78.5 also extends seedwise: equivalent roots cannot be exactly returned on a common probability-one set of seeds. $\square$

**命题 78.17（Actual budgets versus maximum expected cost）。** In the additional random model, $n-2$ remains the sharp selector lower bound for the almost-sure pathwise worst restore count over originals and for a uniform actual or essential-supremum restore budget. It is not a lower bound on $\max_a\mathbb E[r_P(a)]$.

Proof. On every common good seed, 78.8 gives $\max_a r_P(a)\ge n-2$, and also $\max_a c_P(a)\ge L(n-1)$. The finite union of events $\{r_P(a)\ge n-2\}$ has probability one. At least one such event has positive probability, so at least one original has essential-supremum restore count at least $n-2$. The deterministic permutation policies attain the actual bounds. With its explicit lottery resource, the three-original mixture in 78.16 has $\max_a\mathbb E[r_P(a)]=2/3<1=n-2$. Taking a maximum after expectation changes the quantity. The deterministic spectrum in 78.12 is not a spectrum of this different expected-budget problem. $\square$

**假设 78.18（Correspondence conditions for applications）。** The `literature-attested` background methods are future-response congruence, Moore refinement, characterizing word families and ordered singleton search. Relevant background includes Berstel, Boasson, Carton and Fagnot, [Minimization of automata](https://arxiv.org/abs/1010.5318), and Frohme, [Active Automata Learning with Adaptive Distinguishing Sequences](https://arxiv.org/abs/1902.01139). The `repo-derived` onto-selector cost laws here are derived in full from the displayed transition and action contract. The first-stop, restoration and paid-bit conditions below are additional to those background methods.

Chapter 77 supplies a finite, attainable original-indexed frontier for a fixed restoration budget and the first-stop dynamic interface. Its general frontier existence and weight interpretation retain their original scope. Chapter 73 uses labels $C_0,\ldots,C_{49}$, while chapters 74–77 use $C_1,\ldots,C_{50}$ with their own tables. These indexing conventions are preserved; no relabeling or table splice identifies them with the selector. The selector's full-history lower argument gives its own explicit frontier for every restoration budget that permits acquisition. General response minimization supplies neither SAMEoriginal restoration nor measured reports.

The static-tree acquisition and joint-response cost interfaces use an unchanged tree, actual address reports, a complete leaf certificate and their specified fallback. Their restoration reconstructs a static source description; their cached cost counts distinct queried addresses. The selector charges every bit occurrence on an evolving state, and its restoration is the declared same-original action. Literal-image separation, genealogical fibre transport, and single-hole recovery from a supplied compatible history retain their original static objects and do not supply this dynamic access.

The current incoming-lift response recursion requires a common projection and all actual numbered incoming lifts. Its local path decomposition is not an acquisition-time or restoration theorem. The narrow-window acquisition interface uses complete issued words, an endpoint observer, fixed initial phase labels and its stated admissibility and monochromatic-window hypotheses. Its block cost cannot replace the paid first-stop bit count used here. A common terminology of response, recovery, phase or recursion is insufficient for these transfers.

The Mother volume's observation, path-probability and control interfaces require their own joint source, observation, action and environment data. They do not specify the finite table or same-original action in 78.1. SourceCompletion chapter 78 keeps complete typed vertices, incoming guards, entire original pieces and all original edges; its closed-walk conclusions do not furnish a selector readout. Scale chapter 46 follows one selected strict history with all four tree reports and one inherited resource; chapter 47 uses literal disjoint comb holes, complete leaf certificates and distinct-address cache costs. Neither replaces paid first-stop bit occurrences or supplies restoration. Their joint-realization and operation boundaries remain intact.

For a recursive five-class whitebox task, applying this chapter requires specifying $A,Q,T,\delta,j$, demonstrating the stated reports and action permissions, and proving that the task's original labels match $A$. The intermediate results 78.3–78.4 concern future-response representation; 78.5–78.17 concern acquisition using the declared restoration resource. The cost vectors count only executed bit occurrences and SAMEoriginal restorations. Applying them to an external realization requires a faithful object, action, observation and cost correspondence; physical, neural, training, generalization, runtime, storage and energy claims require additional premises.

## 追加锚（本行以下为增补区）

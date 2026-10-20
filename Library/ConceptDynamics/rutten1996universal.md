---
bibkey: rutten1996universal
authors: J. J. M. M. Rutten
year: 1996
title: 'Universal coalgebra: a theory of systems'
doi: null
url: https://ir.cwi.nl/pub/4802/4802D.pdf
claim: System homomorphisms, bisimulation quotients and final behaviour provide the classical basis for exact recursively updateable observation interfaces.
strata_touched: []
license: citation-only
triage: anchor
---

# Systems, residual observations and finite proof growth

**Definition 1 (Source scope).** The institutional report at https://ir.cwi.nl/pub/4802/4802D.pdf, Sections 2–3 and 5–9, supplies systems, homomorphisms, bisimulation, quotients and final behaviour. The deterministic calculations below are elementary specializations and supporting exposition, not new coalgebra theorems. Probability-state attribution is to the existing [Shalizi–Crutchfield note][SHALIZI], under the support conditions stated below. The finite lattice, reachability and finitary closure calculations are proved here as elementary supporting mathematics; no assertion that the cited report contains these particular formulations is made. Related repository suppliers are [computational behaviour][BEHAVIOUR] §§2–4, [process geometry][PROCESS], [static compatibility][STATIC], [internal predictive interfaces][INTERFACE], [predictive memory][MEMORY], [predictive-state updating][UPDATE] and [causal-state factorization][FACTOR]. Their ordinary applications here carry no assertion about a current Lean compilation.

## 1. Task worlds and exact recursive addresses

**Definition 2 (Task world and completion semantics).** A task world is $(S,A,\delta,\lambda,T,G)$, where $A$ is finite, nonempty and linearly ordered, $\delta:S\times A\rightharpoonup S$, $\lambda:S\to Y$, $G\subseteq T\subseteq S$, and terminal states have no legal successors. Write

$$
A(s)=\{a:\delta(s,a)\text{ is defined}\},\qquad
\ell(s)=(\lambda(s),\mathbf1_T(s),\mathbf1_G(s)).
$$

Words are read in chronological order:

$$
\delta^*(s,\varepsilon)=s,\qquad
\delta^*(s,aw)=\delta^*(\delta(s,a),w),
$$

when every transition exists. Completion semantics for a designated proposition domain $\mathcal T$ assigns each $g$ an initial $s_g$ and success set $G_g$, and assumes

$$
g\text{ is true}\quad\Longleftrightarrow\quad
\exists w\in A^*: \delta^*(s_g,w)\in G_g.
\tag{1}
$$

Paths in (1) are finite. The complete graph and its paths are mathematical objects; (1) specifies neither a finite table representation nor an effective lookup algorithm. Configurations may include the observer, retained memory, proof prefix, queries and replies; an observer readout is a function $q:S\to Z$.

**Proposition 1 (History unfolding and residual behaviour).** Every transition system unfolds into a DAG of legal finite histories. Its projection to the last state preserves transitions. If $\bot$ is a fresh illegal-execution symbol, the full future row

$$
B_s(w)=\begin{cases}\ell(\delta^*(s,w)),&w\text{ legal},\\
\bot,&w\text{ illegal}\end{cases}
$$

satisfies, for every legal $a$,

$$
B_{\delta(s,a)}(v)=B_s(av).
\tag{2}
$$

Proof. History vertices are $(s_0,a_1,s_1,\ldots,a_n,s_n)$. An edge appends one legal action and successor; history length increases, so no directed cycle exists. The projection $p(h)=s_n$ obeys $p(h\cdot a)=\delta(p(h),a)$. This includes any observer or lookup operations already in the configurations. The recursive definition of execution gives (2), including simultaneous illegality of both sides. Consequently repeated values of a compressed retained state $q(p(h))$ coexist with an acyclic growing history. $\square$

**Proposition 2 (Fibre criterion and canonical future quotient).** A readout $q:S\to q(S)$ admits an output map $e$ and partial update $U$ with

$$
\ell=e\circ q,\qquad\operatorname{dom}U(q(s),\cdot)=A(s),\qquad
q(\delta(s,a))=U(q(s),a)
\tag{3}
$$

if and only if $q(s)=q(t)$ implies

$$
\ell(s)=\ell(t),\quad A(s)=A(t),\quad
q(\delta(s,a))=q(\delta(t,a))\quad(a\in A(s)).
\tag{4}
$$

For $s\equiv t$ defined by $B_s=B_t$, the quotient $q_*:S\to S/{\equiv}$ satisfies (3). Every readout satisfying (3) has a unique surjection

$$
\gamma:q(S)\longrightarrow S/{\equiv},\qquad q_*=\gamma\circ q.
\tag{5}
$$

Thus it is the coarsest recursively stable representation preserving all these finite future behaviours, without requiring full history retention. This is the deterministic quotient principle of the cited report; compare BEHAVIOUR Theorem 2.2 and the repository factorization supplier.

Proof. Equation (3) gives each part of (4). Conversely set $e(q(s))=\ell(s)$ and $U(q(s),a)=q(\delta(s,a))$ on legal pairs. The three clauses of (4) make output, domain and successor independent of representatives. These are definitions on actual images, so no arbitrary values outside $q(S)$ enter the uniqueness assertion.

If $B_s=B_t$, the empty word gives the same current output, one-letter words give equal legal action sets, and (2) gives equivalent successors. Hence (4) holds for $q_*$. For any exact $q$, induction on word length proves that equal $q$ values have the same legal continuations and the same output after each one; therefore $B_s=B_t$. Define $\gamma(q(s))=[s]$. It is well-defined, surjective, and uniquely prescribed at every point of $q(S)$. $\square$

**Proposition 3 (Future sufficiency does not ensure self-update).** Recoverability of $B_s$ from $q(s)$ alone does not imply (3).

Proof. Take four states $s,t,r_1,r_2$ with the same output, no terminal states and one always legal action $a$, with $s\mapsto r_1$, $t\mapsto r_2$, $r_i\mapsto r_i$. All future rows agree. Put $q(s)=q(t)=0$, $q(r_1)=1$, $q(r_2)=2$. The constant row is recoverable from $q$, but $U(0,a)$ would have to be both one and two. This is the static-versus-updateable distinction already treated in BEHAVIOUR §§2–4. $\square$

**Proposition 4 (Stable refinement).** Suppose $q_0$ preserves $\ell$, set $E_0=\ker q_0$, and define $sE_{n+1}t$ by

$$
sE_nt,\qquad A(s)=A(t),\qquad
\delta(s,a)E_n\delta(t,a)\quad(a\in A(s)).
$$

Then $E_\infty=\bigcap_{n\ge0}E_n$ is the greatest stable equivalence contained in $E_0$. If $q_0=\ell$, it is $\equiv$. If $|S|=N$ and $E_0$ has $c$ classes, there are at most $N-c$ strict refinement rounds.

Proof. Each relation is an equivalence and $E_{n+1}\subseteq E_n$. Membership in every $E_{n+1}$ gives equal action sets and successor membership in every $E_n$, proving stability of the intersection. A stable equivalence $E\subseteq E_0$ lies in every $E_n$ by induction, hence in the intersection. Starting with $\ell$, the same induction says $E_n$ means agreement of future rows on words of length at most $n$; this includes definedness. Intersecting all finite lengths gives $\equiv$. In a finite set each strict refinement adds a class, never exceeding $N$. Equality at one round makes all later rounds equal. Infinite sets have the intersection result, without a finite termination assertion. $\square$

## 2. Auxiliary information and good-action selection

**Definition 3 (Sufficient auxiliary data).** Given $q:X\to Y$ and target $\psi:X\to T$, data $a:X\to A$ are sufficient when there is a decoder on $(q,a)(X)$ with $\psi(x)=d(q(x),a(x))$. Equivalently $\ker(q,a)\subseteq\ker\psi$. This is an information condition relative to both the existing readout and the target.

**Proposition 5 (Joint refinement and exact label count).** The map $r=(q,\psi)$ is the coarsest joint refinement retaining both quantities. If $b:X\to B$ determines both, there is a unique map $\gamma:b(X)\to r(X)$ with $r=\gamma\circ b$. If $X$ is finite and nonempty, set

$$
k_y=|\psi(q^{-1}(y))|,\qquad k=\max_{y\in q(X)}k_y.
$$

The least auxiliary alphabet size is $k$ and the least fixed binary width is $\lceil\log_2k\rceil$.

Proof. Equal $b$ values give equal $q$ and $\psi$, so $\gamma(b(x))=(q(x),\psi(x))$ is well-defined and forced everywhere on $b(X)$. This proves the factorization and coarseness. No uniqueness on unused points of $B$ is asserted.

In a fixed $q$ fibre, two different target values must have different auxiliary labels, since the decoder has the same first argument. Thus at least $k_y$ labels are needed there and at least $k$ globally. Enumerate the distinct target values separately in each fibre using labels $1,\ldots,k_y$; labels may be reused between fibres. The first argument of the decoder chooses the relevant enumeration, so $k$ labels suffice. There are $2^b$ binary words of fixed length $b$, giving the width formula, including zero bits when $k=1$. Computing a one-bit auxiliary $a(x)=\mathbf1_L(x)$ can already require solving $L$; this count supplies no time or acquisition bound. $\square$

**Proposition 6 (Five-atom correlation supplies a missing update).** In the existing [atomic-observation model][ATOMS], the allowed states are $000,100,010,110,001$. With $X=\mathbb E[x]$, $Y=\mathbb E[y]$, $Z=\mathbb E[z]$, $\kappa=\mathbb E[xy]$, the full probabilities are

$$
p_{110}=\kappa,\quad p_{100}=X-\kappa,\quad p_{010}=Y-\kappa,
\quad p_{001}=Z,\quad p_{000}=1-X-Y-Z+\kappa.
\tag{6}
$$

The three marginal means alone do not determine the posterior after observing $x=1$; the four displayed moments determine every prescribed posterior for a positive-probability event.

Proof. Only $110$ has $xy=1$, only $001$ has $z=1$, and splitting the two remaining means gives (6); normalization gives the last entry. These are valid probabilities precisely when each entry is nonnegative, equivalently $Z\ge0$ and $\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y)$, together with their resulting normalization. Compare $\mu_-=(\delta_{100}+\delta_{010})/2$ and $\mu_+=(\delta_{000}+\delta_{110})/2$. Both give $(X,Y,Z)=(1/2,1/2,0)$, but $\kappa=0$ and $1/2$. For $X>0$, the posterior mean is $\mathbb E[y\mid x=1]=\kappa/X$, hence zero and one respectively. The four moments give the full law by (6), so all positive-event conditionals follow. This is the existing model's correlation calculation, not an additional independent discovery. $\square$

**Proposition 7 (Common good actions and noncanonical minimal partitions).** Let $\operatorname{Good}(s)\subseteq A$. There is a selector depending only on $q(s)$ and choosing a good action for every $s$ if and only if

$$
\bigcap_{s:q(s)=z}\operatorname{Good}(s)\ne\varnothing
\quad(z\in q(S)).
\tag{7}
$$

To predict its next address also requires $q(\delta(s,a_z))$ constant throughout that fibre, and legality of each chosen action. A coarsest sufficient partition for good-action selection need not exist.

Proof. A common selector value belongs to every good set in the fibre. Conversely choose the least member of each nonempty intersection in the fixed finite action order. The update requirement is exactly single-valuedness on the selected fibres, a separate condition from choosing a good action. For nonuniqueness take good sets $\{a\},\{a,b\},\{b\}$ on three states. Both partitions $\{s_1,s_2\}\mid\{s_3\}$ and $\{s_1\}\mid\{s_2,s_3\}$ permit a choice, while any common coarsening merges all three and has empty intersection. This differs from the canonical exact-future quotient. $\square$

## 3. Probability residuals and report feedback

**Definition 4 (Recursive predictive laws).** Let $\Sigma$ be finite, $Z$ nonempty, $U:Z\times\Sigma\to Z$, and each $e_z$ a probability vector. Given consistent distributions $Q_z^{(n)}$ on $\Sigma^n$, including $Q_z^{(0)}(\varepsilon)=1$, define

$$
D_z^{(0)}(\varepsilon)=1,\qquad
D_z^{(n+1)}(aw)=e_z(a)D_{U(z,a)}^{(n)}(w).
$$

Consistency of $Q$ means $\sum_aQ_z^{(n+1)}(wa)=Q_z^{(n)}(w)$. All stated laws are on the specified query-state set, which is closed under the declared total update.

**Proposition 8 (Same-update prediction and growth).** The following are equivalent: $Q_z^{(n)}=D_z^{(n)}$ for every state and finite horizon; the residual equations

$$
Q_z^{(n+1)}(aw)=e_z(a)Q_{U(z,a)}^{(n)}(w);
\tag{8}
$$

and the conjunction of $Q_z^{(1)}(a)=e_z(a)$ with

$$
Q_{U(z,a)}^{(n)}(w)=Q_z^{(n+1)}(aw)/e_z(a)
\quad\text{whenever }e_z(a)>0.
\tag{9}
$$

Proof. The generated laws obey (8) by definition. Conversely induction on the horizon, simultaneously for all states, identifies a family obeying (8) with $D$. The $n=0$ instance gives the one-step equation, and division gives (9). For the reverse direction, positive branches can be multiplied. If $e_z(a)=0$, repeated marginalization and nonnegativity give $\sum_{|w|=n}Q_z^{(n+1)}(aw)=Q_z^{(1)}(a)=0$, so every summand vanishes; (8) holds there independently of the successor's law. This covers zero branches without dividing by zero. One-step calibration alone gives no equations at later horizons. $\square$

**Proposition 9 (Conditional-future states and support boundary).** For a consistent string-probability system $P$ with $P(\varepsilon)=1$, define $Q_h(v)=P(hv)/P(h)$ for histories with $P(h)>0$. Set $h\sim k$ if all these finite future probabilities agree. On the nonempty class set define $e_{[h]}(a)=Q_h(a)$ and, when positive, $U([h],a)=[ha]$. These are well-defined and satisfy (8). Zero-probability transitions may be totalized to any existing class. Each class retains its own conditioned future law, and the generated distributions still equal that law. No equality to conditioning on a zero-probability history is asserted.

Proof. Equal conditional futures give equal $Q_h(a)$. For a positive branch,

$$
Q_{ha}(v)=\frac{Q_h(av)}{Q_h(a)}
=\frac{Q_k(av)}{Q_k(a)}=Q_{ka}(v),
$$

so successors agree. The same identity proves (8); zero branch cylinder probabilities vanish by consistency. Arbitrary totalization only multiplies a successor law by zero at that transition. At a class subsequently queried independently, its existing positive-history representative supplies its law and the same argument applies. New off-support states with externally prescribed laws require their own (8); arbitrary totalization does not prove those laws correct. For every class, the next-state law is the pushforward

$$
\Pr(Z'=z'\mid z)=\sum_{a:U(z,a)=z'}e_z(a).
\tag{10}
$$

This is a finite-history conditional calculation. The stationary-process entropy minimality and almost-sure uniqueness in SHALIZI are stronger statements in a different declared model; they are not imported for arbitrary histories here. $\square$

**Definition 5 (Feedback reports).** Let reports lie in a nonempty set $\mathcal P$, with report-sensitive transition $F:S\times\mathcal P\to S$ and a fixed property $h:S\to\mathcal P$. For state $s$ put $R_s(p)=h(F(s,p))$. Complete accuracy of report $p$ means $p=h(F(s,p))$.

**Proposition 10 (Feedback accuracy and finite monotone fixed points).** Accurate reports at $s$ are exactly fixed points of $R_s$. If $\mathcal P$ is a finite complete lattice and $R_s$ is monotone, iteration from its bottom stabilizes at the least fixed point. If reports have an incomplete-information subset, this argument does not ensure that the fixed point is a complete report. Without an existence condition a complete accurate report can fail to exist.

Proof. The accuracy equation is $p=R_s(p)$. Start $p_0=\bot$, $p_{n+1}=R_s(p_n)$. Since $\bot\le p_1$, monotonicity gives an increasing sequence, which is eventually constant in a finite lattice. The constant value is fixed. For any other fixed point $r$, induction gives $p_n\le r$, proving leastness. Membership in a separately designated complete-report subset is not an order consequence. On $\{0,1\}$, $R_s(p)=1-p$ has no fixed point. If accurate reports $p_*(s)$ have been selected, the actual dynamics $s_{t+1}=F(s_t,p_*(s_t))$ obey $p_*(s_t)=h(s_{t+1})$ by substitution. $\square$

## 4. Finite completion and progress

**Definition 6 (Completion language and distance).** In a task world define

$$
\mathcal C(s)=\{w:\delta^*(s,w)\in G\},\quad
H(s)=\mathbf1_{\mathcal C(s)\ne\varnothing},\quad W=H^{-1}(1),
$$

$$
d(s)=\min\{|w|:w\in\mathcal C(s)\}\in\mathbb N\cup\{\infty\}.
$$

The empty minimum is infinity, $1+\infty=\infty$. For any legal prefix $u$,

$$
\mathcal C(\delta^*(s,u))=u^{-1}\mathcal C(s),\quad
u^{-1}L:=\{v:uv\in L\}.
$$

The residual is taken by the same executed prefix $u$.

**Proposition 11 (Least reachability fixed point and unique distance).** For

$$
\mathcal B(X)=G\cup\{s:\exists a\in A(s),\ \delta(s,a)\in X\},
$$

one has $W=\mu\mathcal B$, and $d$ is the unique function to $\mathbb N\cup\{\infty\}$ satisfying

$$
d(s)=0\ (s\in G),\qquad
d(s)=1+\min_{a\in A(s)}d(\delta(s,a))\ (s\notin G).
\tag{11}
$$

If $r:W\to\mathbb N$ vanishes on $G$ and every $s\in W\setminus G$ has a successor in $W$ of strictly smaller rank, then $d(s)\le r(s)$.

Proof. Execution concatenation gives the residual identity in Definition 6. Starting $W_0=\varnothing$, $W_{n+1}=\mathcal B(W_n)$, induction says $W_{n+1}$ consists of states with a successful path of length at most $n$. The union is $W$. A predecessor of a point in that union already enters at some finite next stage, so $\mathcal B(W)=W$. Any prefixed point $\mathcal B(X)\subseteq X$ contains all $W_n$ by induction, proving leastness. On an infinite chain with no successes, both the empty set and the whole chain are fixed; only the least describes finite completion.

The first-step decomposition of shortest paths gives (11). For any other solution $v$, following a successful length-$L$ path backwards gives $v(s)\le L$. If $v(s)=k<\infty$, induction on $k$ constructs a successful length-$k$ path: value zero forces success, while a positive value at a nonsuccess state yields a legal successor of value $k-1$. The minimum is attained because the nonempty action set is finite. Thus $d(s)\le v(s)$ whenever $v$ is finite, and $v(s)\le d(s)$ whenever $d$ is finite; these implications also exclude unequal infinite cases. Finally induction on $r(s)$ chooses a strictly smaller successor and gives $d(s)\le1+d(s')\le1+r(s')\le r(s)$. $\square$

**Proposition 12 (Canonical suffix consistency and a replanning counterexample).** For $s\in W\setminus G$ put

$$
\operatorname{Good}_d(s)=\{a\in A(s):d(\delta(s,a))=d(s)-1\},\qquad
\pi_d(s)=\min\operatorname{Good}_d(s).
$$

This set is nonempty. Repeated $\pi_d$ reaches success in exactly $d(s)$ steps. There is a lexicographically least shortest successful word $P(s)$ satisfying

$$
P(s)=\varepsilon\ (s\in G),\qquad
P(s)=\pi_d(s)P(\delta(s,\pi_d(s)))\ (s\in W\setminus G).
\tag{12}
$$

Full future equivalence preserves $\mathcal C,H,d,\operatorname{Good}_d$ and $\pi_d$. Merely replanning a correct proof at every step need not terminate, even on a DAG.

Proof. Equation (11) provides an action lowering $d$ by exactly one. Recursion on finite $d$ defines (12). Any shortest word begins with such an action; choosing the least first action and recursively the least shortest suffix proves lexicographic minimality. Every step lowers the distance by one, proving the exact termination count and suffix consistency. Equal future rows include equal success tests on every word, giving all stated invariances.

For the negative claim take edges $s_i\xrightarrow a s_{i+1}$ and $s_i\xrightarrow b g_i$ for $i\ge0$, with terminal successes $g_i$. The graph is a DAG and the table word $ab$ is a correct proof from every $s_i$. Executing only its first action and looking up a new word produces $s_0,s_1,\ldots$ forever. Success remains reachable at every step. A repair is (12); another is to retain the chosen residual word, $(s,av)\mapsto(\delta(s,a),v)$, whose length strictly decreases. Correct reachability values, recursive addresses and compatible choice require such a progress argument before actual completion follows. $\square$

## 5. Finitary rule closure and a semantic bridge

**Definition 7 (Rule system).** Let $F$ be a countable fact set, $K_0\subseteq F$, and rules $P_r\Rightarrow c_r$ with finite premise sets. Put

$$
C_0(K)=K,\quad
C_{n+1}(K)=C_n(K)\cup\{c_r:P_r\subseteq C_n(K)\},\quad
\operatorname{Cl}(K)=\bigcup_{n\ge0}C_n(K).
$$

A finite proof DAG, in the sense also used by the repository [proof-structure exposition][FIXED], has finitely many fact-labelled vertices, leaves in $K$ or justified by empty-premise rules, and each other vertex justified by a rule whose premises occur at predecessors. The newly added derivation distance $d_g(K)$ is the least number of sequential rule conclusions needed to obtain $g$, zero if already known and infinity if impossible.

**Proposition 13 (Finite proofs, closure invariance and fair acquisition).** The set $\operatorname{Cl}(K)$ is the least rule-closed superset of $K$ and consists exactly of facts with such finite proofs. Set $D=\operatorname{Cl}(K_0)$. If $K_0\subseteq K\subseteq D$, then

$$
\operatorname{Cl}(K)=D.
\tag{13}
$$

If $K\subseteq K'$, then $d_g(K')\le d_g(K)$. Every reliable monotone growth sequence from $K_0$ whose enabled rules eventually have their conclusions added has union $D$. Two rules already enabled commute as set additions.

Proof. Finitely many premises in the union of closure stages all occur by one common finite stage, so their conclusion occurs at the next. Every rule-closed superset contains all stages by induction, giving minimality. Stage induction builds finite proofs by adjoining a conclusion to finitely many finite predecessor proofs; levels give an acyclic dependency order. Conversely topologically sort a finite proof DAG and induct over its vertices to place its conclusion in a finite stage. The stage construction also gives monotonicity and idempotence of $\operatorname{Cl}$.

From $K_0\subseteq K$ monotonicity gives $D\subseteq\operatorname{Cl}(K)$. Since $D$ is a closed superset of $K$, minimality gives the reverse inclusion. For distance, replay a shortest sequential derivation from $K$ starting with $K'$, skipping conclusions already present; all premises remain available. Infinite distance causes no exception.

Reliability of growth gives each $K_t\subseteq D$. For any rule whose premises lie in the union, finiteness places all premises in a single $K_t$; fairness puts the conclusion in a later one. The union is therefore closed and contains $K_0$, so equals $D$. If two rules are enabled at $K$, both orders give $K\cup\{c_r,c_s\}$, including coincident conclusions. Thus current knowledge $\mathbf1_{g\in K}$ may increase, eventual derivability $\mathbf1_{g\in\operatorname{Cl}(K)}$ stays fixed under (13), and remaining distance cannot increase. None of this identifies derivability with all truth without a semantic bridge. $\square$

**Assumption 8 (Completion semantics on a rule-realizing graph).** The designated completion graph is the finite-rule-execution graph below, or comes with goal-preserving maps between its finite successful paths and those executions. Completion (1) is imposed on this specified graph. Independently, if semantic soundness is desired, initial facts are true and each rule preserves truth. The path correspondence and semantic completeness are separate from monotone closure.

**Proposition 14 (A constructed path–proof bridge).** The graph whose vertices are finite sequences of enabled rule applications starting from $K_0$, whose edges append one enabled rule, and whose success test for $g$ is membership in the accumulated facts, satisfies

$$
\exists\text{ finite successful path for }g
\quad\Longleftrightarrow\quad g\in\operatorname{Cl}(K_0).
\tag{14}
$$

Consequently Assumption 8 and (1) identify designated truth with $D$. Completion on an unrelated graph alone does not do so.

Proof. For each fixed goal $g$, remove outgoing edges once $g$ is present and declare those vertices terminal successes. Truncating at first success does not change existence of a successful path. A finite sequence of enabled rules gives a finite proof for its conclusions: recursively attach each finite premise's earlier justification or its initial-fact leaf. Conversely a finite proof DAG can be topologically ordered, and that order lists enabled rule applications reaching $g$. Proposition 13 gives (14). This constructed graph is acyclic by sequence length. If a finite action alphabet is required, encode the countably many possible finite-premise/conclusion rules by finite binary indices and parse the next index before applying the rule; intermediate parser states are nonsuccessful, so successful finite paths still correspond exactly. An empty rule set is included. With this bridge, (1) gives the advertised truth identification; soundness gives the same implication to semantic truth independently. For failure without a bridge, take one true $g$ with a successful edge in an unrelated task graph, but $F=\{g\}$, $K_0=\varnothing$ and no inference rules. Completion holds in that graph while the rule closure is empty. $\square$

[SHALIZI]: ../Dynamics/shalizi2001computational.md
[BEHAVIOUR]: ../../docs/develop/theory/COMPUTATIONAL_BEHAVIOR_REPRESENTATION_THEORY.md
[PROCESS]: ../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[STATIC]: ../../docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md
[INTERFACE]: ../../docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md
[MEMORY]: ../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md
[ATOMS]: ../../docs/develop/theory/AURIC_FIB_ATOM_OBSERVATION_UPDATE_AND_RETURN_PREDICTION.md
[FIXED]: ../../docs/develop/theory/FIXED_POINT_PHILOSOPHY.md
[UPDATE]: ../../D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate.lean
[FACTOR]: ../../D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization.lean

## 追加锚（本行以下为增补区）

## 6. Source-relative lookup addresses and finite acquisition

**Definition 8 (Source-relative future equivalence).** Let $t$ be one currently live LAB source, let $Q$ be its finite control set, and let $\operatorname{Cont}(t)$ be the finite or infinite words of events that are actually legal from that same source. For $q,r\in Q$, write

$$
q\equiv_t r
\iff
\forall z\in\operatorname{Cont}(t),\quad
\operatorname{bits}(q,z)=\operatorname{bits}(r,z).
\tag{15}
$$

The selected word $\nu$ records the event identities whose selector bit is one. A source-relative predictive address is

$$
(t,\nu,[q]_{\equiv_t}).
\tag{16}
$$

The source $t$ and the selected word are part of the address; a control representative alone is not an address for another source.

**Proposition 15 (Successor closure and complete future behaviour).** Suppose a successful event $e$ updates a control by

$$
C(q,e)=(\delta(q,e),\lambda(q,e)),
\qquad \lambda(q,e)\in\{0,1\}.
\tag{17}
$$

If $q\equiv_t r$, then for every event $e$ legal from $t$,

$$
\lambda(q,e)=\lambda(r,e),
\qquad
\delta(q,e)\equiv_{t\cdot e}\delta(r,e).
\tag{18}
$$

Consequently (16) determines legality, every complete seven-request reply and the actual $\operatorname{NextSelected}$ successor supplied by the LAB interface in [LAB §§36–38][LAB-ACQUISITION].

Proof. Taking the one-event word $e$ in (15) gives equality of the selection bits. For any $z\in\operatorname{Cont}(t\cdot e)$, the concatenated word $ez$ is in $\operatorname{Cont}(t)$. Equality in (15) for $ez$, followed by removal of the common first selection bit, gives equality of the successor bit words on $z$. The source successor $t\cdot e$, selected-word append rule, and complete request semantics are therefore the same for either representative. The result is source-relative and does not identify hidden control states outside the equivalence class. $\square$

**Assumption 16 (Supplied finite address presentation).** As in [LAB Definition 37.1][LAB-ACQUISITION], there is a finite address-class set $H$, a root class $h_0$, and maps $\ell,\rho:H\to H$ such that each current leaf is an $\alpha$- or $\beta$-leaf labelled by one of the classes $h$. The selector reads only the class of the event address, with finite transition table

$$
(\delta,\lambda):Q\times\{P,S\}\times H\to Q\times\{0,1\}.
\tag{19}
$$

At class $h$, the local source operations are

$$
P_h:a_h\longmapsto b_h,
\qquad
S_h:b_h\longmapsto b_{\ell(h)}+a_{\rho(h)}.
\tag{20}
$$

A finite current source is represented by the vector $m(t)\in\mathbb N^{2|H|}$ of its $a_h$ and $b_h$ leaf counts. A nonzero count means that an actual leaf of that class exists and can be selected for the corresponding legal operation.

**Proposition 17 (Finite count abstraction and actual lifting).** Under Assumption 16, the relation $q\equiv_t r$ is decidable from the finite vector $m(t)$. Abstract operation paths in the count system lift step by step to legal operations on the actual source, and the count update is the projection of that actual operation.

Proof. $P_h$ decreases the $a_h$ count and increases $b_h$; $S_h$ decreases $b_h$ and increases the indicated $b_{\ell(h)}$ and $a_{\rho(h)}$. If the relevant count is nonzero, choose one actual leaf of that class. The operation changes no other required class count, so induction on the abstract path gives an actual path with the same class sequence and selector bits. Conversely every actual operation has one of the transitions (20), so its count projection is an abstract path.

To decide equivalence, run the two finite control states over the same abstract event paths while recording a disagreement whenever their output bits differ. The set of count vectors from which a disagreement is reachable is upward closed under componentwise order: extra leaves can be ignored while following the same path. For a transition $e$, with input vector $i_e$ and output vector $o_e$, the least predecessor covering a vector $v$ is

$$
\operatorname{pre}_e(v)=i_e+(v-o_e)^+,
\tag{21}
$$

where $(u)^+$ is taken componentwise. Backward iteration from the disagreement events, followed by minimalization, computes the finite basis $B_{q,r}$ of this upward-closed set. Dickson's lemma gives finiteness of every minimal basis and termination of the finite-basis iteration. Hence

$$
q\not\equiv_t r
\iff
\exists v\in B_{q,r},\quad v\le m(t).
\tag{22}
$$

The upward-closure computation is an address-class calculation; the lifting paragraph supplies the required actual legal witness and prevents the finite counter from being mistaken for a free source oracle. This is the finite presentation and coverability route of [LAB §§36–38, especially Lemma 37.2 and Theorem 37.3][LAB-ACQUISITION]. Geffroy–Leroux–Sutre, arXiv:1607.05956v1, Lemma 3.1 supplies stationarity of the growing upward-closed sequence, Lemma 4.1 supplies finite minimal bases, and Lemmas 4.3–4.4 supply the covering-predecessor formula and its set extension. $\square$

**Theorem 18 (Finite candidate elimination on one live source).** Let a publicly supplied nonempty finite family $(C_i,Q_i,q_i^0)_{i\in I}$ of candidate LAB controls be given, with exactly one fixed but unknown candidate installed from its declared initial control on the known $\alpha$-seed source. There is only one actual source; it cannot be reset, copied or replaced. Assume each candidate supplies Assumption 16's finite presentation and every complete request has a finite effective reply. There is a finite acquisition procedure that returns a self-sufficient predictor for the complete seven-request task, as in [LAB supply application 41.3][LAB-ACQUISITION].

Proof. Let $h$ be the complete actual request/reply history. Maintain its common current source description $t_h$ from the known seed and each actual new growth identity. For a successful NextSelected reply, only its second identity is the new event fed to the selector; the first identity is recalled history. Ordinary queries, refusals, OutOfRange and BadFrame feed no event. For each candidate, simulate $h$ from that candidate's own public initial control and retain it exactly when every complete reply agrees with the actual reply. Write $J_h$ for these candidates, $q_i(h)$ for their current controls and $\nu_i(h)$ for their selected words. The genuine installation remains in $J_h$. Every surviving simulation has the same source $t_h$, since its complete growth replies give the same new actual identities; only the candidate control and selected word may differ. These are local computations on supplied programs and acquired identities, not reads of hidden control or selection marks.

Form the finite product $H=\prod_{i\in I}H_i$ of the supplied address classifiers, using their root tuple and coordinatewise left/right maps. On the tagged disjoint union $Q^\sqcup=\bigsqcup_{i\in I}Q_i$, each control uses its own coordinate's original table and stays within its tag. Proposition 17 applied to this supplied product decides cross-candidate source-relative equivalence using the leaf counts of the same $t_h$. By [LAB §41.2 and application 41.3][LAB-ACQUISITION], two surviving candidates have identical complete future behaviour exactly when

$$
\nu_i(h)=\nu_j(h),\qquad
(i,q_i(h))\equiv_{t_h}^{\sqcup}(j,q_j(h)).
$$

If all surviving candidates agree in this sense, choose one finite current representative and return its predictor. Otherwise choose a disagreeing pair. If their selected words already differ, actually issue FetchSelected at an index where the literal identities differ or one word is out of range. Its complete reply distinguishes the pair without changing the source.

If their selected words agree, their residual controls are inequivalent. Using the product decision and actual lifting in Proposition 17, find a finite source-legal event word on which their selection bits differ. An effective search enumerates finite event words by total binary encoding length, checks legality from $t_h$ and computes both candidates; each layer is finite and a finite witness exists. Truncate the word at its first unequal selector bit. Actually submit exactly these addressed growth requests, serially, to the same live source. Let $m$ be the common selected-word length immediately before that last event, including any selections from earlier events of this test. The last event appends its actual identity in exactly one of the two candidate simulations. Now actually submit FetchSelected$(m+1)$: one candidate predicts that identity and the other predicts OutOfRange. The ordinary Growth replies alone need not reveal the unequal bit. This is the complete-reply separation of [LAB Proposition 36.2 and application 41.3][LAB-ACQUISITION].

All growth frames in the chosen test are legal on the same evolving source independently of which candidate is installed, including when the genuine installation is a third candidate. Delete candidates only by disagreement with actual complete replies. The final selected-query reply excludes at least one member of the chosen pair, while the genuine installation is retained. Recompute the surviving current states and equivalences at the already changed source; no test returns to an earlier cut. Each separating test executes one actual continuation and removes a candidate, so at most $|I|-1$ tests occur. This counts tests only: every actual growth request and every actual FetchSelected query, including OutOfRange replies, counts as a completed request; all actual work, frames, retained material and any other completed queries or refusals remain charged. There is no bound here on witness length or local search work.

At termination all survivors have the same selected word and residual future class, and one is genuine. The chosen representative, supplied tables, current source and common selected word therefore give a finite self-sufficient predictor without an unknown installation parameter. For subsequent requests, (18) updates that representative on each actual new event, and its computed selection bit updates the word. Equality of the surviving future behaviours makes these predictions equal to the genuine service, including complete NextSelected replies and actual source successors. Induction over subsequent finite request words proves continued correctness. Every test is finite and there are finitely many tests, so acquisition terminates. $\square$

**Proposition 19 (Depth-threshold acquisition cost).** For $n\ge1$, in the supplied two-candidate family in which $C_0$ never selects a growth event and $C_n$ selects exactly an event whose address depth is at least $n$, any certification procedure on the live source needs at least $n+2$ successful growth events and $n+3$ completed requests before it can return a correct self-sufficient predictor. A matching procedure uses $n+2$ growth requests followed by one distinguishing selected query.

Proof. From the initial $\alpha$ root, a successful event at depth $d\ge n$ requires $d$ distinct strict-ancestor splits and the root promotion before the depth-$d$ event itself. Thus a depth-$n$ event requires $n$ strict-ancestor splits, one root promotion and that event, giving $n+2$ successful growths. A refused address, an incomplete frame and a query index create no source event, and a completed request creates at most one successful growth. Until a threshold event occurs, both selected words are empty and all complete replies agree. Its ordinary Growth reply still agrees, so the first distinguishing selected-query reply requires a later completed request, giving at least $n+3$. From every finite common current source, further legal growth can reach the threshold and a selected query can distinguish the two residual tasks. Hence a correct self-sufficient predictor cannot return on their common history before such a distinction.

For the upper bound, execute exactly $P_\varepsilon S_\varepsilon S_L\cdots S_{L^n}$, with $n+2$ actual growth requests, and then actually issue FetchSelected$(1)$. The $C_0$ candidate returns OutOfRange, while $C_n$ returns the depth-$n$ selected identity $S_{L^n}$. For $n=1$, the word is $P_\varepsilon S_\varepsilon S_L$, with one strict-ancestor split. The live source, selected word and current permission are retained, so (18) supplies the continuing predictor. This is [LAB Theorem 42.2][LAB-ACQUISITION], with the request and material boundaries of §§41–43. $\square$

**Theorem 20 (A merely existential finite presentation does not yield uniform acquisition).** There is no single uniform finite-return certification algorithm for the candidate class in which every instance has some finite effective address presentation but the presentation, a size bound and an extraction method are not supplied.

Proof. Let $M_e$ be any finite machine and let $H(e,d)$ mean that bounded simulation has observed $M_e$ halt within the first $d$ stages. Define two one-state candidates

$$
Z(e_{\mathrm{event}})=0,
\qquad
D_e(k,p)=\mathbf 1_{H(e,|p|)}.
\tag{23}
$$

Every finite address has a terminating bounded simulation. If $M_e$ never halts, $D_e$ is the same selector as $Z$; if the first halt is at stage $\tau$, $D_e$ selects exactly at depth at least $\tau$. Thus each fixed instance satisfies the semantic promise that a finite presentation exists.

Assume a uniform certification algorithm $A$ always returns after finitely many actual successful events on the installation $Z$. Let $B_e$ be the largest successful event depth before that return, with $B_e=0$ when none occurs. If $M_e$ halts first at $\tau>B_e$, replacing the installation by $D_e$ leaves every pre-return selected bit, complete reply, source successor and request transcript unchanged: all observed event depths are below $\tau$. The same finite address and predictor are therefore returned for $Z$ and $D_e$.

From the common current source one can legally extend the left $\beta$ chain to depth at least $\tau$. A later selected query distinguishes the candidates: $D_e$ returns a selected identity while $Z$ returns OutOfRange, and a subsequent $\operatorname{NextSelected}$ request, when used, has different actual successors. Correctness of one self-sufficient predictor would then require two different future behaviours from the same returned state. Hence

$$
M_e\text{ halts}\Longrightarrow\tau\le B_e.
\tag{24}
$$

Simulate $M_e$ for $B_e$ stages. If it has halted, answer halting; otherwise (24) implies that it never halts. This decides the halting problem, a contradiction. The argument is [LAB Theorem 44.2][LAB-ACQUISITION], using one live source, complete replies and actual future successors; it does not infer a presentation from a semantic existence promise. $\square$

**Convention 21 (Attribution and boundary).** The source-relative quotient, successor closure, finite presentation, candidate elimination, depth-threshold and non-acquisition results above are the substantive [LAB §§36–45][LAB-ACQUISITION] results, especially supply application 41.3 and Theorems 42.2 and 44.2, and their mathematical consequences; they are not re-attributed as new repository discoveries. The finite-basis method is literature-attested in Geffroy–Leroux–Sutre, arXiv:1607.05956v1. The negative theorem uses the standard halting obstruction, with Turing's §8 printing formulation as the undecidability source. A finite presentation is an effective supplied object; a statement that each instance merely has some finite presentation is an existence quantifier and does not provide a uniform extractor. $\square$

[LAB-ACQUISITION]: ../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md

## 追加锚（本行以下为增补区）

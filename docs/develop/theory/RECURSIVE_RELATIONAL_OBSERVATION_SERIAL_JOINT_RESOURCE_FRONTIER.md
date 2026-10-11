# Serial recovery of a complete original row with joint resource prices

## 1. The entire source fiber and the three charged coordinates

**Assumption 1.1 (source, retained information, and actual entry).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

Every source is a nonempty finite ordered free tree. There is no supplied common source shape, size, depth, template, or execution cutoff. Every word in $\mathcal P=\{L,R\}^{*}$ is a legal physical read address, including $\varepsilon$ and absent addresses. The literal reply $r_u(p)$ belongs to $\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.

Use the complete entry of [SERIAL_COMPLETE_ROW_PRICE](RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md), abbreviated SCR, Assumption 1.1. In particular, $P,Q$ are arbitrary finite prefix-free original cut sets, allowed to be empty or to contain the root. The full old row $R=(C,\pi)$ was acquired by the all-source producer of [SPARSE_LITERAL_HISTORY_TRANSPORT](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md), abbreviated SLH, Definition 59.2. Its concrete exterior, original existence guards, repeated occurrences of each old class, and every disequality between different old classes are retained. A finite actual mixed-epoch literal history $H=((n_i,p_i,c_i))$ and the complete accessible control determine precisely

$$
D=\mathcal U_R(H)
 =\{u\in\mathcal T:R_P(u)=R,\quad
                 r_{\rho^{n_i}u}(p_i)=c_i\text{ for every }i\}
 \ne\varnothing.
\tag{JRF.1.1}
$$

The same original-root register has actually reached authenticated epoch $N\ge\max(\{0\}\cup\{n_i\})$. Its content is $\rho^N u$. Public installation, permissions, task, and accessible initial control are common on $D$. Any source-dependent cache, archive, allocation length, timing information, or other accessible field must already be represented in this entry; retaining an additional distinction changes the fiber. The target is the whole original $R_Q(u)$: concrete exterior, reached holes in original address order, and their full equality partition. It is neither a prescribed trace nor a finer tuple of selected literal answers.

**Definition 1.2 (actual services and sourcewise costs).** Let $\mathcal C(D,N,Q)$ be the common deterministic effective serial programs that correctly output $R_Q(u)$ and terminate on each $u\in D$. Their only new source-dependent input is the reply to an actual $\mathsf{Read}(p)$ on the one current register. Their other source actions are actual $\mathsf{ApplyRho}$ and absorbing $\mathsf{Halt}$. Choices of address, updates, and stopping may depend on acquired replies and the actual accessible control. There is no backward reset, moved root, hidden source oracle, free producer, unrecorded clock, or extra equality port. Local computation and working storage are supplied separately. No uniform running-time bound is assumed. After a genuine halt, continuation requires a separately supplied entry.

For $A\in\mathcal C(D,N,Q)$ and $u\in D$, define

$$
 c_A(u)=(q_A(u),d_A(u),\ell_A(u))\in\mathbb N^3,
 \qquad
 \ell_A(u)=\sum_{\text{actual new reads }p}|p|.
\tag{JRF.1.2}
$$

Here $q_A$ counts every actual new raw call, including repetitions; $d_A$ counts actual post-entry $\mathsf{ApplyRho}$ actions. A root read has address length zero but still costs one raw call. Each $|p|$ is the length of the literal physical address submitted on that call, with its original-root prefix included. Address construction, storage, transmission hardware, local computation, installed program, output, retention, authentication, and physical update work have no price assigned by (JRF.1.2). In particular, an action count is not a time or energy measurement.

**Definition 1.3 (three different optimization objects).** Write

$$
 b(A)=\bigl(\sup_D q_A,\sup_D d_A,\sup_D\ell_A\bigr)
 \in(\mathbb N\cup\{\infty\})^3,
 \qquad
 \mathcal F=\{b\in\mathbb N^3:\exists A\in\mathcal C(D,N,Q),\ b(A)\le b\}.
\tag{JRF.1.3}
$$

Thus $\mathcal F$ consists of simultaneous upper budgets, not necessarily exactly attained cost vectors. Its Pareto basis means its coordinatewise minimal elements. Sourcewise dominance means $c_{A'}(u)\le c_A(u)$ for every same source $u$. It is stronger than $b(A')\le b(A)$, and neither inequality means equality of profiles.

For a supplied rational vector $\lambda=(\lambda_q,\lambda_d,\lambda_\ell)\ge0$, the separate weighted objective is

$$
 W_\lambda(A)=\sup_{u\in D}
       \bigl(\lambda_q q_A(u)+\lambda_d d_A(u)+\lambda_\ell\ell_A(u)\bigr),
 \qquad
 W_\lambda^*=\inf_{A\in\mathcal C(D,N,Q)}W_\lambda(A).
\tag{JRF.1.4}
$$

The sum is formed on each actual finite run before taking the supremum. A zero weight ignores that coordinate's magnitude; no $0\cdot\infty$ convention is needed inside the sum. In general (JRF.1.4) is different from $\lambda\cdot b(A)$.

**Convention 1.4 (existing suppliers).** SLH Theorem 74.4 supplies the effective predicate $\mathsf{GB}(P,Q,R,H)$, its equivalence to existence of a uniform finite raw budget, and an actual static service when it holds. SCR Theorem 4.2 supplies effective finite exact row predicates after GB; SLH Theorem 61.1 supplies joint feasibility and source witnesses with all old class constraints. These ordinary results are reused with their entire admitted domains. The proofs below concern the additional operational correspondence for (JRF.1.2). They are ordinary mathematics, not Lean kernel verification or physical execution certification.

## 2. Shortening late-epoch probes without changing any reply

**Definition 2.1 (a shortest word with prescribed weight and final edge).** Put $w(p)=\#_L(p)+2\#_R(p)$, and let $\omega(L)=1$, $\omega(R)=2$. For $t\ge\omega(e)$, define

$$
 Z_e(t)=R^{\lfloor(t-\omega(e))/2\rfloor}
          L^{(t-\omega(e))\bmod2}e,
 \qquad
 h_e(t)=1+\left\lceil\frac{t-\omega(e)}2\right\rceil.
\tag{JRF.2.1}
$$

Then $Z_e(t)$ ends in $e$, has weight $t$, and has length $h_e(t)$. Every nonempty word of weight $t$ ending in $e$ has length at least $h_e(t)$, since its preceding letters each have weight at most two. The displayed word attains this bound. For fixed $e$, $h_e$ is nondecreasing on its domain.

**Lemma 2.2 (nonexpansive backward epoch transport).** There is an effective address map $S(n,m,p)$ for all $n\ge m\ge5$ satisfying

$$
 \forall u\in\mathcal T,\qquad
 r_{\rho^n u}(p)=r_{\rho^m u}(S(n,m,p)),
 \qquad |S(n,m,p)|\le |p|.
\tag{JRF.2.2}
$$

The labels, including $\mathsf{absent}$, are unchanged. The address map is independent of the source and imposes no source-depth bound.

Proof. The guarded leaf formula SCR (2.1), with $\lambda_0=\alpha$, $\lambda_1=\beta$, states that a nonempty suffix $s$ ending in $e$ exists in $\rho^j\lambda_b$ precisely when

$$
 j+b-w(s)\ge2-\omega(e).
\tag{JRF.2.3}
$$

When it exists, residual values zero, one, and at least two give $\alpha,\beta,\mathsf{branch}$, respectively. The empty suffix always exists. Two nonempty suffixes with the same last edge, whose weight difference equals the epoch difference, therefore have exactly the same reply. Also SCR (2.7) gives

$$
 w(s)\le j-2\quad\Longrightarrow\quad
 r_{\rho^j v}(s)=\mathsf{branch}\quad\text{for every }v\in\mathcal T.
\tag{JRF.2.4}
$$

If $w(p)\le n-2$, set $S(n,m,p)=\varepsilon$. Both replies are branch by (JRF.2.4), and the length inequality holds. This includes $p=\varepsilon$.

Otherwise factor $p=xy$, taking $x$ to be the shortest prefix for which $r=w(y)\le n-2$. Since each removed edge has weight one or two,

$$
 n-3\le r\le n-2,\qquad
 t=m-n+r\in\{m-3,m-2\}.
\tag{JRF.2.5}
$$

Here $x,y$ are nonempty: $x$ is needed by the strict inequality on $w(p)$, and $r\ge n-3\ge2$. Let $e$ be the last edge of $p$, also the last edge of $y$, and set

$$
 S(n,m,p)=xZ_e(t).
\tag{JRF.2.6}
$$

The word is defined since $t\ge m-3\ge2$. If the original tree first reaches a leaf at a strict prefix $a$ of $x$, the old and new remaining suffixes are $(x\setminus a)y$ and $(x\setminus a)Z_e(t)$. They are nonempty, end in the same $e$, and their weights differ by $m-n$. Equation (JRF.2.3) preserves both existence and residual, hence the whole reply. If $x$ is reached in the original tree, apply (JRF.2.4) inside the arbitrary subtree there: $w(y)\le n-2$ and $t\le m-2$, so both replies are branch. These cases exhaust all finite original trees, including paths that were originally absent.

Finally $t\le r$, and Definition 2.1 gives

$$
 |Z_e(t)|=h_e(t)\le h_e(r)\le |y|.
$$

Adding $|x|$ proves the literal length inequality. All operations are finite word and integer operations. $\square$

The difference from SCR Theorem 2.2 is the one-sided condition $n\ge m\ge5$ and the nonexpansive literal-length conclusion. SCR's forward padding and bound $|T(n,M,p)|\le|p|+M-1$ do not supply this conclusion. No least universal threshold is asserted.

## 3. A dominating operational normalization for every serial comparator

**Theorem 3.1 (retain early actions, cap later actual updates).** Put

$$
 M=\max(N,5),\qquad U=M-N.
\tag{JRF.3.1}
$$

For every $A\in\mathcal C(D,N,Q)$ one can effectively construct $A^c\in\mathcal C(D,N,Q)$ such that, on each $u\in D$,

$$
 \operatorname{out}_{A^c}(u)=\operatorname{out}_A(u),\quad
 q_{A^c}(u)=q_A(u),\quad
 d_{A^c}(u)=\min(d_A(u),U),\quad
 \ell_{A^c}(u)\le\ell_A(u).
\tag{JRF.3.2}
$$

Every actual epoch of $A^c$ lies in $[N,M]$. Every read and update of the simulated run before it would exceed $M$ is performed at its original epoch and address. In particular, all reply-dependent decisions at epochs zero through four, including halt before the first update, are retained. Pointwise termination is preserved without assuming a uniform bound on $A$'s original actions or local work.

Proof. Keep the acquired entry and separate actual and simulated records. Simulate $A$ from epoch $N$; let $n$ be its simulated epoch. Maintain the actual epoch as $\min(n,M)$. A simulated update is performed on the actual register if $n<M$, and otherwise changes only the local simulated state. A simulated read at $p$ is performed at $p$ if $n\le M$; if $n>M$, actually read $S(n,M,p)$. Lemma 2.2 makes the returned literal value exactly the one $A$ would obtain on the same $u$. Induction on the finite original execution therefore preserves its simulated control, successive replies, choices, and output.

Each simulated read produces exactly one actual read. Before the cap the address length is unchanged, and after it Lemma 2.2 makes the length no larger. Actual updates are exactly the first $\min(d_A(u),U)$ updates. Each simulated step and each address transformation takes finite local work, so a finite run of $A$ yields a finite run of $A^c$. The program halts when the simulation halts and has no outgoing source action afterward. Its actual receipts record only its actual epochs and physical addresses. A simulated late update is neither an actual update nor an authenticated receipt. $\square$

**Lemma 3.2 (the only zero-length information opportunities).** Every serial service can be effectively replaced by a pointwise dominating one, with the same output and pointwise termination, for which

$$
 q(u)\le\ell(u)+s_N,\qquad s_N=\max(0,2-N).
\tag{JRF.3.3}
$$

This replacement does not increase updates and can be applied after Theorem 3.1.

Proof. Simulate the given control. For a repeated request to the same physical address at the same actual epoch, use its already acquired literal value locally. The register is unchanged between such reads; the epoch is part of the cache key. The first new read at that pair is still an actual paid read. Root replies at every epoch at least two are branch for all sources, by (JRF.2.4), so simulate these without calling the source at all. Root replies at epochs zero and one can each require at most one actual read; only epochs at least $N$ are available, giving at most $s_N$. All other actual reads have nonempty addresses, and hence each contributes at least one to $\ell$. This proves (JRF.3.3).

The simulation supplies the same replies to the original control. It deletes only actual reads, preserves the actual updates, and preserves each finite original execution. Skipped reads are not inserted into the actual receipt list. An epoch-zero root read determines the epoch-one root reply as well, but that additional saving is unnecessary for the bound. $\square$

**Corollary 3.3 (finite address budgets cannot conceal infinitely many necessary reads).** A uniform finite literal-address budget for a correct service exists if and only if GB holds. If GB fails, every correct service has both $\sup_D q_A=\infty$ and $\sup_D\ell_A=\infty$.

Proof. GB failure excludes finite raw budgets by SLH Theorem 74.4. If a correct $A$ had $\sup_D\ell_A=L<\infty$, Lemma 3.2 would give a correct service with at most $L+s_N$ reads, a contradiction. Conversely, the static finite service supplied by GB has a finite reply tree, hence finitely many installed addresses and a finite total address budget. No source bound follows from this finite program. $\square$

**Lemma 3.4 (shortest physical occurrence of an old class).** Let $B$ be the old class set and $p_i$ its reached hole addresses. For each class $b$, choose $a_b$ of minimum physical length among its occurrences, using shortlex only to break ties, and put $\delta_b=|a_b|$. Replacing a read $p_i s$ by $a_{[i]}s$ preserves its reply on every $u\in D$ at every epoch and never increases literal length. A read with no old-hole prefix has a source-independent value computable from $C$ and the actual epoch, and can be simulated without a raw call.

Proof. SLH Theorem 60.2 gives

$$
 r_{\rho^j u}(p_i s)=r_{\rho^j z_{[i]}}(s)
                    =r_{\rho^j u}(a_{[i]}s).
\tag{JRF.3.4}
$$

The selected occurrence has $|a_{[i]}|\le|p_i|$. Without a hole prefix, the value is exactly SLH's $\chi_C(j,p)$, including concrete leaves' later descendants, strict ancestors of holes, and absent paths. Simulate the original control with these exact replies as in Theorem 3.1; output and termination are preserved and all three costs weakly decrease. The class name remains the original canonical name; only its read location changes. $\square$

The canonical least hole index need not be shortest. For instance, the single class occurring at $LLL$ and $R$ in $\langle\langle\langle z,\alpha\rangle,\alpha\rangle,z\rangle$ is canonically named by $LLL$, whereas $R$ is shorter. A length proof must use the actual chosen physical occurrence, not merely a class suffix length.

## 4. Exact finite skeletons with unbounded address variables

**Definition 4.1 (source and terminal predicates).** Suppose GB holds. Reuse SCR Definition 4.1 with version chains through $M$: for each old class $b$, the finite label sets $X_{b,j}$ encode the arbitrary finite tree $z_b$ and its exact $j$th image, $0\le j\le M$. The formula $\operatorname{Adm}(X)$ includes all class disequalities, the complete mixed history, and the concrete exterior conditions. Its satisfying assignments are in bijection with the entire $D$. Sets for different classes live on the same suffix universe; they need not be disjoint.

SCR Theorem 4.2 constructs the finite exact image $\mathscr R=R_Q(D)$ and predicates $\operatorname{Row}_r(X)$ and $\operatorname{SameRow}(X,Y)$. They describe full original rows, including exterior and original existence, rather than any finer auxiliary observation. Their construction uses a finite original-prefix test only to express the target; it does not require a service to acquire that test. In particular, terminal sources with different prefix vectors may be combined whenever their full rows agree.

**Definition 4.2 (an unpadded serial read skeleton).** For an integer $k\ge0$, take a finite rooted tree with at most $k$ read vertices along each path. A vertex is either an absorbing halt or a read with four reply children. At each read vertex $v$, choose an epoch $m_v\in\{N,\ldots,M\}$, a class $b_v\in B$, and a first-order address variable $s_v$. Read epochs are nondecreasing along a path. Its physical request is $a_{b_v}s_v$ at epoch $m_v$. Before a read, the service actually performs the difference between its chosen epoch and its preceding actual epoch. A halt has no children and adds no actions. In particular, no reads are added after early termination.

For a leaf $t$, let $k_t$ be the number of its read ancestors, and let $e_t$ be their final epoch, taking $e_t=N$ for a root halt. Define

$$
 d_t=e_t-N,\qquad
 L_t(\mathbf s)=\sum_{v\prec t}(\delta_{b_v}+|s_v|),\qquad
 \operatorname{Path}_t(X;\mathbf s)
 =\bigwedge_{v\prec t}\operatorname{Reply}_{c(v,t)}
                          (X_{b_v,m_v},s_v).
\tag{JRF.4.1}
$$

Here $c(v,t)$ is the edge reply on the path to $t$. Empty paths have the usual empty conjunction and zero costs. Say the skeleton is correct when

$$
 \forall X\,\forall Y\,
 \left[(\operatorname{Adm}(X)\land\operatorname{Adm}(Y))
 \Longrightarrow
 \bigwedge_t
 \left((\operatorname{Path}_t(X;\mathbf s)\land
        \operatorname{Path}_t(Y;\mathbf s))
       \Longrightarrow\operatorname{SameRow}(X,Y)\right)\right].
\tag{JRF.4.2}
$$

All skeleton choices and all $s_v$ are chosen before the universal source quantifiers. Only already acquired replies select which vertex is visited. A leaf is reachable precisely when $\exists X\,(\operatorname{Adm}(X)\land\operatorname{Path}_t(X;\mathbf s))$.

**Theorem 4.3 (two exact budget decision procedures).** Under GB, for every $k,d,L\in\mathbb N$ it is decidable whether there is a correct service with

$$
 \sup_D q_A\le k,\quad\sup_D d_A\le d,
\tag{JRF.4.3}
$$

and it is decidable whether there is a correct service with

$$
 b(A)\le(k,d,L).
\tag{JRF.4.4}
$$

In each true case a finite actual attaining-within-budget service is effectively constructible. The first decision leaves address lengths entirely unbounded. These decisions cover every comparator in Definition 1.2, including arbitrary reply-dependent serial schedules and pointwise finite local work.

Proof. First consider (JRF.4.3). Enumerate the finitely many skeleton shapes of read depth at most $k$, class labels, and monotone epochs at most $N+\min(d,U)$. For each, existentially quantify its finitely many $s_v$ in (JRF.4.2). The resulting finite disjunction is a WS2S sentence. No length comparison between address variables is used. It is decidable by the logic suppliers in §10.

For necessity, take any comparator satisfying (JRF.4.3), apply Theorem 3.1 and Lemma 3.4, and remove terminal updates after the last read by computing the same output locally before halting. These changes preserve correctness and do not increase either budget. At each reachable reply prefix, the subsequent local work, simulated events, and actual updates up to the next read or halt form one fixed finite segment. It is fixed because all source-dependent acquired inputs agree; it is finite because at least one source reaches that prefix and the comparator terminates there. There are at most $1+4+\cdots+4^k$ reply prefixes. Thus its reachable control unrolls to a finite skeleton with fixed finite suffixes and legal monotone epochs. This is an existence argument for an arbitrary program; it does not assume an algorithm deciding reachability in arbitrary code.

At a reachable early halt, retain a halt. At an unreachable reply child, install an immediate halt. No padding is necessary. Two sources reaching the same halt must have the same full output, so (JRF.4.2) holds. All source assignments in that formula correspond to actual sources in $D$, with every old guard, repetition, and disequality still present. Hence the sentence is true.

For sufficiency, extract a satisfying skeleton and finite suffix tuple. This is effective: after a positive decision, enumerate finite tuples and test (JRF.4.2) with the suffixes fixed until a witness is found. Every test terminates and a witness exists. Alternatively, extract singleton-marked address witnesses from its finite tree automaton. For each leaf, add its chosen physical epoch/address/reply constraints to the whole original $R,H$. SLH Theorem 61.1 decides reachability and, when nonempty, supplies a finite source witness. Compute that witness's full $Q$ row. Equation (JRF.4.2) makes the row independent of the witness, so it is the correct constant terminal output. Unreachable leaves receive any fixed output.

Install this finite table. Execute the actual nonnegative epoch differences and actual physical reads in order. Induction on the reply path shows that the actual source satisfies its path formula and reaches a nonempty leaf, where the output is its original row. Every run has at most $k$ reads and at most $d$ updates and is finite. Hypothetical chains and leaf witnesses are used to construct the program; they are not extra accessible source registers or knowledge of the actual source.

For (JRF.4.4), use the same necessity construction, which also does not increase length by Lemmas 2.2 and 3.4. In every reachable read, $\delta_{b_v}+|s_v|\le L$. Enumerate these finitely many literal suffixes and skeletons, rather than unrestricted variables. Test correctness and require $L_t\le L$ on each reachable leaf, using the same joint reachability decision. Unreachable branches impose no cost constraint. Conversely a passing tree implements the displayed costs exactly on each reachable path. This is a finite decision procedure and constructs a service. If $B=\varnothing$, $D=\{C\}$ and a zero-cost root halt settles both tests directly. $\square$

**Corollary 4.4 (exact costs of a finite service).** Every constructed finite service has effectively computable sourcewise path costs and exact coordinatewise worst budgets. For each coordinate maximum, an actual source attaining it can be produced. A maximum of a weighted sum is computed by summing on each reachable leaf and then maximizing; it too has an actual-source witness. Different coordinate maxima need not have a common witness.

Proof. There are finitely many leaves, each has the fixed cost $(k_t,d_t,L_t)$, and exact reachability with a source witness is decidable. Remove empty leaves from the numerical maximum. Every remaining cost is realized by its source witness, and every source follows one remaining leaf. $D\ne\varnothing$ guarantees at least one such leaf. $\square$

## 5. An effective complete finite Pareto basis

**Definition 5.1 (one static supplier and a finite read bound).** When GB holds, choose the actual finite static service supplied by SLH §74. From its finite probe set and read bound compute any finite upper budgets

$$
 (K_0,0,L_0),\qquad K_0,L_0\in\mathbb N.
\tag{JRF.5.1}
$$

For example, use SLH (74.6) for $K_0$ and multiply it by the maximum physical address length in its finite template and prefix menus for $L_0$. Their addresses include original-hole prefixes. A sharper value is unnecessary. Set

$$
 K=\max(K_0,L_0+s_N).
\tag{JRF.5.2}
$$

Neither $K_0$ nor $L_0$ is asserted optimal.

**Lemma 5.2 (a finite rectangle cofinal for worst budgets).** Every correct comparator whose worst budget vector is finite is weakly dominated in worst budgets by a correct finite service with read budget at most $K$ and update budget at most $U$.

Proof. Apply Theorem 3.1, then Lemma 3.2, to obtain $A'$ with $b(A')\le b(A)$ and $\sup_D d_{A'}\le U$. Write its finite worst read and length costs as $q'$ and $L'$. Equation (JRF.3.3) gives $q'\le L'+s_N$.

If $q'\le K$, unroll its finite reachable reply tree as in Theorem 4.3. Its addresses and epoch segments are finite, and the resulting finite service has no larger costs. If $q'>K$, then $q'>K_0$ and $L'\ge q'-s_N>L_0$. The static supplier (JRF.5.1) therefore has no larger worst cost in any coordinate. It has read budget at most $K$ and zero updates. This branch compares maxima; it does not assert that the supplier is cheaper on each individual source. $\square$

**Theorem 5.3 (complete effective joint feasible region and attainment).** For every input of Assumption 1.1 an effective algorithm has the following outcome.

If GB fails, $\mathcal F=\varnothing$. If GB holds, it returns a nonempty finite set $\mathcal B\subseteq\mathbb N^3$ with

$$
 \boxed{\quad
 \mathcal F=\{b\in\mathbb N^3:\exists v\in\mathcal B,\ v\le b\},
 \qquad \mathcal B=\operatorname{Min}(\mathcal F).
 \quad}
\tag{JRF.5.3}
$$

For each $v\in\mathcal B$ it returns a finite actual serial service $A_v$ with $b(A_v)=v$ exactly, together with physical addresses, halt outputs, and source witnesses for each coordinate maximum. Its correctness is on the entire original $D$. The algorithm has a proved stopping rule and requires no guessed address or source cutoff.

Proof. Decide GB. Failure excludes finite raw budgets, hence excludes every finite triple. Suppose GB holds and calculate $K,U$ from §§3 and 5. There are finitely many pairs

$$
 0\le k\le K,\qquad 0\le d\le U.
\tag{JRF.5.4}
$$

For each pair, use the unbounded-address decision of Theorem 4.3 to decide (JRF.4.3). Discard false pairs. For every true pair, extract a finite service and compute its finite worst address cost $L^{\rm wit}_{k,d}$. Use the second decision of Theorem 4.3 over the finite interval $0\le L\le L^{\rm wit}_{k,d}$ to find

$$
 L_{k,d}=\min\{L\in\mathbb N:(k,d,L)\in\mathcal F\}.
\tag{JRF.5.5}
$$

Retain a witness service for each true minimum. The crucial order is the decision of existence with no address bound, followed only in true cases by witness extraction and a bounded integer search. False cases never enter an unbounded witness enumeration. Every invoked logical decision terminates, every true existence has a finite witness, and there are finitely many pairs and finitely many integer tests per pair. This proves effective termination.

Let $\mathcal V$ be the finite set of triples $(k,d,L_{k,d})$ retained. It is nonempty because the static supplier fits the grid. Every element is a feasible upper budget. Conversely, let $b\in\mathcal F$ and choose any service with $b(A)\le b$. Lemma 5.2 supplies a correct service with finite worst vector $(k',d',L')\le b$, where $(k',d')$ lies in (JRF.5.4). That pair is true and $L_{k',d'}\le L'$. Thus some member of $\mathcal V$ is at most $b$. Since a finite set has a minimal member below each of its members, $\mathcal B=\operatorname{Min}(\mathcal V)$ gives the equality of upsets in (JRF.5.3). A minimal member of one of these equal upsets is a minimal member of the other, proving the second equality.

For $v\in\mathcal B$, the retained witness service satisfies $b(A_v)\le v$. Its exact worst vector is itself a feasible budget. A strict inequality in any coordinate would contradict minimality of $v$, so equality holds. Corollary 4.4 supplies all requested maxima and witnesses. The three maximizing sources can be different. $\square$

**Corollary 5.4 (a finite family of genuine whole-fiber services).** When GB holds, the finitely many services $A_v$ are cofinal for coordinatewise finite worst budgets: every allowed finite-budget comparator is weakly dominated in those budgets by one of them. Taking the union of their finite epoch/address menus gives a finite menu that realizes the whole Pareto basis.

Proof. Apply (JRF.5.3) to $b(A)$ and use $b(A_v)=v$. Menu union preserves each included service. The menu is obtained only after comparison with all permitted strategies in Theorems 3.1, 4.3, and 5.3. It is not a restriction assumed in the lower bound. $\square$

The finite family does not replicate every original sourcewise profile, every original trace, or every timing record. Theorem 3.1 gives sourcewise dominance by an effective transformation depending on the comparator. Theorem 5.3 gives a comparator-independent finite basis only after taking coordinate suprema. Nor does (JRF.5.3) assert that every upper triple can be attained with three independently adjustable exact costs: literal lengths, reads, and updates remain coupled by actual actions.

**Corollary 5.5 (upper budgets with infinite coordinates).** Define $\overline{\mathcal F}$ as in (JRF.1.3), allowing budget coordinates in $\overline{\mathbb N}=\mathbb N\cup\{\infty\}$. If GB holds, then

$$
 \overline{\mathcal F}
 =\{b\in\overline{\mathbb N}^{\,3}:\exists v\in\mathcal B,\ v\le b\}.
\tag{JRF.5.6}
$$

If GB fails, then

$$
 \overline{\mathcal F}
 =\{(\infty,d,\infty):d\in\overline{\mathbb N}\},
\tag{JRF.5.7}
$$

whose unique minimal extended budget $(\infty,0,\infty)$ is attained by a pointwise terminating static service.

Proof. If GB holds and a service meets an extended budget with a finite read coordinate, its finite reachable reply tree has only finitely many addresses and finite deterministic update segments. It thus has finite worst costs in all three coordinates, irrespective of whether those other coordinates were constrained. Theorem 5.3 supplies a basis member below its actual vector. If the length coordinate is finite instead, first apply Theorem 3.1 and Lemma 3.2. These transformations preserve every finite coordinate constraint and give a finite read bound, reducing to the preceding case. If both the read and length budgets are infinite, the static supplier (JRF.5.1) satisfies the budget for every nonnegative update bound, and some basis member lies below it. The reverse inclusion follows by executing the basis service.

If GB fails, Corollary 3.3 forces both indicated infinite coordinates for every correct service. The static whole-original-tree traversal described in Theorem 7.1 has zero updates and terminates on every finite source, giving the reverse inclusion and attainment. Its construction uses the historical literal decoder and does not depend on this corollary. $\square$

## 6. Finite whole-source games and the common-realization requirement

**Proposition 6.1 (exact joint tables for a supplied finite menu).** Suppose GB holds and $\mathcal M$ is any finite menu of actual epoch/address pairs in $[N,M]$. One can effectively construct exactly

$$
 \mathcal J(\mathcal M)=
 \left\{\left(R_Q(u),
       (r_{\rho^m u}(p))_{(m,p)\in\mathcal M}\right):u\in D\right\},
\tag{JRF.6.1}
$$

and give a common original-source witness for each of its rows. The table can be used as a finite source quotient for services restricted to $\mathcal M$, with the actual epoch retained as part of the game state. Its terminal condition is constancy of the full original row.

Proof. For each of the finitely many candidate reply vectors and each $r\in\mathscr R$, test their conjunction with $\operatorname{Adm}(X)$ and $\operatorname{Row}_r(X)$. Fixed physical requests are expressed using their unique old-hole prefix and fixed suffix, or $\chi_C$ outside holes. This is a WS2S formula. Its nonemptiness has exactly the joint-source meaning in (JRF.6.1), not separate marginal feasibility. A witness assignment fills $C$ with class trees and yields the actual source. Equivalently, use SCR's finite original-prefix partition and SLH Theorem 61.1, imposing the whole vector at once.

Each actual source produces one table row. If a program makes a legal monotone sequence of menu requests, induction on the acquired replies shows that its surviving table rows are exactly the images of compatible sources in $D$. The actual epoch forbids moving backward even when an earlier-epoch column remains in the table. Read action $(m,p)$ after epoch $j\le m$ costs $(1,m-j,|p|)$; its update part is physically performed before that read. A halt costs zero further actions and is allowed for a constant target value. Thus a finite legal strategy tree translates both ways with exactly the same costs on the corresponding sources. $\square$

The finite rows in (JRF.6.1) are observations of the whole fiber, not a supplied finite prototype promise. A row's source witness is a mathematical realization of a joint profile and is never substituted for the unknown actual source. Refining this table to identify its individual rows is not required when several rows have the same original $Q$ row.

## 7. Exact rational weighted worst-run prices, including zero weights

**Theorem 7.1 (effective weighted minimization and an actual minimizer).** For every rational $\lambda\ge0$, (JRF.1.4) has an effectively computable value in $\mathbb Q_{\ge0}\cup\{\infty\}$ and a correct actual service attaining it.

1. If $\lambda_q=\lambda_\ell=0$, then $W_\lambda^*=0$, whether or not GB holds.
2. If $\lambda_q+\lambda_\ell>0$ and GB fails, then $W_\lambda^*=\infty$; each individual source still admits finite termination, and a static whole-source recovery service attains this infinite supremum.
3. If GB holds, a finite actual reply tree attaining $W_\lambda^*$ can be effectively constructed. Its criterion is the same-source sum in (JRF.1.4), not a weighted sum of separate worst coordinates. This remains true when one or two weights vanish.

Proof. First supply a pointwise total static service for every input, regardless of GB. At epoch $N$, use SLH Theorem 2.2's finite historical literal decoder to traverse the original tree: decode the original root, recurse on the children only after an original branch is confirmed, and terminate each original leaf. Each decode needs at most two current reads. Every actual original tree is finite, so the traversal terminates and recovers a finite exact description. Compute its full $Q$ row and halt. No actual update occurs and no original raw receipt is fabricated. Thus when only updates have positive weight the value is zero. This also covers the all-zero weight vector. When GB holds, the finite static supplier of Definition 5.1 attains the same zero value, so a finite reply tree is available in this case as well.

If GB fails and $\lambda_q>0$, every service has unbounded raw cost by SLH Theorem 74.4, so every weighted supremum is infinite. If instead $\lambda_\ell>0$, Corollary 3.3 gives the same conclusion from unbounded length. The static service just constructed attains the infinite supremum. This does not claim an infinite run on a finite source.

Now suppose GB holds and $\lambda_q+\lambda_\ell>0$. The supplier (JRF.5.1) gives the finite rational upper bound

$$
 B_0=\lambda_qK_0+\lambda_\ell L_0.
\tag{JRF.7.1}
$$

The transformations of Theorem 3.1 and Lemma 3.2 dominate costs on each same source; consequently they do not increase $W_\lambda$. It suffices to compare services with actual updates at most $U$. A comparator with weighted cost at most $B_0$ can also be given a finite raw-depth bound. If $\lambda_q>0$, take

$$
 k_\lambda=\left\lfloor B_0/\lambda_q\right\rfloor.
\tag{JRF.7.2}
$$

Every individual raw count is bounded by this integer. If $\lambda_q=0$ and $\lambda_\ell>0$, first clean by Lemma 3.2 and take

$$
 L_\lambda=\left\lfloor B_0/\lambda_\ell\right\rfloor,
 \qquad k_\lambda=L_\lambda+s_N.
\tag{JRF.7.3}
$$

When both weights are positive, (JRF.7.2) suffices for depth and $L_\lambda$ as defined in (JRF.7.3) also bounds length. Applying Lemma 3.4 if needed only decreases the same-source sum.

For a rational threshold $z\in[0,B_0]$, decide whether a skeleton of depth at most $k_\lambda$ has correctness (JRF.4.2) and, on every reachable leaf,

$$
 \lambda_q k_t+\lambda_d d_t+\lambda_\ell L_t\le z.
\tag{JRF.7.4}
$$

If $\lambda_\ell>0$, enumerate the finite physical addresses with length at most $L_\lambda$ and test (JRF.7.4) with exact leaf reachability, as in Theorem 4.3. If $\lambda_\ell=0$, then $\lambda_q>0$. For every fixed skeleton shape and epoch/class labeling, the left side of (JRF.7.4) is independent of the suffix variables. For each leaf violating that numerical inequality, add

$$
 \neg\exists X\,(\operatorname{Adm}(X)\land
                        \operatorname{Path}_t(X;\mathbf s))
\tag{JRF.7.5}
$$

to the WS2S formula. Existentially quantify the arbitrary suffixes. There are finitely many skeleton choices; thus this is a decidable unbounded-address test. A true formula has an effectively extractable witness and actual terminal outputs exactly as in Theorem 4.3. Neither case penalizes an unreachable leaf.

These tests have both operational directions. Any comparator satisfying the threshold can be normalized and unrolled within the displayed bounds, with no increase of its same-source costs, and therefore passes a test. Conversely a passing skeleton is executed by the actual service of §4; each source follows a reachable leaf, where its real sum satisfies (JRF.7.4). This proves threshold equivalence against all allowed comparators.

Take a positive common denominator $a$ for the three weights. Each finite run's weighted sum belongs to $a^{-1}\mathbb N$. A bounded nonempty subset of this lattice has a maximum in the same lattice. Therefore every finite $W_\lambda(A)\le B_0$ lies on that lattice. Decide the finitely many thresholds $0,1/a,\ldots,B_0$ in order; $aB_0$ is an integer and the supplier guarantees a true test by the last value. Extract a service at the first true threshold. A smaller weighted value would be a smaller lattice threshold with a true test, a contradiction. This proves exact minimization and attainment. Corollary 4.4 gives an actual source attaining the finite weighted maximum. $\square$

The finite family in §5 is not used to minimize (JRF.1.4): a service with a worse vector of separate maxima can have a better same-source weighted sum. The weighted construction preserves joint path costs throughout. Finite logical effectiveness gives no claim of a practical optimizer or a bound on installation, working memory, or physical running time.

## 8. A whole-fiber update/read tradeoff and two invalid shortcuts

**Theorem 8.1 (an exact two-point joint frontier on an infinite admitted fiber).** Take the acquired single-root-hole row, the actual history $H=((0,RL,\mathsf{absent}))$, authenticated entry $N=0$, and original recut $Q=\{L\}$. The entire admitted fiber and its full outputs are

$$
 D=\{\alpha,\beta\}\cup
       \{\langle x,\alpha\rangle:x\in\mathcal T\}\cup
       \{\langle x,\beta\rangle:x\in\mathcal T\},
\tag{JRF.8.1}
$$

$$
 r_\alpha=\alpha,\quad r_\beta=\beta,\quad
 r_{L\alpha}=\langle\square_1,\alpha\rangle,\quad
 r_{L\beta}=\langle\square_1,\beta\rangle,
\tag{JRF.8.2}
$$

with the unique one-hole equality partition in the latter two rows. Its Pareto basis for actual calls, actual updates, and literal length is exactly

$$
 \mathcal B=\{(2,0,1),(1,1,1)\}.
\tag{JRF.8.3}
$$

Proof. SCR Theorem 7.2 establishes (JRF.8.1) as an entire-fiber equality: a root leaf makes $RL$ absent, and a branch has $RL$ absent exactly when its right child is a leaf. It also establishes the four distinct complete rows and the arbitrary-address one-read lower bound at epoch zero.

For the first vector, read the root at epoch zero. A leaf reply determines its concrete no-hole row and halts; a branch reply is followed by a read at $R$ and the appropriate one-hole row. The worst costs are exactly $(2,0,1)$ on this whole fiber. For the second vector, perform one actual update and read $R$. In the order of (JRF.8.2), its replies are

$$
 (\mathsf{absent},\alpha,\beta,\mathsf{branch}),
\tag{JRF.8.4}
$$

so one read of a length-one address identifies the complete row. Its costs are $(1,1,1)$ on every source.

Every correct service needs at least one new read: without a new reply, common control and updates give the same output on the four different rows. Every correct service also needs a nonempty address on at least one source. Indeed choose the same $x$ in $\langle x,\alpha\rangle$ and $\langle x,\beta\rangle$. Every root reply at every epoch is branch for both. If a service used only root reads on all sources, induction through its reply-dependent actions would give the same finite output on these two sources, contrary to their different rows. Thus every finite feasible budget has $q\ge1$ and $L\ge1$.

If its update budget is zero, it is static at epoch zero, so SCR Theorem 7.2 forces $q\ge2$ and the first vector dominates its budget. If its update budget is positive, it is at least one, and the second vector dominates its budget. The two displayed feasible vectors are incomparable, proving (JRF.8.3) and its complete coverage of all reply-dependent schedules. The arbitrary $x$ has no size or depth bound. $\square$

**Example 8.2 (raw-only normalization changes charged costs).** On the fiber of Theorem 8.1, the one-update one-read service has actual costs $(1,1,1)$. SCR Theorem 3.1's epoch-zero-to-five normalization instead makes five actual updates. Its transported epoch-one probe at $R$ is

$$
 T(1,5,R)=RZ^{\rm SCR}_R(4)=RLLR,
$$

using SCR's $Z^{\rm SCR}_R(t)=L^{t-2}R$. Its costs are $(1,5,4)$. Replies and output are preserved, but both new resource coordinates increase. Likewise, directly using the least-index old-class representative in place of a shorter occurrence can increase literal cost, as Lemma 3.4's example shows. Theorem 3.1 here retains the first service's epoch-one decision and does not force an early move to five.

**Example 8.3 (maxima of different runs cannot be added).** On the same whole fiber, consider the following correct service. Read the epoch-zero root. If it is a leaf, perform two actual updates, then halt with the already known concrete row. If it is a branch, read $R$ at epoch zero and halt with the one-hole row. Its sourcewise costs are

$$
 c_A(u)=
 \begin{cases}
 (1,2,0),&u\in\{\alpha,\beta\},\\
 (2,0,1),&u=\langle x,\alpha\rangle\text{ or }\langle x,\beta\rangle.
 \end{cases}
\tag{JRF.8.5}
$$

The updates in the first case precede the genuine halt; no stopped service is resumed. With weights $(1,1,1)$ the same-source maximum is three, whereas the sum of separate coordinate maxima is $2+2+1=5$. Each maximum in the latter expression is individually real, but they cannot be combined into one actual run. The example illustrates the distinction between the objectives; it does not assert that this particular service is Pareto minimal.

## 9. Infinite cases, retained boundaries, and the recovered relation

**Proposition 9.1 (degenerate and infinite cases).** The following statements use the same target and admission domain as the main theorems.

1. If there are no reached old holes, $D=\{C\}$ and the Pareto basis is $\{(0,0,0)\}$. If $R_Q$ is constant on $D$, the same basis holds. Conversely, any correct zero-read service forces that constancy, even if it performs updates.
2. $Q=\{\varepsilon\}$ gives a constant single-root-hole row. $Q=\varnothing$ requires the complete original tree, with its actual GB classification; it does not mean an empty task.
3. If GB fails, every correct service has infinite worst raw and address costs, while there is a correct static pointwise terminating service with budget vector $(\infty,0,\infty)$. No finite Pareto vector exists. A finite output image alone does not imply GB.

Proof. The zero-hole claim follows from SLH Theorem 59.4. For constant output, a common source witness supplies that known value and a root halt has zero cost. For the converse, without a new source reply all choices and the final output are fixed by the common entry; updates give no additional information. The interpretation of the two $Q$ cases is the original row definition. Corollary 3.3 and the static traversal in Theorem 7.1 give the third assertion. SLH Example 75.2 supplies a source-faithful finite-output obstruction: the whole fiber $\{\langle z,z\rangle:z\in\mathcal T\}$, recut at $LL,LR,RL,RR$, has four complete rows but arbitrarily deep legal sources with identical finite original prefixes and different new partitions. Its old repeated class is retained, and GB fails. $\square$

**Proposition 9.2 (what the operational relation recovers).** Under GB, the retained whole-fiber relation and full original-row task determine exactly the finite upper-budget feasibility relation (JRF.5.3) and every rational weighted worst-run value (JRF.1.4), with actual attaining services under the stated paid interfaces. This does not recover the actual historical action sequence from the output row, nor the original source from a noninjective row.

Proof. Theorems 5.3 and 7.1 supply the first claim. The two services in Theorem 8.1 return the same row on each source and have different actual update/read records, so the row cannot determine which record occurred. For any fixed right leaf, all trees $\langle x,\alpha\rangle$ in (JRF.8.1) have the same $Q$ row and arbitrarily different $x$. Thus that row does not determine the original source. $\square$

**Proposition 9.3 (a new retention cut requires its own interface).** After obtaining $r=R_Q(u)$, suppose a separately supplied retention operation makes the entire accessible source-related state precisely a recoverable encoding of $r$ and common installation. Relative to the original entry, the new source fiber is exactly

$$
 D\cap R_Q^{-1}(r).
\tag{JRF.9.1}
$$

If acquired receipts, old $R,H$, simulation state, allocation lengths, or other distinctions remain accessible, their conditions must also be intersected. None of the cost theorems supplies that forgetting operation or a global producer that enlarges (JRF.9.1) to all trees with row $r$.

Proof. This is SCR Proposition 8.1 and SLH Proposition 68.3 under the same complete-access condition. Membership in the old entry forces $u\in D$, and recovery of $r$ forces its row equation. Conversely, under the stipulated access restriction any source in that intersection produces the same complete new state. Further accessible distinctions can only refine it. The services of this volume actually perform their reads and updates, but their output correctness alone does not certify the additional access restriction. $\square$

The relation added here is operational: a late probe can be represented at a bounded actual epoch without increasing any charged coordinate, while early time decisions remain available. The root/length relation then makes complete finite frontier recovery effective. Direct reuse of raw minimax gives neither relation. A transport lemma alone would leave the unbounded-address stopping obligation, and a mere finite-budget decision would leave the unknown Pareto search horizon. Theorems 4.3 and 5.3 join these missing directions. Leaving the raw result unchanged gives no test for the budgets in Theorem 8.1; this companion gives that test without replacing the source fiber or boundary task. It establishes this recovery relation for the three specified resources, not a general equivalence between physical space, elapsed time, memory, and boundary.

## 10. Sources, exact reuse contracts, and mathematical scope

**References 10.1 (ordinary source results and logic).** Repository citations in this volume refer to the fixed source snapshot [218be7281172af6782430b48a638e2bef2075e10](https://github.com/the-omega-institute/trureturing/tree/218be7281172af6782430b48a638e2bef2075e10).

| Source | Statement used and applicability boundary |
| --- | --- |
| [SCR, §§1–8](https://github.com/the-omega-institute/trureturing/blob/218be7281172af6782430b48a638e2bef2075e10/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md) | Entire-row serial contract; §2 guarded positive-epoch reply formula; §4 exact finite row predicates after GB; §5 source/strategy logic; §7 whole-fiber example and static raw lower bound; §8 retention boundary. Its raw-only normalization is not a joint-cost supplier. |
| [SLH, §§59–62, 69, 74–75](https://github.com/the-omega-institute/trureturing/blob/218be7281172af6782430b48a638e2bef2075e10/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md) | Full acquired rows and guards, classwise transport, joint feasibility, complete actual-control handoff, ground-binding finite-budget classification, finite physical static supplier, and native infinite-budget obstructions. §52.2 supplies the all-source constant-root threshold; §47 instead fixes an expansion-bit family and a source-independent supplied epoch schedule with static segments. Its exact cumulative read/address result does not optimize the present reply-dependent updates. |
| [JOINT_MOMENT_FIBERS, §§28–30](https://github.com/the-omega-institute/trureturing/blob/218be7281172af6782430b48a638e2bef2075e10/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md) | Full-source leaf-sensitive tasks with costs evaluated on finitely many supplied public prototypes, using distinct addresses. Its prototype response core does not supply a finite source promise or serial raw-call frontier here. |
| N. Klarlund and A. Møller, [MONA Version 1.4 User Manual, §§7.1–7.2, pp. 39–40](https://www.brics.dk/mona/mona14.pdf) | `literature-attested`: first-order positions in the infinite binary address tree, finite sets of positions, and bottom-up tree-automaton decision and counterexample machinery for WS2S. No uniform size bound on the quantified finite source sets is required. These sections supply logic, not an actual free-tree cost correspondence. |
| H. Comon et al., [Tree Automata Techniques and Applications, 2008 author version, HAL v1](https://inria.hal.science/hal-03367725v1/document), Lemma 3.3.4, Theorem 3.3.8, Corollary 1.2.3 | `literature-attested`: effective recognizable encodings of definable tuples of finite subsets of the successor tree; WSkS decidability; a nonempty finite tree automaton has an accepted term of height at most its state count. First-order suffixes can be singleton tracks. The height bound applies to a formula's witness encoding, not to unknown sources in $D$. |

The bounded source comparison above establishes the stated reuse contracts, not a global absence or priority claim. The cost-preserving late-probe relation, capped operational simulation, effective finite budget rectangle and frontier extraction, and separate same-source weighted construction are `repo-derived` ordinary consequences proved in this volume. Generic finite decision-tree optimization, integer minimization, and automaton decidability are established suppliers. No global novelty claim is attached to them or to their use here.

**References 10.2 (formal declarations and their different contracts).** The public and private source statements below provide relevant existing interfaces; no compiled application of them to the present theorems is asserted.

| Pinned declaration source | Exact boundary |
| --- | --- |
| [ActualTreeReadoutAcquisition](https://github.com/the-omega-institute/trureturing/blob/218be7281172af6782430b48a638e2bef2075e10/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean), `readout`, `Policy`, `paid`, `source_foundation` | Four literal replies at every finite address; fixed-source query-or-Boolean policies; `paid` is the set of distinct addresses. `source_foundation` includes full labelled-leaf rigidity and third-image membership obligations. It does not define actual interleaved updates or the three costs here. |
| [ActualExactSupportPruning](https://github.com/the-omega-institute/trureturing/blob/218be7281172af6782430b48a638e2bef2075e10/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.lean), `support_pruning_contract`, private `old_prefix`, `new_prefix`, `prescribed_actual_support` | Fixed-source actual-prefix and cache preservation from a supplied support and admissibility contract. Exact prescribed supports use the owning bounded allowed-source domain. This is not a uniform source cutoff for (JRF.1.1). |
| [ActualExactTraceCompiler](https://github.com/the-omega-institute/trureturing/blob/218be7281172af6782430b48a638e2bef2075e10/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.lean), `strategy_exact_run`, `strategy_admissible`, private `exact_actual_prefix_replay`, `execute_suffix` | Exact fixed-$U$ traces, coarse-factorizing policies, supplied replay hypotheses, and the owning allowed-source domain. These are stronger trace requirements in a different action model; they do not turn a simulated late event into a current receipt. |
| [ActualJointResponseCostCore](https://github.com/the-omega-institute/trureturing/blob/218be7281172af6782430b48a638e2bef2075e10/D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.lean), `representative`, `Recipe`, private `normalization_foundation`, `result` | Shortlex representatives of actual full response vectors and a finite cost core on a nonempty injective family of positive prototypes, under fixed-source globally correct membership strategies and distinct-address cost. The finite evaluated prototype family is not the present entire fiber. |

Stationary common-law Borel kernels and full endpoint boxes in the adjacent late-contact setting, and calibrated full cyclic-signal bispectra with nonvanishing Fourier amplitudes and uniform error in the bispectrum setting, have no supplied actual-source/action/cost correspondence to Assumption 1.1. Their identifiability or stability statements therefore do not transfer this frontier to those models.

The universal statements here rest on the displayed ordinary proofs and the cited ordinary suppliers. Finite diagnostics cannot establish their whole-domain quantifiers; there is no Lean proof, implemented decision procedure, complexity guarantee, or measured physical-cost theorem in this volume. Actual installation, local computation, literal address generation, working memory, receipt preservation, authentication, retention, and future handoff remain separately supplied and charged interfaces.

## 追加锚（本行以下为增补区）

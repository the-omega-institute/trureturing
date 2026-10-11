# Recovery of intrinsic depth from a retained relational row

> **本卷的机器契约。** This is a `generic-v1` theory volume and a reference input. Lean declarations and their accepted axiom closures remain the mathematical source of truth. The volume is append-only; the anchor at the end is the boundary for later additions. No statement below is presented as kernel-verified.

## 1. Contract, source and retained row

**定义 1.1（原来源与原生读口）。** The source domain is the set $\mathcal T$ of all nonempty finite free ordered binary trees

$$
T ::= \alpha\mid\beta\mid (S,T).
$$

The native operation is

$$
\rho(\alpha)=\beta,\qquad \rho(\beta)=(\beta,\alpha),\qquad
\rho((S,T))=(\rho(S),\rho(T)).
$$

Put $I_n=\rho^n[\mathcal T]$ and $\nu(t)=\max\{n:t\in I_n\}$. Thus $\nu$ is maximal inverse-generation depth of the current tree. It is not an entrance count, an elapsed time, or a clock reading. A legal request is any finite absolute word $q\in\{L,R\}^*$, including a word that skips an ancestor. Its reply is one of $\alpha,\beta,\mathsf{br},\mathsf{abs}$ according to the static tree, with absent replies below leaves.

**假设 1.2（实际取得的完整 row handoff）。** A single common producer starts from the prescribed source-independent initial condition, fully acquires one current source $u$, and hands off a public finite prefix-free cut $P$. The producer computes the exterior shape $C$ and the complete equality partition $\pi$ of the cut values. Repeated classes receive one common value and distinct classes receive unequal values. At handoff every accessible source-dependent field, including handles, lengths, control positions, old archives and timing, factors through

$$
R=(C,\pi).
$$

The source is stationary after handoff. The row is an actual image of this producer; it is not a combination of observations obtained from different sources. The row-only fiber is

$$
U_R=\{C[(z_b)_{b\in B}] : z_b\in\mathcal T,\ z_b\ne z_c\text{ for }b\ne c\},
\tag{RDR.1}
$$

where $B$ is the finite set of equality classes and every occurrence of class $b$ is filled by the same $z_b$. There is no retained literal, signed, clock, source-label or history field in $R$.

**定义 1.3（根深度服务）。** A row-only consumer receives $R$ and common installed data, may perform local computation, and may make static native `Read(q)` requests with the four replies above. It has no equality, image-membership, update, stream, reroot, clock or source-selection oracle. A service is *row-uniform with bound $K_R$* when one deterministic effective consumer halts on every $u\in U_R$, returns $\nu(u)$, and makes at most $K_R$ new reads. Maximum queried word length, total submitted word length, producer work, retained memory, local computation and elapsed time are separate resources.

The exact row correspondence in (RDR.1) is the supplied common-producer result. The present volume studies the remaining root task after class values have been forgotten.

## 2. The finite class summary and its exact joint image

**定义 2.1（atomic ray and $Q$ summary）。** Let

$$
T_n=\rho^n(\alpha),\qquad e(t)=1\ \Longleftrightarrow\ t=T_n\text{ for some }n,
\qquad Q(t)=(\nu(t),e(t)).
$$

The existing pair law is

$$
Q((s,t))=
\begin{cases}
(b+2,1),&Q(s)=(a,1),\ Q(t)=(b,1),\ a=b+1,\\
(\min(a,b),0),&\text{otherwise}.
\end{cases}
\tag{RDR.2}
$$

For the finite exterior $C$, let $E_C$ be bottom-up evaluation of (RDR.2), with $\alpha=(0,1)$, $\beta=(1,1)$, and one shared variable $(a_b,e_b)$ for every old class $b$.

**定理 2.2（全等式、全不等式下的 class-summary correspondence）。** A tuple $((a_b,e_b))_{b\in B}\in(\mathbb N_0\times\{0,1\})^B$ is realized by pairwise distinct class trees exactly when

$$
 b\ne c,\ e_b=e_c=1\ \Longrightarrow\ a_b\ne a_c.
\tag{RDR.3}
$$

Consequently the exact attainable root-depth spectrum is

$$
\Sigma_R=\{\nu(u):u\in U_R\}
 =\{\operatorname{first}(E_C((a_b,e_b)_b)):\text{(RDR.3) holds}\}.
\tag{RDR.4}
$$

**证明。** Every atomic summary $(n,1)$ is the single tree $T_n$, so two distinct classes cannot share it; this proves necessity. For sufficiency, assign $T_{a_b}$ to every flag-one class. For a flag-zero class choose a nonleaf all-$\alpha$ primitive tree $p_b$; distinct classes at equal depth use distinct shapes, and assign $z_b=\rho^{a_b}(p_b)$. Primitive-ray uniqueness makes values with different depths unequal, injectivity of $\rho$ keeps distinct seeds unequal at equal depth, and a primitive endpoint cannot equal the atomic endpoint $\alpha$. Repeated occurrences reuse the selected value. The exact row-fiber correspondence then fills one actual source of the same producer, with every required disequality. Evaluating its root by the supplied pair law gives (RDR.4). This is a joint realization of one source, not independent evidence pasted together. $\square$

## 3. Exact spectrum and a finite construction when a concrete leaf remains

**定理 3.1（leafless/unbounded and anchored/bounded alternatives）。** If $C$ has no concrete $\alpha$ or $\beta$ leaf, then $\Sigma_R=\mathbb N_0$. If $q$ is a concrete leaf of $C$ at address length $d$ and label $\lambda$, put

$$
K_q=2d+\mathbf 1_{\lambda=\beta},\qquad K=\min_q K_q.
\tag{RDR.5}
$$

Then $\Sigma_R$ is nonempty and $\Sigma_R\subseteq\{0,\ldots,K\}$. The finite spectrum can have gaps.

**证明。** In the leafless case choose distinct nonleaf all-$\alpha$ primitive seeds for the classes, fill $C$, and apply the same $\rho^n$ to every class value. Since $C$ contains only pair constructors and holes, all class disequalities persist and the filled tree is primitive; its depth is exactly $n$. For a concrete leaf, the leaf has depth $0$ for $\alpha$ and $1$ for $\beta$, while every pair edge can increase $\nu$ by at most $2$ under (RDR.2). Following that leaf gives $\nu(u)\le K_q$, hence the minimum bound. Nonemptiness is supplied by the attained row itself. The example $C=(\square,\alpha)$ with one class has spectrum $\{0,2\}$, so bounded does not mean interval. $\square$

**定义 3.2（finite anchored state model）。** Assume $K<\infty$. Use states

$$
A_j\ (0\le j\le K),\qquad D_j\ (0\le j<K),\qquad H.
$$

$A_j$ means exactly $T_j$; $D_j$ means $\nu=j$ and the tree is not $T_j$; $H$ means a non-atomic tree of depth at least $K$ (it may also represent an atomic $T_j$ with $j>K$ inside an internal computation). Give $A_j,D_j$ level $j$ and $H$ level $K$. Concrete $\alpha$ is $A_0$ and concrete $\beta$ is $A_1$.

Define the finite transition $\otimes_K$ as follows. For $A_i,A_j$ with $i=j+1$, return $A_{j+2}$ when $j+2\le K$ and return $H$ otherwise. In all other cases return $D_m$ when $m=\min(\ell(x),\ell(y))<K$, and return $H$ when $m=K$, where $\ell$ is the state level. Evaluate $C$ with one shared state per class.

**定理 3.3（有限 anchored spectrum procedure）。** The levels of the finite-state evaluation of $C$ are exactly $\Sigma_R$. Thus enumerating the finitely many legal class-state assignments (different classes may not both receive the same $A_j$) is a complete effective procedure for computing the anchored spectrum and an attaining class assignment.

**证明。** Map every actual class value to its state. The exceptional branch of (RDR.2) is preserved whenever its two atomic indices can affect a root of level at most $K$; an atomic index above $K$ cannot be adjacent to a represented index below $K$, and every remaining use is the minimum branch, which is represented by the state levels. Since (RDR.5) bounds the root, the projected root level is its exact depth. Conversely, realize $A_j$ by $T_j$, realize $D_j$ by $\rho^j(p_b)$, and realize $H$ by $\rho^K(p_b)$, choosing distinct nonleaf all-$\alpha$ primitive seeds whenever classes are different. The realization lemma (Theorem 2.2) supplies one actual source with all equalities and disequalities and the row correspondence. The finite evaluation therefore gives both inclusions. $\square$

## 4. Native acquisition of the missing finite pattern

**定义 4.1（atomic-type pattern）。** For $u=C[(z_b)]\in U_R$, set

$$
\theta_R(u)_b=
\begin{cases}
j,&z_b=T_j\text{ for some }0\le j\le K,\\
*,&\text{otherwise}.
\end{cases}
$$

A legal pattern never assigns one integer $j$ to two different classes. For a legal $\theta$, let $V_R(\theta)$ be the set of root levels obtained by finite-state evaluation when integer-labelled classes are fixed to $A_j$ and every $*$ class ranges over $D_0,\ldots,D_{K-1},H$, subject to the same atomic collision rule.

**定理 4.2（pattern fibre and finite native menu）。**

$$
V_R(\theta)=\{\nu(u):u\in U_R,\ \theta_R(u)=\theta\}.
\tag{RDR.6}
$$

Moreover $\theta_R(u)$ is acquired by reading, for each class representative address $p_b$, every suffix $w$ with $|w|\le K$. There are at most

$$
|B|(2^{K+1}-1)
\tag{RDR.7}
$$

calls, maximum absolute word length at most $\max_b|p_b|+K$, and total submitted literal length at most

$$
(2^{K+1}-1)\sum_b|p_b|+|B|K2^K.
\tag{RDR.8}
$$

These are sufficient row-specific bounds, not optimal prices.

**证明。** The finite-state realization in Theorem 3.3 proves (RDR.6). A template $T_j$ has height at most $j\le K$. The complete four-reply table below depth $K$ therefore matches the table of $T_j$ exactly only when the source value itself is $T_j$: a matching branch has all the required children, and a matching template leaf has no child, so no extra descendant can remain. Comparing the representative table with the finitely many templates decides whether its class is $j$ or $*$. Repeated classes need one representative only. Summing the finite menu gives (RDR.7) and (RDR.8). $\square$

## 5. The exact row-uniform service criterion

**定理 5.1（finite criterion for bounded native recovery）。** For a fixed attained anchored row $R$, a row-uniform exact root-depth service with some finite read bound exists if and only if

$$
\forall\text{ legal }\theta,\qquad |V_R(\theta)|=1.
\tag{RDR.9}
$$

When (RDR.9) holds, the menu of Theorem 4.2 followed by the unique value of $V_R(\theta)$ is a constructive service. The row-only zero-read condition is instead

$$
\text{zero new reads}\quad\Longleftrightarrow\quad |\Sigma_R|=1.
\tag{RDR.10}
$$

These are different conditions. A collection of rows has a service on every attained row exactly when (RDR.9) holds for each row in that collection; the theorem does not assert one bound uniform across infinitely many different rows.

**证明。** Sufficiency is the explicit finite menu. For necessity, suppose a bounded service has bound $K'$. Across its finitely many reply histories there are finitely many addresses; let $d$ be their maximum length. If some legal $\theta$ has two values in $V_R(\theta)$, use the finite lifting from Theorem 3.3 with primitive seeds whose every leaf is deeper than $d$ at each $*$ class. A state $D_j$ is realized by $\rho^j(p)$ and $H$ by $\rho^K(p)$; seeds can be chosen with arbitrarily large height and distinct shapes. Keep all integer-labelled classes fixed. The resulting two finite actual sources have the same row and the same replies at every address of length at most $d$, but different root depths. The bounded consumer follows the same run and is wrong on one source. The same construction rules out a service restricted to any fixed address radius, even if it may repeat calls without a call bound. No infinite source is used. $\square$

## 6. Minimum additional retained alphabet

**定义 6.1（conditional ambiguity and retained code）。** For an anchored row define

$$
M_R=\max_{\theta}|V_R(\theta)|.
\tag{RDR.11}
$$

This is finite because the pattern set and the finite state model are finite. An additional producer-retained code is a finite message $E(u)$ computed from the actually acquired source before the row handoff; its alphabet is counted conditional on the already retained $R$.

**定理 6.2（最小 extra alphabet）。** If $C$ has a concrete leaf, the least finite alphabet cardinality of an additional producer-acquired code that permits some row-uniform exact root-depth service is exactly $M_R$. Equivalently, a fixed-width field needs $\lceil\log_2 M_R\rceil$ conditional bits. A realizing producer retains

$$
E(u)=r_R(u),
$$

the zero-based rank of $\nu(u)$ in the increasing list $V_R(\theta_R(u))$. The later consumer acquires $\theta_R(u)$ by Theorem 4.2 and selects that rank. Both pieces of information refer to the same actual source.

**证明。** The rank code has $M_R$ values and gives an actual finite-call consumer. Conversely let a code have $m<M_R$ values and suppose a bounded service exists. Choose $\theta$ with $|V_R(\theta)|=M_R$. The service has a finite address menu over the $m$ code values and finitely many reply histories; let $d$ bound its addresses. For each of the $M_R$ distinct root values, the finite lifting constructs a finite same-row source with pattern $\theta$ whose $*$ values have no leaves within depth $d$. All these sources agree on the entire menu. Two receive the same code by pigeonhole, so the consumer makes the same requests and returns the same value on two different depths, a contradiction. The lower bound applies to arbitrary source-dependent encodings, not only rank labels. $\square$

**推论 6.3（leafless obstruction）。** If $C$ has no concrete leaf, no finite additional alphabet together with a finite uniform read bound can recover exact $\nu$ on $U_R$. A code with $m$ values and a $K'$-read four-reply consumer has at most $m4^{K'}$ reply/code terminal combinations, while Theorem 3.1 supplies infinitely many attainable depths. An unbounded integer retained by the producer or sourcewise unbounded reacquisition is a different contract.

## 7. Two source-specific separations

**命题 7.1（bounded target range with unbounded native price）。** Let the exterior be $C=(\beta,\square)$ with one class and a cut $P=\{R\}$ at the hole. Then

$$
\Sigma_R=\{0,1,2\},
$$

but every exact source-total row-only service has unbounded new calls, unbounded phase-distinct queried addresses, unbounded maximum address length, and unbounded total submitted address length.

**证明。** Formula (RDR.2) gives depth $2$ when the hole value is $\alpha$, and otherwise $\min(1,\nu(z))$, so the three values occur. Let $z_h$ be the perfect height-$h$ all-$\beta$ tree, $h\ge1$. It is $\rho$ of a perfect all-$\alpha$ primitive tree and has depth $1$. For each of its $2^{h-1}$ left-child leaf addresses $w$, make a separate comparison source by changing only that leaf from $\beta$ to $\alpha$. The changed source has depth $0$ because a left child equal to $\alpha$ violates the first-image grammar. A leaf-label change changes only the reply at that exact address. On $(\beta,z_h)$, a terminating exact run must therefore query every $Rw$ or it returns the same answer on the corresponding comparison source. Each such word has length $h+1$, so the run uses at least $2^{h-1}$ calls and has total length at least $(h+1)2^{h-1}$. As $h$ grows, all four coordinates are unbounded. Repeated calls and arbitrarily deep or absent probes do not see a skipped leaf label. $\square$

**命题 7.2（genuinely acquired one-bit, one-read repair）。** Let $C=(\square,\beta)$ with one class and cut $P=\{L\}$. The same full-acquisition producer additionally computes and retains

$$
\eta=\mathbf 1_{I_1}(x),
$$

where $x$ fills the hole. The grammar $I_1::=\beta\mid(\beta,\alpha)\mid(I_1,I_1)$ is a supplied finite image test. The consumer returns $0$ when $\eta=0$; when $\eta=1$, it reads the absolute address $LR$ and returns $3$ exactly on reply $\alpha$, and $1$ otherwise. This is exact on the same actual row fiber, uses at most one new read of length $2$, and one bit is necessary for any uniformly bounded service on this row.

**证明。** Here the spectrum is $\{0,1,3\}$. If $x\notin I_1$, the pair has depth $0$. If $x\in I_1$, its only exceptional member with right child $\alpha$ is $T_2=(\beta,\alpha)$; the address $LR$ returns $\alpha$ exactly for $T_2$, while $x=\beta$ or a composite $I_1$ value returns $\mathsf{abs}$, $\beta$ or $\mathsf{br}$ and hence depth $1$. The finite state model gives $M_R=2$: the non-atomic pattern $*$ has possible depths $0$ and $1$, while each atomic pattern is single-valued. Theorem 6.2 proves the one-bit lower bound, and the displayed producer/consumer attains it. Retaining $\nu$ itself would use three conditional values and zero reads; retaining root $Q$ supports the separate construction-context family but is stronger than this root-only field. $\square$

## 8. Resource and ownership boundaries

**命题 8.1（what this recovery relation does and does not buy）。** The statements above separate the following coordinates.

- The target spectrum is (RDR.4), with all naturals exactly in the leafless case and possible gaps in the anchored case.
- Zero-read identifiability is (RDR.10). Sourcewise finite termination is available from complete representative-class traversal and finite parsing, but its call count depends on the actual finite values; it is not a uniform bound.
- A call bound, maximum literal length, total literal length and number of phase-distinct addresses are separate quantities. Proposition 7.1 gives simultaneous lower growth without identifying calls with word length.
- The conditional alphabet in Theorem 6.2 excludes the cost of $R$, installation, handoff, physical storage, producer computation, encoding time and lifetime retention. It is a task-relative message count, not a physical-memory theorem. Internal $Q$ evaluation, state enumeration and parsing are finite local computations and are separately charged.
- $\nu$ and the retained row do not recover actual entrance, old event order, elapsed time, or arbitrary future native replies. A complete retained tree gives a stronger zero-read future interface, and retaining root $\nu$ or root $Q$ serves named root/context tasks under their own handoff contracts. None of these baselines is the new row-only criterion.
- Every post-handoff read is a new call even if the producer queried the same address during full acquisition. A lower bound on phase-distinct addresses is not a lower bound on lifetime-new addresses.

The equality producer owns the exterior, the complete partition and all declared handoff fields. The named root-depth task owns either the later paid reacquisition in Theorem 5.1 or the optional extra code in Theorem 6.2. No obligation to retain every class $Q$, every descendant depth, a full tree, or every future response is inferred.

## 9. Reuse, literature and unresolved extensions

**文献表态。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| [JM §§36, 49–50](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md) | `repo-derived`: primitive-ray uniqueness, the $Q$ pair law and the separate construction-context task are reused. They do not provide the acquired-row spectrum or the native service criterion. |
| [SLH §§59–65](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md) | `repo-derived`: actual common producer, complete exterior/equality handoff and exact row fiber. Its prescribed finite literal tasks do not imply a bounded exact-$\nu$ service. |
| [NativeCutFibers.lean](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean) and [NativeDepthPatterns.lean](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean) | `repo-derived`: class filling, distinctness, original-prefix locality and rank/depth suppliers. These source inspections are not new Lean verification of this volume. |
| [Native intrinsic depth certificates](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_INTRINSIC_DEPTH_CERTIFICATES.md) | `repo-derived`: leaf-cone locality and finite source witnesses are credited as suppliers; its static per-tree certificate price is a different consumer. |
| [Acquired intrinsic depth calibration](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_INTRINSIC_DEPTH_CALIBRATION.md) | `repo-derived overlap boundary`: its right-spine and forward-lag contract is different; no right-spine action or delayed clock is used here. |
| [FIB geometry continuation III §82](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md#82-rank-three-transport-carrier-point-source-stability-and-target-fibre-defect) | `repo-derived overlap boundary`: conditional Lie-group/point-source energy statements leave native source-to-space correspondence open; no spatial action is imported here. |
| Dexter Kozen, “On the Myhill–Nerode Theorem for Trees” (1992), [author PDF](https://www.cs.cornell.edu/~kozen/Papers/mn.pdf) | `literature-attested`: contexts and congruence for finite ranked ground terms. It does not acquire an unknown native tree or price arbitrary-address reads. |
| Barguñó, Creus, Godoy, Jacquemard and Vacher, “Decidable Classes of Tree Automata Mixing Local and Global Constraints Modulo Flat Theories” (2013), [arXiv:1302.6960](https://arxiv.org/abs/1302.6960) | `literature-attested`: decidable emptiness with equality/disequality constraints. It is not a theorem about this producer, this read port or bounded service. |
| Buhrman and de Wolf, “Complexity measures and decision tree complexity” (2002), [author PDF](https://homepages.cwi.nl/~rdewolf/publ/qc/dectree.pdf) | `literature-attested`: decision-tree and sensitive-block methodology. The finite leaf-flip family supplies the native same-row realization here. |
| — | `suspected-novel`: the joint class-summary formula, finite anchored state procedure, criterion (RDR.9), and minimum conditional alphabet are proposed as repository-derived consequences. This bounded check does not establish external priority or exhaustive novelty. |

**开放问题 9.1（more informative acquired histories）。** The proof uses the bare complete row fiber (RDR.1). If literal words, signed histories, cross-epoch relations or other acquired fields are retained, they can remove the deep finite witnesses used in Theorems 5.1 and 6.2. Extending the criterion then requires a new simultaneous lifting lemma preserving every added equality, disequality and guard. A generic automaton emptiness result or one feasible representative does not supply that lemma. Uniform optimization of physical memory, producer cost, computation, prescribed call budgets and actual elapsed time is also outside this volume.

**产地。** The volume follows the repository’s formal-thinking-and-answer and theory-volume-template conventions. It is a single theory-only continuation of the selected finite row-depth outcome; the mathematical statements above are ordinary proofs and bounded supplier applications, with no Lean, Blueprint, registry, digestion or tooling claim.

## 10. Finite verification boundary

No numerical program or new test is part of this volume. The finite menus and state transitions in §§3–6 are explicit mathematical constructions; they establish finite termination of the stated procedures, not a complexity bound and not a kernel verification. The source contract remains the original static four-reply interface.

## 追加锚（本行以下为增补区）

# Original-source timed release recovery and acquired future memory

This volume fixes one original conservative four-coordinate diffusion and the causal release service supplied for it. It distinguishes deterministic observation cuts, actual release arrivals, finite same-path banks, and a countable refinement limit. The source is not killed or reset at contact.

## 1. Canonical source, service, and information fields

For every original $a,\eta>0$, retain the same $G=H^1\times\mathbb R$, coordinates, identity $e$, Haar measure, unit Green field, selector, positive normalized $h$, probability $m=h^2\mu$, full form, nonnegative generator $K$, conservative semigroup $T_s$, and e-start diffusion $Z$ as in the original source volume and the retained emission volume. Contact with $e$ is not a kill.

Fix $\varepsilon,\delta>0$ before a run. Install exactly the causal release service with source mode $E$ (the first excursion reaching age $\varepsilon$) and killed mode $C$ at actual contact or $D$ at the $\delta$ timeout with the current state. Let

$$
R_0=0,\quad P_0=e,\quad (R_i,\operatorname{type}_i,P_i)
$$

be the actual indexed releases. At an arrival, the service discloses the complete four-coordinate point $P_i=Z_{R_i}$, exact original timestamp and type. While a request is pending, the observer sees only the exact clock and nonarrival. There is no cancellation, adaptive timeout, deadline query, future timestamp, excursion mark, seed, actuator, or extra source read.

Let $H_T$ be the finite marked prefix through the known horizon $T$, including silence to $T$, and let $G_T$ be its usual augmentation. Let

$$
A_T=(\text{mode at }T,\ \text{last released point},\ \text{elapsed age at }T)
$$

be the actually updated controller tuple. The source owner supplies the calibrated service, source path and exact marks. The observer owns actual requests, retained prefixes and later calls. These are explicit ideal premises; no additional physical installation is demanded by the conditional statements.

## 2. Common positive-time versions

**(C1) Lemma 2.1 (one common reached-state version).** There is one properly exceptional off-source set $N\subset G\setminus\{e\}$ with $m(N)=0$ such that, for every $p\notin N$ and every $s>0$, the full transition law from $p$ has a density with respect to $m$, with the transition identities jointly measurable in $(p,s)$. The e-start law at every $s>0$ has density $g_s$ with respect to $m$.

**Proof.** The full-form local ellipticity and Riesz construction give continuous positive-time representatives off $e$, with local form bounds and conservation. Choose a countable determining family of compactly supported continuous functions together with the constant one and rational positive times. Remove the union of their proper-association and polar exceptional sets. For each remaining $p$, path continuity and positive-time semigroup continuity extend equality from rational times to every real time; a fixed positive half-step gives the required evaluation bound. The reached non-source release points have an $m$-absolutely-continuous law under the original release coupling, so they avoid $N$. The e-start density is supplied separately. A statement valid only for a different null set at each time would not suffice for random remaining horizons; the common version is the needed strengthening. ∎

**(C1a) Lemma 2.2 (no deterministic arrival).** For every fixed $T>0$, the probability of an arrival at exactly $T$ is zero.

**Proof.** A contact at $T$ implies $Z_T=e$, which is null by the positive-time e-start density. A source-mode $E$ at $T>\varepsilon$ implies $Z_{T-\varepsilon}=e$, also null, and it cannot occur earlier than $\varepsilon$. At $T=\varepsilon$, the small-excursion Levy mass is infinite while the long-excursion normalizer is finite; hence the atom at zero duration is zero. A killed timeout $D$ at $T$ implies a prior $E$ at one of the countably many values $T-k\delta$. Local finiteness of releases completes the proof. ∎

**(C1b) Lemma 2.3 (usual augmentation at a deterministic cut).** At a fixed deterministic $T$, completion and right-continuous augmentation of the raw marked-prefix field add no state information relevant to conditional laws: every variable measurable in all completed fields at $T+1/n$ has a version measurable at $T$.

**Proof.** Represent the variable at $T+1/n$ as a measurable function of the finite prefix at that horizon and evaluate the same function on the $T$ prefix extended by no arrival. The two values differ only if an arrival occurs in $(T,T+1/n]$, whose probability tends to zero by local finiteness. Closure under convergence in probability yields a $T$-measurable version. Exact horizon and nonarrival remain in the prefix. ∎

## 3. Deterministic cuts and actual arrivals

**(C2) Theorem 3.1 (diffuse deterministic-cut posterior).** For every fixed deterministic $T>0$ and fixed $\varepsilon,\delta>0$,

$$
\mathcal L_e(Z_T\mid G_T)\ll m\quad\text{almost surely}.
\tag{3.1}
$$

Consequently every $G_T$-measurable estimator of $Z_T$, and every estimator of any one original coordinate, has exact-equality probability zero. An independent source-independent random seed does not improve this probability.

**Proof.** By Lemma 2.2 there is no arrival at $T$. On the event $N_T=n$ of $n$ completed releases, condition at the genuine indexed stopping time $R_n$, not at a retrospectively selected last-arrival time. Put $r=R_n$, $p=P_n$, and $a=T-r>0$. In source mode the current subprobability is

$$
\mathbb P_p\bigl(Z_a\in dq,\ D_\varepsilon(0)>a\bigr),
$$

which is dominated by the common density from Lemma 2.1 (and by $g_a m$ when $p=e$). In killed mode the corresponding subprobability is

$$
\mathbb P_p^0(Z_a\in dq),\qquad a<\delta,
$$

again dominated by the full transition density. Normalize on the positive-survival histories and choose arbitrary versions on null histories. Measurable disintegration gives absolute continuity of the conditional law for each $n$; summing over $n$ gives (3.1), and Lemma 2.3 passes it to the usual augmentation.

Because $m=h^2\mu$ is absolutely continuous with respect to four-dimensional Lebesgue measure, singleton and coordinate-hyperplane fibers are null. The conditional law assigns zero mass to every exact estimator fiber, and integrating proves the zero success probability. Adding an independent seed only forms a mixture of the same conditional measures, so it cannot create an atom. ∎

**(C3) Theorem 3.2 (arrival recovery).** At every actual arrival $R_i$, the disclosed point satisfies $P_i=Z_{R_i}$ and is acquired exactly at that stopping time. This does not contradict Theorem 3.1: a random release time is not a fixed deterministic cut.

**Proof.** Equality is part of the causal service contract. Countably many indexed releases share one probability-one event. Lemma 2.2 says each fixed deterministic time misses all arrivals almost surely, while a genuine indexed arrival discloses its current point. A later arrival supplies a later point, not the point at an earlier deterministic cut. ∎

## 4. Silence-conditioned future law and finite banks

For a source-mode request write $W_\varepsilon(dv,dc,dq)$ for the primitive future wait, type and point kernel, and for killed mode write $K_\delta(p;dv,dc,dq)$ for the corresponding kernel. If the current age is $a$, define the silence-conditioned kernels

$$
W_\varepsilon^{>a}(dv,dc,dq)=
\frac{1_{v>a}W_\varepsilon(dv,dc,dq)}{W_\varepsilon(v>a)},
$$

$$
K_\delta^{>a}(p;dv,dc,dq)=
\frac{1_{v>a}K_\delta(p;dv,dc,dq)}{K_\delta(p;v>a)}.
$$

The denominators are positive on realized histories.

**(C4) Theorem 4.1 (future-law memory).** For every finite future marked-release experiment under the fixed service, its conditional law after time $T$ factors through $A_T$. In source mode use $W_\varepsilon^{>a}$; in killed mode use $K_\delta^{>a}(p;\cdot)$; subtract $a$ from the next wait and update the tuple after each arrival. Thus the routes

$$
H_T\longrightarrow A_T\longrightarrow\text{future law}
\quad\text{and}\quad
H_T\longrightarrow\text{future law}
$$

agree. The tuple does not reconstruct the old archive, the realized future, or $Z_T$ at a deterministic cut.

**Proof.** Apply the strong Markov property at the genuine last indexed release $R_n$. The observed silence is exactly the event that the next primitive wait exceeds the current age. Conditional probability therefore restricts and normalizes the primitive kernel as displayed. At an arrival, set the point to the disclosed $P_i$, set the mode to its type, and reset age to zero; between arrivals increase age with the original clock. Iteration gives every finite future marked law. Since the construction uses the actual common source and service kernel, it is a law factorization rather than an installed numerical evaluator. ∎

**(C5) Theorem 4.2 (finite common-path bank).** Suppose $J<\infty$ fixed-scale copies of the service are explicitly installed on the same actual path $Z$. The full joint acquired prefix through any fixed deterministic $T>0$ still has an $m$-absolutely-continuous posterior for $Z_T$.

**Proof.** Merge the finitely many genuine stopping lists and coalesce ties. The merged list is locally finite and has no deterministic arrival by Lemma 2.2. Conditional on the full source past at the $n$th merged release, the remaining positive horizon has a density by Lemma 2.1. Restricting this joint future law to all-channel nonarrival through $T$ preserves domination by the past law times $m$. Measurable disintegration over the actual joint prefix and summation over $n$ gives the result. The argument permits dependent timers and overlapping services; separate marginal samplers on separate paths do not establish it. ∎

## 5. Countable same-path refinement

Let $(\varepsilon_n,\delta_n)$ satisfy $\varepsilon_n\vee\delta_n\downarrow0$, and install the canonical services on the same $Z$. Let $V^n$ be their held last-released path.

**(C5b) Theorem 5.1 (uniform refinement and raw-path field).** For every finite $T$,

$$
\sup_{s\leq T}|V_s^n-Z_s|
\leq\Omega_T(Z;\varepsilon_n\vee\delta_n)\longrightarrow0
\quad\text{almost surely}.
\tag{5.1}
$$

Moreover, after completion,

$$
\sigma\bigl(\text{all canonical prefixes through }T\bigr)
=\sigma(Z_s:0\leq s\leq T).
\tag{5.2}
$$

**Proof.** The supplied same-path modulus bound gives (5.1) for each $n$. Intersect the corresponding probability-one events over the countable family. Continuity of $Z$ on $[0,T]$ makes the modulus tend to zero. Hence every rational-time coordinate $Z_q$ is measurable with respect to the union of all prefixes as the limit of $V_q^n$; continuity then gives every real-time coordinate and the forward inclusion in (5.2). Conversely, each timer, type and announced mark is a causal Borel path functional through $T$, except on the countable tie and version null sets. This gives the reverse inclusion after completion. The limit uses countably many installed services and exact marks; it is not a finite terminating acquisition, a finite-bit theorem, or an enlarged source-filtration identity. ∎

## 6. Independent meanings, costs, suppliers, and limits

Space is the actual current four-coordinate point. Time is original elapsed time with actual release timestamps and types. Boundary is the causal contact/age/timeout service. Memory is $H_T$ or the tuple $A_T$ according to the declared future-law task. At actual arrivals Boundary and Memory acquire Space; at deterministic cuts Theorem 3.1 prevents a general finite-record inverse. No mutual four-view theorem follows.

For one service through $T$, the number of releases obeys

$$
N_T\leq 2\lfloor T/\varepsilon\rfloor+\lfloor T/\delta\rfloor.
$$

At most $N_T+1$ primitives are initiated and at most one is pending. A literal retained prefix stores tags, exact timestamps, four-coordinate real marks, horizon, source identity, frame, references, parsing buffers and rights. The fixed-register tuple stores mode, point, age and context for future-law prediction, but exact real arithmetic, kernel evaluation, backing and access remain charged. A finite bank pays the sum of all installation and event bills plus up to $J$ pending requests on the same path.

The countable limit has no finite upper bill, supplied rate, finite precision, energy, memory, or terminating exact decoder. At an actual arrival, retaining the disclosed point is the cheapest already-earned exact point for that cut. For approximate current state, the existing held-path consumer is sufficient under its own assumptions. An exact current query would change the interface and pays its own installation. Keeping the full archive remains necessary when historical queries are part of the task; $A_T$ is sufficient only for the stated future marked-law task.

The timed service, causal coupling, reached-state law, event bounds and modulus are credited to the original Free Diffusion §§15, 24--28 sources. The added composition is the common positive-time version, silence-conditioned posterior, deterministic-cut/arrival contrast, finite same-path bank persistence, and completed countable raw-path equality. Finite posterior or sample-and-hold results with different target spaces do not replace this proof. The original source, exact clock, service rights and records remain hypotheses. This conditional boundary does not establish physical conformance, an arbitrary stopping-time obstruction, native hidden-coordinate recovery, a finite exact acquisition from all scales, or completion of the sustained common-source objective.

Appendix II §127 at public source revision `53571cd1a456f5c649d46ac73f818bb1fd7760e7` retains the same original $a,\eta$, $m=h^2\mu$, full form, conservative semigroup and e-start density. Its $P=T_d$ and $g=g_t$ concern deterministic positive equal gaps, and its localized mixed-pencil negative index and $\beta=0$, $\alpha>0$, $\gamma\neq0$, $\gamma>-\alpha$ interval retain that domain. The source correspondence is exact, but a quadratic-form index does not establish a common reached-state transition version, a silence-conditioned conditional law, a no-deterministic-arrival statement or a same-path refinement identity. Those C conclusions use the actual release stopping times, common positive-time densities and causal path functionals proved above and supplied by the Free Diffusion construction. No deterministic-gap pencil result changes the release interface, initialization, contact rule or clock.

The excursion normalization and recurrent-point correspondence are credited to Fukushima--Tanaka, *Ann. I. H. Poincare PR* 41 (2005), §3.1, Theorem 3.1 and equations (3.4)--(3.12), under the source-specific correspondence $S=G$, $a=e$, $S_0=G\setminus\{e\}$ and $m=h^2\mu$. The exact-timestamp/silence comparison is related to Rabi--Moustakides--Baras, arXiv:0904.4358, §§1.1--1.3, with its ideal-clock scope; neither reference supplies the present four-dimensional posterior, finite common-path bank, or countable field equality.

## 追加锚（本行以下为增补区）

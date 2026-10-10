# Event-aware supplementary memory below the canonical response-index bound

## 115. A strict finite gap after Boundary Dynamics §114.99

This standalone continuation supplies a fixed finite obstruction to identifying the number of canonical future-response functions with the least supplementary memory. Its new result is the exact gap $D_{\rm read}=D_{\rm blind}=2<H_{\rm resp}=3$, with the original completed-event interface and canonical decoder. It does not replace the response-index upper bound of [Boundary Dynamics](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md) §114.4 or repackage its construction as an optimality theorem.

This is `repo-derived` ordinary mathematical prose with bounded finite computation, not Lean verification or a physical law. Existing supplies are cited below; no external originality claim is made. Only this new volume carries the continuation; existing theory text is unchanged.

### 115.1 Fixed source, observations and decoder

Use Boundary Dynamics §§105.1, 108.1 and 114.1 with $r=3,m=2,d=1$, $\mathbb F_2=\{0,1\}$ and

$$
Q=3,\quad L=28,\quad\ell=29,\quad n=58,\quad B=27,\quad c_0=30.
$$

The source has one actual hidden depth $K=k\ge1$, or one fixed common prior $\mu$, throughout seed acquisition and payload. Restored fresh Reads are conditionally independent given $k$, with $\Pr(\alpha)=r_k=F_{k+1}/F_{k+3}$. Paid pairs $\alpha\beta$ and $\beta\alpha$ produce seed bits 0 and 1; equal pairs are discarded with paid retries. The acquired seed $R=\rho$ is retained. Both seeds have probability $1/2$ before acceptance; no seed is conditioned away.

The original parser recognizes $w_{j,0}=(\beta\alpha)^j\alpha$ and $w_{j,1}=(\beta\alpha)^j\beta\beta$. All original returns, retries, unfinished parsing, rejected executions and infinite noncompletion remain. Only completed markers count toward $n$. The passive selector does not query, stop or resample the source; the payload continues after its bookmark to the actual original $\mathrm{Stop}_{b_{58}}$, after which there is no Read.

For a marker prefix $u$ of length $c$, define the original bare boundary

$$
v_i=\rho^{i-1},\quad v_{29+i}=v_i\ (1\le i\le29),\quad
C_\rho=\sum_{i=1}^{29}v_i,\qquad
b_\rho(u)=(c,\beta,h)=\left(c,|u|,C_\rho+\sum_{i=1}^c v_i u_i\right).
$$

Here $|u|$ is integer Hamming weight, field sums are in $\mathbb F_2$, and $0^0=1$. Correct recovery is required exactly on $E_\rho=\{R=\rho,Q_{58}=(0,29),h(w)=0\}$. Every compatible balanced zero-return word has joint mass $\frac12\sum_k\mu(k)r_k^{29}(1-r_k)^{58}>0$, or the corresponding fixed-depth term. This reuses the original positive-source law; it does not assert seed independence after acceptance.

For each bare address $b$, let $U_b$ be all prefixes with that address, $\mathcal F_b$ all length-$58-c$ suffixes with weight $29-\beta$ and field sum $h$, and $N_b=|\mathcal F_b|$. Let $W_b\subseteq U_b$ be prefixes still active after the current selector decision, and $\mathcal S_b\subseteq U_b$ those first selected exactly there. The decoder $\mathscr D_{\pi^-}$ is the original total decoder of §§105–106, 113–114, instantiated with the fixed selector below: nonterminal codes are zero-based colex ranks in the entire $\mathcal S_b$; terminal codes use the entire actual-Stop block. Colex compares from the last differing position, with $0<1$.

The receiver obtains only frozen $(\rho,\ell,c,\beta,h)$, frozen $z$, actual suffix $Y$ and actual Stop. Keep the decoder's full nonnegative-integer code domain, original interface checks and fixed empty-word default. In particular, do not add an acceptance or $N_b>0$ check, truncate its code domain to $\{0,1\}$, or change its behavior on zero-completion addresses with legal dictionary ranks.

### 115.2 The complete fixed selector

**Definition 115.1 (one removed early pair).** Enumerate $e_1=\{1,2\}$, $e_2=\{1,3\}$, $e_3=\{2,3\}$. Define $\pi^-$ from §108.1's $\pi_3$ by deleting only the early-pair trigger for $e_2$. From its fixed initialized control, on every binary 58-marker word:

1. At or before marker 27, first encountering 0 causes immediate first freeze; otherwise the prefix is $1^{27}$.
2. Read identity positions 28–30 without freezing before position 30. An all-zero identity block freezes at 30. With at least two identity ones, let the first two local positions form $e_t$ and freeze at tail position $6+t$, regardless of that marker's value. This includes rejected blocks with three ones.
3. With exactly one identity one at local position $i\in\{1,2,3\}$, wait through tail position $3+i$. A first tail one at $j\le3+i$ freezes immediately exactly when $j\in\{1,3\}$ and $i\in e_j$. Otherwise schedule freeze at

$$
f(i,j)=9+6(i-1)+j.
$$

If no one has appeared through $3+i$, freeze on that deadline's zero. At the deadline a one takes precedence over the zero rule. In particular, all $j=2$ cases use $f(i,2)=11,17,23$ for $i=1,2,3$, respectively.

After any delayed schedule is set, subsequent markers do not revise it; at its target freeze regardless of marker value. After the first freeze, selection and snapshot remain latched while the original source continues. Every non-marker event holds the selection state. These rules apply to all complete words, not merely accepted words. Their disjoint target intervals are early pair $\{1,3\}$, zero deadline $4$–$6$, two-one target $7$–$9$, and delayed target $10$–$27$; $f$ is injective on its scheduled $(i,j)$ addresses. Thus each word has exactly one causal first freeze, no later than $30+27=57<58$.

Every finite raw-event prefix also has defined passive behavior: initialization is fixed, incomplete seed/parser phases and non-marker events hold, and only actually completed markers trigger the rules. Infinite noncompletion need not acquire a bookmark. Malformed formal addresses use the existing fixed default, without inventing a source event or changing the original parser. The selector's control $\kappa$ remains an original paid component; it is not supplied to the blind encoder.

### 115.3 Response functions and the distinguishing table

Use the persistent-register capacities $D_{\rm read},D_{\rm blind}$ of §108.1: read may inspect $\kappa$, blind may not. Both use one fixed initial value and the same register for acquisition and frozen output. Blind inputs include public parameters, acquired $\rho$, synchronous old/new bare fields, current completed marker, original generic parser phase and the already completed continue/first-freeze event. They exclude control copies, private persistent phases, prefix histories, future decisions and an extra output register.

For each positive active address, define the canonical response $g_u:\mathcal F_b\to[D_\rho]$ of §114.3: replay the initialized fixed selector on $uy$ and return the original canonical rank at its first freeze. Here $D_\rho$ is the maximum positive selected-fiber size, including the original two terminal Stop blocks. Set $D=\max_\rho D_\rho$ and

$$
H_{\rm resp}(\pi^-)=\max\left(\{1,D\}\cup
\{|\{g_u:u\in W_b\}|:\rho\in\{0,1\},\ c<58,\ N_b>0\}\right).
$$

This counts distinct future code functions at each shared bare address; it does not count minimal register values when actual decision events remain inputs.

At $\rho=1$, let $u_i$ be the length-three one-hot word and $p_i=1^{27}u_i$. All three are active at $b=(30,28,1)$. The compatible suffixes have one one. With $y_1=10^{27}$ and $y_3=0010^{25}$:

| Active past | $g_{p_i}(y_1)$ | $g_{p_i}(y_3)$ | Acquired $z$ |
| --- | ---: | ---: | ---: |
| $p_1$ | 0 | 0 | 0 |
| $p_2$ | 1 | 0 | 1 |
| $p_3$ | 0 | 1 | 0 |

For every other compatible suffix of weight one, all three rows return singleton rank 0. At $j=1$ the selected pair is $(p_1,p_2)$ in colex order; at $j=3$ it is $(p_2,p_3)$, after adjoining the same zeros and triggering one. The excluded member is delayed and receives singleton rank 0. Thus these are three distinct full functions, although $p_1,p_3$ have the same acquired register value.

### 115.4 Exact bounds and a causal two-state realization

**Proposition 115.2 (strict response-index gap).** On the complete original two-seed source and the fixed interface above,

$$
D_{\rm read}(\pi^-)=D_{\rm blind}(\pi^-)=2< H_{\rm resp}(\pi^-)=3.
$$

Proof of the selected-fiber and register lower bounds. If a balanced word first deviates from $1^{27}$, its selected prefix is the unique $1^{c-1}0$ at that address. Otherwise exactly two ones remain among 31 positions. An all-zero identity block has one selected past. A two-one identity block has no tail ones and its distinct pair target identifies a singleton. A one-hot block has exactly one tail one: retained early pairs have two members, and each delayed or zero-deadline address has one. Target intervals do not overlap, and delayed addresses identify $(i,j)$. No terminal leaf exists. Hence $D_\rho\le2$ for both seeds.

For $\rho=1$, $p_1y_1$ and $p_2y_1$ are positive accepted words with different selected pasts, the same frozen $(1,29,31,29,0)$, suffix $0^{27}$ and Stop 0. A one-value register cannot decode both. This proves $D_{\rm read}\ge2$ and $D_{\rm blind}\ge2$, and $D=2$.

Proof of the response bound. The table gives $H_{\rm resp}\ge3$. Before or through marker 27 there is only the active all-one prefix. At markers 28–29, each fixed weight admits at most two active identity prefixes. At marker 30 and afterward, one-hot prefixes with no tail one have at most three possibilities. Any positive active past that already contains both residual ones has only the all-zero future; its future selected fiber is a singleton, by the disjoint schedule classification, so its response is the constant 0 even when several pasts share a bare address. These cases cover all positive active addresses with initial $1^{27}$; dead addresses do not enter the maximum. Restricting to seed 0 introduces no additional prefix possibilities or selected collisions. Consequently every response image has size at most three, giving $H_{\rm resp}=3$.

Construction of the upper bound. Initialize $z=0$ in $\{0,1\}$. Previously frozen and non-marker events hold with priority. On an unfrozen marker transaction, let $c'=c+1$ be the new position and $a$ the marker. Apply the original phase/address consistency checks, including synchronized new fields; malformed addresses take default 0. On a valid address:

1. If $c'\le27$, write 0.
2. If $28\le c'\le30$, a first identity one (old $\beta=27$) writes $\operatorname{color}(c'-27)$, where $\operatorname{color}(1)=\operatorname{color}(3)=0$, $\operatorname{color}(2)=1$. A second or later identity one clears to 0; zeros hold.
3. In the tail put $j=c'-30$. Old $\beta\ne28$ clears to 0. With old $\beta=28$ and $a=1$, an actual first freeze at $j=1$ keeps $z$, an actual first freeze at $j=3$ writes $1-z$, and all other cases write 0. With old $\beta=28$ and $a=0$, an actual first freeze writes 0 and continue holds.

Write the resulting value before the original first-freeze latch; then use that same register's frozen value. This is a total function of allowed transaction inputs, with no stored identity, schedule, mode or $\kappa$ replica.

Canonical-output proof. The first identity one writes its color, and zeros preserve it until a tail one or deadline. An early $e_1$ freeze produces ranks $(0,1)$ for $i=(1,2)$; an early $e_3$ freeze produces ranks $(0,1)$ for $i=(2,3)$ by complementing the colors. A non-early tail one clears to 0 before its later singleton freeze. Zero deadlines clear to 0. All-zero identity, two-one identity and first-deviation branches freeze 0. Thus every accepting first freeze emits the original colex rank for seed 1.

For seed 0 only positions 1 and 30 have coefficient 1, and $C_0=1$. With initial $1^{27}$, acceptance is exactly $b_{30}=0$, so $p_3$ is absent. The $e_1$ pair remains intact with ranks 0,1; the $e_3$ fiber becomes the singleton $p_2$, whose complemented color is 0. Every other accepting branch is still a singleton emitting 0. Early-deviation branches are unique for either seed. This proves canonical output on both $E_\rho$, without altering rejected executions. Deterministic induction over completed markers proves the stated invariant; holding rules extend totality to every finite original raw-event prefix.

The construction gives $D_{\rm blind}\le2$; a read encoder can ignore $\kappa$, so $D_{\rm read}\le2$. Together with the lower bounds this proves the proposition in ordinary mathematics.

### 115.5 Composition and the smallest original consumer

The composition condition is exact synchronization: each supplied decision event must come from the same initialized $\pi^-$ on the same actual source history and completed marker; the register update must finish before that transaction's original latch. Selection must not depend on $z$. Old/new fields, acquired seed, frozen snapshot, suffix and Stop must refer to that same execution. Under these conditions the original decoder applied to the emitted rank returns the actual selected past on $E_\rho$. An event from another history, an earlier latch or a speculative event does not satisfy this composition condition.

The smallest consumer of the gap is the existing single-snapshot selected-past decoder. At the shared address $(30,28,1)$ it need not receive the identity or a three-valued response index. For the merged $p_1,p_3$, suffix $y_1$ freezes them at tail positions 1 and 22, respectively, with rank 0 in the $e_1$ pair and rank 0 in a singleton; suffix $y_3$ freezes them at positions 12 and 3, with ranks 0 and 1. Their differing realized decisions and frozen positions supply the missing context. In contrast, the simultaneous $e_1$ freeze keeps $p_1,p_2$ distinct by the one-bit rank.

Thus a register value need not determine the complete future response function at a bare address. Canonical response indices remain a sufficient closed representation; they are not a lower bound for this supplementary-register contract. The actual completed continue/freeze event is a supplied transaction input, not a readable selector-state copy. It conveys no uncompleted decision and adds no new receiver field. The original selector, its control and event-production costs remain part of the supplied system.

### 115.6 Bounded evidence, supplies and four expressions

The bounded computation enumerates the $\binom{31}{2}=465$ balanced words extending $1^{27}$, independently orders selected pasts by colex, forms active response vectors over their compatible suffixes, and compares every accepting emitted value with its canonical rank:

| Actual seed | Residual balanced words checked | Accepted | Maximum selected fiber | Maximum response image | Two-state failures |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 465 | 435 | 2 | 2 | 0 |
| 1 | 465 | 465 | 2 | 3 | 0 |

The latest first freeze among these residual words is marker 57. This is bounded finite computation, not the proof of all-path totality or of the lower bounds. The $2^{58}$ complete-word enumeration was not performed. Earlier-deviation prefixes and rejected/noncompleted raw histories are covered by the ordinary branch and holding proofs above, not by these residual counts.

| Existing supply | Exact use and remaining boundary |
| --- | --- |
| Boundary Dynamics §§104–108, 114 | Positive support, single-snapshot/Stop contract, colex decoder, two register contracts, complete $r$-schedule and response-index upper bound. The new selector deletes one trigger and adds the strict $2<3$ witness; it does not duplicate the original complete-pair $2$ versus $r$ separation. §§109–113 supply related factorization, width, support and paid implementations, not this gap. |
| [Recovery Geometry](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) §§34–35 | §34 supplies the distinction between compatible recovery maps and actual-source completion. §35's periodic gradient estimates supply no memory bound or metric here; no analytic/physical transfer is inferred. |
| [Transport Memory](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) §§64–72 | Preserve actual response supports, original outputs, supplied resources and shared-address successor obligations. Its full Moore/controller counts are different resources from this one supplementary alphabet. |
| [Context Geometry](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) §§82–90 | Common-history constraints, source access, references and operation closure remain explicit; static response correspondence does not install a new readable event or clock. Its preparation and control costs are not removed here. |
| [Atomic Generation](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) §12 | A readable cut/record requires an explicit supplied port. Here the completed-event input is already in §108.1's contract, rather than inferred from an abstract relation. |

The four-expression relation is task-relative. **Space** is the supplied ordered set of marker positions and identity/tail incidence pairs, with no recovered physical distance. **Time** is causal prefix extension and the first-freeze order, with no absolute clock or elapsed-duration recovery. **Boundary** is the original frozen $(\rho,\ell,c,\beta,h)$ together with actual suffix and Stop. **Memory** is the supplementary $z$, interpreted jointly with those supplied fields and transaction events. These are linked on one actual history; they are not four independently sufficient or freely interchangeable descriptions of the entire source.

### 115.7 Unresolved limits

The gap disproves general equality of $H_{\rm resp}$ with the least event-aware supplementary alphabet; it does not provide an arbitrary-selector minimization theorem, a general compatible-cover formula, or an unbounded family of such gaps. Whether event access is necessary for every two-state realization is not established. Suppressing the event input changes the contract and requires a separate capacity analysis.

Selector control, seed acquisition, parser, current/frozen boundary, ROM and table generation/addressing, field and integer computations, transaction workspace, full decoder domain, output storage, Read/return/retry costs, time and energy are all separate supplied resources. No total-memory, paid-cost, physical implementation or Pareto optimum follows from the alphabet count. The construction does not recover return histories, acquisition transcripts, hidden depth, a physical metric or an absolute clock. Broader relation-level recovery and infinite-parameter extensions remain open.

## 115.99 追加锚

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

## 116. A cyclotomic counterfamily to the degree-uniform square-root bound

The degree-uniform alternative in [Boundary Dynamics](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md) §114 has a negative answer in its original paid-source experiment. There are initialized finite complete passive selectors with $D_{\rm read}=D=2$ and $D_{\rm blind}/(D\sqrt n)\to\infty$. The construction below keeps every acquired seed and the original total canonical decoder. Its lower bound uses positive common continuations on which the complete allowed inputs, including the completed selection events, agree. It does not identify a large response image with a memory minimum; §115's distinction remains in force.

The original experiment and its suppliers are taken at the fixed revision `c5e5c2c0f50f73bd6f75b3ecf2ea4e31b6d29226`. The continuation through §115 and the separate later comparison are taken at `ead132fb284340a8b3a70b957a974196f85fecc3`. The theorem concerns the former experiment; the latter revision does not change its source, interface or correctness domain.

### 116.1 Parameters and the unchanged original contract

**Definition 116.1 (the public family and actual source).** For an integer $k\ge2$, let

$$
H=3^k,\qquad a=\max\{j\ge0:j\text{ is even and }2^j\le H\},\qquad
 d=2H,\quad \ell=2H+a,\quad n=2\ell=4H+2a,
\qquad f(X)=X^{2H}+X^H+1.
$$

In particular $a\ge2$, $2^a\le H<2^{a+2}$ and $a<H$. Lemma 116.3 proves that the public representation $\mathbb F_{2^d}=\mathbb F_2[X]/(f)$ is valid. Write $\theta=[X]$ in this representation. The family index $k$ is public and is distinct from the original hidden source depth.

Set the original source parameter to $m=2$. There is one actual hidden depth $K_{\rm src}=h\ge1$ throughout seed acquisition and payload, or one fixed common prior $\mu$ on those depths with the same single $K_{\rm src}$ used throughout. Given $h$, restored fresh Reads are conditionally independent, with

$$
r_h=\Pr(\alpha\mid h)=\frac{F_{h+1}}{F_{h+3}},\qquad
\Pr(\beta\mid h)=1-r_h,\qquad \frac13\le r_h\le\frac12.
$$

Use the actual initialized source and paid acquisition of Boundary Dynamics §§100.1–100.2 and 110.1. A paid pair $\alpha\beta$ supplies seed bit 0, a paid pair $\beta\alpha$ supplies bit 1, and equal pairs are discarded with paid retries. After $d$ acquired bits, retain the resulting actual field element $R=\rho$. All $2^d$ seeds occur with probability $2^{-d}$ before acceptance. The procedure neither conditions on $R=\theta$ nor repeats an acquired seed. No old record, hidden-depth query, growth, reset, replay, clock or new source port is supplied.

The original payload parser has segments

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta,\qquad j\ge0.
$$

Only completed markers count toward $n$. All original paid Reads, restorations, returns, retries, rejected executions, unfinished parser states and infinite noncompletion remain. After a bookmark the source still executes the remaining original payload and delivers the actual $\mathrm{Stop}_{b_n}$; there is no Read after that Stop. The bookmark is not a source Stop.

For a marker prefix $u$ of length $c$, the original bare fields are

$$
\begin{aligned}
v_i&=\rho^{i-1},&v_{\ell+i}&=v_i\quad(1\le i\le\ell),&
C_\rho&=\sum_{i=1}^{\ell}v_i,\\
b_\rho(u)&=(c,\beta,h_u),&\beta&=|u|,&
h_u&=C_\rho+\sum_{i=1}^c v_i u_i.
\end{aligned}
$$

Here $|u|$ is integer Hamming weight, field addition has characteristic 2, and $0^0=1$. The correctness domain remains exactly

$$
E_\rho=\left\{R=\rho,\ Q_n=(0,\ell),\
 C_\rho+\sum_{i=1}^n v_i b_i=0\right\},
$$

where $Q_n$ counts payload return circles and marker weight. It is a retrospective event, not a source sampler or an available acceptance bit. By the original joint-source law, every balanced zero-return marker word satisfying the field equation has joint mass with its seed

$$
2^{-d}\sum_{h\ge1}\mu(h)r_h^\ell(1-r_h)^{2\ell}>0,
$$

with the sum replaced by the corresponding fixed-depth term when the depth is fixed. The two halves and seed are not mixed under separate depth draws.

**Definition 116.2 (selected cells, supplemental register and decoder).** For a fixed actual seed and bare address $b=(c,\beta,h)$, put

$$
\begin{aligned}
U_b&=\{u\in\{0,1\}^c:|u|=\beta,\ b_\rho(u)=b\},\\
\mathcal F_b&=\left\{y\in\{0,1\}^{n-c}:|y|=\ell-\beta,\
             \sum_{i>c}v_i y_i=h\right\},\qquad N_b=|\mathcal F_b|,\\
W_b&=\{u\in U_b:\text{no prefix of }u\text{, including }u,\text{ has been selected}\},\\
\mathcal S_b&=\{u\in U_b:\text{the first selection is exactly at }u\},\\
\mathcal S_n^{\rho,e}&=\{u\in\mathcal S_{(n,\ell,0)}:u_n=e\},\qquad e\in\{0,1\}.
\end{aligned}
$$

Suffix indices retain their original full-word positions. These sets are defined on all marker prefixes, without acceptance pruning. In particular $W_b$ is the after-decision active set. The original source rectangle of §§102.2 and 104.2 says that every pair in $U_b\times\mathcal F_b$ is realized by a positive zero-return accepted history with this seed. A causal selector deletes whole past rows, so the corresponding selected and active rectangles are $\mathcal S_b\times\mathcal F_b$ and $W_b\times\mathcal F_b$.

Use the original capacities

$$
D_\rho=\max\left(\{0\}\cup
 \{|\mathcal S_b|:c<n,\ N_b>0\}\cup
 \{|\mathcal S_n^{\rho,0}|,|\mathcal S_n^{\rho,1}|\}\right),
\qquad D=\max_{\rho\in\mathbb F_{2^d}}D_\rho.
$$

Colex orders words by their largest differing coordinate, with 0 before 1 and ranks starting at 0. For each public instance fix the original total function $\mathscr D_\pi$ of §§110.3, 113.2 and 114.1 on its entire nonnegative-integer code domain. At a nonterminal address it inverts rank $z$ in the entire $\mathcal S_b$; at a terminal accepting address it uses the entire block $\mathcal S_n^{\rho,e}$ after the actual $\mathrm{Stop}_e$ is delivered. Its original interface checks and fixed empty-word default are retained. A zero-completion nonterminal address that passes those checks still has its original dictionary outputs at every legal rank. There is no added $N_b>0$ check, suffix-consistency test or truncation of the integer domain to the register's emitted values.

The receiver obtains just one frozen $(\rho,\ell,c,\beta,h)$, frozen $z$, actual remaining marker suffix $Y$, and actual original Stop. It receives no selector state, other snapshot, delivery-time reading or history. $D_{\rm read}$ and $D_{\rm blind}$ minimize the size of one supplemental persistent alphabet $\mathcal Z$ for this same decoder, with the same fixed initial value 0 before seed acquisition and the same register for acquisition and frozen output. Co-read may inspect the paid selector control $\kappa$. Blind may inspect only the original public parameters and acquired $\rho$, synchronous old/new bare fields, current completed marker, its own current $z$, original paid generic parser/root/unselected/frozen/final-marker/Stop phases, and the actually completed continue/first-freeze event. There is no custom phase, private persistent mode, selector address or copy of $\kappa$, past-label stream, prefix, acquisition transcript, future decision or future marker input. Non-marker events and previously frozen paths hold $z$. A triggering transaction writes the new value before the original first-freeze latch.

### 116.2 The classical algebra and the midpoint rectangle

**Lemma 116.3 (cyclotomic supplier with the required parameters).** The polynomial $f=\Phi_{3^{k+1}}$ is irreducible over $\mathbb F_2$. The element $\theta$ has multiplicative order $3H$, and

$$
1,\theta,\ldots,\theta^{2H-1}\text{ is an }\mathbb F_2\text{-basis},\qquad
\theta^{2H}=1+\theta^H.
$$

Proof. The prime-power cyclotomic identity gives $\Phi_{3^{k+1}}=1+X^H+X^{2H}$. For completeness, the order calculation is elementary. For $j\ge0$,

$$
v_3(4^{3^j}-1)=j+1.
$$

At $j=0$ this is $4-1=3$. If $A\equiv1\pmod3$, then $A^3-1=(A-1)(1+A+A^2)$ and, writing $A=1+3b$, one has $1+A+A^2=3(1+3b+3b^2)$, whose 3-adic valuation is 1. This proves the formula by induction. Consequently the order of 4 modulo $3^{k+1}$ divides $3^k$ and divides none of its proper divisors, so it is $H$. The order of 2 is even, since its reduction modulo 3 has order 2. Squaring then shows that this order is $2H$.

The classical finite-field cyclotomic factor-degree theorem now applies with field size 2 and conductor $3H$, which are coprime: every irreducible factor of $\Phi_{3H}$ has degree $\operatorname{ord}_{3H}(2)=2H$. As $\deg f=2H$, $f$ is irreducible. Equivalently, every root of $f$ has exact order $3H$: it is a root of $X^{3H}-1$, and a root of $X^H-1$ would give $f=1$ in characteristic 2. The polynomial $X^{3H}-1$ is squarefree, and the Frobenius orbit of such a root has length $\operatorname{ord}_{3H}(2)$. That is the same factor-degree argument. The basis and displayed relation follow. These are classical supplier facts, not new cyclotomic assertions. $\square$

For a binary word $t=(t_0,\ldots,t_{a-1})$, write $T(X)=\sum_{i=0}^{a-1}t_iX^i$, and let

$$
u(t)=t\,0^{H-a}\,t\,0^{H-a}\,t\in\{0,1\}^{\ell},\qquad
\mathcal A=\{u(t):|t|=a/2\},\qquad W=\binom a{a/2}.
$$

**Lemma 116.4 (the entire relevant midpoint fiber).** At seed $\theta$ and

$$
b_*=(\ell,3a/2,C_\theta),
$$

one has $U_{b_*}=\mathcal A$ and

$$
\mathcal F_{b_*}=\{1-u:u\in\mathcal A\},\qquad N_{b_*}=W>1.
$$

Thus every pair from $\mathcal A\times\mathcal F_{b_*}$, not just a complementary pair, is an actual positive accepted history in the original source.

Proof. A length-$\ell$ word $x$ has zero evaluation at $\theta$ exactly when its binary polynomial $P_x$, of degree less than $\ell$, is divisible by $f$. The quotient is a unique polynomial $T$ of degree less than $a$, including the zero polynomial. Since $a<H$, the three supports in $fT=T+X^HT+X^{2H}T$ are disjoint. Hence such $x$ is exactly $u(t)$, and its integer weight is $3|t|$. Weight $3a/2$ gives precisely $\mathcal A$.

At the midpoint the repeated half-coefficients identify a suffix with a length-$\ell$ word $y$. Its field equation is $\sum_{i=1}^{\ell}\theta^{i-1}y_i=C_\theta$. This is equivalent to zero evaluation of $1-y$. Its weight is $|1-y|=3a/2$. The first part therefore gives the stated entire suffix set. In particular its cardinality is $W$, which is at least 2. The original source rectangle and its positive common-depth mass give the last assertion. No conditional sampler or future readout has been introduced. $\square$

### 116.3 A finite schedule on all marker words

**Lemma 116.5 (the reused matching schedule, including the smallest case).** The $W$ colex-ordered vertices of $\mathcal A$ admit a specified list of $W-1$ perfect matchings, each with $W/2$ ordered edges, in which every unordered pair occurs in exactly one matching. The $W$ different first-$a$-bit keys of the suffixes in $\mathcal F_{b_*}$ can be mapped onto these matchings.

Proof. The integer $W$ is even, since $\binom a{a/2}=2\binom{a-1}{a/2-1}$. If $W=2$, use the sole edge in the sole matching and map both attainable keys to it. This includes $a=2$.

For $W\ge4$, identify the colex-ordered vertices, in that order, with $0,1,\ldots,W-2,\infty$. In round $j\in\mathbb Z/(W-1)$ the first edge is $\{\infty,j\}$, followed, in order $t=1,\ldots,W/2-1$, by

$$
\{j+t,j-t\}.
$$

Every nonzero residue modulo the odd integer $W-1$ has a unique representation as one of $t,-t$ in this range. Thus each round is a perfect matching. An edge incident to $\infty$ has a unique round. For two distinct finite vertices $x,y$, its round is the unique $j=(x+y)/2$ modulo $W-1$, and its edge is then uniquely specified by the sign-pair of $(x-y)/2$. Division by 2 is valid for every odd $W-1$; no primality assumption is needed. This is the matching formula already used in Boundary Dynamics (110.15).

The attainable keys are $1-t$ for $|t|=a/2$ and are all different. Order these $W$ keys by colex, with indices $i=0,\ldots,W-1$, and map index $i$ to round $\min(i,W-2)$. This is onto the $W-1$ rounds. Extend this public map, denoted $J$, to every other binary key of length $a$ by assigning round 0. For $W=2$ use $J=0$ on every key. $\square$

**Definition 116.6 (the selector $\pi_k$).** Initialize a deterministic passive selector before seed acquisition, with no selected bookmark and empty marker-prefix control. It holds during seed extraction and parser non-marker events. Once the actual seed has been acquired, use the following rules.

1. If $\rho\ne\theta$, select the empty payload prefix at the root. The payload still runs to its original Stop.
2. At seed $\theta$, select nothing before $c=d=2H$. At that position continue exactly for prefixes

$$
t\,0^{H-a}\,t\,0^{H-a},\qquad t\in\{0,1\}^a,
$$

and select every other length-$d$ prefix there, independently of any future completion or acceptance.
3. Surviving paths continue through the next $a$ first-half markers. Their midpoint prefixes are

$$
u(t,r)=t\,0^{H-a}\,t\,0^{H-a}\,r,\qquad t,r\in\{0,1\}^a.
$$

Partition these prefixes into the nonempty sets

$$
G_{s,\beta_0}=\{u(t,r):t\mathbin\oplus r=s,\ 2|t|+|r|=\beta_0\}.
$$

Here $\oplus$ is bitwise addition modulo 2. For fixed $s$, $t$ determines $r$, so $|G_{s,\beta_0}|\le2^a$. The distinguished group is $G_{0,3a/2}=\mathcal A$.
4. Continue through the first $a$ actual second-half markers and call their length-$a$ word $q$. In group $\mathcal A$, use matching $J(q)$ from Lemma 116.5. Assign each midpoint prefix its matching edge index $g\in\{1,\ldots,W/2\}$. In every other group, order its members by colex and partition them into adjacent pairs and, if necessary, a final singleton; let $g$ be the resulting block index. In either case select at the absolute marker position

$$
c=\ell+a+g.
$$

All later markers leave this schedule unchanged, regardless of their values.

Implement $\pi_k$ with a fixed initialized finite control that retains the actual marker prefix until its first selection and then holds it. From the empty initial prefix it appends each actually completed marker while unselected, using the resulting prefix to compute the gate, group, key and scheduled index by the rules above. Finite public tables implement these functions, including the matching and rank dictionaries. This specifies a real initialized control, rather than a leaf family lacking an acquisition program. Its state, tables and initialization are separately paid. It is not a small-control claim. None of its prefix, group, key, edge or schedule addresses is exposed to the blind register as a phase or reference. Only the original completed continue/first-freeze event is supplied. Once selected, the bookmark and frozen register are latched while the original source and parser continue.

The rules concern actually completed markers. At any finite seed/retry/return/parser prefix they give the corresponding holding behavior; infinite noncompletion is allowed without a bookmark. The original generic stages distinguish those cases and previous freezing. Formal malformed control addresses may use fixed holding/default transitions; they do not add an actual source event or permit a second bookmark.

### 116.4 Global selected-cell control

**Proposition 116.7 (completeness and all selected cells).** The selector of Definition 116.6 is finite, initialized, causal, passive and complete on every length-$n$ binary marker word. For every actual seed and every nonterminal address, including rejected and zero-completion addresses,

$$
|\mathcal S_b|\le2.
$$

Both terminal Stop blocks are empty. More precisely $D_\theta=2$, $D_\rho=1$ for $\rho\ne\theta$, and $D=2$.

Proof. Each prescribed decision uses only the actual seed and already acquired marker prefix. The only branch with a root selection is the corresponding off-target-seed branch. At the target seed, a path either selects at the gate or reaches one midpoint group. Each such group has at most $2^a$ members, hence at most $2^{a-1}$ blocks; the matching group has $W/2\le2^{a-1}$ edges. For every even $a\ge2$, $a\le2^{a-1}$, so every scheduled relative second-half position $j=a+g$ satisfies

$$
a+1\le j\le a+2^{a-1}\le2^a\le H<\ell.
$$

Thus every complete word is selected strictly before $n=2\ell$. Earlier first selections latch, later rules do not revise them, and every word has exactly one. Bounded marker-prefix control and finite tables give finitely many selector states for each fixed public $k$; arbitrary raw retries and return circles require no unbounded selector counter. These facts prove totality on all finite original event prefixes as well as completeness on full marker words. They do not force a noncompleting source path to finish.

It remains to control all selected cells, rather than just the accepted target group. At an off-target seed the only selected past is the empty word, so every selected fiber is a singleton. Its root has positive completions: for example any first half $x$ followed by $1-x$ is balanced with zero fingerprint at that seed. Hence $D_\rho=1$ there.

At seed $\theta$, the coefficients of the first $d$ positions are a basis by Lemma 116.3. Consequently the field coordinate at $c=d$ is injective on all $d$-bit prefixes. Every gate-rejected selected cell is therefore a singleton, whether or not it has a completion.

Consider any gate survivor with midpoint prefix $u(t,r)$. Write $s=t\oplus r$, $S(X)=\sum_{i<a}s_iX^i$, $B_r(X)=\sum_{i<a}r_iX^i$, and let $p$ be its actual second-half prefix of length $j\le H$, with polynomial $P_j$ of degree less than $j$. Its current bare field and weight obey

$$
\begin{aligned}
h-C_\theta&=(1+\theta^H)S(\theta)+P_j(\theta),\\
\beta&=2|t|+|r|+|p|=\beta_0+|p|.
\end{aligned}
$$

Indeed the midpoint evaluation is $T(\theta)+\theta^HT(\theta)+\theta^{2H}B_r(\theta)=(1+\theta^H)(T+B_r)(\theta)$. After this reduction, all displayed exponents are below $2H$: $\deg S<a<H$ and $\deg P_j<H$. In the basis $1,\theta,\ldots,\theta^{2H-1}$, coordinates $H,\ldots,H+a-1$ of $h-C_\theta$ give exactly $s$. Subtracting $(1+\theta^H)S(\theta)$ then recovers the whole actual word $p$, including its length from $c$. Finally $\beta_0=\beta-|p|$ recovers the group index. This determination uses no completion equation, weight restriction from acceptance or event pruning.

Every scheduled selection lies in this range $j\le H$. Thus a bare address at such a selection determines one group and one actual second-half prefix, hence the key $q$ and, in $\mathcal A$, the matching round. The position determines $g=j-a$. Only the members of that one scheduled block can first select at this address. There are at most two, and appending the same $p$ does not identify distinct midpoint words. No gate cell, root cell or terminal cell shares its position. There are no other selected prefixes. This proves $|\mathcal S_b|\le2$ even when $N_b=0$, including all rejected group/key branches. As every complete word selects before $n$, both $\mathcal S_n^{\rho,0}$ and $\mathcal S_n^{\rho,1}$ are empty for every seed.

Every member of $\mathcal A$ passes the gate and continues through the midpoint decision. Lemma 116.4 therefore gives $W_{b_*}=U_{b_*}=\mathcal A$. For attainment, choose an edge of a matching on $\mathcal A$ and choose $y\in\mathcal F_{b_*}$ whose first-$a$-bit key maps to that round; the map is onto. The edge's two endpoints, followed by this same $y$, are positive accepted histories by Lemma 116.4. They first select together at their edge's position, with the same bare fields. Their selected prefixes are distinct. The remaining part of this actual $y$ certifies $N_b>0$ there. This gives a positive selected cell of size 2, proving $D_\theta=2$ and $D=2$. The argument also applies to the single-edge case $W=2$. $\square$

### 116.5 The lower bound for every legal blind encoder

**Proposition 116.8 (actual identical-input conflicts).** Every legal initialized blind supplemental encoder for this instance and $\mathscr D_{\pi_k}$ has an entire alphabet of size at least $W$.

Proof. Fix one actual finite seed-acquisition transcript giving $R=\theta$, with no discarded equal pair: use $\alpha\beta$ or $\beta\alpha$ for each bit in the public representation of $\theta$. At each fixed source depth this transcript has probability $[r_h(1-r_h)]^d>0$. Use this same transcript for all histories considered below. The blind register begins at the same 0 before it, and the selector begins at its specified fixed initialization; there is no free seed or history-dependent initialization.

For every $u\in\mathcal A$, append the zero-return raw payload realization of its midpoint prefix, interpreting 0 as $\alpha$ and 1 as $\beta\beta$. All these histories reach $b_*$ with no previous selection and with the same original generic completed-marker phase and continue event. Denote the register value there by $z_u$. They are actual extendable histories of the unchanged source. All have midpoint integer weight $3a/2$; no unaccounted phase or elapsed-source-time distinction is supplied to the blind register.

Take any distinct $u,u'\in\mathcal A$. Their vertices share an edge in exactly one matching. Choose a suffix $y\in\mathcal F_{b_*}$ whose key maps to this matching. Both $uy$ and $u'y$ are balanced zero-return accepted words. With the fixed seed transcript their complete raw histories have, for example, the strictly positive common-depth mass

$$
[r_h(1-r_h)]^d r_h^\ell(1-r_h)^{2\ell}
$$

at a fixed depth, or the positive sum of these expressions against the one common prior $\mu$. This is an ordinary positive event of the paid source, not a request to sample conditional on acceptance.

Suppose $z_u=z_{u'}$. Continue these two histories using the same actual zero-return realization of $y$. Their old midpoint bare fields agree. Identical appended markers give identical subsequent old and new bare fields by the original update equations, and their acquired seeds and public parameters are the same. The complete raw continuations are identical, so generic parser stages, current marker transactions and all non-marker events agree as well.

Before the scheduled edge position, both selections continue. During key acquisition no member of either history freezes. After the key, the chosen matching assigns both endpoints to the same edge index $g$; neither endpoint belongs to an earlier edge. Consequently the completed decision event is continue for both until $c=\ell+a+g$, when it is first-freeze for both. These are the actual events of the original selector, not events computed or read from hypothetical future controls. At no intervening transaction do the two histories supply different permissible phases, events, current markers, references or old/new bare fields. Their inaccessible selector controls may differ, but neither control nor its address is an allowed blind input.

The blind transition is a deterministic function of those complete allowed inputs and its one current register value. Induction over the actual event sequence therefore preserves equality of the two values, including the triggering marker's write before the common latch. The same argument covers any separately paid transient calculation, since no additional persistent value or private phase may carry information between transactions. After first-freeze the held register values remain equal.

At reception, the two frozen bare tuples, frozen codes, remaining actual suffixes and actual original Stop values are identical. Their selected pasts are different because their midpoint prefixes were different. A single function $\mathscr D_{\pi_k}$ cannot return both distinct pasts on this one input. This contradicts correctness on both positive accepted histories. Hence $z_u\ne z_{u'}$ for every pair, so at least $W$ different values of the same retained alphabet are actually attained at this midpoint.

The choice of common continuation may depend on the pair. It is only a proof witness within the actual source support and is never supplied to an encoder. The proof uses equality of the completed decision events up to the same freeze; different response functions or a fiber cardinality alone would not justify this induction. $\square$

### 116.6 The quantitative counterfamily

**Theorem 116.9 (original degree-uniform square-root alternative).** For every integer $k\ge2$, the parameters of Definition 116.1 give an irreducible public polynomial $f$ and an explicit initialized finite complete passive selector $\pi_k$ in the original $m=2$ experiment such that

$$
D_{\rm read}(\pi_k)=D(\pi_k)=2,\qquad
W=\binom a{a/2}\le D_{\rm blind}(\pi_k)<\infty.
$$

These conclusions hold for every fixed original hidden depth and every fixed common depth prior throughout acquisition and payload. One can keep the same such depth or prior across the whole family. Every encoder comparison within an instance uses its same original total canonical decoder on the entire original integer domain. In particular

$$
\frac{D_{\rm blind}(\pi_k)}{D(\pi_k)\sqrt n}\longrightarrow\infty.
$$

Proof. Lemma 116.3 validates the field representation, and Proposition 116.7 gives $D=2$ on the whole acquired-seed source. The co-read attainment $D_{\rm read}=D$ and existence of a finite initialized total blind encoder with this same decoder are precisely the suppliers of Boundary Dynamics §§106.3 and 110.3, applied to the finite initialized selector just specified. Their hypotheses hold: all complete marker words select once, the original source and Stop are unchanged, seed acquisition precedes payload, and the one register has its fixed initial value before seed acquisition.

For this particular selector the co-read supplier also has a direct realization. In Definition 116.6's paid prefix-control implementation, hold $z=0$ through acquisition and every continuing marker transaction. At a first selection, use the actual prefix from that readable control, appending the current marker if needed, and the public finite dictionary to write its colex rank in the entire $\mathcal S_b$ before latching. Off-target root selection writes 0. Proposition 116.7 bounds every one of these dictionaries by 2 even at zero-completion addresses, so all these writes lie in $\{0,1\}$. Previously frozen and non-marker events hold; inconsistent formal inputs have the original fixed default. This is a total initialized one-register implementation using only separately paid readable selector state and allowed transaction timing. It supplies exactly the original leaf codes. The positive two-member cell in Proposition 116.7 forces at least two distinct frozen values even for co-read, so the attained value is exactly 2.

Proposition 116.8 supplies the all-encoder blind lower bound. To make the finite upper existence explicit, recall §110.3's supplied program. Its alphabet size is the finite maximum of $D$ and the sizes of all positive after-decision active sets $W_b$ over all actual seeds and nonterminal addresses. In a positive active cell it retains the actual prefix's colex rank in $W_b$. On a marker transaction, inverse lookup at the old allowed address and current $z$ determines that prefix in temporary workspace; append the actual marker, then write its rank in the new $W_b$ on continue, or its canonical rank in the entire new $\mathcal S_b$ on first-freeze. On a new zero-completion cell write 0. A dead cell cannot acquire a positive completion by extension, since the possible suffixes split by the next marker. Thus an accepted history never loses a required distinction through that default. Invalid formal addresses default to 0; seed acquisition, non-markers and previously frozen paths hold. The root value is 0, and all first-freeze writes precede the latch. Here no terminal leaf occurs; the original supplier's actual-Stop block rule remains its terminal definition. Finite tables can evaluate these functions using only allowed transaction inputs, with every temporary prefix cleared afterward. Their preparation, storage, addressing and workspace are separately paid. This gives a total finite blind program, without claiming a small bound or equality with $W$, and leaves the decoder unchanged on all integers. All source witnesses above have positive mass at each original depth, so the same proof works for any single common depth prior.

For divergence, the central binomial coefficient is the largest coefficient in $(1+X)^a$, as follows from the adjacent-coefficient ratio. Summing all $a+1$ coefficients therefore gives

$$
W\ge\frac{2^a}{a+1}>\frac{H}{4(a+1)}.
$$

Also $n=4H+2a\le6H$ and $a\le\log_2 H=k\log_2 3$. Thus

$$
\frac{D_{\rm blind}}{D\sqrt n}
\ge\frac{W}{2\sqrt n}
>\frac{\sqrt H}{8\sqrt6(a+1)}
\ge\frac{3^{k/2}}{8\sqrt6(k\log_2 3+1)}
\longrightarrow\infty.
$$

The endpoint $a=2$, $W=2$ uses the single-edge schedule and still satisfies every finite-instance claim; no large-parameter assumption was used for completeness, selected-cell control or the blind lower bound. This disproves a degree-independent bound $D_{\rm blind}\le C D\sqrt n$ for all the original instances. It leaves intact the fixed-degree and seed-order-dependent bounds of §112 and the explicitly conditional bounds of §114. $\square$

### 116.7 Suppliers and the uncovered embedding

The number-theoretic part is literature-attested. [Anna-Maurin Graner, *Closed formulas for the factorization of $X^n-1$, the $n$-th cyclotomic polynomial, $X^n-a$ and $f(X^n)$ over a finite field for arbitrary positive integers $n$*, arXiv:2306.11183v2, Introduction](https://arxiv.org/html/2306.11183v2#S1) states the coprime-conductor factor-degree theorem used in Lemma 116.3. The prime-power identity and finite-field degree criterion are also supplied by mathlib at the fixed revision `56a005855ea17e0b0958f73ec801ae140b0a1679`: [Polynomial.cyclotomic_prime_pow_eq_geom_sum](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean), [Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible and ZMod.irreducible_of_dvd_cyclotomic_of_natDegree](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/Cyclotomic/Factorization.lean). Their finite-field hypotheses here are $q=2$, $2\nmid3H$, conductor $3H$ and multiplicative order $2H=\deg f$. Reading these declarations is not a compiled application or a Lean certificate for this section.

| Fixed supplier | Exact use and limit |
| --- | --- |
| [Fibonacci Atomic Relation Generation](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§2–5 at `c5e5c2c0f50f73bd6f75b3ecf2ea4e31b6d29226` | The original ordered tree syntax, substitution and composition observations retain their separate meanings. The source alphabet here does not turn quantity recovery into tree/history recovery or supply a universal reduction. |
| Boundary Dynamics §§100.1–100.2, 102.2 and 104.2 at `c5e5c2c0f50f73bd6f75b3ecf2ea4e31b6d29226` | Actual paid uniform seed and one-depth law; positive same-cell past/future rectangles. These supply actual support, rather than an accepted-only source. |
| Boundary Dynamics §§104.3, 105.1–105.2, 106.1–106.3 and 110.1–110.3 at the same pin | Initialized complete finite control, passive bookmark, original Stop blocks and receiver, fixed initial register, total co-read attainment and finite blind attainment with common leaf codes. Control and decoder resources remain supplied and paid. |
| Boundary Dynamics (110.15) and §§110.5–110.6 at the same pin | The round-robin matching and same-input merger argument are reused. The present embedding changes neither the event-aware interface nor the source. The matching does not itself supply the cyclotomic gate or the all-cell bound. |
| Boundary Dynamics §§112–114 at the same pin; this continuation §115 at `ead132fb284340a8b3a70b957a974196f85fecc3` | Periodic/fixed-degree bounds, full-integer decoder identity and the original unresolved degree-uniform alternative remain in their stated scopes. The exponential-fiber and unique-tail obstacles of §114.9 and the response-count/minimum gap of §115 are respected by the pair-specific, identical-event continuations above. The $d=1$ resource bounds of §113 are not extended to this growing-degree family. |
| [Joint Moment Fibers](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md) §42.1 at `718f48862606f2a12a01bf0349a23ee2521010b0` | Its mention of a cyclotomic single-response direction is credited as an existing direction. That section explicitly does not install an instrument or prove an acquisition saving; it supplies no original-source realization of this counterfamily. |

The original packet's formal background also keeps its exact domains. `FinitePrefixAntichainBudget.result` concerns finite antichain prefix budgets; `WellFoundedLeafMassConservation.result` concerns unconditional mass in countable well-founded trees. `CanonicalPredictiveStateSufficiency.canonical_predictive_state_is_sufficient` concerns a finite PMF future-law quotient and conditional independence; `PredictiveStateUnifilarUpdate.unifilar_predictive_update` requires its conditioned-extension relation on an infinite-stream law. Their sources and owning Scribes are respectively `D5/S0/History/{FinitePrefixAntichainBudget,WellFoundedLeafMassConservation}.lean`, `D5/S3/ObserverMemory/PredictionFactors/CanonicalPredictiveStateSufficiency.lean`, `D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate.lean`, and the corresponding `Blueprint/D5/` mirrors with `.scribe.cs` suffix. They are suppliers already identified in the original fixed packet, not proofs of this quantitative embedding. Likewise the fixed-map result in `D5/S3/ObserverMemory/Prediction/ForwardMergePersistence.lean` and its Scribe is structural background for merge persistence; Proposition 116.8 explicitly performs induction under the complete changing transaction inputs. No new formal specialization of any of these results is claimed.

The uncovered `repo-derived` delta is the embedding into the original acquired restart-power source: the length-$d$ basis gate leaves a three-block cyclotomic midpoint rectangle, and the separated high basis coordinates recover the actual suffix prefix and group for every later selected cell. This permits all unordered midpoint pairs to have positive common continuations with identical decision events while every selected cell has size at most 2. Neither classical irreducibility, a large fiber, a perfect-matching table nor a generic finite transducer alone supplies that conjunction. This is a source-specific ordinary mathematical result, with no global originality or exhaustive literature claim.

The fixed comparison from `9d21f183c84b1c4807ee0db33e0c05a1a5bbde2a` to `ead132fb284340a8b3a70b957a974196f85fecc3` is a separate comparison, not a replacement source pin or a newest-dev assertion. Its Boolean-constraint, graph-norm, homological and quantum suppliers have different stated objects. The later AURIC terminal-history, word-purity and environment results, certificate-preserving quotients and strict-real joint-incidence results concern their own observation/action contracts. None is used to grant an extra input, source sampler or decoder change here. This bounded comparison does not assert semantic non-overlap with every repository or literature result.

### 116.8 Resource coordinates and remaining recovery obligations

The measured resource is only the single supplemental retained alphabet: the co-read alphabet is exactly two values, or one fixed data bit; every legal blind alphabet has at least $W$ values, hence needs at least $\lceil\log_2 W\rceil$ fixed data bits. The lower bound counts actual midpoint acquisition values of that same register, not just its final code image. Its frozen accepting outputs are still canonical ranks 0 or 1. No sharp blind minimum, total-memory optimum or physical cost optimum is determined.

The other costs remain distinct and paid:

- The actual $d$-bit seed, acquisition-bit index, extraction phase and first letter of a trial pair, all paid Reads/restorations and equal-pair retries; source service and original payload return circles, parser, true final marker and original Stop production/delivery.
- The public field representation and coefficients, field/integer arithmetic, selector description and actual initialization, its retained marker-prefix control, group/key/edge/schedule tables and their construction, storage and addressing. Co-read access is access to this paid controller; it is not two total machine states.
- Public references and their held availability, old/new field synchronization, current and frozen bare snapshots, original generic stages and latch, transaction workspace, and any local control replay. Workspace is charged even if cleared at the transaction boundary; it cannot retain a hidden blind mode between transactions.
- The common decoder's entire nonnegative-integer input handling, dictionaries and lookup or recomputation work, decoding workspace, and selected-past output materialization, storage and emission. Codes outside the emitted alphabet and legal ranks at zero-completion cells remain duties of the same decoder.

For the particular positive witnesses used in Proposition 116.8, the no-discard seed transcript uses $2d$ paid Reads and a balanced zero-return full payload uses $3\ell$ paid Reads, followed by the original Stop; source restoration/service and local computations still have their own costs. This is a witness count, not a worst-case bound on actual runs. Arbitrarily many seed retries and payload return circles remain possible in the original experiment. A finite program and finite selector control for each public instance do not bound the entire source history, preparation peak, table size, transaction workspace, output costs, elapsed time or energy uniformly in $k$.

The four-expression advance is relative to this original continued-recovery task. Ordered marker positions and paired coefficient incidence supply a spatial relation; causal prefix extension and the actual first-freeze order supply a temporal relation; the original bare snapshot with actual suffix and Stop is the boundary; and the acquired supplemental register is memory used by the same decoder on that same run. The theorem rules out the proposed degree-uniform square-root relation between those two supplemental-memory permissions in this supplied common process. On $E_\rho$, selected markers also recover their literal zero-return payload past through $0\mapsto\alpha$ and $1\mapsto\beta\beta$.

It does not recover an unknown source, hidden depth, the seed-acquisition transcript, full return-circle/raw history, rejected past, physical metric, absolute clock or elapsed duration. Original source service is assumed exactly as in the cited experiment; no physical implementation of it is constructed. Nor are four independently sufficient views of the whole process, full route agreement and dynamic compatibility for all operations, a universal alpha/beta reduction, or total-resource minimality proved. These remain separate obligations of the full four-expression programme. The bounded source-specific counterfamily does not complete that programme.

## 116.99 追加锚

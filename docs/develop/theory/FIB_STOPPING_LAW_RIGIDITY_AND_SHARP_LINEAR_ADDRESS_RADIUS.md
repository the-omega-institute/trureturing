# FIB stopping-law rigidity and sharp linear address radius

For each positive total paid-read budget $k$, one explicit stopping law has exact minimum law-preserving address radius $2k+1$. Every lawful representative of that law makes a read at distance at least $2k+1$ with probability at least $(1+p^k+(1-p)^k)/2$, and the explicit rule attains equality. These conclusions hold at each fixed biased interior parameter, for either original endpoint and every unchanged independent seed space. They concern the full joint law of the seed, actual endpoint, output, return indicator and paid count.

The resulting universal lower bound is linear. Together with the inherited upper bound it gives $2k+1\le\rho_{\mathrm{law}}(k;p,j,\nu)\le2^{k+1}-1$ for $k\ge1$. The exact universal values at budgets zero and one are $0$ and $3$. The universal polynomial-versus-superpolynomial radius question remains open.

**Reference and proof status.** This volume supplies ordinary mathematical statements and proofs, not Lean-kernel evidence or machine admission. Its stopping-law results are an exposition of the supplied stopping-law rigidity proposal and its independent checking proofs. The source, acquisition contract, finite-tree and source-section interfaces, exponential upper bound, and whole-signature result retain their supplier ownership. No external priority claim is made.

**Text convention.** Numbered claims and GitHub math delimiters follow the theory-volume convention. Once integrated, existing text is retained; additions and corrections belong beyond the terminal append anchor. The volume uses the `generic-v1` content convention without asserting ingestion or a ledger state.

## 1. The complete original source and acquisition problem

**Definition 1.1 (One joint law on the original integer clock).** Fix

$$
0<p<1,\qquad p\ne\tfrac12,\qquad j\in\{0,1\},
\qquad \pi_0=1-p,\quad\pi_1=p.
$$

Let $\varphi$ be uniform on $\{0,1\}$, independently of iid Bernoulli$(p)$ spins $(S_\ell)_{\ell\in\mathbb Z}$. With hidden alphabet $\mathcal A=\{a_0,a_1,b_0,b_1\}$, define the original joint hidden-visible law $J_p$ by

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

These are the original emitted-bit coordinates, including every separator. An active transition takes $a_s$ to $b_t$ with probability $\pi_t$ and emits $s\oplus t$; the following transition copies $b_t$ to $a_t$ and emits zero. The stationary state masses are $\pi_s/2$ for each of $a_s,b_s$: incoming mass at $b_t$ is $\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and copying gives the same incoming mass at $a_t$. Thus (1.1) has the ordered hidden-visible cylinder factors of [Original, Proposition 2.1 and (2.2)][Original], including intervals beginning in either state class. Uniform phase and reindexing of the iid spins preserve this one law under an integer shift. In particular $X_tX_{t+1}=0$ at every $t$. Neither the law nor its clock is replaced.

**Definition 1.2 (Actual endpoint table).** The target is the actual $H_j$. Write $H_j=h_{j,\varphi,S_{q_{j,\varphi}}}$, where the entire table is

$$
\begin{array}{c|c|c|c|c}
j&\phi&q_{j,\phi}&h_{j,\phi,s}&2q_{j,\phi}+\phi\\ \hline
0&0&0&a_s&0\\
0&1&0&b_s&1\\
1&0&1&b_s&2\\
1&1&0&a_s&1
\end{array}
\tag{1.2}
$$

Thus $q_{j,0}=j$, $q_{j,1}=0$, and $2q_{j,\phi}+\phi\in\{j,j+1\}$. For instance, when $j=0,\phi=1$, coordinate zero is the separator after active coordinate $-1$, and $H_0=b_{S_0}$. This includes the negative-index seam. The endpoint remains $j$, regardless of the spin coordinate used to describe it. At fixed $j$, the hidden state class $a$ or $b$ determines the source phase as a mathematical event; this does not grant a protocol phase access.

**Definition 1.3 (Unchanged arbitrary seed and lawful events).** Fix any probability space $(\mathsf U,\mathcal U,\nu)$ independent of the entire $J_p$ source, and put $\mathbb P_p=J_p\otimes\nu$. Keep its variable $u$ and distribution unchanged. All random public data and internal randomness are part of this same independent variable; fixed public data may include $p,j,k$. A finite acquired record is an ordered list

$$
r=((t_1,x_1),\ldots,(t_n,x_n))
\in(\mathbb Z\times\{0,1\})^n,
\qquad n\in\mathbb N_0.
\tag{1.3}
$$

A measurable next-event rule uses only those public data, $u$, and this record. Its next event is a read at an integer address, a finite return of a state $A\in\mathcal A$, or indefinite internal continuation without further read or return. A finite event may follow internal waiting; its occurrence, kind, address or output, and finite waiting time are measurable functions of precisely those available data. Waiting therefore supplies no extra source information. The reply to a read at $t$ is only the actual $X_t$ in (1.1).

Every actual call costs one, including repeated addresses, compulsory separator zeros, negative or positive addresses, remote reads and disconnected address sets. Later ignoring a reply never refunds its call. Before a budget is imposed, internal nonreturn after any finite count, including zero, and infinite-read nonreturn are allowed. A protocol may return before reading or output a state from the wrong phase. Null records and the usual measurable completion versions are included.

No new randomizer, source-dependent seed or timing, hidden-state or spin read, phase oracle, half-line or tail observation, reset, source switch, moving endpoint, or erased-coordinate substitution is available. This is the full contract of [Original, Definition 9.1][Original] and [Paid-return, Definition 1.2][PaidReturn]; it imposes no connectedness, consecutiveness or predetermined-address restriction on competitors.

**Definition 1.4 (Hard total cap and full law).** Let $\tau$ be the return time, with $\tau=\infty$ on every nonreturn, and let $N$ count all actual reads. They are separate quantities. A pathwise hard total cap $k\in\mathbb N_0$ requires $N\le k$ on every execution, including nonreturns and exceptional source/seed paths. Put

$$
D=\mathbf1_{\{\tau<\infty\}},\qquad
O=\begin{cases}A&D=1,\\\bot&D=0,\end{cases}
\qquad Z=(H_j,O,D,N),\qquad\bot\notin\mathcal A.
\tag{1.4}
$$

The finite alphabet of $Z$ under the cap is

$$
\mathcal Z_k=\{(h,o,d,n):h\in\mathcal A,\space
o\in\mathcal A\cup\{\bot\},\space
d=\mathbf1_{\{o\ne\bot\}},\ 0\le n\le k\}.
\tag{1.5}
$$

A representative preserves exactly the joint law of $(u,H_j,O,D,N)$ on the original source/seed product. It must therefore preserve correlations with every measurable seed event. A nonreturn at depth $n$ keeps its $n$ paid calls and means internal continuation forever, not a return with an omitted output. A cap only on returning paths is insufficient: a rule making $k+1$ repeated reads and then never returning satisfies every return-only cap but has an $N$-law impossible under total cap $k$.

Literal records, address names, ordered tree shape, potential replies at unvisited nodes, and whole-tree signatures are not preserved statistics. Nor is numerical return time, or equality of original and replacement outputs on each realized source sample, required. Preserving a risk or return marginal alone would be weaker than the required full joint law.

**Definition 1.5 (Radius and universal objective).** A radius-$R$ rule, for $R\in\mathbb N_0$, uses only actual integer read addresses satisfying $|t-j|\le R$. Define $\rho_{\mathrm{law}}(k;p,j,\nu)$ to be the least such radius sufficient to represent every lawful total-cap-$k$ input on this given seed space, with the same full joint law and total cap. Finiteness follows from the inherited construction proved in Section 7. The representative may use arbitrary adaptive addresses and a different tree, labels or acquired record, and may depend on the fixed public $p$. No whole-signature constraint is included.

## 2. The inherited semantic tree interface and a same-seed consequence

**Lemma 2.1 (Semantic normalization, including nonreturn depths).** A lawful total-cap-$k$ rule has a measurable seed-dependent representation by finite binary read trees of height at most $k$. Read nodes carry integer addresses; leaves carry labels in $\mathcal A\cup\{\bot\}$. A leaf's depth is its exact actual paid count, including at a $\bot$ leaf. Normalization preserves $Z$ and every actual read sequence; all formal binary branches can be capped as well.

Proof. Replace finite internal delays by fixed finite delays, retaining the distinction between a finite next event and indefinite internal continuation. At every formal record of length $k$, replace a request for another read by internal nonreturn without that call. Keep a return or an existing internal nonreturn there. On a path already obeying the total cap, this suppresses no actual event. A finite number of finite waits is still finite, so the return indicator, output and count are preserved; only numerical finite timing values can change. The same observation shows preservation of the actual read sequence. Inconsistent or null formal branches are now capped too.

At fixed $u$, unfold the semantic next-event rule. A read has two ordered children, for replies zero and one. A return or internal nonreturn is a terminal with the corresponding label. There is no read at depth $k$, so the tree has at most $2^k-1$ read nodes when $k\ge1$, and none when $k=0$. Repeated addresses remain separate nodes and separate charges. Terminal depths are not padded.

The set $\mathcal T_k$ of these trees is countable: there are finitely many shapes and terminal labellings at bounded height, with a finite tuple of integer labels for each. Give it the discrete sigma-algebra. To prove $u\mapsto T(u)$ measurable, build the finitely many possible positions successively. A preceding record $r(u)$ takes values in a countable set. If $F(u,r)$ is any measurable next-event condition, evaluation at the varying record is measurable because its event is

$$
\bigcup_r\bigl(\{u:r(u)=r\}\cap\{u:F(u,r)\}\bigr).
\tag{2.1}
$$

Induct over the potential positions, using a dummy label where an earlier terminal removes a position. Finite events and indefinite continuation are already measurably distinguished in the contract. Completion versions can be chosen together over the countably many records; product-null changes leave the source-section identities unchanged. This proves the assertion without a regular conditional distribution on singleton seeds. It is the inherited interface of [Original, Theorems 12.2–12.3][Original], not an effective procedure for deciding divergence of arbitrary code. $\square$

**Lemma 2.2 (A seed-independent full law forces its deterministic source sections).** Suppose a total-cap-$k$ input ignores $u$ and has source law $w=(w_z)_{z\in\mathcal Z_k}$. Any lawful representative preserving its full $(u,Z)$ law has, at $\nu$-almost every seed, a normalized deterministic tree with source law exactly $w$.

Proof. For its measurable tree selector from Lemma 2.1, define

$$
a_z(u)=J_p(Z^{T(u)}=z).
\tag{2.2}
$$

This function is measurable because $T(u)$ has countable range. Independence of the source and seed and product-measure integration give

$$
\mathbb P_p(u\in B,Z=z)=\int_B a_z(u)\,d\nu(u)
\qquad(B\in\mathcal U).
\tag{2.3}
$$

Full joint-law preservation makes this equal to $\nu(B)w_z$ for every $B$. Consequently $a_z=w_z$ almost everywhere. Indeed, if $a_z-w_z$ were positive on a set of positive measure, one of its measurable sets where it exceeds $1/n$ would have positive measure; integration there would contradict (2.3). Apply the same argument to its negative. There are finitely many $z$, so intersect their full-measure equality sets. Every seed in the resulting measurable set has precisely $w$ as its deterministic source law.

These are integrals of source sections on the original product, not conditioning on singleton seeds, splitting atoms, or adding randomness. They work for arbitrary atomic or nonstandard seed spaces. Allowed completion versions change neither the integrals nor the conclusion. The general measurable source-section interface is inherited; this lemma records its exact consequence for the seed-independent stopping law used below. $\square$

## 3. A lawful stopping witness and its complete joint masses

**Definition 3.1 (The stopping rule).** For $k\ge1$, put

$$
\psi=1-j,\qquad q=j,\qquad
2q+\psi=j+1.
\tag{3.1}
$$

By (1.2), in phase $\psi$ the actual endpoint is $b_{S_q}$; in the opposite phase it is of class $a$. Let $W_{k,j}$ ignore $u$ and query, in order,

$$
t_i=j+2i+1,\qquad 1\le i\le k.
\tag{3.2}
$$

It returns $a_1$ immediately after the first reply one. If all $k$ replies are zero, it returns $a_0$ after call $k$. Choose fixed finite internal waits. The choice of parity $\psi$ is public address design, not an observation of the actual phase. For budget zero, use the separate convention $W_{0,j}$ that immediately returns $a_0$ without a read.

**Theorem 3.2 (Exact full law of the witness).** Put

$$
T_m=\pi_0^m+\pi_1^m\quad(m\ge1),\qquad T_1=1,
\qquad d_i=T_i-T_{i+1}=\pi_0^i\pi_1+\pi_1^i\pi_0>0.
\tag{3.3}
$$

For every $k\ge1$, $W_{k,j}$ is one $p$-independent lawful rule on the original clock, returning after between one and $k$ paid calls on every formal branch. Its only nonzero source masses are, for $s\in\{0,1\}$,

$$
\begin{aligned}
J_p(H_j=b_s,O=a_1,D=1,N=i)&=\frac{\pi_s}{2}d_i
&& (1\le i\le k),\\
J_p(H_j=b_s,O=a_0,D=1,N=k)&=\frac{\pi_s}{2}T_{k+1},\\
J_p(H_j=a_s,O=a_0,D=1,N=k)&=\frac{\pi_s}{2}.
\end{aligned}
\tag{3.4}
$$

Every other tuple has mass zero, including every $D=0$ tuple and every $N=0$ tuple. For every $B\in\mathcal U$, each displayed joint mass with $u\in B$ is exactly $\nu(B)$ times its displayed value. Its address radius is $2k+1$.

Proof. In phase $\psi$, (3.2) queries active spin edges with left endpoints $q+1,\ldots,q+k$. Their spins $S_{q+1},\ldots,S_{q+k+1}$ are disjoint from $S_q$. The first $r$ replies are zero exactly when those first $r+1$ spins are all equal, an event of probability $T_{r+1}$. For $r=0$ the probability is $T_1=1$. The first one therefore occurs at $i$ with probability $d_i$, while no one in all $k$ calls has probability $T_{k+1}$. Each event is independent of the actual target spin $S_q$.

In the other phase all queried addresses are separators, so every reply is zero and the output is $a_0$ at count $k$. Multiplying by the phase weight $1/2$ and target mass $\pi_s$ proves every line of (3.4). At count $k$ the $a_1$ and $a_0$ outputs are different tuples. The telescope

$$
\sum_{i=1}^k d_i+T_{k+1}=T_1=1
\tag{3.5}
$$

proves normalization in phase $\psi$, and the other phase already has mass one conditionally. The finite lists and next-event decisions are measurable and use only acquired replies. All calls are actual and paid, without an oracle or extra random variable. Independence from the unchanged $u$ gives the rectangle masses. Finally $t_i-j=2i+1$, so the largest distance is $2k+1$. $\square$

## 4. What this full law forces in every representative

**Theorem 4.1 (Stopping-tree rigidity from law alone).** Fix any single allowed $p$ and $k\ge1$. Let $Q$ be any lawful total-cap-$k$ rule on the given independent seed space with the same full $(u,H_j,O,D,N)$ law as $W_{k,j}$. At almost every seed, its normalized deterministic tree has one continuing all-zero branch of $k$ calls. Each such call has parity $\psi$; a reply one returns $a_1$ at that paid depth, and the final zero child returns $a_0$. Its $k$ zero-branch spin edges are distinct, form one consecutive path, and have no vertex at the unchanged target index $q$.

Proof. Lemma 2.2 supplies a full-measure set of good seeds at which the deterministic source law is exactly (3.4). Fix one such seed. Conditional on phase $\psi$, denoted phase $B$ in this proof, the required event $O=a_1,N=i$ has positive mass $d_i$ for every $1\le i\le k$. In the opposite phase, denoted phase $A$, the required output and count are $a_0,k$ with probability one. These phase-conditional statements follow from the preserved endpoint classes $b$ and $a$ in (3.4); phase access is not an operation of $Q$. Both phases have $D=1$ almost surely and no mass at $N=0$.

First derive the stopping structure by induction. The root must read: a return there has count zero, and internal nonreturn has $D=0$. Suppose the first $i-1$ calls on the zero branch have parity $\psi$ and their one children have already returned $a_1$ at their own paid depths. This is vacuous for $i=1$. Phase $A$ surely follows those separator-zero replies, so it must make call $i$ when $i\le k$, since its prescribed count is $k$.

If call $i$ had the opposite parity, its phase-$B$ reply would be identically zero. All earlier one branches have stopped. Thus the positive prescribed phase-$B$ event $O=a_1,N=i$ would force the zero child's next event to be a finite return of $a_1$. Any extra read would increase the count; internal continuation forever would not return. In phase $A$, however, the prior calls impose no spin conditions because they were separators. This new active edge has a zero reply with probability

$$
c=\pi_0^2+\pi_1^2>0.
\tag{4.1}
$$

The very same zero child would return $a_1$ on that positive-mass phase-$A$ event, contradicting its required output $a_0$. Hence call $i$ has parity $\psi$.

Its zero child is now reached surely in phase $A$, so it cannot return $a_1$. The positive phase-$B$ mass $O=a_1,N=i$ must come from its one child, forcing that child's next event to be a finite $a_1$ return at count $i$. For $i<k$, the zero child must lead to a further read: a return or internal nonreturn would violate the phase-$A$ law. At $i=k$ its zero child must return $a_0$. This proves the structure, including $k=1$, from the law itself. No record or tree-shape preservation was assumed.

Let $t'_i$ be these zero-branch addresses and define their spin-edge left endpoints and zero cylinders by

$$
e_i=\frac{t'_i-\psi}{2},\qquad
C_r=\{S_{e_i}=S_{e_i+1}:1\le i\le r\},\qquad C_0=\Omega.
\tag{4.2}
$$

Within phase $B$, for $1\le r<k$, the cylinder $C_r$ is precisely the event $N>r$. Summing (3.4), conditionally on the positive-probability source event $\varphi=\psi,S_q=s$, yields

$$
\begin{aligned}
J_p(C_r\mid\varphi=\psi,S_q=s)
&=\sum_{i=r+1}^k d_i+T_{k+1}=T_{r+1}.
\end{aligned}
\tag{4.3}
$$

For $r=k$, $C_k$ is precisely the $a_0$ output event in phase $B$, and has the same conditional value $T_{k+1}$. Thus (4.3) holds for every $1\le r\le k$ and both spin values. Averaging over $s$ also gives

$$
J_p(C_r\mid\varphi=\psi)=T_{r+1}.
\tag{4.4}
$$

These are ordinary conditionings on finite source events of positive mass, not on singleton seeds. They explicitly retain the dependence on the actual endpoint spin.

Next prove the path geometry. The first edge is one consecutive one-edge path. Suppose the first $i-1$ edges, for $2\le i\le k$, are distinct and form a consecutive path. Their zero constraint has probability $T_i$. An additional integer-line edge either repeats an existing edge, extends an end of this path, or is vertex-disjoint from it. These are exhaustive: a new edge meeting the path can only add an outside neighbor at an end, since every internal edge of a consecutive path is present.

A repetition leaves probability $T_i$ unchanged, contradicting the prescribed smaller $T_{i+1}$. An extension forces one extra independent spin into the constant block and gives exactly $T_{i+1}$. A disjoint edge would instead give $cT_i$, by independence of its two new spins. Put $a=\max(p,1-p)$ and $b=\min(p,1-p)$, so $a>b>0$, $a+b=1$, and $c=a^2+b^2$. Since $a-c=b(a-b)$ and $b-c=-a(a-b)$,

$$
\begin{aligned}
T_{i+1}-cT_i
&=a^i(a-c)+b^i(b-c)\\
&=ab(a-b)(a^{i-1}-b^{i-1})>0
\qquad(i\ge2).
\end{aligned}
\tag{4.5}
$$

So a disjoint edge cannot have the required probability either. Every step extends the path. There are exactly $k$ distinct consecutive edges and $k+1$ consecutive spin vertices. This strict comparison is valid at the one fixed allowed $p$; it uses no polynomial-identity argument obtained by varying $p$.

Finally suppose the actual target index $q$ were one of those vertices. The event $C_k$ would force every other one of the $k$ spins in the path to equal $S_q$. Independence would give

$$
J_p(C_k\mid\varphi=\psi,S_q=s)=\pi_s^k.
\tag{4.6}
$$

But (4.3) requires the same value $T_{k+1}$ for both $s=0,1$, whereas $\pi_0^k\ne\pi_1^k$ because $k\ge1$ and $p\ne1/2$. This contradiction proves detachment from $q$. The argument infers detachment from the full target law rather than imposing a signature or a samplewise coupling. $\square$

## 5. Exact witness radius and sharp forced remote-read probability

**Theorem 5.1 (Exact law-only witness radius).** For every $k\ge1$, every allowed fixed $p$, either $j$, and every given independent seed space, the exact minimum preserving radius for $W_{k,j}$ is $2k+1$ among all lawful total-cap-$k$ representatives of its full joint law. This includes representatives depending on $p$, using the seed measurably, and changing all addresses, tree shapes and labels.

Proof. Fix a good seed of a competing rule as in Theorem 4.1. Write its consecutive zero-branch vertex path as $[L,L+k]\cap\mathbb Z$. Since $q$ is outside it, either $L\ge q+1$ or $L+k\le q-1$.

In the first case its largest queried edge left endpoint is $L+k-1\ge q+k$. One of its actual query addresses is therefore at least

$$
2(q+k)+\psi=j+2k+1.
\tag{5.1}
$$

In the second case its smallest queried left endpoint is $L\le q-k-1$, giving an actual query address at most

$$
2(q-k-1)+\psi=j-2k-1.
\tag{5.2}
$$

Thus a zero-branch address has distance at least $2k+1$ from the unchanged $j$. This is an actual positive-mass obstruction: in phase $A$ all $k$ zero-branch calls are executed surely, and in phase $B$ every zero prefix has the positive probability in (4.4). The forced read is not an unreachable formal node. Integrating over the full-measure good-seed set excludes every smaller-radius representative. The witness itself has radius $2k+1$ by Theorem 3.2, so the bound is attained. The identities $q=j,\psi=1-j$ cover $j=0$ with phase one and $j=1$ with phase zero without moving $H_j$. $\square$

**Theorem 5.2 (Sharp remote-read probability).** Under the same hypotheses every such representative $Q$ satisfies

$$
\mathbb P_p\bigl(\text{some actual paid read }t\text{ has }|t-j|\ge2k+1\bigr)
\ge\frac{1+T_k}{2}.
\tag{5.3}
$$

The witness $W_{k,j}$ attains equality. In particular the probability is one at $k=1$.

Proof. At a good seed let $m$ be the first zero-branch call at distance at least $2k+1$. Theorem 5.1 gives $1\le m\le k$. Every one child returns immediately, so making any threshold-remote read is exactly reaching this call $m$. In phase $A$ this occurs surely. In phase $B$ it occurs precisely when the preceding $m-1$ replies were zero, with probability $T_m$ by (4.3)–(4.4), or $T_1=1$ if $m=1$. Its source-section probability is therefore exactly

$$
\frac{1+T_m}{2}\ge\frac{1+T_k}{2},
\tag{5.4}
$$

because $T_r-T_{r+1}=d_r>0$. The selected tree and this finite-call event are measurable; equivalently $m$ is a function on the countable tree space at good seeds. Integrate (5.4) over the good-seed set. Its complement has measure zero and contributes no negative probability. Lemma 2.1 preserved every actual read sequence, so the inequality holds for the original competitor too, not only its normalized tree. This also excludes evasion by changes on null source or seed paths, even if radius were interpreted almost surely.

For $W_{k,j}$, the distances are $2i+1$, so the threshold is first reached at $m=k$. Its phase-$B$ probability of reaching that call is $T_k$, and its other-phase probability is one. This attains (5.3) on the same seed space without using its randomness. When $k=1$, $T_1=1$. $\square$

## 6. Universal lower bound and exact small budgets

**Corollary 6.1 (Universal linear lower bound).** For every $k\ge1$,

$$
\rho_{\mathrm{law}}(k;p,j,\nu)\ge2k+1.
\tag{6.1}
$$

Proof. $W_{k,j}$ belongs to the full input class on every given seed space. Theorem 5.1 excludes every smaller radius for this one input even against the full representative class. A radius representing every input must therefore be at least $2k+1$. $\square$

**Theorem 6.2 (Exact universal radii at budgets zero and one).** For every allowed $p,j,\nu$,

$$
\rho_{\mathrm{law}}(0;p,j,\nu)=0,
\qquad\rho_{\mathrm{law}}(1;p,j,\nu)=3.
\tag{6.2}
$$

Proof. With cap zero no read is possible. Keep the original measurable seed-dependent return state or internal nonreturn. It has the same full law and no addresses, so the least nonnegative radius is zero. In particular $W_{0,j}$ has radius zero. Neither the positive-budget stopping formula nor (5.3) is asserted at $k=0$.

For cap one, Lemma 2.1 gives at each seed either an immediate terminal or one read $t$ with two terminal labels, including $\bot$ where appropriate. Keep the immediate terminals and both labels of any read tree. Let $\phi$ be the parity of $t$, set $q'=q_{j,\phi}$ from (1.2), and put

$$
B=2q'+\phi\in\{j,j+1\}.
\tag{6.3}
$$

In active phase $\phi$, the old edge touches $q'$ exactly when $t=B-2$ or $t=B$. If it touches, replace its address by $B$. Conditional on this phase and target spin $S_{q'}=s$, either touching direction has reply $s\oplus V$, with $V$ an independent Bernoulli$(p)$ spin. The replacement therefore preserves the entire target/reply law, even though it can change which oriented slot touches the target.

If the old edge is disjoint from $q'$, replace its address by $B+2$. The new edge uses spins $q'+1,q'+2$, disjoint from the target, so both old and new replies are an independent XOR of two Bernoulli$(p)$ spins. In the other source phase, both addresses have the same inactive parity and return the separator zero. The endpoint table is unchanged. Averaging the two phases preserves $(H_j,\text{reply})$ in both cases.

The two kept terminal labels then preserve $(H_j,O,D,N)$, including exact depth one at a nonreturn. Each replacement lies in $[j,j+3]$. The classification is a deterministic measurable map on the countable tree space, independent of $p$. Integrating the per-tree identities over every measurable seed event as in (2.3) proves the required full joint-law identity. Hence radius three suffices for every cap-one input. Theorem 5.1 at $k=1$ gives the matching lower bound three, and Theorem 5.2 says that every representative of that particular witness makes a distance-at-least-three read surely. This upper argument is a one-read specialization of the inherited finite compression interface, not a new general compression theorem. $\square$

## 7. Inherited exponential upper bound and whole-signature comparison

**Definition 7.1 (The stronger oriented whole-tree signature).** For a normalized tree with read positions $v$, addresses $t_v$ and parities $\epsilon_v$, form, separately for each $\phi\in\{0,1\}$,

$$
\mathcal I_\phi=\{*\}\cup\{(v,-),(v,+):\epsilon_v=\phi\},
\tag{7.1}
$$

with indices

$$
\iota_\phi(*)=q_{j,\phi},\qquad
\iota_\phi(v,-)=\frac{t_v-\phi}{2},\qquad
\iota_\phi(v,+)=\frac{t_v-\phi}{2}+1.
\tag{7.2}
$$

The signature records the ordered tree shape, terminal labels and depths, node parities, and the full equivalence relation of equal indices in each $\mathcal I_\phi$. The target slot and minus/plus orientations are distinguished. This includes all potential nodes, even those on incompatible reply branches. There is no relation between slots belonging to different source-phase alternatives. This is the existing signature of [Original, Theorem 12.2][Original] and Address Definition 2.2.

**Lemma 7.2 (Inherited signature sufficiency).** Equal signatures give equal $Z$-laws for every allowed $p$.

Proof. Fix a phase $\phi$. Its slots occupy finitely many distinct spin indices $V$. Each assignment $s:V\to\{0,1\}$ has mass

$$
\prod_{z\in V}\pi_{s(z)}.
\tag{7.3}
$$

Equal signatures identify their occupied indices bijectively through the slots, sending the actual target slot to the target slot. Transporting $s$ preserves its product mass. The target state is $h_{j,\phi,s(q_{j,\phi})}$; the potential reply at an active node is the XOR of its two ordered slot spins, and all inactive-node replies are zero. Thus the entire potential-reply array and $H_j$ have the same conditional law. Average using the original phase weights $1/2,1/2$.

Execution of the fixed ordered tree is a deterministic function of this array: use the reply at each visited node and stop at its terminal. Its label and depth give $O,D,N$, including $\bot$ and the exact depth of nonreturn. Applying this function proves the asserted law identity. This comparison uses finite-coordinate products of the same source; it offers no runtime access to unvisited replies or spins. $\square$

**Lemma 7.3 (Inherited two-capacity packing).** Let $E\subset\mathbb Z$ consist of $m$ distinct spin-edge left endpoints. Adjoin a distinguished target vertex $q'$ to the integer-line graph with edges $\{e,e+1\}$ for $e\in E$. Its occupied vertices admit an injective map fixing $q'$, translating every component without reversal, whose mapped queried edge left endpoints all lie in $[q'-m,q'+m]\cap\mathbb Z$.

Proof. Every component is a consecutive interval of vertices with all its internal edges present; a missing integer-line edge would separate the component. Keep the target component $[q'-l,q'+r]\cap\mathbb Z$ fixed. It has $a=l+r$ edges, allowing $l=r=0$. The detached components have positive edge lengths $\ell_1,\ldots,\ell_C$, total edge count $d=m-a$, and vertex sizes $s_i=\ell_i+1$.

Their sizes split into two groups with totals $x\le d$ and $y\le d+1$. For $C=0$ use empty groups. For $C=1$ put its $d+1$ vertices in the second group. For $C\ge2$, each $s_i\le d-C+2$ since the other $C-1$ components have at least one edge each. In any fixed ordering take the shortest initial segment whose size sum $x$ is at least $C-1$. It exists since the total size is $d+C$. Before its final term the integer sum is at most $C-2$, hence

$$
C-1\le x\le(C-2)+(d-C+2)=d,
\qquad y=d+C-x\le d+1.
\tag{7.4}
$$

Order components by their least original vertex, using that order for the split. Translate the first group's components, in order, into consecutive disjoint vertex blocks occupying $[q'-l-x,q'-l-1]$, and the second group's into blocks occupying $[q'+r+1,q'+r+y]$. Map each vertex by its component's translation. This is injective and fixes the target component. All internal orientations and all equalities among target and edge slots are preserved exactly. Different blocks may have adjacent vertices, but the connecting edge is not a mapped queried edge; adjacency imposes no equality or dependence on distinct iid spins. Repeated occurrences of one edge all use its same mapped pair, while retaining their separate paid nodes.

The smallest occupied vertex is at least $q'-l-d\ge q'-m$, and the greatest is at most $q'+r+d+1\le q'+m+1$. A mapped edge has two consecutive occupied vertices, so its left endpoint is in $[q'-m,q'+m]$. If $m=0$ there is no queried edge to bound. The ordering, split and translations specify the construction without using $p$. $\square$

**Theorem 7.4 (Inherited uniform upper bound, with full same-seed law).** For $k\ge1$, put $M=2^k-1$. Every lawful total-cap-$k$ rule has a lawful representative on the same unchanged seed space with all addresses in

$$
[j-2M,j+2M+1]\cap\mathbb Z,
\tag{7.5}
$$

and with the same full joint law of $(u,H_j,O,D,N)$. The output is capped on every formal branch. Consequently

$$
\rho_{\mathrm{law}}(k;p,j,\nu)\le2M+1=2^{k+1}-1.
\tag{7.6}
$$

For a supplied normalized tree, a single relabelling independent of $p$ preserves its entire signature for both phase alternatives simultaneously. This is Address Theorem 4.1, retained as an inherited result.

Proof. A normalized height-$k$ tree has at most $M$ read nodes. For each parity $\phi$, collect the distinct spin edges

$$
E_\phi=\{(t_v-\phi)/2:\epsilon_v=\phi\},
\qquad m_\phi=|E_\phi|\le M,
\tag{7.7}
$$

and adjoin its actual target $q_{j,\phi}$. Apply Lemma 7.3 separately in each parity, fixing that target and mapping every edge by a translation of its component. For a node of parity $\phi$, let $e'_v$ be its mapped left endpoint and set its one new actual address to

$$
t'_v=2e'_v+\phi.
\tag{7.8}
$$

This assigns an actual integer to every node in one tree before execution. It does not choose between phase-dependent runtime rules. In actual source phase $\phi$, exactly that parity is active, with the packed slot equalities, and all other nodes remain separators. A node has an active-edge constraint only in its own parity. Distinct phase alternatives therefore impose no cross-phase slot constraint; (7.8) realizes both conditional signatures simultaneously.

The new addresses of parity $\phi$ lie between $2q_{j,\phi}+\phi-2m_\phi$ and $2q_{j,\phi}+\phi+2m_\phi$. Formula (1.2) places the base at $j$ or $j+1$, so (7.5) follows. Injectivity and component orientation preserve all slot equalities and inequivalences, with repeated nodes still paid separately. Lemma 7.2 gives the fixed-tree $Z$-law identity. Leaf labels and depths are kept even on internal nonreturn.

For an arbitrary given seed, normalize as in Lemma 2.1. The specified packing is a map $C_j$ on the countable discrete space $\mathcal T_k$, hence measurable. Select $C_j(T(u))$ at seed $u$ and run it with actual replies. Define internal nonreturn on records inconsistent with that tree, making the next-event rule total. The countable measurable partition into selected trees and each tree's finite record tests prove lawfulness. Selection uses only $u$ and public data, with no added coin or source information. For every $z\in\mathcal Z_k$ and $B\in\mathcal U$,

$$
\begin{aligned}
\mathbb P_p(u\in B,Z^{\mathrm{input}}=z)
&=\int_B J_p(Z^{T(u)}=z)\,d\nu(u)\\
&=\int_B J_p(Z^{C_j(T(u))}=z)\,d\nu(u)\\
&=\mathbb P_p(u\in B,Z^{\mathrm{representative}}=z).
\end{aligned}
\tag{7.9}
$$

Since $\mathcal Z_k$ is finite, these rectangles specify the full joint law, on arbitrary seed spaces with their permitted completions. The formal cap follows from the retained tree height. Every step of the fixed-tree packing is independent of $p$, and its product identity holds for every allowed $p$. If the original rule itself uses $p$ as public data, its tree may depend on that fixed $p$; no joint measurability in a varying parameter is asserted. At $k=0$, keep the no-read terminal rule directly. $\square$

**Theorem 7.5 (Inherited exact signature radius and its law-only limitation).** Let $\rho^{\mathrm{sig}}_{k,j}$ be the least radius representing every normalized height-at-most-$k$ tree while preserving the complete Definition 7.1 signature, with target, node-slot positions, orientations, parities, ordered branches, labels and depths fixed. For $k\ge1$,

$$
\rho^{\mathrm{sig}}_{k,j}=2^{k+1}-1.
\tag{7.10}
$$

Its lower-bound witness nevertheless has a radius-zero representative of its full $(u,H_j,O,D,N)$ law. This is Address Theorem 5.2, not a law-only exponential lower bound.

Proof. Theorem 7.4 gives the signature upper bound. For the lower bound, use the complete binary read tree of depth $k$ and enumerate its $M=2^k-1$ read nodes $v_0,\ldots,v_{M-1}$. With $q=j$ and $\psi=1-j$ as in (3.1), give node $v_i$ address

$$
t_i=2(q+1+i)+\psi\qquad(0\le i<M).
\tag{7.11}
$$

Return $a_0$ at every leaf. This is a lawful deterministic rule making exactly $k$ actual calls on every branch. In phase $\psi$, all potential edges together form a length-$M$ path on vertices $q+1,\ldots,q+M+1$, detached from the target $q$. In the other phase every node is a separator.

For any assignment preserving this whole signature, let $b_i$ be the left endpoint of the phase-$\psi$ spin edge at $v_i$. The plus slot of $v_i$ equals the minus slot of $v_{i+1}$ in the original signature, so it forces

$$
b_{i+1}=b_i+1\qquad(0\le i<M-1).
\tag{7.12}
$$

The occupied vertices are therefore exactly $[b_0,b_0+M]\cap\mathbb Z$. Target inequivalence forces $q$ outside this interval. If $b_0\ge q+1$, its last edge has actual address at least $2(q+M)+\psi=j+2M+1$. If $b_0+M\le q-1$, its first edge has address at most $2(q-M-1)+\psi=j-2M-1$. Thus radius at least $2M+1$ is necessary. For $M=1$ equation (7.12) is empty, but the single edge and target inequivalence give exactly the same alternatives. Reflections interchanging oriented slots and translations moving the target do not preserve this signature. This proves (7.10).

For law alone, this input has $O=a_0,D=1,N=k$ constantly. Read the actual address $j$ exactly $k$ times, paying every occurrence, ignore all replies and return $a_0$. The replacement has radius zero and exactly the same full joint law with $H_j$ and every seed event. It preserves neither the potential slot geometry nor the acquired record. Consequently the exponential signature obstruction cannot be used as an exponential law-only obstruction. $\square$

## 8. The unresolved universal target and scope of the result

**Open question 8.1 (Unchanged universal polynomial-versus-superpolynomial radius).** For the complete Definitions 1.1–1.5 problem, does every total-budget-$k$ rule admit an exact full-joint-law representative in a radius bounded polynomially in $k$, or is there a superpolynomial obstruction for that weaker law-only requirement? The required source, endpoint, clock, fixed public bias, arbitrary unchanged independent seed, actual-call charging, adaptive integer addresses and full $(u,H_j,O,D,N)$ objective remain exactly as stated. This is Address Open question 5.3, retained as unresolved.

The established comparison, for every allowed fixed $p,j,\nu$, is

$$
2k+1\le\rho_{\mathrm{law}}(k;p,j,\nu)\le2^{k+1}-1
\qquad(k\ge1),
\tag{8.1}
$$

with the universal values determined here only at $k=0,1$. Corollary 6.1 and Theorem 7.4 prove the two inequalities. A linear lower bound permits polynomial upper growth; an exponential upper bound also permits superpolynomial minimum growth. Neither inequality decides the question. The exact radius $2k+1$ of the one stopping witness is not a universal upper bound at larger budgets.

For this witness the endpoint/output/count law forces one continuing path with $k$ edges. Other laws may combine different histories and labels. Nothing proved here forces exponentially many incompatible potential nodes to maintain simultaneous geometry under law equivalence. A polynomial universal construction must still supply one compatible actual adaptive rule across all branches and both phase alternatives and then a measurable lift on the given seed. Packing each separately realized path would not prove that. A superpolynomial lower construction must still give an obstruction invariant under every lawful law-equivalent representative; the present single-path rigidity supplies only a linear one.

**Boundary 8.2 (Parameters, return and representation).** All positive-budget rigidity claims are at each single allowed fixed biased interior $p$, even against competitors using that public parameter. Equation (4.5) loses strictness at $p=1/2$, and (4.6) loses the unequal-spin contradiction there. At $p=0,1$ the positive stopping masses $d_i$ vanish. These parameters are excluded, not silently included. No joint measurability in varying $p$ is required.

The witness always returns. The comparison class still allows internal nonreturn at any finite paid depth and source-null or inconsistent records. Its prescribed $D=1$ law rules out positive-probability nonreturn for a representative; no allowed operation was removed to obtain that fact. Every count, including a terminal nonreturn count in the general representation, retains all actual calls. Bounds restricted to returns cannot replace the total cap.

Equality of laws is on the original source/seed product and includes every seed event. It does not assert samplewise equality of replies, records, outputs or counts between input and representative. No numerical return-time preservation is promised. The two-phase conditional arguments are calculations within one actual source, not permission to observe its phase or splice incompatible runtime choices. No seed atom is split and no additional randomizer is introduced.

The semantic tree reduction is an existence argument for measurable next-event rules. The explicit packing computes a relabelling only when a complete finite tree, including its internal-divergence terminals, is already supplied. It gives no effective arbitrary-code compiler, divergence decision procedure, or effective selector for arbitrary presentations of seed spaces.

**Boundary 8.3 (Other resources and other open problems).** Address radius is the resource studied here. It is separate from internal work, address encoding, numerical precision, persistent state, physical storage, memory, expected paid-cost optimization and numerical return time. No bound or optimum for those resources follows. Nor does the witness evaluate a larger-budget classification-risk frontier or an optimal adaptive protocol. General finite representative existence, compact attainment and budgeted-return projection remain inherited existence results, not numerical optima established here.

No conclusion is supplied for expected-cost-only inputs, unbounded histories, empirical learning, neural training, kernel verification, whole-domain attainment or global originality. [Original, Open Problem 6.4][Original] about arbitrary-finite hidden attainment and separation is unchanged. The broader autonomous research objective remains active beyond this partial source result; no completion of it is asserted.

## 9. Supplier attribution and mathematical ownership

**Attribution 9.1 (Exact scope of inherited and stopping-law content).** The following are mathematical source attributions. The proofs above carry the claims directly; a checking disposition is not a premise replacing a proof.

| Supplier or content | Scope and ownership |
| --- | --- |
| [Original, Proposition 2.1, (2.2), Definition 9.1 and (9.4)][Original] | The one stationary XOR law, original emitted-bit clock, complete acquisition contract and actual endpoint table. |
| [Original, Theorems 12.2–12.3][Original] | Semantic finite trees, complete oriented slot signature, finite representative existence and measurable same-given-seed source-section representation. Sections 2 and 7 reproduce the needed ordinary arguments; these interfaces are not newly attributed to this volume. |
| [Original, Sections 13–14][Original] | Seed-partition image, compact attainment and budgeted-return projection. They supply background existence conclusions, not a numerical risk optimum here. |
| [Paid-return, Definitions 1.2–1.3 and Section 6][PaidReturn] | Actual paid-call charging, distinction between return-restricted quantities and total count, and resource boundaries. No risk inequality supplies an address argument. |
| *FIB finite paid reads: explicit address compression and the exact whole-signature radius*, Lemmas 3.1–3.2 and Theorems 4.1, 5.2 | The component capacities, target-fixing packing, uniform upper radius $2^{k+1}-1$, exact whole-signature radius and its radius-zero law-only example. Section 7 retains their proofs and existing ownership. |
| Supplied stopping-law rigidity proposal, partial theorem, complete joint masses, proof and corollaries; independent checking proofs C1–C10 | The explicit $W_{k,j}$, law-forced stopping structure, fixed-$p$ path and target-detachment proof, exact witness radius $2k+1$, sharp probability $(1+T_k)/2$, universal linear lower bound and exact zero/one-budget conclusions. Sections 3–6 present these results with full ordinary proofs. |
| Independent checking proofs C11–C13 | The inherited upper-bound verification, stronger-signature distinction and unresolved universal target, with their original mathematical ownership retained. |

The relative increment over the three supplied theory texts is stopping-law rigidity, its sharp law-only radius and remote-read probability, and the consequent universal linear lower bound. The one-read upper specialization is not a new general compression theorem. The proposal and checking proofs own the supplied partial results; this volume consolidates their mathematical exposition. Finite iid products, elementary integer-line path geometry and product-measure integration retain their usual meanings and are not claimed as new general methods.

**Literature status and proof boundary.** The stopping-law synthesis is `repo-derived` relative to the supplied mathematical sources. No external literature search or claim of worldwide priority supports it. Existing nested literature attributions are not promoted to independent certification. The assertions here rest on the ordinary proofs written in this volume, not on numerical execution, approval, machine admission or a kernel certificate. The unresolved universal question and the distinct original attainment problem remain as stated.

[Original]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[PaidReturn]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md

## 追加锚（本行以下为增补区）

# KBONACCI complete-controller memory

**定义 40.0（Parent source and numbering）。** Sections 40–41 use the weights, actual joint source and INITIAL contracts of [Self-calibrating boundaries](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md). References to its Sections 15–27 and their numbered formulas retain that parent scope; Sections 40–41 and formulas bearing those prefixes belong to this volume. The controller is deterministic, every running instruction emits an actual complete block, and all program, branch, saved INITIAL-value and persistent literal-output memory is included in its finite state set. A probability law over proposed output labels is a different object from this controller.

## 40. Exact complete-controller memory at the seven-phase three-block fee

Section 26 prices emitted blocks for its dyadic INITIAL target family $(k,m)=(2^{r+1}-2,2^r)$, $r\ge3$. The present section returns to the seven-phase experiment $(k,m)=(6,4)$ of Section 24 and minimizes the complete controller state count at adaptive worst fee at most three blocks, including internal control and persistent outputs. The GLOBAL fee objective in Section 26 retains its own contract; the complete-controller objective below allows adaptive branches.

Section 27's full INITIAL internal even-support zero/one/three fee classification retains its own $m\ge5$ parameters, INITIAL targets and GLOBAL fee contract. It does not alter the original $(6,4)$ result or supply its complete-controller memory optimum.

**定义 40.1（Original experiment and complete finite controller）。** Fix the original order $k=6$ and block width $m=4$ of Definition 24.1. Its weights and matched binary coefficients are

$$
G_i=2^i\quad(0\le i<6),\qquad
G_i=\sum_{h=1}^{6}G_{i-h}\quad(i\ge6),\qquad
\gamma_i=G_i\bmod2=\mathbf1_{\{0,6\}}(i\bmod7).
\tag{40.1}
$$

The coefficient equality is supplied by (15.1), equivalently (24.2), and the [minimal modular observer, Section 13, (30)–(31), and Theorem 14.1](https://github.com/the-omega-institute/trureturing/blob/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md). Bits are read in increasing original weight order. A live history $w=w_0\cdots w_{N-1}$ has length divisible by four, avoids six consecutive ones, and has record $(x,\theta,s)$ with $x=\sum_{i<N}w_iG_i\bmod2$, $\theta=N\bmod7$, and terminal run $s$. Rejected histories have the distinct absorbing record $\bot$. The source is the full actual joint image

$$
Q=(\mathbb F_2\times\mathbb Z/7\mathbb Z\times\{0,1,2,3,4,5\})\sqcup\{\bot\}.
\tag{40.2}
$$

All $84$ live INITIAL triples and bottom are included, with unknown history and length. Joint realization is supplied by Lemma 15.1: choose $N\ge s+2$, $N\equiv0\pmod4$, $N\equiv\theta\pmod7$, set $e=\bigoplus_{i=N-s}^{N-1}\gamma_i$, and take

$$
w=(x\oplus e)0^{N-s-1}1^s.
\tag{40.3}
$$

Coprimality permits arbitrarily large such $N$. The first bit has coefficient one, the zero interval separates it from the terminal run, and this same legal word attains all three coordinates. The complete-block history $11111100$ attains $\bot$. These unobserved witnesses are not controller inputs or continuation fees.

Both original action alphabets are retained separately and here coincide:

$$
\mathcal A_{\rm all}=\{0,1\}^4,
\qquad
\mathcal A_{\rm loc}=\{B\in\{0,1\}^4:B\text{ internally avoids }1^6\}
=\{0,1\}^4.
\tag{40.4}
$$

Each action executes all four bit updates in its displayed order. On current live record $(y,\phi,t)$, zero gives $(y,\phi+1,0)$; one gives $(y\oplus\gamma_\phi,\phi+1,t+1)$ if $t<5$, and gives $\bot$ if $t=5$. Both bits preserve $\bot$. Phase arithmetic is modulo seven. Let $T_B$ be this fourfold composition and $o(y,\phi,t)=y$, $o(\bot)=\bot$, with response alphabet $O=\{0,1,\bot\}$. Only $o(T_B(q))$ is read after an action; interior values are unavailable. The original word $1111$ remains an available action and succeeds whenever its inherited tail permits it.

There is one free INITIAL observation $o(q_{\rm INITIAL})$. The immutable targets and bottom labels are

$$
\begin{aligned}
f_{\rm ph}(x,\theta,s)&=\theta,& f_{\rm ph}(\bot)&=0,\\
f_{\rm vp}(x,\theta,s)&=(x,\theta),& f_{\rm vp}(\bot)&=(0,0).
\end{aligned}
\tag{40.5}
$$

Neither target is evaluated on a later record. These are the conventions of Definitions 18.1 and 24.1 and the [irreversible target-acquisition volume, Definitions 1.2 and 2.1, Convention 1.3, and Open Problem 11.2](https://github.com/the-omega-institute/trureturing/blob/3d77b305316f29834675427be4c971ad06e73b57/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md).

A complete deterministic finite controller for a target with codomain $Y$ is $(K,c,u,v)$, with finite state set $K$ and total maps

$$
\begin{aligned}
c&:O\longrightarrow K,\\
u&:K\longrightarrow
 \{\operatorname{Emit}(B):B\in\{0,1\}^4\}
 \sqcup\{\operatorname{Halt}(a):a\in Y\},\\
v&:K\times O\longrightarrow K.
\end{aligned}
\tag{40.6}
$$

Initialize once to $c(o(q_{\rm INITIAL}))$. At state $z$, Halt returns its literal label and persists: $v(z,o)=z$ for every $o$. Emit executes its word, reads its endpoint, and moves to $v(z,o(T_B(q)))$. All usable stages, branch selectors, saved INITIAL values, input/output archives, stopping decisions and persistent output states belong to $K$. No external counter, archive, clock, source promise, reset, copy, interior read or further free device read is supplied. The physical device record remains part of the experiment but is not a separately accessible controller register. Cycles and sharing across branches or execution depths are allowed.

Each actually emitted block costs one, or four emitted bits. Clearing, waiting, padding and remaining bits after internal rejection execute and are charged. Halt costs no block. Success means finite stopping with $f(q_{\rm INITIAL})$ for every source. Define

$$
M_3(f)=\min\{|K|:(K,c,u,v)\text{ is complete and successful with worst emitted fee }\le3\}.
\tag{40.7}
$$

Running and Halt states both count. Theorem 24.2 already supplies adaptive worst-fee minimum three and the separate one-GLOBAL-stream minimum four. The additional question here is complete memory at that adaptive fee; GLOBAL common-word constraints are not imposed.

**定理 40.2（Exact complete-controller minima）。** Under Definition 40.1, separately for either original alphabet,

$$
\boxed{M_3(f_{\rm ph})=18=11+7,\qquad
M_3(f_{\rm vp})=26=12+14.}
\tag{40.8}
$$

Every successful complete controller at worst fee at most three needs at least eleven, respectively twelve, running states and seven, respectively fourteen, persistent literal Halt states. Both bounds are simultaneously attained. Bottom reuses a live output label.

Proof. Put $j=-\theta_{\rm INITIAL}\pmod7$, represented in $0,\ldots,6$. After $h$ blocks current phase is $-j+4h$; $h$ is only a proof index. Reuse the literal charge law (24.7)–(24.8), for any nonrejecting $B=abcd$:

$$
\begin{aligned}
(R_0(B),\ldots,R_6(B))&=(a,a\oplus b,b\oplus c,c\oplus d,d,0,0),\\
y_{h+1}\oplus y_h&=R_{j-4h}(B),\qquad
\bigoplus_{i=0}^{6}R_i(B)=0.
\end{aligned}
\tag{40.9}
$$

Here $d$ is the fourth bit. The controller receives absolute endpoint values, not increments or phase indices.

### 40.1 Unrestricted lower bound

The common-tail capacity argument of Corollary 19.3 applies in this form. Candidates at one controller state, with one common current tail and at most $h$ further blocks each, may have different current values, phases, origins and earlier histories. The selected word rejects all or none, since legality depends only on tail and bits. Common rejection gives identical absorbing responses and identical future controller evolution, so only one required label can succeed. Otherwise there are at most two endpoint children, each again with common tail. Early Halt also yields one label. Induction from $h=0$ permits at most $2^h$ distinct labels in such a successful support. Bottom is not a third useful distinguishing response.

Fix free INITIAL value $x$. Its root must run because seven labels occur. A first bit one rejects the actual sources $(x,\theta,5)$ for every $\theta$, irreversibly merging unequal labels. Every root therefore starts zero, is safe on all old tails and gives a common endpoint tail. For root $0bcd$, (40.9) gives an even-sized positive set contained in $\{1,2,3,4\}$; its zero set contains $0,5,6$. Each child has two blocks left and capacity four. Positive-set sizes zero and two leave seven and five labels in the zero child. Thus its size is four, forcing $b=b\oplus c=c\oplus d=d=1$. This recovers the root of (24.11):

$$
B_{\rm root}=0101,\qquad A=\{1,2,3,4\},\qquad Z=\{0,5,6\}.
\tag{40.10}
$$

It ends in tail one and both children must run. Roots $c(0),c(1)$ are distinct: if equal, response zero puts $x=0,j\in Z$ and $x=1,j\in A$ in one successor, with common tail one, seven different labels for either target, and only two blocks left.

Name the four first-block occurrences $A_0,A_1,Z_0,Z_1$, retaining INITIAL $x$; these are not yet assumed distinct states. All sixteen second words are safe from tail one. At $A_x$, second word $abcd$ has increments $(d,0,0,a)$ at $j=1,2,3,4$, by (24.12). Each child has one block left and capacity two. Thus $a=d=1$, allowing independently any of $1001,1011,1101,1111$. The mandatory pairs are

$$
P=\{2,3\},\qquad Q=\{1,4\},\qquad
y_P=x\oplus1,\quad y_Q=x
\quad\text{after two blocks}.
\tag{40.11}
$$

Their inherited tails may depend on the middle bits and are retained.

At $Z_x$, second-word increments at $j=0,5,6$ are $(c\oplus d,a\oplus b,b\oplus c)$. A constant response leaves three labels for one block and is impossible; hence a singleton and a pair remain. At final depth every word $efg\ell$ has row

$$
(r_0,r_1,r_2,r_3,r_4,r_5,r_6)
=(0,e,e\oplus f,f\oplus g,g\oplus\ell,\ell,0).
\tag{40.12}
$$

Pair $\{0,6\}$ already has common current value and tail and has identically zero final increments. No last word splits it, whether safe or uniformly rejecting. The mandatory $Z_x$ pair $T_x$ must be $\{0,5\}$ or $\{5,6\}$. Its singleton may Halt or continue for another block.

The four first-block states are distinct. For value-phase any two supports have at least six distinct INITIAL labels, common tail one and two blocks left, exceeding capacity four. For phase any $A/Z$ union has seven labels and fails likewise. If $A_0=A_1$, their common second word acts on complementary current values for each $j$. Either absolute next response then puts all four $A$ phase labels in one successor with common tail and one block left, exceeding capacity two. The same argument for $Z_0=Z_1$ gives three labels in either successor and fails. No common-second-word constraint is imposed on different states.

There are six mandatory final-pair occurrences $P_x,Q_x,T_x$, $x=0,1$. Each pair has common tail and two unequal labels, so its last word must be safe and give both absolute responses zero and one. Both fixed successors must immediately Halt because the actual executions have spent three blocks. Pairs sharing one final running state must use a word safe for each, even with different tails, and fit all labels into its same two Halt successors. A union of more than two pair labels cannot share.

For value-phase all six pair target sets are disjoint: within $x$ their phase sets differ, and across $x$ their immutable first coordinates differ. Six final running states are necessary.

For phase, different sets from $P,Q,T$ cannot share since their label union has more than two elements. The two $P$ occurrences across $x$ cannot share either, despite equal phase-label sets. Their corresponding $j$ have complementary current values by (40.11) and equal current phase $-j+8$. A common safe word adds the same increment, so their absolute responses remain complementary. One occurrence needs two different Halt labels on zero and one; the other needs the assignments reversed. A single $v$ cannot do both. Rejection of either occurrence instead destroys its distinction. This argument permits different tails. The same obstruction holds for the two $Q$ occurrences. These four $A$-derived final states need at least one additional $T$ state, giving five. The two $T$ occurrences may share when actual current values align.

These depth counts cannot collapse. Every root uses $0101$. At a first-block $A$ occurrence that word gives increments $(1,0,0,0)$, leaving three labels together; at $Z$ it gives $(1,1,1)$, also leaving three. Neither can finish in one further block, so roots cannot equal first-block states. Every mandatory final-pair state has both binary successors Halt. Roots have both successors running, and every first-block state has at least one running successor because a pair remains. Final-pair states cannot equal either earlier type. These are conflicts of fixed instructions and successors, not a tree-node count or an acyclicity assumption. Cycles, cross-depth and cross-branch reuse, and singleton continuation cannot remove them.

Thus running-state lower bounds are $2+4+5=11$ and $2+4+6=12$. Seven, respectively fourteen, live labels occur on actual sources and require distinct literal Halt states because $u$ is a function. Halt states are disjoint from running states. Bottom's label is already live. The total lower bounds hold over every complete controller (40.6).

### 40.2 Complete eighteen-state phase attainment

Let $K$ contain the eleven running states below and seven states $H_0,\ldots,H_6$. Define $u(H_\theta)=\operatorname{Halt}(\theta)$ and $v(H_\theta,o)=H_\theta$ for every $o$. Initialization is $c(0)=R_0$, $c(1)=R_1$, $c(\bot)=H_0$. The table supplies every running instruction and response. Rank is a mathematical function on $K$, zero at every Halt.

| Phase state | Emitted word | Response $0$ | Response $1$ | Response $\bot$ | Rank |
| --- | --- | --- | --- | --- | --- |
| $R_0$ | $0101$ | $Z_0$ | $A_0$ | $H_0$ | $3$ |
| $R_1$ | $0101$ | $A_1$ | $Z_1$ | $H_0$ | $3$ |
| $A_0$ | $1111$ | $Q_0$ | $P_0$ | $H_0$ | $2$ |
| $A_1$ | $1111$ | $P_1$ | $Q_1$ | $H_0$ | $2$ |
| $Z_0$ | $0100$ | $H_0$ | $S$ | $H_0$ | $2$ |
| $Z_1$ | $0001$ | $H_0$ | $S$ | $H_0$ | $2$ |
| $P_0$ | $0110$ | $H_5$ | $H_4$ | $H_0$ | $1$ |
| $P_1$ | $0110$ | $H_4$ | $H_5$ | $H_0$ | $1$ |
| $Q_0$ | $0110$ | $H_6$ | $H_3$ | $H_0$ | $1$ |
| $Q_1$ | $0110$ | $H_3$ | $H_6$ | $H_0$ | $1$ |
| $S$ | $0001$ | $H_2$ | $H_1$ | $H_0$ | $1$ |

Actual live supports follow. Every listed $(x,j)$ includes all six INITIAL old tails. Current phase at depth $d$ is $-j+4d$.

| State | Depth $d$ | INITIAL $x$ | INITIAL $j$ support | Current value | Current tail |
| --- | --- | --- | --- | --- | --- |
| $R_x$ | $0$ | $x$ | $0,1,2,3,4,5,6$ | $x$ | $0,1,2,3,4,5$ |
| $A_x$ | $1$ | $x$ | $1,2,3,4$ | $x\oplus1$ | $1$ |
| $Z_x$ | $1$ | $x$ | $0,5,6$ | $x$ | $1$ |
| $P_x$ | $2$ | $x$ | $2,3$ | $x\oplus1$ | $5$ |
| $Q_x$ | $2$ | $x$ | $1,4$ | $x$ | $5$ |
| $S$ | $2$ | $0$ | $5,6$ | $1$ | $0$ |
| $S$ | $2$ | $1$ | $5,6$ | $1$ | $1$ |

The root's first zero safely clears every old tail inside its paid block and ends in tail one. Second word $1111$ safely reaches tail five, and $0110$ then starts zero. Other second words start zero and are safe; final $0001$ is safe from both tails at $S$. No live source rejects.

By (40.9), $0100$ on $Z$ at depth one has increments $(0,1,1)$ at $j=0,5,6$; $0001$ has $(1,0,0)$. Thus $Z_0$ uses $0100$ and $Z_1$ uses $0001$, sending their singletons to $H_0$ and their pairs to $S$ with current value one. The two tails at $S$ differ, but its zero-first word is safe for both. At final depth $0001$ adds one at $j=5$ and zero at $j=6$, giving absolute values zero and one and labels $H_2,H_1$. This merger uses actual correlated supports without identifying their entire device records.

For $0110$, final row (40.12) is $(0,0,1,0,1,0,0)$; the support values give exactly the listed $P/Q$ labels $-j\pmod7$. All running transitions strictly lower rank, including bottom transitions. Rank is determined by the state and supplies no external countdown. Termination takes at most three emissions. Each of the eleven running states and seven persistent Halts is reached by an actual source.

### 40.3 Complete twenty-six-state value-phase attainment

Use twelve running states below and fourteen states $H_{x,\theta}$, $x\in\mathbb F_2$, $\theta\in\mathbb Z/7\mathbb Z$. Set $u(H_{x,\theta})=\operatorname{Halt}((x,\theta))$ and $v(H_{x,\theta},o)=H_{x,\theta}$ for all $o$. Initialization is $c(0)=R_0$, $c(1)=R_1$, $c(\bot)=H_{0,0}$. Every Halt has rank zero.

| Value-phase state | Emitted word | Response $0$ | Response $1$ | Response $\bot$ | Rank |
| --- | --- | --- | --- | --- | --- |
| $R_0$ | $0101$ | $Z_0$ | $A_0$ | $H_{0,0}$ | $3$ |
| $R_1$ | $0101$ | $A_1$ | $Z_1$ | $H_{0,0}$ | $3$ |
| $A_0$ | $1111$ | $Q_0$ | $P_0$ | $H_{0,0}$ | $2$ |
| $A_1$ | $1111$ | $P_1$ | $Q_1$ | $H_{0,0}$ | $2$ |
| $Z_0$ | $0100$ | $H_{0,0}$ | $S_0$ | $H_{0,0}$ | $2$ |
| $Z_1$ | $0100$ | $S_1$ | $H_{1,0}$ | $H_{0,0}$ | $2$ |
| $P_0$ | $0110$ | $H_{0,5}$ | $H_{0,4}$ | $H_{0,0}$ | $1$ |
| $P_1$ | $0110$ | $H_{1,4}$ | $H_{1,5}$ | $H_{0,0}$ | $1$ |
| $Q_0$ | $0110$ | $H_{0,6}$ | $H_{0,3}$ | $H_{0,0}$ | $1$ |
| $Q_1$ | $0110$ | $H_{1,3}$ | $H_{1,6}$ | $H_{0,0}$ | $1$ |
| $S_0$ | $0001$ | $H_{0,2}$ | $H_{0,1}$ | $H_{0,0}$ | $1$ |
| $S_1$ | $0001$ | $H_{1,1}$ | $H_{1,2}$ | $H_{0,0}$ | $1$ |

The $R,A,Z,P,Q$ supports are those above. Both $Z_x$ states now use $0100$: the $j=0$ singleton reaches $H_{x,0}$ and $S_x$ has $j=5,6$, current value $x\oplus1$ and tail zero. Word $0001$ gives the listed final responses. Legality and rank decrease follow as above. The first output component is remembered INITIAL $x$, never current or final device value. Every running state and all fourteen Halts are reached.

In either construction, twelve live records with $j=0$ emit two blocks, the other seventy-two emit three, and INITIAL bottom emits none. The worst fee is exactly three blocks or twelve emitted bits, including all zero and one bits. The tables, initialization, Halt loops and bottom conventions specify complete $(K,c,u,v)$ without separate output latches or program stages. They attain both running and output lower bounds, proving (40.8). $\square$

The identification method has mature primary precedents. E. F. Moore, [*Gedanken-Experiments on Sequential Machines* (1956), printed pp. 129–131](https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf), treats adaptive identification of one machine's beginning state, distinguishes multiple-copy experiments, and includes absorbing destructive failure. Petra van den Bos and Frits Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2, Section 4, Definition 11 and Figure 3](https://arxiv.org/html/1907.11034v2), supply adaptive distinguishing graphs and irreversible-merger context. One input here is one complete block, one observation its actual endpoint, and only unequal immutable INITIAL labels need separation. A. Larrauri and R. Bloem, [arXiv:2105.10292v2, Section 5, Theorem 4](https://arxiv.org/html/2105.10292v2), supply minimization by closed compatible covers of a given observation machine, with initial coverage and successor closure. Total tables above supply closure; the forced-state incompatibilities separately range over all permitted policies. Minimizing one preselected tree alone would not prove that bound. These suppliers provide methods, not equality (40.8). The coefficient, source, charge, root and optimal-fee results of §§15, 18 and 24 retain their credited roles. Equality (40.8) is a `repo-derived` source-specific ordinary mathematical deduction without a global novelty or priority claim.

**命题 40.3（Conditional static names and the missing operational correspondence）。** Suppose state names are freely chosen fixed-length binary words avoiding $11$, each with a preceding zero seam. Abstract names do not restrict actions. The elementary Fibonacci count is $F_{\ell+2}$ at length $\ell$, with $F_1=F_2=1$: partition by final zero or final $01$ to obtain the recurrence, starting with counts one at length zero and two at length one. Hence (40.8) gives conditional static naming requirements

$$
F_7=13<18\le F_8=21\quad\Longrightarrow\quad\ell_{\rm ph}=6,
\qquad
F_8=21<26\le F_9=34\quad\Longrightarrow\quad\ell_{\rm vp}=7.
\tag{40.13}
$$

Unrestricted binary names require five bits for either count. These capacities neither recode original action $1111$ nor impose a no-$11$ action alphabet, and assign no installation, update, readout, gate, time, energy or physical-memory costs. The missing operational FIB/KB correspondence must relate actual sources, observations, literal actions, updates, stopping and immutable INITIAL targets, preserving every original legal word, absorbing failure and every emitted fee. Accessible state-name storage and maintained access costs also need that correspondence. Static naming does not supply it. Other parameters, INITIAL targets and native fee transport retain their separate mathematical obligations.

## 追加锚（本行以下为增补区）
## 41. Exact complete-controller memory at fee at most one for full INITIAL even supports

Section 27 supplies the full INITIAL internal even-support family and its emitted-block fee classification. Here the resource is the number of states of a complete finite controller at worst emitted-block fee at most one. The complete-controller convention of Definition 40.1 is used with length-$m$ literal actions. Its seven-phase fee-three minima $18$ and $26$ retain their separate parameters and targets. The result below concerns the Section 27 family, permits adaptive selection using the single free INITIAL reading, and counts every running and persistent output state.

**定义 41.1（Original joint source, INITIAL target and complete memory）。** Fix

$$
m\ge5,\qquad k=2m-2,\qquad T=k+1=2m-1,
\qquad U=\{2,\ldots,m-1\},\qquad P=\mathbb Z/T\mathbb Z.
\tag{41.1}
$$

Retain the original weights $G_i=2^i$ for $0\le i<k$ and $G_i=\sum_{h=1}^kG_{i-h}$ thereafter, with bits read in increasing original weight position. The supplied matched coefficient cycle is

$$
c_i=G_i\bmod2=\mathbf1_{\{0,T-1\}}(i\bmod T),
\tag{41.2}
$$

extended periodically to integer indices. At complete-block endpoints the live record is $(v,\theta,s)$, where $v\in\mathbb F_2$, $\theta\in P$, and $0\le s<k$ is the inherited terminal run of ones. The independent rejection record is $\bot$. On a live record the literal bit operations are

$$
\begin{aligned}
d_0(v,\theta,s)&=(v,\theta+1,0),\\
d_1(v,\theta,s)&=
\begin{cases}
(v\oplus c_\theta,\theta+1,s+1),&s+1<k,\\
\bot,&s+1=k,
\end{cases}\\
d_b(\bot)&=\bot\qquad(b\in\{0,1\}).
\end{aligned}
\tag{41.3}
$$

Phases are modulo $T$. The source is the image of all actual finite original complete-block histories, including empty and rejected histories. Since $\gcd(m,T)=1$, it is exactly

$$
Q=(\mathbb F_2\times P\times\{0,\ldots,k-1\})\sqcup\{\bot\}.
\tag{41.4}
$$

The simultaneous history witnesses establishing this equality are given below. Thus (41.4) is an actual joint source, rather than a product of separately reachable marginals. INITIAL history and length are unknown and unavailable to the controller.

Choose even subsets $H_0,H_1\subseteq U$, allowing either to be empty. Choose labels $A_v,B_v\in Y$ with $A_v\ne B_v$ separately for $v=0,1$, and an arbitrary $y_\bot\in Y$. There is no restriction on cross-value or bottom-label coincidences. With $j=-\theta_{\rm INITIAL}\pmod T$, represented by $0,\ldots,T-1$, the target is

$$
f(v,-j,s)=
\begin{cases}
B_v,&j\in H_v,\\
A_v,&j\notin H_v,
\end{cases}
\qquad 0\le s<k,\qquad f(\bot)=y_\bot.
\tag{41.5}
$$

Every target value refers to the immutable INITIAL record. In particular, later scalar changes never change the required $v$ in (41.5). Every phase outside $U$, every inherited legal tail, and initial bottom remain in the source.

Both original action alphabets separately equal $\{0,1\}^m$ here: a word of length $m<k$ cannot internally contain $1^k$. This equality of literal action sets does not remove rejection across the seam with the inherited tail. For $X=X_0\cdots X_{m-1}$, let $T_X=d_{X_{m-1}}\circ\cdots\circ d_{X_0}$. Execute every one of these $m$ updates. The response alphabet is $O=\{0,1,\bot\}$, with $o(v,\theta,s)=v$ and $o(\bot)=\bot$. Only the absolute endpoint response $o(T_X(q))$ is supplied; the device supplies neither its scalar increment nor any interior observation.

A complete deterministic finite controller is $(K,c,u,\Delta)$, with finite $K$ and total maps

$$
\begin{aligned}
c&:O\longrightarrow K,\\
u&:K\longrightarrow
\{\operatorname{Emit}(X):X\in\{0,1\}^m\}
\sqcup\{\operatorname{Halt}(a):a\in Y\},\\
\Delta&:K\times O\longrightarrow K.
\end{aligned}
\tag{41.6}
$$

It initializes once to $c(o(q_{\rm INITIAL}))$, using its one free initial value/bottom reading. A state with instruction $\operatorname{Emit}(X)$ executes its fixed literal word, reads the full-block endpoint, and moves to $\Delta(z,o(T_X(q)))$. A state with instruction $\operatorname{Halt}(a)$ returns its fixed literal label and is persistently absorbing: $\Delta(z,r)=z$ for every $r\in O$. There is no uncharged internal state transition between these instructions. In particular, a running state cannot freely change to a Halt state without executing its block.

All runtime phase, program, branch, saved INITIAL-value, archive, stopping and output memory belongs to $K$. There is no external initial-value register, output register, counter, clock, archive, reset, copy, interior reading, further free device reading or observation from an unexecuted branch. The actual device record is part of the experiment, not a separately accessible controller register. Arbitrary finite cycles and sharing, including sharing across INITIAL fibres or execution depths, are permitted. A constant fibre or initial bottom may continue rather than stop freely if correctness and the fee bound permit it.

Every actual Emit costs one complete block: all $m$ emitted bits count, including zeros, waits, padding and the remainder after any interior rejection. Halt costs no block. Success requires finite stopping with $f(q_{\rm INITIAL})$ for every $q_{\rm INITIAL}\in Q$. Define

$$
M_{\mathrm{fee}\le1}(f)=
\min\{|K|:(K,c,u,\Delta)\text{ is complete and successful, with worst emitted-block fee }\le1\}.
\tag{41.7}
$$

This resource counts the entire controller, including persistent literal outputs. Define the actual output set, active-fibre count and sharing indicator by

$$
\begin{aligned}
Y_{\rm act}&=\{A_0,A_1,y_\bot\}\cup\{B_v:H_v\ne\varnothing\},
&L&=|Y_{\rm act}|,\\
n&=\mathbf1_{H_0\ne\varnothing}+\mathbf1_{H_1\ne\varnothing},\\
\epsilon&=
\begin{cases}
1,&H_0=H_1\ne\varnothing,
\quad A_0=B_1\text{ and }B_0=A_1,\\
0,&\text{otherwise}.
\end{cases}
\end{aligned}
\tag{41.8}
$$

A stipulated $B_v$ on an empty support need not be an actual output and is omitted unless it coincides with an actual label. All equalities here are mathematical equalities of labels.

**定理 41.2（Universal exact complete-controller minimum）。** Under Definition 41.1, separately for either original alphabet,

$$
\boxed{M_{\mathrm{fee}\le1}(f)=L+n-\epsilon.}
\tag{41.9}
$$

Every successful complete controller with this fee bound needs at least $L$ persistent literal Halt states and at least $n-\epsilon$ running states. One total controller simultaneously attains both bounds. Equivalently:

| Support case | Necessary running states | Exact total states |
| --- | --- | --- |
| $H_0=H_1=\varnothing$ | $0$ | $L$ |
| Exactly one support is nonempty | $1$ | $L+1$ |
| Both supports are nonempty and unequal | $2$ | $L+2$ |
| Equal nonempty supports and $A_0=B_1$, $B_0=A_1$ | $1$ | $L+1$ |
| Equal nonempty supports without both crossed equalities | $2$ | $L+2$ |

Proof. The lower bound ranges over every controller (41.6), not just one chosen identification tree. The source and literal identities in the next subsection are the supplied Section 27 and INITIAL target-cost interfaces specialized to (41.1). Their explicit forms fix the actual-source and absolute-response premises of the argument.

### 41.1 Actual source witnesses and the unique literal inverse

For any $v\in\mathbb F_2$, $j\in P$ and $0\le s<k$, coprimality gives arbitrarily large $N$ satisfying

$$
N\equiv0\pmod m,\qquad N\equiv-j\pmod T,\qquad N\ge s+2.
$$

Put $a=\bigoplus_{i=N-s}^{N-1}c_i$, with empty XOR zero, and use the one history

$$
w=(v\oplus a)\,0^{N-s-1}1^s.
\tag{41.10}
$$

Its first factor is one bit and has coefficient $c_0=1$. The intervening zeros separate it from the terminal run $s<k$. Its first bit contributes $v\oplus a$, its terminal run contributes $a$, its phase is $-j$, and its tail is exactly $s$. Its length is divisible by $m$, and each length-$m$ block is available under either original alphabet. This single legal history therefore realizes the entire INITIAL record $(v,-j,s)$. The two-block all-one history $1^{2m}$ realizes bottom: its individual blocks are available because $m<k$, while their accumulated run reaches $k$. The unobserved witness lengths are not controller inputs or added continuation fees. These are the joint witnesses credited to Lemma 15.1 and (25.3), in the present parameters.

For a first word $X$ that succeeds from an INITIAL source, its scalar increment is

$$
q_X(j)=\bigoplus_{i=0}^{m-1}X_i c_{-j+i}.
\tag{41.11}
$$

The ordered first path is $W_0=\{0,1,\ldots,m\}$. Substitution of the two coefficient residues in (41.2), using $T=2m-1>m$, gives the supplied path identity

$$
\begin{aligned}
q_X(0)&=X_0,\\
q_X(j)&=X_{j-1}\oplus X_j\qquad(1\le j<m),\\
q_X(m)&=X_{m-1},\\
q_X(j)&=0\qquad(m<j<T).
\end{aligned}
\tag{41.12}
$$

Every bit occurs twice in the XOR over $W_0$, so its total charge is even. Conversely the first $m$ equations recursively force

$$
X_i=\bigoplus_{h=0}^i q_X(h)\qquad(0\le i<m).
\tag{41.13}
$$

The final endpoint equation holds exactly when the total charge is even. Thus an even charge assignment on the whole path has one unique literal inverse, with zero charge outside it. In particular, for an even $H\subseteq U$ the supplied inverse is

$$
\mathcal B_0(H)_i=\bigoplus_{h=0}^i\mathbf1_H(h),
\qquad 0\le i<m.
\tag{41.14}
$$

It starts zero because $0\notin H$, and ends zero because $|H|$ is even and $m\notin H$. These identities are Interface 1.4, equations (1.4)–(1.5), of the [INITIAL target-cost volume](KBONACCI_INITIAL_TARGET_COST_THEORY.md#1-one-reader-one-joint-prior-and-one-fee), also used in (27.4)–(27.5). The inverse is a literal action, not an arbitrary parity oracle; its old-tail safety must still be checked.

### 41.2 Universal Halt and active-root lower bounds

For every $a\in Y_{\rm act}$ an actual source has INITIAL target $a$. Successful finite stopping must visit a state whose fixed instruction is $\operatorname{Halt}(a)$. Distinct labels require distinct such states, since $u$ assigns one instruction to a state. Hence at least $L$ persistent literal Halts are necessary, irrespective of how those states are reached or shared. Every $A_v$ is realized outside $U$, every active $B_v$ is realized on $H_v$, and $y_\bot$ is realized at initial bottom by (41.10) and (41.4).

Every controller state actually reached immediately after an emission must have a Halt instruction. An Emit instruction there would execute a second full block and violate the fee bound on that source; no uncharged internal transition is available. This excludes reachable running cycles or a further running-state reuse on such executions by the contract itself. Unreachable cycles are allowed. It also allows constant-fibre and bottom continuations, but forces their reached first-emission successors to Halt.

Fix an active fibre $v$, so $H_v\ne\varnothing$. All of its live sources initialize to $R_v=c(v)$. Actual phases in $H_v$ and outside $U$ require the unequal labels $B_v$ and $A_v$. A literal Halt at $R_v$ cannot serve both, so $u(R_v)=\operatorname{Emit}(X)$ for some fixed word $X$.

First, $X_0=0$ is forced. If $X_0=1$, every actual record $(v,-j,k-1)$ rejects at the first bit. Choose $j\in H_v$ and $j_*=m+1$. The latter is an actual phase outside $W_0$ and outside $U$, since $m+1<T$ for $m\ge5$. These sources require $B_v$ and $A_v$ respectively. They start at the same controller state and, after the entire paid word including its post-rejection remainder, give the same absolute endpoint $\bot$. Their common successor cannot return both unequal labels. Absorption would preserve their indistinguishability even at a larger horizon. Thus every active root starts zero.

This first zero clears every inherited tail inside the paid word. Its remaining $m-1<k$ bits cannot form a forbidden run. Therefore $X$ succeeds on every live source in this fibre, including all old tails, and gives absolute endpoint $v\oplus q_X(j)$.

At the actual phase $j_*=m+1$, (41.12) gives $q_X(j_*)=0$. Correctness and the fee bound force

$$
u(\Delta(R_v,v))=\operatorname{Halt}(A_v).
\tag{41.15}
$$

Now take any phase in $H_v$. It must return $B_v\ne A_v$, so it cannot give endpoint $v$. It gives endpoint $1-v$ and forces the second absolute-response constraint

$$
u(\Delta(R_v,1-v))=\operatorname{Halt}(B_v).
\tag{41.16}
$$

Both binary response rows are reached on actual sources. They now force the entire charge assignment: if $j\in H_v$ had charge zero, (41.15) would return $A_v$ incorrectly; if $j\notin H_v$ had charge one, (41.16) would return $B_v$ incorrectly. Consequently

$$
q_X(j)=\mathbf1_{H_v}(j)\quad(j\in P),
\qquad X=\mathcal B_0(H_v)
\tag{41.17}
$$

by the unique inverse (41.13). There is no choice of a different root word that avoids either fixed successor requirement. This argument uses absolute responses throughout: it has not supplied an external remembered INITIAL value or an increment register.

If both fibres are active and their roots share one state, its fixed emitted word is the same. Equation (41.17) forces $H_0=H_1$. The common absolute response zero must satisfy (41.15) for INITIAL value zero and (41.16) for INITIAL value one. Its single literal Halt instruction therefore forces $A_0=B_1$. Similarly its absolute response one forces $B_0=A_1$. These necessary conditions are precisely

$$
R_0=R_1\quad\Longrightarrow\quad
H_0=H_1\ne\varnothing,
\quad A_0=B_1,\quad B_0=A_1.
\tag{41.18}
$$

If the supports differ, the emitted words conflict; if they agree but the crossed equalities fail, at least one absolute-response output instruction conflicts. Equality of output sets alone does not suffice. Conversely, under both crossed equalities and equal supports, the two root words and both binary successor requirements agree, as the construction below shows.

Thus the mandatory active roots require at least $n-\epsilon$ distinct running states. These are disjoint from the $L$ Halt states because one state has one fixed instruction. This proves $|K|\ge L+n-\epsilon$ for every complete successful controller.

No free-stop assumption on inactive fibres or bottom entered the lower bound. In fact they can be normalized to free stopping without adding states: success already provides a Halt for each $A_v$ and $y_\bot$, so change only their once-used initialization entries to those states. Leave $u$ and every $\Delta$ entry unchanged. The targets on these initial fibres are constant, and the modification cannot increase fee. This optional normalization also does not restrict arbitrary sharing or cycles in the original controller.

### 41.3 Matching total controller on every original source

Create one state $h_a$ for each distinct $a\in Y_{\rm act}$. Its instruction is $\operatorname{Halt}(a)$ and all three response updates are self-loops. Create a root $R_v$ for each active fibre. Identify the two roots exactly when $\epsilon=1$, and otherwise keep them distinct. The complete instruction and update tables are

| State | Fixed instruction | Response $0$ | Response $1$ | Response $\bot$ |
| --- | --- | --- | --- | --- |
| $h_a$, each $a\in Y_{\rm act}$ | $\operatorname{Halt}(a)$ | $h_a$ | $h_a$ | $h_a$ |
| $R_0$, if $H_0\ne\varnothing$ | $\operatorname{Emit}(\mathcal B_0(H_0))$ | $h_{A_0}$ | $h_{B_0}$ | $h_{y_\bot}$ |
| $R_1$, if $H_1\ne\varnothing$ | $\operatorname{Emit}(\mathcal B_0(H_1))$ | $h_{B_1}$ | $h_{A_1}$ | $h_{y_\bot}$ |

When the roots are identified, every table entry agrees: the words agree by equality of supports; the response-zero labels agree by $A_0=B_1$; the response-one labels agree by $B_0=A_1$; and both bottom rows use $h_{y_\bot}$. Shared output labels always refer to the same $h_a$. Initialization is total:

$$
c(v)=
\begin{cases}
R_v,&H_v\ne\varnothing,\\
h_{A_v},&H_v=\varnothing,
\end{cases}
\qquad c(\bot)=h_{y_\bot}.
\tag{41.19}
$$

Each active word starts and ends zero by (41.14). Its first zero clears every old tail, including $k-1$, and the remainder has length $m-1<k$, so every live source succeeds. Its actual full-block endpoint is

$$
o(T_{\mathcal B_0(H_v)}(v,-j,s))
=v\oplus\mathbf1_{H_v}(j).
\tag{41.20}
$$

For INITIAL value zero, the root's zero and one responses return $A_0$ and $B_0$. For INITIAL value one they return $B_1$ and $A_1$ respectively. In either case this is exactly (41.5) for every $j$ and every original inherited tail. An inactive fibre returns $A_v$ at its initialization Halt, and initial bottom returns $y_\bot$ there. Bottom response rows from roots are defined even though the constructed active words cannot reject on live sources; they also provide a literal total update on absorbing device bottom.

Every running state moves directly to a persistent Halt after its one emission, including on bottom. Termination is finite, with zero blocks on constant fibres and initial bottom, and one block on active fibres. Every emitted bit belongs to that paid complete block. All control, stopping and persistent-output storage lies in

$$
|K|=L+n-\epsilon.
\tag{41.21}
$$

Every Halt is reached by an actual source because its label belongs to $Y_{\rm act}$, and every root is reached by an active actual fibre. If $n=0$, the same construction has only the $L$ Halts and worst fee zero. If $n>0$, an active fibre actually emits a block, so worst fee is one. This attains the unrestricted lower bound and proves (41.9). $\square$

### 41.4 Equal supports with different complete memory

**命题 41.3（Crossed versus aligned absolute-response consumer）。** Fix $m=5$, $k=8$, $T=9$ and

$$
H_0=H_1=\{2,3\},\qquad
\mathcal B_0(H_0)=\mathcal B_0(H_1)=00100.
\tag{41.22}
$$

Let $a\ne b$ and choose $y_\bot=a$. The following two targets have the same supports, the same two actual output labels, and the same adaptive and GLOBAL minimum emitted-block fee one, supplied by Theorem 27.2. Their complete-controller minima at fee at most one differ:

| Label assignment | $(A_0,B_0,A_1,B_1,y_\bot)$ | $(L,n,\epsilon)$ | Exact minimum |
| --- | --- | --- | --- |
| Crossed | $(a,b,b,a,a)$ | $(2,2,1)$ | $3$ |
| Aligned | $(a,b,a,b,a)$ | $(2,2,0)$ | $4$ |

Proof. Equation (41.14) gives the displayed literal word. Its only nonzero charges in (41.12) are at $j=2,3$. It starts zero and succeeds on all $2Tk=144$ live INITIAL records, including tail seven, under both original alphabets. With initial bottom the full source has $145$ records. Formula (41.9) gives the two exact counts, and the following tables expose the absolute-response difference without an external saved INITIAL value:

| Target and running state | Emit | Response $0$ | Response $1$ | Response $\bot$ |
| --- | --- | --- | --- | --- |
| Crossed $R$ | $00100$ | $h_a$ | $h_b$ | $h_a$ |
| Aligned $R_0$ | $00100$ | $h_a$ | $h_b$ | $h_a$ |
| Aligned $R_1$ | $00100$ | $h_b$ | $h_a$ | $h_a$ |

Both controllers also contain precisely $h_a,h_b$, with the literal Halt instructions and all three self-loops of Section 41.3. Crossed initialization is $c(0)=c(1)=R$, $c(\bot)=h_a$. Aligned initialization is $c(0)=R_0$, $c(1)=R_1$, $c(\bot)=h_a$. The tables and initialization give all states, instructions and response rows.

In the crossed target the absolute endpoint already selects its literal output regardless of INITIAL value. In the aligned target, the same absolute endpoint requires opposite labels for the two INITIAL values. For example response zero arises outside $H_0$ at INITIAL value zero, requiring $a$, but inside $H_1$ at INITIAL value one, requiring $b$. These are actual full-source executions. The unique common root word cannot alter this conflict. Two running states retain the required distinction inside $K$. Equal support, fee and output count therefore do not determine complete action-memory compatibility. The lower bound excludes another word, rejection, a running cycle or a hidden free transition as a three-state aligned alternative. $\square$

### 41.5 Applicability and boundaries

**假设 41.6（Scope of the complete-memory objective）。** The source, action, observation, target and complete-controller conditions remain exactly those of Definition 41.1. The universal ordinary proof is Sections 41.1–41.3; agreement on finite instances neither replaces that proof nor enumerates every permitted finite controller.

The equality depends on the exact source and memory contract. A successful original controller with fewer than $L$ literal output states, or fewer than $n-\epsilon$ running states, would contradict the corresponding lower argument. Such a controller must retain every actual oldtail-$k-1$ source and outside-window phase, charge every emitted block, use only absolute endpoint observations, and include all runtime and persistent-output memory in $K$. Removing those sources, exporting INITIAL value or output storage, reading an interior point, or supplying an uncharged control transition changes the problem. A failure of one constructed word to clear an actual legal tail, an endpoint different from (41.20), or a conflicting shared response row would instead invalidate the displayed attainment; it would not by itself exclude another attainment.

The label counts and crossed equalities are mathematical finite-set statements. For arbitrary labels they assert no uniform decidable equality procedure, executable installation algorithm or installation cost. A computational implementation would require an effective presentation of the finite equality partition. A complete-memory optimum at fee two, a general parameter optimum and a physical-memory/bit/time correspondence remain separate questions. The static naming discussion in Boundary 40.3 retains its missing operational correspondence. Targets outside (41.5), other widths or orders, odd supports, tail-sensitive targets, and the general immutable INITIAL fee objective retain their separate unresolved obligations.

**数学引文 41.7（Suppliers and mature methods）。** Definition 27.1 supplies the original full-source even-support family, matched coefficients, immutable targets, complete-block actions and fee contract. Theorem 27.2 supplies its already established adaptive/GLOBAL zero/one/three classification, including the consumer's fee-one statement. It is credited reuse, not a new fee classification here. Lemma 15.1 and (25.3) supply the joint history construction; Definitions 18.1 and 25.1 supply original INITIAL acquisition semantics. The source-specific formulas (41.10)–(41.14) expose these interfaces without claiming a new general observer or inverse theorem. [INITIAL target-cost theory, Interface 1.4](KBONACCI_INITIAL_TARGET_COST_THEORY.md#1-one-reader-one-joint-prior-and-one-fee) supplies the ordered full-path charges and inverse.

Definition 40.1 supplies the complete finite-controller convention, total initialization and response maps, fixed instructions and persistent literal outputs. Its Theorem 40.2 has separate $(k,m)=(6,4)$, fee-three phase and value-phase contracts and retains the minima $18$ and $26$; neither number prices (41.5). The additional deduction here is the universal fee-one root rigidity (41.15)–(41.17), its exact two-absolute-response sharing obstruction (41.18), and simultaneous attainment (41.19)–(41.21). Proposition 41.3 consumes that obstruction while keeping support, emitted fee and actual output count fixed.

The mature identification and compatibility methods are those cited in Section 40. E. F. Moore, [*Gedanken-Experiments on Sequential Machines*, printed pp. 129–131](https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf), treats identification of an unknown beginning state and destructive failure. Petra van den Bos and Frits Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, Section 4, Definition 11 and Figure 3](https://arxiv.org/html/1907.11034v2), provide adaptive completed-trace and irreversible-merger semantics. A. Larrauri and R. Bloem, [arXiv:2105.10292v2, Section 5, Theorem 4](https://arxiv.org/html/2105.10292v2), supply closed compatible covers with initial coverage and successor closure for a given observation machine. Here compatibility requires both the fixed literal action and its absolute-response-to-Halt rows to agree. The lower proof first forces these requirements for every permitted controller, so it is stronger than minimizing a preselected tree. These named sources are `literature-attested` background methods, rather than a source of formula (41.9). The complete-memory equality and its label consumer are `repo-derived` source-specific ordinary mathematical deductions without a global literature-priority assertion.

## 追加锚（本行以下为增补区）

# KBonacci full-positive-window logarithmic prices

This continuation of the [canonical INITIAL-target cost theory][IC] prices every repeated-label table on one actually acquired full positive window at odd $m\ge3$, $k=m+1$. It gives a single physical suffix, including its seam proof, rather than treating arbitrary binary questions as available actions. It then consumes that suffix in full INITIAL targets with unbounded exact adaptive and one-GLOBAL-stream fees.

The text is ordinary mathematical reference input, without Lean or kernel certification. It follows the `generic-v1` claim convention and retains a final addition anchor. Authorship is by one delegated author applying `formal-thinking-and-answer` and `theory-volume-template` under pure-theory authorization. Repository prior is exposed; no independent-prior, model-diversity, independent-review or literature-priority claim accompanies these proofs. The original all-parameter, all-attainable-target objective remains unresolved.

## 73. Every label table on an actual full positive window

**定义 73.1（The actual archive, INITIAL labels and local prices）。** Retain [IC, Definitions 1.1–1.3, Interface 1.4 and Definition 65.1]: the original integer KBonacci weights, matched $V_k\bmod2$ reading, full jointly attainable complete-history prior, immutable INITIAL record labels, free initial scalar or independently labelled absorbing bottom, and observations only at complete endpoints. Assume

$$
m\ge3\text{ odd},\qquad k=m+1,\qquad T=m+2,
\qquad \gcd(m,T)=\gcd(m,2)=1.
\tag{73.1}
$$

Both original control alphabets contain all $m$-bit words because $m<k$; crossing a seam can still cause absorbing rejection. Every actually issued complete block costs one, including waits, padding, repairs and a block rejecting before its observed endpoint. There is no reset, copy, intermediate reading, hidden INITIAL clock or borrowed sibling archive.

Fix either remembered free INITIAL value and an actual chronological archive. Its known already paid block at absolute issued index $a\ge0$ has a successful positive-difference child with full support

$$
A=W_a=[am,(a+1)m]\pmod T.
\tag{73.2}
$$

The candidates share this entire acquired archive and have a common current scalar. Require one well-defined immutable INITIAL label $\lambda(j)$ per surviving phase $j=-\theta_{\rm INITIAL}\in A$: all surviving original records at that phase have that same label. This is a substantive hypothesis. Source legality does not imply it, and a full controller must also preserve the labels of every actual first-zero merger and every rejected band. No label or continuation assumption is made about another child or free-value fibre.

Write $u=am\pmod T$. Since every vertex of $W_a$ has parent charge one, the supplied inverse [IC, (1.5), Chapter 65] forces that very parent word to be

$$
P_m=101\cdots01=(10)^{(m-1)/2}1.
\tag{73.3}
$$

It has an internal zero and terminal tail one. Its successful candidates therefore have actual common current tail one, regardless of their tails before the parent. Survival of its leading one is part of the actual archive, not a newly assumed arrival. Its current phase at this child is $-j+(a+1)m\pmod T$.

Let $D_{\rm ad}$ be the minimum additional worst-branch emitted-block fee of an adaptive continuation from this child. Let $D_{\rm child\text{-}pre}$ require one fixed literal suffix for this child, with stopping and decoding based on the source's own endpoints. These prices exclude the already paid prefix of $a+1$ blocks. They do not require compatibility with unrelated live siblings. Put $n=|\lambda[A]|$.

For the construction alone rotate phase coordinates by $u$, writing $x=j-u\pmod T$, so $A$ becomes $\{0,\ldots,m\}$; write $\lambda(x)$ for the transported table. This rotation is a calculation using the known issued index, not an observation of INITIAL phase or a physical operation. All resulting words are issued at their actual indices $a+r$.

**定义 73.2（Missed vertices and sufficient seam conditions）。** For $n\ge3$ put

$$
d=\lceil\log_2 n\rceil\ge2,\qquad z=m+1,
\qquad e_r=m+1-2r,\qquad s_r=e_r+1=m+2-2r
\quad(1\le r\le d).
\tag{73.4}
$$

Here $d\le(m+1)/2$. Indeed, $n\le m+1=2q$, $q\ge2$, and the elementary induction $2^q\ge2q$ gives $\lceil\log_2(m+1)\rceil\le q$. Thus $e_r\ge0$ and $s_r\ge1$. The actual window at index $a+r$, in the rotated coordinates, starts at $s_r$, wraps if necessary, and misses exactly $e_r$, since $m\equiv-2\pmod T$. It contains the excluded child vertex $z$. Its last vertex is $e_r-1\pmod T$. In particular, for $r\ge2$, the last vertex of the preceding window is exactly its own first vertex $s_r$.

Let $\mathcal Y=\lambda[A]$. For each label $L\in\mathcal Y$ define a finite list $\mathcal L_L\subseteq\{0,1\}^d$ by the following clauses on $y=(y_1,\ldots,y_d)$:

$$
\begin{aligned}
y_r&=0&&\text{whenever }L=\lambda(e_r),\quad 1\le r\le d,\\
y_1&=0&&\text{whenever }L=\lambda(m),\\
y_{r-1}y_r&=0&&\text{whenever }L=\lambda(s_r),\quad 2\le r\le d.
\end{aligned}
\tag{73.5}
$$

Repeated labels collect all their clauses. The first line makes unavailable coordinates zero; the second makes the first literal word start zero. The third will make the two literal bits adjacent to each later block boundary not both one. These are sufficient physical seam conditions, not necessary conditions for every optimal stream.

**引理 73.3（Simultaneous codes with one explicit four-label alternative）。** If $d\ge3$, or if $d=2$ except for the case below, the lists (73.5) admit an injective choice

$$
c:\mathcal Y\longrightarrow\{0,1\}^d,
\qquad c(L)\in\mathcal L_L.
\tag{73.6}
$$

The only case requiring the alternative is $d=2$, $n=4$, and the four labels

$$
L_A=\lambda(m-1),\quad L_B=\lambda(m),\quad
L_C=\lambda(m-3),\quad L_D=\lambda(m-2)
\tag{73.7}
$$

are distinct. In that case use the injective code

$$
c(L_A)=00,\qquad c(L_B)=01,\qquad
c(L_C)=10,\qquad c(L_D)=11.
\tag{73.8}
$$

It obeys the first two lines of (73.5), and only the boundary clause for $L_D$ is relaxed. Both alternatives give one code per label; no phase in another archive supplies information or a parity constraint.

**证明。** Apply the existing finite Hall distinct-representative theorem [H] to these lists. Only the list inequalities need proof here. There are $d+1$ displayed unary-clause occurrences and $d-1$ pair-clause occurrences, hence at most $2d$ labels with any clause. Every list contains the zero vector. A subfamily of $q$ lists containing the full cube has union size $2^d\ge n\ge q$.

The empty subfamily's inequality is immediate. Consider a nonempty subfamily with no full-cube list, so $q\le2d$. For $q=1$ its zero vector suffices. For $q=2$, the zero vector and every unit vector in coordinates $2,\ldots,d$ belong to the union: such a unit vector can violate a unary clause on at most one label, and violates no pair clause. The union has size at least $d\ge2$.

For $3\le q\le d+1$, every unit vector belongs to the union. Coordinate one has at most two unary-clause occurrences, all other coordinates at most one, and no unit vector violates a pair clause. Thus no unit vector is forbidden by all these $q$ labels. Together with zero this gives union size at least $d+1\ge q$.

For $q\ge d+2$ and $d\ge3$, one has $q\ge5$. Any vector of weight two violates unary clauses on at most three labels: one occurrence at each of its two coordinates, and possibly the extra occurrence at coordinate one. It violates a pair clause on at most one additional label, since its two occupied coordinates give at most one adjacent pair. It is therefore forbidden on at most four labels and belongs to the union. Consequently that union contains every vector of weight at most two and has size at least

$$
1+d+\binom d2\ge2d\ge q.
\tag{73.9}
$$

These cases verify every Hall inequality for $d\ge3$. They also verify every subfamily of size at most three when $d=2$. A four-list subfamily for $d=2$ can have no full-cube member only if each of the four clause occurrences belongs to a different label. Those occurrences are exactly (73.7). If they are not distinct, any four-list subfamily contains a full cube and its Hall inequality holds. If they are distinct, $n\le4$ implies they are all the labels, and the displayed alternative (73.8) is available. This proves the statement. The finite Hall theorem itself is credited reuse, not an added theorem about generic matching. ∎

**构造 73.4（One actual fixed suffix）。** Choose the codes of Lemma 73.3. On the actual ordered window at index $a+r$ prescribe the rotated physical charge $q_r$ by

$$
\begin{aligned}
q_r(x)&=c_r(\lambda(x))&& (x\in A\setminus\{e_r\}),\\
q_r(z)&=\bigoplus_{x\in A\setminus\{e_r\}}c_r(\lambda(x)),\\
q_r(e_r)&=0.&&
\end{aligned}
\tag{73.10}
$$

The last line is the charge outside this window. By the first line of (73.5), including alternative (73.8), it is also the desired code coordinate at $e_r$. The full window charge is even. Its unique literal inverse is the complete $m$-bit word

$$
B_r=(x_{r,0},\ldots,x_{r,m-1}),\qquad
x_{r,i}=\bigoplus_{h=0}^i q_r(s_r+h\bmod T).
\tag{73.11}
$$

Thus the fixed suffix is $B_1\mid\cdots\mid B_d$. Compensation at $z$ prescribes bits of these very words; it supplies neither a source nor another observation. For a successful source the successive endpoint differences are precisely $c_1(\lambda(x)),\ldots,c_d(\lambda(x))$. At the last endpoint return the unique label with this code. The controller uses its remembered current baseline and its own subsequent endpoints. No phase reading is required. It may stop earlier at a homogeneous prefix, but the displayed attainment can simply issue all $d$ suffix blocks on every candidate of this child.

**引理 73.5（Every seam of that same suffix is safe）。** The suffix (73.11) succeeds on all candidates of Definition 73.1 and emits exactly $d$ paid complete blocks when the final-endpoint decoder is used. No clearing, waiting or repair block is omitted from its fee.

**证明。** For the list choice (73.6), its first literal bit is

$$
x_{1,0}=q_1(m)=c_1(\lambda(m))=0.
\tag{73.12}
$$

This clears the actual inherited tail one. For $r\ge2$, the supplied endpoint equations and the common boundary vertex $s_r$ give

$$
x_{r-1,m-1}=c_{r-1}(\lambda(s_r)),\qquad
x_{r,0}=c_r(\lambda(s_r)),\qquad
x_{r-1,m-1}x_{r,0}=0.
\tag{73.13}
$$

There is a zero among the two bits directly adjacent to each such block boundary. No run of ones can cross that boundary. Each individual word has length $m<k$, so it cannot contain $1^k$ internally. These facts prove safety of the entire emitted concatenation, even if one later word happens to be all ones. The final endpoint needs no extra cleanup.

In alternative (73.8) the first word again starts zero, because its leading phase is $m$ with label $L_B$ and first coordinate zero. The first window ends at $m-2$ with label $L_D$, so its last bit is one. Its preceding charge, at $m-3$ with label $L_C$, is also one; the endpoint inverse therefore makes its penultimate bit zero. Its actual terminal tail is exactly one. The second window starts at $m-2$ and its first three charges, at $m-2,m-1,m$, are $1,0,1$. Formula (73.11) gives the literal prefix $110$, hence leading run exactly two. This single seam has length

$$
1+2=3<m+1=k
\tag{73.14}
$$

for every $m\ge3$. Both blocks are internally safe, and there are no other suffix seams. This proves the same attainment in this alternative, including $m=3$. The relaxed code condition does not hide a paid repair: the short safe run is already inside the two displayed words. ∎

**定理 73.6（Exact full-positive-window price, every repeated-label table）。** For every actual archive of Definition 73.1, under either original control alphabet,

$$
\boxed{D_{\rm ad}=D_{\rm child\text{-}pre}=
\begin{cases}
0,&n=1,\\
2,&n=2\text{ and }\mathsf E,\\
1,&n=2\text{ and not }\mathsf E,\\
\lceil\log_2 n\rceil,&n\ge3,
\end{cases}}
\tag{73.15}
$$

Here the exact supplied exception is

$$
H=\{u+m,u+2m\}\pmod T=\{u+m,u+m-2\}\pmod T,
\qquad
\mathsf E:\quad
\lambda=L\text{ on }H,\quad
\lambda=M\text{ on }A\setminus H,
\quad L\ne M.
\tag{73.16}
$$

These are additional child fees. The $n\ge3$ attaining suffix is one actual stream (73.11), shared by all its continuing response children. The constant and binary clauses, including the paid two-block exception, are exactly credited overlap with [IC, Theorem 65.2].

**证明。** For $n\ge3$, Lemmas 73.3 and 73.5 give a legal fixed suffix with fee $d$. Its charge on each original surviving phase is its label's code, including zero at unavailable vertices, and injection makes the final decoder correct for arbitrary repetitions of labels. Thus $D_{\rm ad}\le D_{\rm child\text{-}pre}\le d$.

For the lower bound apply [S10, Lemma 3.2] to this actual common-value, common-tail child. Every literal action either succeeds on all its candidates or rejects all. At any subsequent successful output child, value and tail are again common. A nonconstant node cannot use uniform rejection to acquire a label, at its endpoint or at any later depth, because bottom is absorbing. Successful blocks have at most two endpoint outcomes. Therefore every correct adaptive continuation of worst additional fee $h$, including arbitrary waits, padding, repairs and endpoint stops, has at most $2^h$ distinct-label leaves. There are $n$ labels on actual sources sharing the starting archive, so $n\le2^h$ and $h\ge d$. This is an all-literal-action lower bound, not a restriction to (73.11). It also lower-bounds fixed suffixes. Both inequalities give equality.

For $n=1$ the common label is already determined and the child stops at zero additional fee. For $n=2$, the next window misses only $u+m-1$ in $A$; the one-coordinate condition of [IC, (65.2)] is automatically satisfied because this missed support is a singleton. Theorem 65.2 gives price one except precisely (73.16), whose unique separating one-block inverse is $1^m$ and rejects from actual tail one. In that exception its actual paid suffix is $0^m\mid110^{m-2}$, of price two. These clauses are supplied mathematics and are not claimed as new content. ∎

## 74. Full INITIAL consumers with unbounded exact total fees

**定义 74.1（A complete target, including every original tail）。** Let $d\ge2$, $n=2^d$, and choose any odd $m\ge n-1$. Put $k=m+1$, $T=m+2$. Take any table $\lambda:\{0,\ldots,m\}\to Y$ with exactly $n$ distinct labels, allowing arbitrary repetitions and ordering. Enlarge the label set with distinct fresh $R,C\notin\lambda[\{0,\ldots,m\}]$. On both free-value fibres define the entire INITIAL record target

$$
f^\lambda(v,-j,s)=
\begin{cases}
R,&s=m,\\
\lambda(j),&0\le s<m,\quad 0\le j\le m,\\
C,&0\le s<m,\quad j=m+1,
\end{cases}
\qquad f^\lambda(\bot)=L_\bot,
\tag{74.1}
$$

where $L_\bot$ is arbitrary and independent. Its history target is explicitly $F^\lambda(w)=f^\lambda(q(w))$. This specifies the INITIAL-history factorization; it does not infer it from source legality. Here $q(w)$ is the original endpoint record of the source history before any controller action, including $q(w)=\bot$ for rejected histories.

**定理 74.2（Exact adaptive and GLOBAL prices for all these full consumers）。** Under Definition 74.1, for both original alphabets,

$$
\boxed{C_{\rm ad}(f^\lambda)=C_{\rm pre}(f^\lambda)=1+d.}
\tag{74.2}
$$

A GLOBAL stream for this fixed full target is

$$
P_m\mid B_1\mid\cdots\mid B_d,
\tag{74.3}
$$

with $a=u=0$ in Construction 73.4. The same words serve both free INITIAL values. Root rejection and the successful zero-difference sibling stop at the first paid endpoint, and initial bottom stops freely. Only the full positive child emits the suffix. Different full targets may choose different codes and hence different GLOBAL streams.

**证明（all jointly actual sources and literal attainment）。** Every specified INITIAL $(v,-j,s)$ has the supplied single-history witness [IC, (1.3); S1, Convention 1.3; S15, Section 1]. Explicitly choose

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad
\ell\ge s+2,\qquad
\eta=\bigoplus_{i=\ell-s}^{\ell-1}c_i,
\qquad w(v,j,s)=(v\oplus\eta)0^{\ell-s-1}1^s,
\tag{74.4}
$$

where $c_i=\mathbf1_{\{0,T-1\}}(i\bmod T)$. Coprimality supplies arbitrarily large such $\ell$. The separating zero makes this word legal, its first bit compensates the terminal run contribution, its value is exactly $v$, its phase is $-j$, its tail is $s$, and its length is a multiple of $m$. It is one source simultaneously realizing these coordinates, split into complete internally legal source blocks. Its unobserved length is not supplied to the controller. An all-one complete-block history of length at least $k$ separately realizes initial bottom.

Append exactly (74.3) to each source that has not stopped. The actual root $P_m$ has leading run one. It rejects precisely INITIAL tail $s=m$, and that band has the single label $R$. Rejection remains absorbed through the rest of that issued root; all $m$ bits belong to its one paid complete block, and its only readout is bottom at the completed endpoint. Every $s<m$ obeys $s+1\le m<k$, reaches the root's first zero, and then finishes safely. At each fixed INITIAL phase these surviving tails merge, but (74.1) has the same INITIAL label on all of them. This explicitly verifies the parent's label-preservation conditions.

The root's full charge is one on $\{0,\ldots,m\}$ and zero at $z=m+1$. Its successful zero-difference child is therefore homogeneous $C$ and stops with $C$ at fee one. Its positive child is exactly $A=W_0$ with common current tail one and table $\lambda$. Theorem 73.6 gives its one fixed suffix $B_1|\cdots|B_d$, and Lemma 73.5 proves the safety of this very suffix and the seam after the root. Decode successive differences of each source's own scalar outputs; both free INITIAL values give the same codes and the same returned INITIAL labels. Initial bottom has its independent free output and returns $L_\bot$ without an issued word.

Thus all live descendants share (74.3); no unrelated live sibling is flattened into a child optimum. The only other successful sibling is homogeneous and has already stopped. All actual positive-child sources, which exist by (74.4), can be kept through all $d$ suffix blocks and pay exactly $1+d$. No additional wait, padding block, repair, cleanup, rejected block or observation is used. This proves the full GLOBAL upper bound with its actual worst fee.

**证明（every competing root and the whole-target lower bound）。** Fix either free INITIAL value. At every phase the actual original tails $m-1$ and $m$ have different labels: a low phase label or $C$, versus fresh $R$. Therefore free stopping is impossible.

Any root starting zero lets both these tails reach that zero at a fixed phase; their scalar and phase agree and the zero merges their entire records. They then have the same complete root endpoint archive and every deterministic future archive, so no later protocol can return their unequal INITIAL labels. Such a root is impossible in any correct controller, irrespective of its later depth.

Any root with at least two leading ones, including the zero-free root, sends both these original tails to bottom before its completed endpoint. Their rejection times are unobserved, and absorption makes their subsequent archives identical. These roots are equally impossible in every correct controller. Consequently every correct root has leading run exactly one and its second bit zero. This exhausts all literal roots, not just alternating roots.

For each remaining root every INITIAL tail $s<m$ at every phase survives its leading one, is cleared by its second bit, and survives the internally shorter-than-$k$ remainder. Its successful endpoint candidates have common tail on each observed archive. The low sources on this one free-value fibre carry all $n$ labels of $\lambda$ and the fresh label $C$, hence $n+1$ distinct labels. The first root yields at most two successful scalar endpoints on these sources. At every later nonconstant low-source archive a literal action cannot supply a useful common rejection outcome, and any successful action supplies at most two scalar endpoints, by the same actual common-tail argument as [S10, Lemma 3.2]. A whole controller of worst fee $h$ can therefore have at most $2^h$ different low-source leaves, even with adaptive inputs and early endpoint stopping. Necessarily

$$
2^h\ge n+1=2^d+1,
\qquad h\ge d+1.
\tag{74.5}
$$

This count includes the first paid root among its $h$ blocks; it never calls that root free. Every unequal-label pair and every phase used in this argument has its own joint original history (74.4). A different policy on the other free-value fibre does not avoid the same bound on this fibre. Since preset controllers are adaptive controllers, (74.5) lower-bounds both costs. Together with (74.3) it proves (74.2). ∎

**构造 74.3（An explicit unbounded symbolic stream family）。** The full-target theorem already supplies every power-of-two label table of Definition 74.1. The following subfamily needs no matching selection to specify its emitted words. For every $d\ge4$, put

$$
N=2^d,\qquad m=N-1,\qquad k=N,\qquad T=N+1,
\qquad \lambda(j)=j\quad(0\le j<N).
\tag{74.6}
$$

For $0\le j<N$ let $b_t(j)$ be bit $t$ of its $d$-digit binary expansion, with bit zero least significant. Use the coordinate order

$$
t_r=r\ (1\le r\le d-2),\qquad
t_{d-1}=d-1,\qquad t_d=0,
\qquad e_r=N-2r,
\tag{74.7}
$$

and the completely specified code

$$
c_r(j)=b_{t_r}(j)\oplus b_{t_r}(e_r).
\tag{74.8}
$$

For $s_r=N+1-2r$ define $q_r$ and every literal bit $x_{r,i}$ by (73.10)–(73.11), with $z=N$. The actual full stream is

$$
(10)^{(N-2)/2}1\ \bigm|\
(x_{1,0}\cdots x_{1,N-2})\ \bigm|\ \cdots\ \bigm|\
(x_{d,0}\cdots x_{d,N-2}).
\tag{74.9}
$$

Every factor has exactly $m=N-1$ bits, specified by finite parity expressions in $d,r,i$. It is a literal stream on the original reader, not an abstract list of questions. Extend its target by (74.1), for example with $R=N$, $C=N+1$ and arbitrary independent $L_\bot$.

**命题 74.4（Physical realization and exact growing fees of the explicit family）。** For every $d\ge4$, (74.9), with the stopping rules of Theorem 74.2, attains

$$
C_{\rm ad}=C_{\rm pre}=d+1,
\qquad\text{worst emitted bits}=(d+1)(2^d-1).
\tag{74.10}
$$

**证明。** Coordinate permutation and the fixed coordinate XORs in (74.8) make the codes a bijection onto $\{0,1\}^d$. Each missed coordinate is zero at $e_r$, so the literal inverse realizes these exact codes. For $r<d$, $t_r\ge1$ and the adjacent integers $e_r,e_r+1=s_r$ are respectively even and odd. They differ only in bit zero. Thus $c_r(s_r)=0$ and every one of the first $d-1$ suffix words starts zero. All their incoming seams are safe.

The last suffix word may start one. Its preceding word ends at $s_d=N-2d+1$. Both $s_d$ and $e_{d-1}=N-2d+2$ lie in $[N/2,N-1]$, since $2^{d-1}\ge2d$ for $d\ge4$. Their most significant bits are both one, so

$$
c_{d-1}(s_d)=b_{d-1}(s_d)\oplus b_{d-1}(e_{d-1})=0.
\tag{74.11}
$$

The penultimate word ends zero, clearing the last seam. Hence the entire suffix is safe, all words have length $m<k$, and the root-to-suffix seam starts zero as well. This directly proves physical attainment for the explicit stream; it does not require (73.5)'s sufficient list clauses to hold in every coordinate. Its label codes are injective, the root's other archives are homogeneous, and the full lower bound (74.5) applies. Thus the exact fee is $d+1$. A positive-child source emits every block in (74.9), giving exactly the displayed number of bits. The ordinary symbolic proof covers every $d\ge4$, not just finite samples. ∎

## 75. Supplier overlap, acceptance obligations and remaining boundaries

**数学引文 75.1（Exact reused suppliers and the new cost connection）。** The [canonical volume][IC] and its three merged companions [M], [T3] and [F4] are inputs at [revision 174ea5d1e5feaf45e708bac23737eb1f46b90540](https://github.com/the-omega-institute/trureturing/tree/174ea5d1e5feaf45e708bac23737eb1f46b90540/docs/develop/theory). Their statements retain their own hypotheses. The canonical manuscript and these companions are consumed by reference and are not rewritten here.

| Supplier | Exact use and boundary |
| --- | --- |
| [IC, Chapter 1; S1, Definitions 1.2–2.1, Convention 1.3, Proposition 2.2, Lemmas 4.2–4.3, Theorem 5.2 and Note 5.3] | Original joint prior and matched record, immutable INITIAL labels, paid endpoint-only control, joint history (74.4), irreversible first-zero and rejection losses, and semantic/effective distinction. A history target's record factorization must be given or proved; legality alone is insufficient. |
| [S2, Sections 13–14, Theorem 14.1] | The original recurrence has coefficient cycle $c_i=\mathbf1_{\{0,T-1\}}$ and period $T=k+1$. No state-count or future-window count is substituted for a paid block fee. |
| [S10, Interface 2.1 and Lemma 3.2; S15, Section 1, Definitions 1.1 and 2.1, Proposition 4.2] | Actual same-word path charges and inverse, endpoint bits, strict inherited-tail safety, common-tail binary lower bound, INITIAL-parent preservation and the separation of child-preset from GLOBAL obligations. |
| [IC, Definition 65.1 and Theorem 65.2] | The actual full-positive parent and tail, exact constant and binary prices, and precisely (73.16)'s charged exception. These shallow clauses are overlap, not new claims. |
| [IC, Chapter 11; H] | Finite Hall distinct representatives. Chapter 11's forbidden-band source lists and guard concern a different root-zero problem. Here the index set is the label image $\mathcal Y$, and (73.5) also couples consecutive endpoint bits; its new physical inequalities and four-label alternative are proved above. |
| [IC, Chapter 27] | Its fee realization assumes $k\ge2m$, which fails here. Its availability-list definition is an adjacent comparison only. Neither its independent-row seam estimate $2m-2<k$ nor its full-window fee theorem is applied to (73.1). |
| [M, Definition 1.2 and Theorem 2.1; T3, Definition 1.2 and Theorem 2.1; F4, Definition 72.1 and Theorem 72.2] | These price actual all-one-root zero archives, with mixed tails or restricted three-/four-label tables and missed-set conditions. Their arrivals are different from the alternating parent's full positive child, and they supply no arbitrary-$n$ price for Definition 73.1. No consumer optimum is inferred by taking a maximum across their unrelated children. |

The finite Hall theorem is available in pinned mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`, `Mathlib/Combinatorics/Hall/Finite.lean`, as `Finset.all_card_le_biUnion_card_iff_existsInjective'`. It is used only as mathematical literature for finite lists and distinct representatives; no Lean application or compilation is claimed. Targeted source comparison covers the cited supplier passages, canonical Chapters 11, 27 and 65–69, the three companions' defining domains, and the named KBonacci acquisition source directory. It establishes the stated overlap, not an exhaustive absence result about the repository or mathematical literature.

The added reader-specific content is the uniform physical suffix (73.10)–(73.14), its exact arbitrary-repetition $n\ge3$ fee in (73.15), and the all-competing-root full-source connection (74.2). The explicit unbounded stream (74.9) exposes that connection without a matching-selection oracle. The binary lower bound, original reader, finite Hall theorem, shallow exception and history witnesses are credited reuse. This is `repo-derived` ordinary mathematics. No literature-priority or exhaustive novelty assertion is made.

**边界 75.2（Decisive checks and effectivity）。** The construction has concrete falsifiable obligations: $e_r$ is the sole missed phase of the actual window; $z$ belongs to that window and is absent from this child; (73.10) has even full-path charge; (73.11) has exactly $m$ bits and realizes each prescribed charge; the first suffix bit is zero; each generic later boundary obeys (73.13); and the only relaxed four-label boundary has actual tail one and leading run two. A failed obligation would invalidate the claimed attainment, irrespective of label capacity. The all-action lower bound must retain common actual tail after each successful literal action and absorbed common rejection. The full-consumer bound must exclude every root with leading run zero or at least two, not just compare alternating-root continuations. The explicit family additionally requires (74.11). Each obligation is discharged by the ordinary proofs above; finite checks of selected tables can test implementations but cannot replace these uniform proofs.

For arbitrary $Y$ the formulas are semantic existence and minimum statements. With a finite target-partition presentation or decidable label equality, selection is effective: identify the finite label image, form the lists, choose distinct representatives by finite search (or use (73.8)), invert the finite rows, and store their code decoder. No polynomial, bit-complexity or offline-acquisition-cost claim is made. The explicit family uses its displayed binary formulas and requires no such matching search. All online observations remain complete endpoints. Known issued indices supply relative displacement, never an unknown INITIAL clock. Deciding whether an arbitrary history expression factors through $q$, or whether an arbitrary proposed parent preserves its labels, is not supplied by this code selection.

**开放问题 75.3（The preserved original quantifiers）。** The local law requires odd $m\ge3$, $k=m+1$, actual gcd one, an actually paid positive child with precisely $A=W_a$, and one immutable INITIAL label per surviving phase. It does not price smaller arbitrary supports, mixed-tail archives, root-zero children, even $m$, other $k$, or a history target whose factorization has not been supplied. A full extension can have nonhomogeneous rejection or zero siblings, different value-fibre tables, competing admissible roots and incompatible literal suffixes. Equation (73.15) alone gives no GLOBAL fee for such an extension.

The full equality (74.2) additionally requires exactly the complete target (74.1), common tables on both free-value fibres, fresh $R,C$, and a power-of-two number of child labels. For $n\ge3$ that is not a power of two, the same complete target pattern and construction give the full upper bound $1+\lceil\log_2n\rceil$, but the low-label count $n+1$ need not force that value; no exact nonsaturated whole-target formula is asserted here. Arbitrary unrelated live siblings are never flattened into this theorem. The GLOBAL quantifier is one stream for all INITIAL sources of one fixed target, not one stream simultaneously optimal for all different targets.

Definition 1.3 and Open Problem 9.1 of [IC] retain the exact minimum worst-branch ACTUAL emitted-complete-block objective for every attainable immutable INITIAL target and every original $k\ge2,m\ge1$, separately for adaptive control and one GLOBAL preset stream under both original alphabets. The unbounded depth parameter in (74.10) ranges over different finite readers and targets; it neither supplies an infinite-horizon controller for their union nor closes those original quantifiers. Near-full windows and endpoint bits provide a useful concise construction, but that structural simplicity is not a claim of general optimality beyond the proved domains.

[IC]: KBONACCI_INITIAL_TARGET_COST_THEORY.md
[M]: KBONACCI_MIXED_TAIL_ROOT_ZERO_CUT_PRICE.md
[T3]: KBONACCI_THREE_CLASS_ROOT_ZERO_COMPATIBILITY_PRICE.md
[F4]: KBONACCI_FOUR_LABEL_ROOT_ZERO_INTERSECTION_PRICE.md
[S1]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md
[S2]: https://raw.githubusercontent.com/the-omega-institute/trureturing/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md
[S10]: https://raw.githubusercontent.com/the-omega-institute/trureturing/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[S15]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md
[H]: https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Hall/Finite.lean

## 追加锚（本行以下为增补区）

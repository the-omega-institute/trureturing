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

## 76. The complete three-label INITIAL adaptive and GLOBAL law

**定义 76.1（The entire source target and its three tests）。** Retain [IC, Chapter 1] and Definition 73.1's original reader, joint complete-history prior, immutable INITIAL labels, endpoint-only observations and paid literal actions. Assume

$$
m\ge3\text{ odd},\qquad k=m+1,\qquad T=m+2,
\qquad g=\gcd(m,T)=\gcd(m,2)=1.
\tag{76.1}
$$

Thus every phase is actual, and both original alphabets contain every $m$-bit word. Put $A=\{0,\ldots,m\}$ and $z=m+1$. Let $\lambda:A\to Y$ have exactly three labels $L=\lambda[A]$. Choose distinct fresh $R,C\notin L$, and give initial bottom any independent label $L_\bot$. Specify the entire INITIAL target on both free-value fibres by

$$
f(v,-j,s)=
\begin{cases}
R,&s=m,\\
\lambda(j),&s<m,\ j\in A,\\
C,&s<m,\ j=z,
\end{cases}
\qquad f(\bot)=L_\bot,
\qquad F(w)=f(q_{\rm INITIAL}(w)).
\tag{76.2}
$$

The phase coordinate is modulo $T$. In particular the history factorization in (76.2) is specified, not inferred from legality. Set

$$
\begin{aligned}
e&=m-1, &K&=\{\lambda(0),\lambda(1)\},\\
O&=\{\ell\in L:|\lambda^{-1}(\ell)|\text{ is odd}\},\\
\mathsf U&\Longleftrightarrow |O|=2\text{ and }K\nsubseteq O,\\
\mathsf V&\Longleftrightarrow O=\varnothing\text{ and }
|K\cup\{\lambda(e)\}|=3.
\end{aligned}
\tag{76.3}
$$

Since $|A|=m+1$ is even and $|L|=3$, $|O|$ is zero or two. Multiplicities count phases, not INITIAL tails. The costs $C_{\rm ad},C_{\rm pre}$ are exactly [IC, Definition 1.3]; the latter requires one fixed literal stream for this fixed full target, with source-dependent endpoint stopping.

For an even binary row $q$ supported on the actual ordered path $W_t=[tm,(t+1)m]\pmod T$, denote its supplied literal inverse [IC, Interface 1.4] by

$$
\mathcal B_t(q)_i=\bigoplus_{h=0}^{i}q(tm+h\bmod T),
\qquad 0\le i<m.
\tag{76.4}
$$

A row prescribes bits of this one complete word; it adds no action or observation. The first two paths are

$$
W_0=(0,1,\ldots,m),\qquad
W_1=(m,z,0,1,\ldots,m-2),
\tag{76.5}
$$

so $e$ is the sole phase outside $W_1$.

**定理 76.2（Exact whole-class three-label prices）。** For every table in Definition 76.1, under both original alphabets,

$$
\boxed{C_{\rm ad}(f)=2+\mathbf1_{\mathsf U},\qquad
C_{\rm pre}(f)=2+\mathbf1_{\mathsf U\lor\mathsf V}.}
\tag{76.6}
$$

The possible pairs are $2/2$, $2/3$ and $3/3$. The two-block adaptive attainment below specifies the actual two child words. The two-block GLOBAL attainment specifies one second word shared by both live children and both free values. Whenever three blocks are necessary, the supplied Chapter 73 suffix after the alternating root attains that fee on the same entire target.

**证明（joint sources, every competing root, and two-block extraction）。** Use the credited actual history witness [IC, (1.3); S1, Convention 1.3; S15, Section 1]. For every $v,j,s$ appearing in (76.2), choose

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad
\ell\ge s+2,\qquad
\eta=\bigoplus_{i=\ell-s}^{\ell-1}c_i,
\qquad w=(v\oplus\eta)0^{\ell-s-1}1^s.
\tag{76.7}
$$

The actual gcd in (76.1) gives arbitrarily large such lengths. This single legal history simultaneously realizes value $v$, phase $-j$ and tail $s$ at a complete endpoint; its separating zero prevents a forbidden run. Its length is a multiple of $m$ and all its blocks belong to both alphabets. The unobserved length is not a controller input. An all-one complete-block history of length at least $k$ realizes initial bottom separately. Thus every phase and tail used in the argument is an actual joint source.

Fix either free value. At any phase the INITIAL tails $m-1$ and $m$ have different labels, the former in $L\cup\{C\}$ and the latter fresh $R$. Free stopping is impossible. A root beginning zero merges these two actual records at that first zero, with the same scalar and phase. Their complete endpoint archives and all later archives are then identical. A root with at least two leading ones, including $1^m$, rejects both before the first endpoint; the unobserved rejection positions cannot distinguish them, and bottom is absorbing. The supplied first-zero and rejection loss [S1, Lemmas 4.2–4.3; S15, Proposition 4.2] therefore excludes all these roots at every later horizon. Every correct root has prefix $10$.

Every such root rejects exactly $s=m$ and preserves all low tails $s<m$. Each low source reaches its second bit safely because $s+1\le m<k$. That zero merges the low tails separately at each phase, preserving their common label in (76.2); later runs are internally shorter than $k$. All low sources finish with the same actual terminal tail $\rho\le m-2$. If $r$ is this root's successful charge, its physical path and prefix give

$$
r(z)=0,\qquad r(0)=r(1)=1,\qquad
\bigoplus_{j\in A}r(j)=0.
\tag{76.8}
$$

The high band is homogeneous $R$ and stops at its one paid endpoint. The low sources have four labels $L\cup\{C\}$ and at most two successful root outcomes, proving $C_{\rm ad}\ge2$.

Suppose a controller finishes in at most two blocks. Each low root child has common current value and tail. The credited common-tail restriction [S10, Lemma 3.2] makes every next literal word either all-successful or all-rejecting on that child. Uniform rejection cannot finish a nonconstant child, at that endpoint or after absorption; a successful second word has at most two outcomes. Each root child consequently has at most two labels. Their union has four labels, so each has exactly two, their label images are disjoint, and neither can stop at the first endpoint. Every occurrence of a low label must have the same first difference; otherwise the two two-label images would overlap and their union would have fewer than four labels.

The zero child contains $C$, since $r(z)=0$. Hence for a unique $D\in L$, with the remaining labels denoted $E,F$,

$$
r(j)=\mathbf1_{\{\lambda(j)\ne D\}}\quad(j\in A),
\qquad\text{child 0 has }\{D,C\},\quad
\text{child 1 has }\{E,F\}.
\tag{76.9}
$$

Equation (76.8) now forces

$$
|\lambda^{-1}(D)|\text{ even},\qquad D\notin K.
\tag{76.10}
$$

This extraction quantifies every literal root and second action, all attempted rejections, endpoint stops and adaptive choices. A wait still occupies one of the two paid chronological slots and obeys the same equations; no later window can be inserted for free.

**证明（actual adaptive attainment of every admitted even class）。** Conversely choose any $D$ satisfying (76.10). Define $r$ by (76.9), with $r(z)=0$, and issue $B_0=\mathcal B_0(r)$. The row is even because $m+1$ and the size of the $D$ class are even. Its first two bits are $10$. The preceding root proof gives precisely the two live archives (76.9), actual tail $\rho$, and the stopped high band $R$.

On child zero issue the actual pulse

$$
B^{(0)}=010^{m-2}.
\tag{76.11}
$$

Its index-one support is $\{z,0\}$. Since $D\notin K$, phase zero is absent from this child. The successful difference is therefore zero on every $D$ source and one on $C$ at $z$. Its first bit zero clears every actual incoming tail. Return $D$ or $C$ from this source's own two endpoint differences.

Child one is the actual positive child $A_+=A\setminus\lambda^{-1}(D)$ of $B_0$, with exactly two labels. Its missed support $A_+\setminus W_1$ is empty or the singleton $\{e\}$. Its parent contains a zero and $A_+\ne W_0$, so the exact binary law [IC, Theorem 65.2, (65.2)–(65.5)] gives additional fee one: its exceptional full-positive support is absent. The following explicit row exhibits a safe word of that credited completion.

Choose $P\in\{E,F\}$ different from $\lambda(e)$ when $e\in A_+$; otherwise either choice is allowed. Prescribe

$$
q(j)=\mathbf1_{\{\lambda(j)=P\}}
\quad(j\in A_+\cap W_1),\qquad q(e)=0.
\tag{76.12}
$$

Initially set other charges zero. If $\lambda(m)=D$, set $q(m)=0$ and choose $q(z)$ to make the row even; all other $D$ charges remain zero. The actual root ends zero because its last bit is $r(m)=0$, so every resulting $m$-bit word is safe from tail zero.

If $\lambda(m)\ne D$, set $q(z)=q(m)$. The $D$ class has positive even size, excludes $0,1,m$, and loses at most its one vertex $e$ outside $W_1$. Choose any

$$
t\in\lambda^{-1}(D)\cap W_1.
\tag{76.13}
$$

Such $t$ exists and lies in $\{2,\ldots,m-2\}$. Choose its charge to make the row even, leaving the other $D$ charges zero. Both $z$ and $t$ are absent from child one. Formula (76.4) gives $B^{(1)}=\mathcal B_1(q)$ whose first two bits are $q(m),0$, so its leading run is at most one. The actual seam satisfies

$$
\rho+\alpha(B^{(1)})\le(m-2)+1=m-1<k.
\tag{76.14}
$$

Its later runs are internally safe. Both cases realize difference one on $P$ and zero on the other positive-child label, including the missed phase $e$. Return that label from the same source's own second difference. Compensation only prescribed the bits of this one word; no donor source or extra observation was used. The root and both child seams are now checked on the original records. Both low children contain two labels and actual sources, so their two-block fee is attained. The initial free value selects the same difference decoder on both fibres.

An even $D\notin K$ exists exactly when $\neg\mathsf U$: if $O=\varnothing$, all three classes are even and $|K|\le2$; if $|O|=2$, the unique even class is available precisely when $K\subseteq O$. Thus (76.10), the adaptive attainment, and the extraction prove the adaptive two-block criterion.

**证明（the necessary parity of one GLOBAL second word）。** Suppose a GLOBAL controller finishes in two blocks. Extraction gives the same even class $D$ and (76.9). All four low labels remain live until the second endpoint. The one second word must succeed on these common-tail sources and separate the two labels within each first child. Its physical row $q$ is constant on each of $D,C,E,F$, is zero at the missed phase $e$, and has even full-path parity. Let $a\in\{0,1\}$ be its charge on $D$. Its charge on $C$ is $1-a$; precisely one of $E,F$, called $P$, has charge one. Therefore

$$
0=\bigoplus_{j\in W_1}q(j)
=(1-a)\oplus\bigl(|\lambda^{-1}(P)|\bmod2\bigr).
\tag{76.15}
$$

Here $D$ has even size and $q(e)=0$, so deleting the unavailable phase changes no term. If $|O|=2$, $D$ is the unique even label and both positive-child classes are odd. Equation (76.15) forces $a=0$, hence $q(C)=1$. If $O=\varnothing$, it forces $a=1$, hence $q(C)=0$; the unavailable phase must then satisfy $\lambda(e)\ne D$.

Consequently GLOBAL fee two requires an even $D$ outside $K$ and, in the all-even case, outside $\{\lambda(e)\}$. These conditions are equivalent to $\neg\mathsf U\land\neg\mathsf V$. Early stops cannot evade the row condition because both two-label children are live; a second-block rejection cannot help because it merges each entire live child. This is a simultaneous physical-row obstruction, not a maximum of child prices.

**证明（one safe GLOBAL pair of words whenever both tests fail）。** Choose $D$ satisfying the preceding conditions and use the same literal root $B_0=\mathcal B_0(r)$. Let $E,F$ be the other labels and choose $P\in\{E,F\}$ different from $\lambda(e)$; if $\lambda(e)=D$, either choice is allowed. Define the single second row by

$$
\begin{array}{c|cccc}
 &D&C&P&\{E,F\}\setminus\{P\}\\
|O|=2&0&1&1&0\\
O=\varnothing&1&0&1&0
\end{array}
\tag{76.16}
$$

These entries prescribe $q(j)$ at every low-label phase, including $q(z)$ for $C$. They give $q(e)=0$ and even full-path parity by (76.15). Thus the unique word $B_1=\mathcal B_1(q)$ is an actual index-one action.

For $|O|=2$, if $\lambda(m)=D$ the root ends zero; otherwise either $q(m)=0$ makes $B_1$ begin zero, or $\lambda(m)=P$ gives $q(m)=q(z)=1$, making $B_1$ begin $10$. The latter seam has leading run one and obeys (76.14). Every case is safe on both live children.

For $O=\varnothing$, the admitted $D$ differs from $\lambda(e)$. If the root ends one, its penultimate bit is

$$
(B_0)_{m-2}=(B_0)_{m-1}\oplus r(e)=1\oplus1=0,
\tag{76.17}
$$

so its actual terminal tail is exactly one. If it ends zero its tail is zero. Moreover the second row charges every phase in each of the two distinct, nonempty even classes $D,P$. Its support has at least four vertices. The charge support of $1^m$ is only the two endpoints of $W_1$, so $B_1\ne1^m$. It contains a zero and has leading run at most $m-1$. Its actual seam is consequently

$$
\rho+\alpha(B_1)\le1+(m-1)=m<k.
\tag{76.18}
$$

This proves safety of the very same $B_0\mid B_1$ on both low children and both free values, including a nonzero seam. Within each first child the two entries of (76.16) differ. The decoder reads its own root and second differences and returns the unique label in that child's pair. High $R$ sources stop at the completed root; initial bottom stops freely. Every low source emits both paid words. This is one GLOBAL stream for the fixed target.

**证明（credited three-block attainment and the final lower bounds）。** For any table in Definition 76.1, issue the supplied alternating root $P_m=(10)^{(m-1)/2}1$. Exactly the high INITIAL band rejects to $R$. Every low fibre is merged with its label preserved. Its successful zero-difference archive is exactly phase $z$ with label $C$ and stops at fee one. Its positive archive is exactly $W_0=A$, with common tail one and all three labels. Apply Theorem 73.6 with $a=u=0,n=3,d=2$: Construction 73.4 supplies one fixed two-word suffix, and Lemma 73.5 proves both its seam after this actual root and its internal seam. The full-target label-preservation and own-archive decoder are precisely the proof of Theorem 74.2, whose attainment argument does not require $n$ to be a power of two; this is the credited nonsaturated upper bound explicitly retained in Open Problem 75.3. Both free values use the same words. Only the positive child continues; no sibling knowledge is consulted.

The resulting GLOBAL stream has worst fee three, with every issued block paid, including the rejecting root on the $R$ branch. If $\mathsf U$ holds, the all-action extraction forbids adaptive fee two, so both prices equal three. If $\mathsf U$ fails and $\mathsf V$ holds, the adaptive construction gives two while (76.15) forbids every two-block GLOBAL stream, giving three. When both tests fail the common pair gives two, and the four low labels forbid fee below two. All conclusions hold on either free-value fibre separately, so a different adaptive root on the other fibre cannot improve the lower bounds. This proves (76.6) for every table, every odd $m\ge3$, and both original alphabets. ∎

## 77. Inhabited pairs, literal witnesses and mathematical boundaries

**命题 77.1（Each price pair is inhabited by entire INITIAL targets）。** Choose three distinct labels $A_0,B_0,D_0$, with fresh $R,C$ and independent bottom as in (76.2). For every odd $m\ge3$, the table

$$
\lambda(0)=A_0,\qquad\lambda(1)=B_0,\qquad
\lambda(j)=D_0\quad(2\le j\le m)
\tag{77.1}
$$

has price pair $2/2$, whereas

$$
\lambda(0)=\lambda(2)=A_0,\qquad\lambda(1)=B_0,\qquad
\lambda(j)=D_0\quad(3\le j\le m)
\tag{77.2}
$$

has price pair $3/3$. For every odd $m\ge5$, put

$$
\lambda(0)=\lambda(2)=A_0,\qquad
\lambda(1)=\lambda(m)=B_0,\qquad
\lambda(j)=D_0\quad(j\notin\{0,1,2,m\}).
\tag{77.3}
$$

This table has price pair $2/3$. There is no all-even three-label table at $m=3$, so $2/3$ first occurs at $m=5$ in this class.

**证明。** For (77.1), the counts are $1,1,m-1$; its two odd labels are exactly $K$, so $\mathsf U$ and $\mathsf V$ are false. For (77.2), the counts are $2,1,m-2$; the odd labels are $B_0,D_0$, while $A_0\in K$, so $\mathsf U$ holds. For (77.3), the counts are $2,2,m-3$, all positive and even. Here $K=\{A_0,B_0\}$ and $\lambda(m-1)=D_0$, so $\mathsf V$ holds and $\mathsf U$ fails. Theorem 76.2 gives each price. An all-even table with three nonempty cells needs at least six phases in $A$, proving the last claim. These are symbolic families on the full source, not a finite optimum catalogue.

Concrete words expose their actual endpoint decoding. At $m=3$, (77.1) is $(A_0,B_0,D_0,D_0)$, with GLOBAL stream $100\mid010$. The root difference zero means $D_0$ or fresh $C$; the second difference distinguishes them. Root difference one means $A_0$ or $B_0$; the second difference one returns $A_0$ and zero returns $B_0$. The root ends zero and the second word begins zero.

At $m=3$, (77.2) is $(A_0,B_0,A_0,D_0)$, with GLOBAL stream $101\mid011\mid001$. On the root-positive archive the two suffix differences are $00$ for $A_0$, $10$ for $B_0$, and $01$ for $D_0$. The first suffix begins zero after root tail one; the second begins zero after suffix tail two. Fresh $C$ stops on root difference zero and $R$ on root bottom.

At $m=5$, (77.3) is $(A_0,B_0,A_0,D_0,D_0,B_0)$. An adaptive root is $10111$. After root difference zero use $01000$, returning $D_0$ on difference zero and $C$ on one. After root difference one use $00110$, returning $A_0$ on difference one and $B_0$ on zero. Both child words begin zero after the actual root tail three. A GLOBAL stream is $10101\mid00110\mid00111$. Its root-positive suffix codes are $10,01,00$ for $A_0,B_0,D_0$ respectively; the first suffix begins zero and ends zero, so both seams are safe. All these words have the stipulated width, every continued source uses its own endpoint differences, and high rejection and initial bottom follow the stops in Theorem 76.2. ∎

**边界 77.2（Resources, effective input and the unresolved original domain）。** In (76.6) the worst emitted-bit fee is exactly $mC_{\rm ad}$ or $mC_{\rm pre}$ respectively: every issued action is a whole $m$-bit block, even when rejection occurs before its endpoint. Root-reject sources emit one block; initial bottom emits zero. The attaining controllers use one initial read and one complete-endpoint read per issued block. Thus the worst number of subsequent endpoint Reads is the stated block fee, or one more if the free initial read is included in the Read count. There are no intermediate reads or separate calibration experiments. Computational work, storage, label comparison and any external query used to present the target are separate resources, not free emitted blocks or additional bits of physical observation.

For arbitrary unpresented labels, these minimum and attainment statements are semantic. A given finite partition, or a table with decidable equality, makes the choice effective: count each of the three cells, compare the labels at $0,1,e$, choose the displayed $D,P$ and at most one donor, and invert the rows. The two-block constructions need $O(m)$ label comparisons and binary row operations and $O(m)$ stored word bits, with a constant number of label references and observed differences. The three-block alternative can use the supplied Chapter 73 selection on the three labels; its two-bit code search has a constant finite number of assignments, followed by $O(m)$ row operations. These are operation counts, not bit-complexity bounds for arithmetic or arbitrarily represented labels. Input-table and label-representation storage remain separate. No effective factorization algorithm for an arbitrary history expression is obtained from the explicit pullback (76.2).

The theorem requires every part of (76.1)–(76.2): odd $m$, $k=m+1$, the actual full prior, the identical tables on both free-value fibres, exactly three low phase labels, fresh distinct $R,C$, and the homogeneous high tail band. It does not price even widths, other orders, noncoprime readers, different value-fibre tables, coincident root labels, arbitrary acquired supports, tail-dependent tables or history targets with an unproved INITIAL factorization. The GLOBAL stream is shared by all sources of one fixed target; changing that target may change its words. The all-parameter, all-attainable-target objective of [IC, Definition 1.3 and Open Problem 9.1] remains unresolved.

## 78. Exact source comparisons used in the three-label bridge

**数学引文 78.1（Supplier hypotheses and single-source identification）。** [IC, Chapter 1; S1, Definitions 1.2–2.1, Convention 1.3, Proposition 2.2, Lemmas 4.2–4.3 and Note 5.3] supplies the actual joint histories, immutable INITIAL factorization, absorption, endpoint-only archive and semantic/effective boundary consumed in (76.2), (76.7) and the root exclusion. [S2, Sections 13–14, Theorem 14.1] supplies the original matched coefficient cycle, with the original weights rather than a surrogate phase model. [IC, Interface 1.4; S10, Interface 2.1 and Lemma 3.2; S15, Section 1, Definitions 1.1 and 2.1 and Proposition 4.2] supplies literal inversion, strict inherited-tail safety, common-tail rejection and the distinction between separate adaptive child words and a shared stream. These supplied facts are consumed in the proof rather than asserted as additional generic results.

[IC, Definition 65.1 and Theorem 65.2] gives the binary positive-child completion used in (76.12)–(76.14). Its paid exception requires support exactly $W_0$, whereas the chosen positive child omits the nonempty even class $D$. The pulse (76.11) is the inverse of the even charge support $\{z,0\}$ at issued index one under the supplied literal interface [IC, Interface 1.4, (1.4)–(1.5)]; its absent phase-zero donor is verified on the actually acquired zero child here. The entire three-block upper bound is supplied by Theorem 73.6, Lemma 73.5, the label-preservation proof in Chapter 74 and the nonsaturated upper-bound clause of Open Problem 75.3. No new Hall or unrestricted capacity theorem is required.

The parity mechanism in [IC, Chapters 36–38] counts actual phase multiplicities in a common stream. Its fee-realization hypotheses require $m\ge k$, and its room-qualified theorem further requires $a+k+2\le m$ for an eligible cut; neither hypothesis holds at $k=m+1$. In particular the four low labels here have respectively one or three odd cells after adding the singleton $C$ to the three-label table. An unrestricted even two-bit code for those multiplicities does not enforce the actual root charges $r(0)=r(1)=1$ or the unavailable second coordinate $q(e)=0$. The new physical restriction (76.15) uses those conditions together, and the strict seams (76.14), (76.17)–(76.18) verify its attainment. The control-separation archive of [IC, Mathematical Counterexample 34.4; S15, Theorem 8.1] retains its different $k=8,m=4$ reader, seven-phase acquired support and paid prefix. Its distinct child words do not supply a common suffix for (76.2).

The companions [M, Definition 1.2 and Theorem 2.1], [T3, Definition 1.2 and Theorem 2.1] and [F4, Definition 72.1 and Theorem 72.2] condition on an actually emitted $1^m$ root and its zero archive. Their current tails are $m+s$ on the specified low rectangle, and their phase support omits $0,m$. Here that root is impossible for the full target, the correct root has prefix $10$, and its two successful siblings are simultaneously live at fee two. Those companion prices keep their hypotheses and are not substituted for (76.9)–(76.18). The guarded continuation laws of [IC, Chapters 27 and 60–64] require $k\ge2m$, also outside (76.1).

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definition 20 and Figure 3](https://arxiv.org/pdf/1907.11034v2), gives the mature comparison of adaptive distinguishing tests and destructive first actions: their Figure 3 excludes a test when each available first input or output merges a pair that must be distinguished. Here one input is an original literal complete block and an output is its completed endpoint; separation is required for unequal INITIAL labels. That comparison supports the identification contract, not the KBonacci root charges, unavailable vertex, parity criterion or emitted-block fee. Neither generic distinguishing graphs nor independently distinguishable pairs are treated as a proof of the actual common stream. These are ordinary mathematical proofs on the stated suppliers, without a kernel-certification or literature-priority claim.

## 追加锚（本行以下为增补区）

## 79. A dyadic placement law on entire INITIAL targets

**定义 79.1（Two equal-multiplicity tables and their complete extensions）。** Retain the original integer weights, matched $V_k\bmod2$ reader, full jointly attainable complete-history prior and immutable INITIAL records of [IC, Definitions 1.1–1.3]. For an integer $d\ge3$ put

$$
N=2^d,\qquad k=N,\qquad m=N-1,\qquad T=N+1,
\qquad g=\gcd(m,T)=\gcd(N-1,2)=1.
\tag{79.1}
$$

Thus every phase modulo $T$ is actual. Both original control alphabets contain every $m$-bit word, since $m<k$, while cross-block rejection remains absorbing. Only complete endpoints are observed. Every issued complete block is paid, including waits, padding, repairs and a block rejecting before its completed endpoint. INITIAL value, or independent initial bottom, is freely read. No reset, copy, hidden INITIAL clock, intermediate reading or observation from another branch is available.

Let $a_0,\ldots,a_{N-3},D,R,C$ be pairwise distinct labels. Put $A=\{0,\ldots,N-1\}$ and $z=N$. Define

$$
\lambda_{\rm good}(j)=
\begin{cases}
a_j,&0\le j\le N-3,\\
D,&j=N-2,N-1,
\end{cases}
\qquad
\lambda_{\rm bad}=\lambda_{\rm good}\circ\sigma,
\quad \sigma=(0\ \ N-2).
\tag{79.2}
$$

In particular the bad table has $D$ at $0,N-1$, $a_0$ at $N-2$, and $a_j$ at $j$ for $1\le j\le N-3$. Each table has $N-2$ singleton classes and one double class. For $\varepsilon\in\{{\rm good},{\rm bad}\}$ specify the entire target on both free INITIAL value fibres by

$$
f_\varepsilon(v,-j,s)=
\begin{cases}
R,&s=m,\\
\lambda_\varepsilon(j),&0\le s<m,\quad j\in A,\\
C,&0\le s<m,\quad j=z,
\end{cases}
\qquad
f_\varepsilon(\bot)=L_\bot,
\qquad
F_\varepsilon(w)=f_\varepsilon(q_{\rm INITIAL}(w)).
\tag{79.3}
$$

Here $v\in\mathbb F_2$, $j=-\theta_{\rm INITIAL}\pmod T$, and $L_\bot$ is arbitrary and independent; it may coincide with another label. The map $q_{\rm INITIAL}$ is the original record of the source history before any control action. Thus (79.3) explicitly supplies the history pullback and labels every actual record, including both free-value fibres, every original tail $0\le s<k$, and initial bottom. It is not a target evaluated again on the updated record. Write $C_{\rm pre}$ for the original GLOBAL price: one fixed literal stream for all actual sources of this fixed target, with stopping and decoding from each source's own endpoint archive. Different targets may have different streams.

**定理 79.2（The whole-reader price changes under one transposition, at every depth）。** For every integer $d\ge3$, under each original alphabet and the full actual source prior of Definition 79.1,

$$
\boxed{
C_{\rm ad}(f_{\rm good})=C_{\rm pre}(f_{\rm good})=d,
\qquad
C_{\rm ad}(f_{\rm bad})=C_{\rm pre}(f_{\rm bad})=d+1.
}
\tag{79.4}
$$

The same prices hold for the explicit history targets $F_\varepsilon$. The GLOBAL attainments below each use one stream on both free-value fibres. These are whole-target fees from the free INITIAL reading, not additional fees after a chosen root.

**证明（joint sources, the compulsory root and all-action capacity）。** Use the credited single-history witness [IC, (1.3); S1, Convention 1.3; S15, Section 1]. For every $v,j,s$ in (79.3), choose

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad
\ell\ge s+2,\qquad
\eta=\bigoplus_{i=\ell-s}^{\ell-1}c_i,
\qquad w(v,j,s)=(v\oplus\eta)0^{\ell-s-1}1^s,
\quad c_i=\mathbf1_{\{0,N\}}(i\bmod T).
\tag{79.5}
$$

Coprimality in (79.1) makes the congruences compatible and supplies arbitrarily large choices. The separating zero makes this one word legal, its first bit compensates the terminal run's scalar contribution, and its complete-block length, value, phase and tail are simultaneously $\ell,v,-j,s$. Its blocks belong to both alphabets. The all-one history $1^{2m}$ separately realizes bottom: each constituent block is internally legal, and the second block crosses the rejection threshold. The unobserved source lengths are not controller inputs. Consequently every source used below belongs to the full joint prior. The original deterministic record interface and the explicit pullback (79.3) also identify acquisition of $F_\varepsilon$ with acquisition of $f_\varepsilon$ [S1, Proposition 2.2].

Fix either free INITIAL value $v$. At every phase the actual original tails $m-1$ and $m$ have different labels, because the latter is fresh $R$. Free stopping is impossible. A root starting zero merges these two sources at that zero, giving identical current records, identical completed root endpoints and identical future behaviour. A root with at least two leading ones, including the all-one root, rejects both sources before the completed endpoint. Their rejection times are unobserved, and their entire subsequent output archives are absorbing bottom. Neither case can return their different INITIAL labels. Every correct controller must therefore start with a word $B_0$ whose first two literal bits are $10$.

Such a word rejects exactly the high band $s=m$, whose label is $R$. Every low source $s<m$ survives the leading one, reaches the first zero and finishes safely, because all subsequent runs lie inside a word of length $m<k$. At a fixed phase all surviving tails merge with their common INITIAL label preserved. Across every low source the actual terminal tail is the same tail of this root. Let $r(j)$ be its successful endpoint difference. The supplied path equations [IC, Interface 1.4] give

$$
r(z)=0,\qquad r(0)=r(1)=1,
\qquad \bigoplus_{j\in A}r(j)=0.
\tag{79.6}
$$

Within either successful root archive the current value and tail are common. On every later such archive, any literal action either succeeds on all its candidates or rejects all, by [S10, Lemma 3.2]. Common rejection cannot separate unequal INITIAL labels, then or after further absorbed blocks. A successful action has at most two endpoint outcomes, each again with common current value and tail. Induction therefore bounds the number of distinct labels returnable in $h$ further paid blocks by $2^h$, allowing earlier homogeneous endpoint stops. This is the credited binary-tree bound applied to these actual archives. It includes all literal words, all-one words, waits, padding, attempted repairs and rejection; each issued word occupies a paid chronological slot.

There are exactly $N$ low labels, namely $a_0,\ldots,a_{N-3},D,C$. If a whole controller has worst fee $h\ge1$, let $L_b$ be the set of low labels in successful root-difference child $b$. Each child has $|L_b|\le2^{h-1}$, including a child stopped immediately. Their union contains all $N$ labels. Hence $N\le2^h$ and every adaptive controller for either target has fee at least $d$.

Suppose now that a controller finishes in $d$ blocks. The two inequalities $|L_b|\le N/2$ and $|L_0\cup L_1|=N$ force

$$
|L_0|=|L_1|=N/2,\qquad L_0\cap L_1=\varnothing.
\tag{79.7}
$$

Thus every occurrence of a low label has the same root difference; splitting the double class between two archives would violate (79.7). Phase $z$ has label $C$ and difference zero. The positive child therefore has exactly $N/2$ label classes all in $A$. Each contributes one phase, except that $D$ contributes a second phase if it is positive. Root parity in (79.6) consequently says

$$
0=\left(\frac N2\bmod2\right)\oplus r(D)=r(D),
\tag{79.8}
$$

where $r(D)$ is well-defined by (79.7), and $N/2$ is even. For the bad placement phase zero has label $D$, contradicting $r(0)=1$. This rules out fee $d$ even adaptively, whatever later words or endpoint stops are proposed. Together with the preceding capacity bound it gives $C_{\rm ad}(f_{\rm bad})\ge d+1$. The argument was on an arbitrary fixed free-value fibre, so allowing different adaptive roots on the two fibres cannot improve either lower bound.

**证明（one literal $d$-block GLOBAL stream for the good target）。** Extend the good low table to the full phase cycle by $\Lambda(j)=\lambda_{\rm good}(j)$ on $A$ and $\Lambda(z)=C$. We construct a bijection

$$
c:\{a_0,\ldots,a_{N-3},D,C\}\longrightarrow\{0,1\}^d,
\qquad c(D)=0,
\tag{79.9}
$$

with coordinates indexed $t=0,\ldots,d-1$. The cube's zero-sum identity and distinct-code counting are ordinary binary coding algebra, as in [IC, Definition 36.2 and Theorem 37.1]; they are not a new coding optimum. The following finite selection arranges the extra physical restrictions of this reader.

At actual issued index $t$, the path $W_t=[tm,(t+1)m]\pmod T$ has $N$ vertices and misses exactly

$$
e_t=N-2t\quad(0\le t\le d-1).
\tag{79.10}
$$

Indeed $m\equiv-2\pmod T$ and the sole missing vertex is $tm-1\pmod T$. For $t\ge1$ its first vertex is $s_t=N+1-2t$ and its last vertex is $e_t-1$; the last vertex of $W_{t-1}$ is $s_t$. No displayed index wraps ambiguously: $2^d\ge2d+2$ for $d\ge3$, by induction from $d=3$. In particular all $e_t,s_t$ for $2\le t\le d-1$ are distinct singleton phases between $4$ and $N-3$, with $e_t$ even and $s_t$ odd. Their labels are distinct from $a_0,a_1,D,C$.

Choose distinct codes satisfying

$$
\begin{aligned}
c_0(C)&=0,&c_0(a_0)&=c_0(a_1)=1,\\
c_t(a_{e_t})&=0&& (2\le t\le d-1),\\
c_{t-1}(a_{s_t})c_t(a_{s_t})&=0&& (2\le t\le d-1).
\end{aligned}
\tag{79.11}
$$

Here is a complete finite existence argument, within the construction. Reserve zero for $D$. First choose the $d-2$ codes for $a_{e_t}$, avoiding previous choices; each permitted nonzero list has $N/2-1$ elements. Next choose $C$ from the $N/2-1$ nonzero vectors with coordinate zero equal to zero. Next choose $a_0,a_1$ from the $N/2$ vectors with coordinate zero equal to one. These choices always remain possible: $N/2\ge d+1$, so before these successive choices fewer than the relevant list size have been used. Finally choose the $d-2$ codes for $a_{s_t}$. Each nonzero list has $3N/4-1$ elements, since just the quarter with both indicated coordinates one is excluded, and zero has been reserved. Before any such choice at most $2d-2$ nonzero vectors have been used. The inequality $3N/4\ge2d$, valid at $d=3$ and preserved when $d$ increases, makes $3N/4-1>2d-2$. Each choice is therefore possible. Assign the remaining labels the remaining vectors in any order. The constrained labels are distinct, so there is no accumulated condition on a single label. This proves (79.9)–(79.11), including $d=3$.

Each cube coordinate has $N/2$ ones, an even number. The full phase cycle contains one occurrence of every code and one extra occurrence of $c(D)=0$. Therefore

$$
\bigoplus_{j=0}^{N}c(\Lambda(j))=0.
\tag{79.12}
$$

At the missed phase $e_0=z$ the desired coordinate is zero by the first clause of (79.11). At $e_1=N-2$ it is zero because the label is $D$. At every later $e_t$ it is zero by the second clause of (79.11). Prescribe the physical row

$$
\chi_t(j)=c_t(\Lambda(j))\quad(j\in W_t),
\qquad \chi_t(e_t)=0,
\qquad
B_{t,i}=\bigoplus_{h=0}^{i}\chi_t(tm+h\bmod T)
\quad(0\le i<m).
\tag{79.13}
$$

Equations (79.12) and the zero missed coordinate give even full-path parity. The supplied inverse [IC, (1.5)] thus makes $B_t$ one actual complete word realizing this row, including its zero outside $W_t$. Issue the single fixed stream $B_0\mid\cdots\mid B_{d-1}$.

The root's first two bits are $c_0(a_0)=1$ and $c_0(a_0)\oplus c_0(a_1)=0$. Its last bit is $c_0(D)=0$. It therefore has exactly the legal root behaviour proved above: high $s=m$ sources reject to $R$, and every low source survives with its INITIAL label preserved. The first subsequent word starts at $s_1=N-1$, also labelled $D$, so its first bit is zero. For every later boundary the actual adjacent bits are

$$
B_{t-1,m-1}=c_{t-1}(\Lambda(s_t)),\qquad
B_{t,0}=c_t(\Lambda(s_t)),\qquad
B_{t-1,m-1}B_{t,0}=0\quad(2\le t\le d-1).
\tag{79.14}
$$

Thus every boundary has a zero among its adjacent bits. No run of ones crosses a boundary, and no individual word of length $m<k$ contains a forbidden run. These very words are safe on every continuing low source; no paid clearing, wait or repair word has been omitted.

Initial bottom stops freely with $L_\bot$. A root-bottom observation returns $R$ at its completed endpoint, after the whole one paid root. For every successful low source remember its own outputs $v_0,\ldots,v_d$ and form

$$
(v_1\oplus v_0,\ldots,v_d\oplus v_{d-1})
=c(\Lambda(j)).
\tag{79.15}
$$

Return the unique label with this code. The same stream and decoder work for both initial values; the remembered baseline is the source's own free initial reading. Every low source may execute all $d$ words and then stop, so the actual worst fee is $d$. No reading of phase, another archive or another history was used. No extra final cleanup is needed at an endpoint stop, even if the last tail is nonzero. This gives $C_{\rm pre}(f_{\rm good})\le d$ and completes the good equality.

**证明（the credited actual $(d+1)$-block stream for the bad target）。** Use the full-positive-window supplier, Theorem 73.6 with $a=u=0$ and $n=N-1$. Its hypotheses are checked by the following actual arrival, not assumed for a counterfactual child. Issue

$$
P_m=(10)^{(m-1)/2}1.
\tag{79.16}
$$

It has leading run one, an internal zero and terminal tail one. It rejects exactly INITIAL $s=m$, returning $R$ at fee one, and preserves every low-tail label when its first zero merges the original tails. Its charge is one at every $j\in A$ and zero at $z$. The successful zero-difference archive therefore consists exactly of low phase $z$, has label $C$ and stops at fee one. Its successful positive archive has exactly $A=W_0$, common current value $v\oplus1$, common tail one and the table $\lambda_{\rm bad}$ with $N-1\ge7$ labels. All these candidates are actual by (79.5).

For precision, the supplied fixed suffix can be written here without leaving its words or decoder unspecified. Since $\lceil\log_2(N-1)\rceil=d\ge3$, Lemma 73.3 supplies distinct codes $b(L)\in\{0,1\}^d$ for the bad table's labels, now indexed $r=1,\ldots,d$, satisfying exactly

$$
\begin{aligned}
b_r(\lambda_{\rm bad}(N-2r))&=0&&(1\le r\le d),\\
b_1(\lambda_{\rm bad}(N-1))&=0,\\
b_{r-1}(\lambda_{\rm bad}(N+1-2r))\,
 b_r(\lambda_{\rm bad}(N+1-2r))&=0&&(2\le r\le d).
\end{aligned}
\tag{79.17}
$$

The finite Hall selection in that lemma is credited reuse. Its index restriction holds because $d\le N/2$, and $N-2d\ge2$ for $d\ge3$. For each absolute issued index $r=1,\ldots,d$, set $e_r=N-2r$ and prescribe

$$
\begin{aligned}
\psi_r(j)&=b_r(\lambda_{\rm bad}(j))&& (j\in A\setminus\{e_r\}),\\
\psi_r(z)&=\bigoplus_{j\in A\setminus\{e_r\}}b_r(\lambda_{\rm bad}(j)),
&\psi_r(e_r)&=0,\\
H_{r,i}&=\bigoplus_{h=0}^{i}\psi_r(rm+h\bmod T)&& (0\le i<m).
\end{aligned}
\tag{79.18}
$$

These are precisely Construction 73.4 in the present parameters. The path $W_r$ misses only $e_r$ and contains $z$. The donor $z$ is an actual phase elsewhere, but absent from this continuing positive archive; its prescribed charge fixes the bits of this same word and supplies no borrowed information. Each full path is even, and (79.17) makes the unavailable coordinate zero. Thus every $H_r$ has width $m$ and realizes its desired code coordinate on every positive-archive source.

The literal stream for this fixed full bad target is

$$
P_m\mid H_1\mid\cdots\mid H_d.
\tag{79.19}
$$

The first suffix bit is $b_1(\lambda_{\rm bad}(N-1))=0$, clearing the actual inherited root tail one. At every later boundary its two adjacent bits are the two coordinates at phase $N+1-2r$ in the last line of (79.17), so at least one is zero. Individual words have length $m<k$ and are internally safe. This verifies the actual root seam and every internal seam of (79.19), equivalently Lemma 73.5, on the very same sources and words.

For a continuing source the root difference is one. Its own $d$ subsequent endpoint differences are $b(\lambda_{\rm bad}(j))$, so injection returns its unique INITIAL label. Root-zero $C$, root-bottom $R$ and free initial bottom have already stopped as specified. Both free-value fibres use the same words and difference decoder. Actual sources in $A$ execute all $d+1$ paid words, giving this exact worst fee; waits, padding, rejection and terminal stopping require no additional action. This is the supplied nonsaturated full-target upper-bound construction retained in Open Problem 75.3, with its actual parent and label preservation verified here. No equality from Theorem 74.2's power-of-two child-label hypothesis is invoked. Therefore $C_{\rm pre}(f_{\rm bad})\le d+1$. Combine the two upper bounds with the all-action lower bounds and $C_{\rm ad}\le C_{\rm pre}$ to obtain (79.4). ∎

**边界 79.3（Effective inputs, exact resources and surviving quantifiers）。** The good target's worst emitted-bit fee is $(N-1)d$ and the bad target's is $(N-1)(d+1)$, because every action is a whole width-$m$ block even on a root rejecting at its first bit. Each attaining controller has one free initial reading and one subsequent complete-endpoint reading per issued block. Initial bottom emits zero blocks; either root-reject branch emits one. The good construction keeps all low sources through $d$ blocks; the bad construction stops low $C$ after one and keeps the positive archive through $d+1$. No invisible rejected suffix, unpaid padding or final cleanup contributes to these figures.

For arbitrary unpresented label sets the minima are semantic. A finite target-partition presentation, or the named finite table with decidable label equality and its stipulated distinctness, makes the constructions effective. The good selection uses finite searches through the binary cube in the displayed order and then the explicit prefix-XOR inverses. The bad selection uses the finite lists (79.17), a finite distinct-representative search guaranteed by Lemma 73.3, and the same literal inverses. Storing these finitely many words and code decoders suffices; online control uses only its own endpoint outputs and paid issued index. Offline comparison, search, arithmetic, storage and label representation are separate resources, and no bit-complexity bound is asserted. The explicit history pullback is not an algorithm deciding factorization of an arbitrary history expression.

The equality requires exactly $d\ge3$, $k=2^d$, $m=2^d-1$, actual gcd one, the two placements (79.2), the identical entire extensions on both free-value fibres, fresh distinct $R,C$ and the homogeneous high INITIAL band in (79.3). It prices no arbitrary rearrangement of that multiplicity table, different value-fibre tables, coincident high or outside labels, tail-dependent low tables, other orders or widths, noncoprime readers, mixed acquired supports, or history targets without the specified factorization. Each GLOBAL stream is shared across all actual sources of one fixed target; the theorem does not require a simultaneously optimal stream for the two different targets. The original exact adaptive and one-GLOBAL-stream objective for every attainable immutable INITIAL target and every $k\ge2,m\ge1$ [IC, Definition 1.3 and Open Problem 9.1] remains unresolved.

**数学引文 79.4（Exact supplied overlap and the placement content）。** [IC, Chapter 1; S1, Definitions 1.2–2.1, Convention 1.3, Proposition 2.2, Lemmas 4.2–4.3 and Note 5.3] supplies the original source/INITIAL/endpoint contract, joint histories, absorbing rejection, irreversible first-zero loss and the semantic/effective distinction. [S2, Sections 13–14, Theorem 14.1] supplies the matched coefficient cycle for the original integer weights. [IC, Interface 1.4; S10, Interface 2.1 and Lemma 3.2; S15, Section 1, Definitions 1.1 and 2.1 and Proposition 4.2] supplies the literal even-path inverse, common-tail binary bound, strict inherited-tail safety and the distinction between separate adaptive child words and one GLOBAL stream. Their hypotheses are used at the actual complete endpoints above.

The bad upper bound is fully credited to Lemma 73.3, Construction 73.4, Lemma 73.5, Theorem 73.6 and the nonsaturated whole-target upper bound in Open Problem 75.3. The history and label-preservation connection uses the attainment argument in Chapter 74, while that chapter's exact equality assumes a power-of-two child-label count and is not applied to $N-1$. The first-two-bit root exclusion is the same first-zero mechanism consumed in Theorem 76.2. Its exact price classification requires three labels on $A$; here $|\lambda_\varepsilon[A]|=N-1\ge7$, so it supplies neither equality in (79.4).

[IC, Chapters 36–38] already distinguishes finite code algebra from legal fee realization. On the full low phase cycle here, both placements have $N$ labels, one double class $D$ and $N-1$ odd singleton classes. A bijection to the binary cube with $D$ at zero has zero phase XOR for either placement. This familiar algebra and the finite code selection do not themselves price the reader. The wide fee theorems require $m\ge k$, with Theorem 38.1 additionally requiring $a+k+2\le m$ for an eligible cut; neither condition holds here. The actual root restriction (79.6), the saturated adaptive extraction (79.7)–(79.8), the actual missing vertices (79.10) and the safe simultaneous realization (79.13)–(79.15) establish the placement-dependent whole fees. The difference persists even for adaptive control, so it is not obtained by declaring independent child optima compatible.

[M, Definition 1.2 and Theorem 2.1], [T3, Definition 1.2 and Theorem 2.1] and [F4, Definition 72.1 and Theorem 72.2] condition instead on a paid all-one root's zero archive, with phase support excluding $0,m$ and current tails $m+s$. Such an all-one root cannot acquire either full target (79.3). Their restricted binary, three-label and four-label continuation prices are not substituted for this theorem. The independent-row seam and guarded continuation laws [IC, Chapters 27 and 60–64; S15, Theorem 3.4] require $k\ge2m$, also false here. The ordinary supplied binary coding and algebra are credited; the added result is the whole actual reader's unbounded-depth placement pricing with both full INITIAL consumers. This is a `repo-derived` ordinary mathematical deduction on these suppliers, without a Lean/kernel-certification or mathematical-priority claim.

## 追加锚（本行以下为增补区）
## 80. Arbitrary placements and multiplicities with one even phase class

The two placements of Chapter 79 leave open both repeated odd classes and larger odd widths. This chapter prices the entire placement class below. Its new physical selection handles several unavailable-coordinate and seam restrictions on the same label; it does not require those restricted phases to have different labels. The compulsory-root obstruction continues to apply to adaptive control. The attaining construction supplies one literal stream for the entire fixed INITIAL target, rather than independent streams for its root children.

**定义 80.1（The entire one-even-class INITIAL target）。** Retain the original integer weights, matched $V_k\bmod2$ reading and full jointly attainable complete-history prior of [IC, Definitions 1.1–1.3]. Let

$$
d\ge3,\qquad N=2^d,\qquad m\ge N-1\text{ odd},\qquad
k=m+1,\qquad T=m+2,\qquad
g=\gcd(m,T)=\gcd(m,2)=1.
\tag{80.1}
$$

Put $A=\{0,\ldots,m\}$ and $z=m+1$. Let $\lambda:A\to Y$ have exactly $N-1$ labels, with image $L$. For $E\in L$ write $n_E=|\lambda^{-1}(E)|$. Require exactly one even class $D\in L$:

$$
n_D>0\text{ even},\qquad n_E\text{ odd}\quad(E\in L\setminus\{D\}).
\tag{80.2}
$$

Occurrences may have arbitrary placements, and odd multiplicities need not be one. Choose distinct fresh labels $R,C\notin L$. Extend the low phase table by $\Lambda(j)=\lambda(j)$ on $A$ and $\Lambda(z)=C$. On both free INITIAL value fibres specify the full record and history targets by

$$
\begin{aligned}
f(v,-j,s)&=
\begin{cases}
R,&s=m,\\
\Lambda(j),&0\le s<m,
\end{cases}
&&v\in\mathbb F_2,\quad j\in\mathbb Z/T\mathbb Z,\\
f(\bot)&=L_\bot,&&
F(w)=f(q_{\rm INITIAL}(w)).
\end{aligned}
\tag{80.3}
$$

Here $j=-\theta_{\rm INITIAL}$, and $q_{\rm INITIAL}(w)$ is the original endpoint record before any controller action. Initial bottom has an arbitrary independent label $L_\bot$, which may coincide with another label. Equation (80.3) explicitly gives the history pullback and labels every original tail and both values; source legality alone would not supply this factorization.

Both original alphabets contain every $m$-bit word because $m<k$. Cross-block rejection is still absorbing. Only complete endpoints are observed; every issued complete block costs one, including waits, padding, repairs and an issued block that rejects before its endpoint. The initial scalar, or initial bottom, is free. There is no reset, copy, intermediate reading, hidden INITIAL clock or observation borrowed from another branch. Write $C_{\rm ad}$ and $C_{\rm pre}$ for [IC, Definition 1.3]; $C_{\rm pre}$ requires one GLOBAL preset stream for this fixed full target, common to both free-value fibres, with stopping and decoding from each source's own archive.

**引理 80.2（Simultaneous physical codes with accumulated label restrictions）。** Suppose (80.1)–(80.2) hold and $D\notin\{\lambda(0),\lambda(1)\}$. For $1\le t\le d-1$ put

$$
e_t=m+1-2t,\qquad s_t=e_t+1=m+2-2t.
\tag{80.4}
$$

There is a bijection $c:L\cup\{C\}\to\{0,1\}^d$, with coordinates $0,\ldots,d-1$, satisfying all of

$$
\begin{aligned}
c(D)&=0,& c_0(C)&=0,&c_0(\lambda(0))&=c_0(\lambda(1))=1,\\
c_t(\lambda(e_t))&=0&&&&(1\le t\le d-1),\\
c_{t-1}(\lambda(s_t))c_t(\lambda(s_t))&=0&&&&(1\le t\le d-1).
\end{aligned}
\tag{80.5}
$$

Repeated labels collect every indicated restriction, including restrictions involving the root coordinate.

**证明。** The inequality $N\ge2d+2$ holds at $d=3$ and is preserved on increasing $d$: $2^{d+1}\ge4d+4\ge2(d+1)+2$. Consequently

$$
e_{d-1}\ge N+2-2d\ge4.
\tag{80.6}
$$

All $e_t,s_t$ are low phases in $A$, separate from $0,1,z$; the $e_t$ are distinct and so are the $s_t$. Their labels may coincide. In particular $C$ owns none of the last two lines of (80.5). Reserve the zero vector for $D$, whose remaining clauses are automatically satisfied. Let $V=\{0,1\}^d\setminus\{0\}$. For each of the other $N-1$ labels take its list in $V$ specified by (80.5). Call a label positive when it belongs to $K=\{\lambda(0),\lambda(1)\}$; there are at most two positive labels, neither $C$ nor $D$.

The clauses, counted as occurrences before labels are identified, consist of at most two positive conditions $y_0=1$, the condition $y_0=0$ on $C$, one coordinate-zero condition for each $t\ge1$, and one adjacent-pair condition for each $t\ge1$. Thus at most $2d+1$ labels have any condition. Each coordinate-zero occurrence has at most one owner, and each adjacent-pair occurrence has at most one owner. Repetition can accumulate conditions on a list but cannot increase these occurrence counts.

We verify every finite Hall inequality. A subfamily containing a list equal to $V$ has union size $N-1$, at least its number of labels. Otherwise its size $q$ is at most $2d+1$. Write $u_i$ for the unit vector in coordinate $i$. Every non-$C$ list contains $u_0$: it satisfies a positive condition when present, every coordinate-zero condition with index at least one, and every adjacent-pair condition. The $C$ list is exactly the nonzero half cube $y_0=0$, of size $N/2-1\ge3$.

For $q=0$ the inequality is empty, and for $q=1$ these observations give a representative. For $q=2$, if $C$ occurs, its vector $u_1$ and the other list's $u_0$ suffice. Otherwise consider coordinate two, which exists since $d\ge3$. For a nonpositive list use $u_2$, and for a positive list use $u_0+u_2$. Each respective vector satisfies all its conditions except possibly the single coordinate-two zero condition. That occurrence cannot belong to both labels. At least one of these vectors is in the union and differs from $u_0$, proving the inequality.

For $q=3$, inclusion of $C$ already gives three vectors. If $C$ is absent and at most one label is positive, there are at least two nonpositive lists. For each $i=1,2$, the vector $u_i$ fails on such a list only if that label owns the single coordinate-$i$ zero condition. Hence $u_1,u_2$ both belong to the union, as does $u_0$.

The remaining $q=3$ case has two positive labels and one nonpositive label $E$. Among the two positive lists at least one contains $u_0+u_2$, because this vector can fail there only at the single coordinate-two zero condition. If $E$ permits either $u_1$ or $u_2$, that vector, $u_0$ and $u_0+u_2$ are three distinct members of the union. Otherwise $E$ owns both coordinate-one and coordinate-two zero conditions. Neither positive list then owns either of those conditions. The vector $u_0+u_1$ can fail on a positive list only at the single pair condition for coordinates zero and one. At least one positive list permits it. Thus $u_0,u_0+u_1,u_0+u_2$ belong to the union, again proving the inequality.

For every $q\ge4$, all unit vectors belong to the union. The vector $u_0$ is forbidden only by $C$; any $u_i$ with $i\ge1$ is forbidden on at most two positive labels and the one owner of its coordinate-zero condition, hence on at most three labels. Also every $u_0+u_i$, $i\ge1$, belongs to the union: it can violate the $C$ condition, one coordinate-zero condition, and, only when $i=1$, one adjacent-pair condition. Again there are at most three forbidden labels. These are $2d-1$ distinct nonzero vectors, proving all inequalities with $4\le q\le2d-1$.

It remains to consider $q=2d$ or $2d+1$, so $q\ge6$. Every weight-two vector with coordinate zero equal to zero can violate at most two positive conditions, two coordinate-zero conditions and one adjacent-pair condition, on at most five labels. A weight-two vector with coordinate zero equal to one violates at most the three conditions just counted for $u_0+u_i$. Therefore every weight-one or weight-two vector belongs to the union. For $d\ge4$ their number satisfies

$$
d+\binom d2\ge2d+1\ge q;
\tag{80.7}
$$

the first inequality holds at $d=4$ and its difference increases with $d$. For $d=3$ these vectors number six, enough for $q=6$. For $q=7$ the remaining vector $111$ can violate only the $C$ condition, the two coordinate-zero conditions and the two pair conditions: at most five labels. It also belongs to the union, giving all seven nonzero vectors. This completes the Hall inequalities for every possible accumulated-clause pattern.

Apply the existing finite Hall distinct-representative theorem [H] to these $N-1$ lists. It gives an injective choice in $V$, necessarily using all of $V$. Add $c(D)=0$ to obtain the required bijection. The finite matching theorem is credited reuse; the occurrence bounds and list inequalities here arrange the root, unavailable coordinates and every seam of this reader in the presence of arbitrary repeated labels. ∎

**定理 80.3（Exact whole INITIAL fees for the entire placement/multiplicity class）。** For every target (80.3) satisfying Definition 80.1, under each original alphabet,

$$
\boxed{
C_{\rm ad}(f)=C_{\rm pre}(f)
=d+\mathbf1_{\{D\in\{\lambda(0),\lambda(1)\}\}}.
}
\tag{80.8}
$$

The same equality holds for its explicit history pullback $F$. These are total fees from the free INITIAL reading. The exact worst emitted-bit fee is $m$ times (80.8), counting all bits of each issued block, including a rejecting block. Each preset attainment is one actual GLOBAL stream for the fixed full target, on both free-value fibres.

**证明（all joint histories and the compulsory root）。** Every INITIAL record used here has the supplied single-history realization [IC, (1.3); S1, Convention 1.3; S15, Section 1]. To make its application explicit, let $\gamma_i=\mathbf1_{\{0,m+1\}}(i\bmod T)$, the original matched coefficient cycle [S2, Sections 13–14, Theorem 14.1]. For any $v,j,s$ in (80.3) choose

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad
\ell\ge s+2,\qquad
\eta=\bigoplus_{i=\ell-s}^{\ell-1}\gamma_i,\qquad
w(v,j,s)=(v\oplus\eta)0^{\ell-s-1}1^s.
\tag{80.9}
$$

The actual gcd one in (80.1) makes these congruences compatible and supplies arbitrarily large lengths. The separating zero and $s<k$ make this one history legal. Its first bit and terminal run give value $v$, while its complete-block length, phase and tail are simultaneously $\ell,-j,s$. Every constituent block belongs to both alphabets. The history $1^{2m}$ separately realizes initial bottom under either alphabet: each block is internally legal, and rejection occurs across the seam. Neither the choice of witness nor its unobserved length is an input to the controller. The original deterministic record interface and the specified factorization in (80.3) identify acquisition of $F$ with that of $f$ [S1, Proposition 2.2].

Fix either free INITIAL value. At every phase the two actual tails $m-1$ and $m$ have different labels, the latter fresh $R$ and the former in $L\cup\{C\}$. Free stopping is impossible. A root beginning zero merges this pair at that zero, with identical scalar and phase, so its completed endpoint and every future archive agree on their unequal INITIAL labels. A root with at least two leading ones, including an all-one root, rejects both before the first observed endpoint. Their unobserved rejection positions cannot distinguish them, and every later output is absorbing bottom. These supplied irreversible losses [S1, Lemmas 4.2–4.3; S15, Proposition 4.2] exclude both kinds of root at any horizon. Every correct controller must use a root $B_0$ beginning $10$.

Such a root rejects precisely the high tail $s=m$. Every low tail $s<m$ survives its first one because $s+1\le m<k$, reaches its second-bit zero, and finishes safely: later runs lie inside a word of length $m<k$. At each phase this first zero merges low tails with their common INITIAL label preserved. The high band is homogeneous $R$ and is absorbed through the rest of the issued root; its one complete block is paid. All successful low sources have the same terminal tail of $B_0$. If $r(j)$ is the successful root difference, the supplied path equations [IC, Interface 1.4] force

$$
r(z)=0,\qquad r(0)=r(1)=1,\qquad
\bigoplus_{j\in A}r(j)=0.
\tag{80.10}
$$

**证明（every literal adaptive action and the placement obstruction）。** Within a successful root archive, value and tail are common. The supplied common-tail argument [S10, Lemma 3.2] applies to every later literal word: it either succeeds on all candidates or rejects all, independently of phase. Uniform rejection cannot resolve a nonconstant INITIAL label at its completed endpoint or after further absorbed actions. A successful word gives at most two scalar endpoints, and each child again has common current value and tail. Thus an archive with worst additional fee $h$ can return at most $2^h$ different low labels, including homogeneous early endpoint stops. This induction includes all-one words, waits, padding, repairs and attempted rejection. Every issued action consumes one chronological paid slot.

There are exactly $N$ low labels $L\cup\{C\}$ on the chosen value fibre, all actual by (80.9). For a controller of whole worst fee $h\ge1$, let $L_b$ be the low label image of root-difference child $b$. Each satisfies $|L_b|\le2^{h-1}$, and their union contains all $N$ low labels. Consequently $N\le2^h$, proving $C_{\rm ad}\ge d$.

If a controller finishes within $d$ blocks, saturation forces

$$
|L_0|=|L_1|=N/2,\qquad L_0\cap L_1=\varnothing.
\tag{80.11}
$$

Every occurrence of any one low label therefore has the same root difference, denoted $r(E)$. Otherwise that label would occur in both images. The outside label $C$ is in child zero because $r(z)=0$. The positive child has exactly $N/2$ classes, all in $L$. Using their actual phase multiplicities and (80.2), root parity becomes

$$
0=\bigoplus_{j\in A}r(j)
=\left(\frac N2\bmod2\right)\oplus r(D)
=r(D).
\tag{80.12}
$$

Indeed every selected positive class would contribute one if it were odd, whereas the unique even class contributes zero instead; $N/2$ is even. No count of INITIAL tails is substituted for this phase count. If $D=\lambda(0)$ or $D=\lambda(1)$, (80.12) contradicts (80.10). Hence every adaptive controller in that case has fee at least $d+1$. This argument used an arbitrary fixed free-value fibre, so a different adaptive root on the other fibre cannot reduce either lower bound. GLOBAL controllers inherit these bounds.

**证明（one actual $d$-block GLOBAL stream when the even class avoids phases zero and one）。** Choose the bijection of Lemma 80.2. Each coordinate of the full $d$-cube has $N/2$ ones, an even number. On the actual phase cycle, (80.2) and the singleton outside class give

$$
\bigoplus_{j=0}^{m+1}c(\Lambda(j))
=\bigoplus_{E\in(L\cup\{C\})\setminus\{D\}}c(E)
=\left(\bigoplus_{y\in\{0,1\}^d}y\right)\oplus c(D)=0.
\tag{80.13}
$$

This elementary cube identity is credited coding algebra. Its physical realization uses the additional restrictions proved in Lemma 80.2.

At actual issued index $t=0,\ldots,d-1$, put $u_t=tm\pmod T$ and $W_t=[u_t,u_t+m]\pmod T$, in its actual order. Since $m\equiv-2\pmod T$, this window misses exactly $e_0=z$ for $t=0$, and $e_t$ in (80.4) for $t\ge1$. For $t\ge1$ its first vertex is $s_t$, and its last is $e_t-1$. The last vertex of $W_{t-1}$ is $s_t$. Inequality (80.6) ensures all the displayed positive representatives are within the stated cycle; no extra rotation, wait or phase reading is performed.

Set the full phase row $\chi_t(j)=c_t(\Lambda(j))$. Equations (80.5) give $\chi_t(e_t)=0$ at the unavailable vertex, including $\chi_0(z)=0$. Equation (80.13) then gives even parity on $W_t$. The unique supplied literal inverse [IC, (1.5); S15, Section 1] is the complete word

$$
B_{t,i}=\bigoplus_{a=0}^{i}\chi_t(u_t+a\bmod T),
\qquad 0\le i<m.
\tag{80.14}
$$

Issue the single fixed stream $B_0\mid\cdots\mid B_{d-1}$. Its successful physical charge is exactly $\chi_t$ at every phase, including zero outside $W_t$. These rows refer to the one specified stream, simultaneously on both live root children and both free values.

The first two root bits are $c_0(\lambda(0))=1$ and $c_0(\lambda(0))\oplus c_0(\lambda(1))=0$. Thus the root has exactly the high rejection and low preservation proved above. For every subsequent boundary, even-path inversion and the common boundary vertex give

$$
B_{t-1,m-1}=c_{t-1}(\Lambda(s_t)),\qquad
B_{t,0}=c_t(\Lambda(s_t)),\qquad
B_{t-1,m-1}B_{t,0}=0
\quad(1\le t\le d-1).
\tag{80.15}
$$

There is a zero among the two literal bits adjacent to each boundary, including the first one. No run of ones crosses a boundary, and no single word of length $m<k$ contains $1^k$ internally. Hence all continuing low sources survive these very words, regardless of their INITIAL tail. This proves strict seam safety for the entire emitted trace, even if some subsequent word is all ones. No clearing or repair block is implicit.

Initial bottom stops freely with $L_\bot$. Root-bottom sources return $R$ at the completed first endpoint, after every bit of that issued block. Every low source can continue through all $d$ blocks. From its own free initial value and completed scalar endpoints $v_0,\ldots,v_d$, it obtains

$$
(v_1\oplus v_0,\ldots,v_d\oplus v_{d-1})=c(\Lambda(j)).
\tag{80.16}
$$

The inverse of the bijection returns its immutable INITIAL label. Identical words and the same difference decoder work on both free-value fibres; no branch supplies another branch's observation. All low records are actual and execute $d$ words under this stopping rule, so the worst fee is exactly $d$. An endpoint stop needs no final cleanup even when the final tail is nonzero. This gives $C_{\rm pre}\le d$ in the first case of (80.8).

**证明（the actual $(d+1)$-block stream in the obstructed case）。** The upper bound is credited to the full-positive-window supplier, with its arrival checked on this entire target. Issue the actual root

$$
P_m=(10)^{(m-1)/2}1.
\tag{80.17}
$$

It begins $10$, has terminal tail one and rejects exactly INITIAL $s=m$. Its charge is one on all $A=W_0$ and zero at $z$. The successful zero-difference archive is precisely the low phase $z$, has label $C$ and stops at fee one. The positive archive has the actual full support $A$, common scalar $v\oplus1$, common tail one and one retained label $\lambda(j)$ at each phase. All these sources share their own root archive and are actual by (80.9). Every original low-tail merger preserves (80.3); the rejected band is homogeneous $R$. Thus Definition 73.1 holds with $a=u=0$ and $n=N-1\ge7$.

Since $\lceil\log_2(N-1)\rceil=d$, Lemma 73.3 and Construction 73.4 supply an injective code $b:L\to\{0,1\}^d$ obeying (73.5), with coordinates now $1,\ldots,d$. For clarity, the selected suffix is the following one actual sequence. At absolute issued index $r=1,\ldots,d$ put $\widetilde e_r=m+1-2r$, $\widetilde s_r=m+2-2r$, and prescribe

$$
\begin{aligned}
\psi_r(j)&=b_r(\lambda(j))&&j\in A\setminus\{\widetilde e_r\},\\
\psi_r(\widetilde e_r)&=0,&&
\psi_r(z)=\bigoplus_{j\in A\setminus\{\widetilde e_r\}}b_r(\lambda(j)),\\
S_{r,i}&=\bigoplus_{a=0}^{i}\psi_r(\widetilde s_r+a\bmod T)&&0\le i<m.
\end{aligned}
\tag{80.18}
$$

The supplied code restrictions include $b_r(\lambda(\widetilde e_r))=0$, $b_1(\lambda(m))=0$, and $b_{r-1}(\lambda(\widetilde s_r))b_r(\lambda(\widetilde s_r))=0$ for $r\ge2$. The missed coordinate therefore has its desired charge, compensation at $z$ makes the full path even, and (80.18) is the literal inverse of that same row. Compensation is a prescription for bits, never a donor source or an additional observation. The first suffix word starts zero and clears the actual inherited tail one. Every internal suffix boundary has a zero among its adjacent bits by the pair restrictions. Lemma 73.5 proves safety of this very suffix; here $d\ge3$, so its four-label alternative is not needed. All words are internally shorter than $k$.

The single GLOBAL stream is $P_m\mid S_1\mid\cdots\mid S_d$. Its high-root rejection returns $R$ at its completed paid endpoint, its root-zero sources return $C$ there, and initial bottom stops freely. Only root-positive sources continue. Each such source decodes $b(\lambda(j))$ from its own $d$ suffix endpoint differences and returns its unique INITIAL label. Both values use this same stream. Every phase in $A$ has actual continuing low sources that pay exactly $d+1$ complete blocks. No wait, padding, repair, rejection fragment or terminal action is omitted from the fee. There is no other live sibling requiring a different suffix. Therefore $C_{\rm pre}\le d+1$ for the obstructed case. Together with the all-action lower bounds and $C_{\rm ad}\le C_{\rm pre}$, this proves (80.8) and its emitted-bit version. ∎

**实例 80.4（A larger-width repeated-class witness）。** Let $d=3$, $m=11$, $k=12$, $T=13$. Take distinct low labels $D,E_0,\ldots,E_5$ and use the ordered table

$$
\lambda=(E_0,E_1,D,E_2,D,E_3,D,E_4,D,E_0,E_0,E_5).
\tag{80.19}
$$

The even class has four phases, $E_0$ has three, and the other five classes have one each. A code satisfying Lemma 80.2 is

$$
\begin{array}{c|cccccccc}
\text{label}&D&C&E_0&E_1&E_2&E_3&E_4&E_5\\
c(\text{label})&000&010&100&101&110&111&011&001
\end{array}
\tag{80.20}
$$

The first displayed digit is coordinate zero. In (80.4), $\lambda(e_1)=E_0$, $\lambda(e_2)=D$, $\lambda(s_1)=E_5$, and $\lambda(s_2)=E_0$. Thus the positive root condition, an unavailable coordinate and a seam restriction accumulate on $E_0$, all satisfied by its one code. Formula (80.14) gives the literal stream

$$
10011000010\ \mid\ 01111001100\ \mid\ 00111000011.
\tag{80.21}
$$

Its root begins $10$ and ends zero; both following words begin zero. Every low source returns the code in (80.20) from its own three differences. High tail eleven rejects in the first bit and remains absorbed until the paid root endpoint, where it returns $R$; initial bottom stops freely. The whole INITIAL block fee is three and the emitted-bit fee is $33$.

Transposing phases zero and two of (80.19) preserves every class multiplicity but puts $D$ at phase zero. For its entire extension (80.3), Theorem 80.3 gives block fee four and emitted-bit fee $44$, attained by (80.17)–(80.18). This is a falsifiable placement obstruction at a width larger than the minimal dyadic width, with nonsingleton odd and even classes. It illustrates the uniform law rather than furnishing an additional finite-table optimality claim.

**数学引文 80.5（Source correspondence and the uncovered physical delta）。** [IC, Chapter 1; S1, Definitions 1.2–2.1, Convention 1.3, Proposition 2.2 and Lemmas 4.2–4.3] supplies the original record, single jointly actual history, INITIAL factorization, endpoint-only archive and irreversible first-zero/rejection losses. The objects in (80.9) use its original $v,-j,s$ together in one history; (80.3) supplies the required target pullback. [S2, Sections 13–14, Theorem 14.1] supplies the matched coefficient cycle for the original integer weights, not a surrogate phase model. Actual $g=1$, complete chronological index $t$ and $m<k$ are checked in (80.1), (80.9) and (80.14).

[IC, Interface 1.4; S10, Interface 2.1 and Lemma 3.2; S15, Section 1, Definition 1.1 and Proposition 4.2] supplies the even-path inverse, strict seam contract, common-tail binary bound and INITIAL-parent preservation. Its actions here are the complete words (80.14) or (80.17)–(80.18), not unrestricted binary questions. Its destructive root outcomes are observed only after the entire paid root. The lower bound uses the common-tail restriction on every later literal action, rather than just actions selected by the construction.

[H] supplies finite Hall distinct representatives. Its finite index set here is $(L\cup\{C\})\setminus\{D\}$, its candidate set is the nonzero $d$-cube, and its lists are the simultaneous physical clauses (80.5). Lemma 80.2 checks every union inequality, including repeated owners, before applying that theorem. Chapter 73 uses different lists, containing zero and selecting only the positive child's codes; its Lemmas 73.3 and 73.5 and Theorem 73.6 are credited in the $(d+1)$-block upper bound. The attained root-positive child has exactly their actual support and tail. Chapter 74's exact equality requires a power-of-two child-label count and is not applied to $N-1$; only its full-source connection and the nonsaturated upper bound retained in Open Problem 75.3 are reused.

Chapter 79 proves two placements at $m=N-1$ with singleton odd classes and one double class. Its root saturation and placement obstruction are credited mechanisms in (80.10)–(80.12). Its code selection assumes distinct constrained labels, so does not supply Lemma 80.2 when restrictions accumulate on repeated classes. The new result is the uniform physical matching and simultaneous stream (80.5), (80.14)–(80.16), joined to the exact whole-source price for every placement and every multiplicity in (80.2), at all odd widths (80.1). It is not merely the supplied $(d+1)$-block upper bound.

[IC, Definitions 36.1–36.2 and Theorems 37.1 and 38.1] supplies the distinction between multiplicity-based code algebra and legal fee realization. Its wide-reader assumption $m\ge k$, and the additional room condition of Theorem 38.1, fail here. Even though the elementary zero-sum cube assignment exists for the present multiplicities, it alone says nothing about the root prefix, actual unavailable vertices or seams. Those are proved above. The child-price laws [M], [T3], [F4] instead condition on a paid all-one root's zero archive; that root is excluded for (80.3). Independent-row laws [IC, Chapters 27 and 60–64; S15, Theorem 3.4] require $k\ge2m$, also false here. No fee bridge from those different domains is presumed.

This is `repo-derived` ordinary mathematics on the cited source interfaces and finite Hall theorem. The scoped source comparison concerns those hypotheses and constructions, not an exhaustive absence or literature-priority result. No Lean, kernel verification, ingestion, coverage or freezing is claimed.

**注记 80.6（Effectivity, resources and the surviving original goal）。** For an arbitrary semantic target, (80.8) is an existence and minimum statement. A finite target-partition presentation or decidable label equality makes the constructions effective: count actual phase classes, identify $D$, build the finite lists, choose representatives by finite search, invert the prescribed rows and retain their finite decoders. The obstructed case uses the already supplied finite selection of Chapter 73. No polynomial runtime, offline bit-complexity, acquisition-history cost or controller-memory optimum is asserted. Known issued-block indices determine the windows; they never reveal the unknown INITIAL source length. The semantic/effective distinction is the supplied [S1, Note 5.3] boundary.

The proved class still requires $d\ge3$, $k=m+1$, odd $m\ge2^d-1$, actual gcd one, exactly $2^d-1$ low phase labels with precisely one even class, the identical low table on both free-value fibres, fresh distinct $R,C$, and the homogeneous high-tail band in (80.3). Different targets may use different GLOBAL streams. The theorem does not price other parity profiles or label counts, even widths, other orders or gcds, nonfresh high/outside labels, different value-fibre tables, tail-dependent low labels, mixed acquired supports, competing eligible roots in other target classes or history targets without a supplied INITIAL factorization. Unbounded $d$ ranges over different finite readers and targets; it gives no single protocol for their union.

The original exact minimum worst-branch ACTUAL emitted-complete-block objective for every attainable immutable INITIAL target and every $k\ge2,m\ge1$, separately for adaptive control and ONE GLOBAL preset stream per fixed target under both original alphabets [IC, Definition 1.3 and Open Problem 9.1], remains unresolved. Equation (80.8) settles this entire restricted placement/multiplicity class and preserves those remaining quantifiers.

## 追加锚（本行以下为增补区）

## 81. Three even joined classes and an unbounded two-value GLOBAL surcharge

Different INITIAL-value tables can each admit a short fully paid protocol while requiring a longer common stream. The value join of [IC, Chapter 29] specifies which labels that stream must simultaneously separate. The new restriction below combines saturated response capacity, the compulsory literal root and the actual vertices unavailable at subsequent chronological indices. It gives an exact whole-target GLOBAL price and an explicit unbounded family whose adaptive price is half that GLOBAL price.

**定义 81.1（The full two-value target and its three even joined classes）。** Retain the original integer KBonacci weights, matched $V_k\bmod2$ reader, actual complete-history prior and record updates of [IC, Definitions 1.1–1.3 and Interface 1.4]. Fix

$$
h\ge3,\qquad m\ge2^h-1\text{ odd},\qquad
k=m+1,\qquad T=m+2,\qquad
g=\gcd(m,T)=\gcd(m,2)=1.
\tag{81.1}
$$

Thus all phases modulo $T$ are actual. Put $A=\{0,\ldots,m\}$ and $z=m+1$. Let $\lambda_0,\lambda_1:A\to Y$ be two finite phase tables, and let their ordered join be

$$
\Gamma(j)=(\lambda_0(j),\lambda_1(j)),\qquad j\in A.
\tag{81.2}
$$

Require exactly $2^h-1$ nonempty joined classes. Precisely three distinct classes $U,V,W$ have positive even phase multiplicities, and every other joined class has odd phase multiplicity. Require the placements

$$
\Gamma(0)=U,\qquad \Gamma(1)=V,\qquad
\Gamma(m+1-2t)=W\quad(1\le t<h).
\tag{81.3}
$$

Choose common labels $R,C$ that are distinct and fresh relative to $\lambda_0[A]\cup\lambda_1[A]$. Specify the entire immutable INITIAL record target and its history pullback by

$$
\begin{aligned}
f(v,-j,s)&=
\begin{cases}
R,&s=m,\\
\lambda_v(j),&0\le s<m,\quad j\in A,\\
C,&0\le s<m,\quad j=z,
\end{cases}
&&v\in\mathbb F_2,\quad j\in\mathbb Z/T\mathbb Z,\\
f(\bot)&=L_\bot,&&F(w)=f(q_{\rm INITIAL}(w)).
\end{aligned}
\tag{81.4}
$$

Here $q_{\rm INITIAL}(w)$ is the original endpoint record before any controller action. The independent $L_\bot$ is arbitrary and may coincide with another label. Equation (81.4) labels every original tail $0\le s<k$, both free INITIAL values and all rejected source histories. It explicitly supplies INITIAL factorization; the target is never reevaluated on an updated record.

Only complete endpoints are read. The free initial reading gives the INITIAL scalar value or initial bottom. Every issued complete block costs one, including waits, padding, repairs and a block rejecting before its completed endpoint. Both original alphabets contain every $m$-bit word because $m<k$, with cross-block rejection still absorbing. The prices $C_{\rm ad}$ and $C_{\rm pre}$ are [IC, Definition 1.3]; the latter means ONE GLOBAL preset literal stream for this one fixed target, on all original sources and both values, with source-dependent endpoint stopping. No reset, copy, intermediate observation, hidden INITIAL clock or observation from another archive is available.

**定理 81.2（Exact whole GLOBAL price from the three-even-class placement obstruction）。** For every target of Definition 81.1, under either original alphabet,

$$
\boxed{C_{\rm pre}(f)=C_{\rm pre}(F)=h+1.}
\tag{81.5}
$$

Its exact worst emitted-bit fee is $m(h+1)$. The attainment below is one actual common stream. The theorem does not assert an adaptive-price formula for every pair of tables satisfying Definition 81.1.

**证明（actual sources, necessary roots and the joined control obligation）。** Every original record in (81.4) has the credited joint-history realization [IC, (1.3); S1, Convention 1.3; S15, Section 1]. Explicitly, with $\gamma_i=\mathbf1_{\{0,m+1\}}(i\bmod T)$, choose

$$
\begin{aligned}
\ell&\equiv0\pmod m,&
\ell&\equiv-j\pmod T,&
\ell&\ge s+2,\\
\eta&=\bigoplus_{i=\ell-s}^{\ell-1}\gamma_i,&
w(v,j,s)&=(v\oplus\eta)0^{\ell-s-1}1^s.
\end{aligned}
\tag{81.6}
$$

The actual gcd one supplies arbitrarily large compatible lengths. This single legal history simultaneously has INITIAL scalar $v$, phase $-j$, tail $s$ and complete-block length $\ell$. Its separating zero prevents a forbidden run, and its first bit compensates the terminal run's scalar contribution. Every constituent block belongs to both alphabets. The actual history $1^{2m}$ separately realizes initial bottom: both individual blocks are internally legal, and the second crosses the rejection threshold. These histories establish the joint prior; their unobserved lengths are not controller inputs. The explicit pullback in (81.4) identifies acquisition of $F$ with acquisition of $f$ [S1, Proposition 2.2].

Fix either free INITIAL value and any phase. The actual original tails $m-1$ and $m$ have unequal INITIAL labels, a low label versus fresh $R$. Free stopping is impossible. A root beginning zero merges this pair at that first zero, with identical current value and phase. Their completed endpoint archives and every later archive then coincide. A root with at least two leading ones, including the all-one root, rejects both before its completed endpoint. Their unobserved rejection positions do not distinguish them, and bottom is absorbing. The supplied first-zero and rejection losses [S1, Lemmas 4.2–4.3; S15, Proposition 4.2] exclude these roots at every horizon. Hence every correct root, adaptive or preset, starts with the literal prefix $10$.

Every such root rejects exactly INITIAL $s=m$. Every low $s<m$ survives its first one, since $s+1\le m<k$, reaches the second-bit zero and finishes safely. At a fixed INITIAL phase, that zero merges only low tails with the same component label in (81.4). All successful low sources have a common current tail, the root's terminal tail. Its successful phase-charge row $\chi_0$ necessarily obeys the original inverse interface:

$$
\chi_0(z)=0,\qquad \chi_0(0)=\chi_0(1)=1,
\qquad \bigoplus_{j\in A}\chi_0(j)=0.
\tag{81.7}
$$

For a fixed literal stream, successful endpoint differences and rejection times depend on INITIAL phase and tail, not on INITIAL scalar value. At any shared difference prefix, correctness on both actual value fibres therefore requires separation of the ordered labels (81.2). This is the credited exact preset value-join law [IC, Definition 29.1 and Theorem 29.2]. Apply it to the entire target (81.4), whose joined high label is $\widehat R=(R,R)$, joined outside label is $\widehat C=(C,C)$ and joined low table is $\Gamma$. It preserves the original worst paid depth and the same physical stream, including endpoint stops and absorbing rejection. It changes only decoding: successful scalar complementation is computed from the one acquired archive and the remembered initial value. No additional source, counterfactual action, branch output or physical experiment is used.

For the lower bound it thus suffices to price this scalar-independent joined target on either actual fixed-value fibre. It has exactly $2^h$ low labels, the $2^h-1$ classes in $A$ and the fresh $\widehat C$ at $z$. All are actual by (81.6).

**证明（all-action saturation and the impossible $h$-block common stream）。** After the necessary root, every low archive has common current value and tail. For every later literal action, not just the words constructed below, [S10, Lemma 3.2] gives either common success or common rejection on such an archive. Common rejection cannot resolve two unequal INITIAL labels, at that endpoint or after any absorbed suffix. A successful action gives at most two endpoint outcomes, each again with common value and tail. An archive with at most $a$ further paid blocks consequently has at most $2^a$ distinct-label leaves. This induction allows all literal words, all-one words, waits, padding, attempted repairs, rejection and homogeneous endpoint stops.

The root has at most two successful low children. Thus a whole controller of worst fee $H\ge1$ has at most $2^H$ low-label leaves, and $2^h$ actual low labels force $H\ge h$. Suppose a GLOBAL controller finishes in $h$ blocks. Equality in this count forces its low-source decision tree to be the complete binary tree of depth $h$: its root children have disjoint label images of size $2^{h-1}$, and recursively every depth-$t$ child has $2^{h-t}$ labels with disjoint images in its two children. Any overlap, earlier homogeneous stop or missing useful child would give fewer than $2^h$ distinct labels.

In particular every low source remains live before depth $h$, every issued word succeeds on all low sources, and each low label has exactly one full difference code. The common stream therefore induces a bijection

$$
c:\Gamma[A]\cup\{\widehat C\}\longrightarrow\mathbb F_2^h,
\tag{81.8}
$$

with coordinates indexed $t=0,\ldots,h-1$. This assertion also follows by counting columns: different low labels require different codes, $2^h$ labels already occupy all $2^h$ vectors, and so no label can use a second vector. Saturation is what permits one code per label here; that property is not assumed for arbitrary repeated-label protocols.

At issued index $t$ the original ordered path is $W_t=[tm,(t+1)m]\pmod T$. Since $m\equiv-2\pmod T$, its sole missed phase is

$$
e_0=z,\qquad e_t=m+1-2t\quad(1\le t<h).
\tag{81.9}
$$

All displayed representatives are distinct low phases for $t\ge1$: $2^h\ge2h+2$ for $h\ge3$ implies $e_{h-1}\ge4$. The successful physical row $\chi_t$ is zero at $e_t$ and has even total path charge [IC, (1.4)]. Consequently the full phase-code XOR vanishes:

$$
\bigoplus_{j\in A\cup\{z\}}c(\widehat\Lambda(j))=0,
\qquad
\widehat\Lambda(j)=
\begin{cases}
\Gamma(j),&j\in A,\\
\widehat C,&j=z.
\end{cases}
\tag{81.10}
$$

Each coordinate of the full $h$-cube has $2^{h-1}$ ones, an even number. Thus the XOR of all distinct codes in (81.8) is zero. On the actual phase cycle, the three even classes contribute zero and every other class, including the singleton $\widehat C$, contributes its code once. Comparing with the full-cube XOR gives

$$
c(U)\oplus c(V)\oplus c(W)=0.
\tag{81.11}
$$

The root condition (81.7) and placements (81.3) give $c_0(U)=c_0(V)=1$. Equation (81.11) then gives $c_0(W)=0$. At each subsequent chronological index $1\le t<h$, the missed phase $e_t$ has class $W$, so (81.9) forces $c_t(W)=0$. Hence $c(W)=0$, and (81.11) becomes $c(U)=c(V)$, contradicting the bijection and $U\ne V$. No $h$-block GLOBAL controller exists. Together with the capacity bound this proves $C_{\rm pre}(f)\ge h+1$.

This argument rules out every competing preset stream and its stopping rule. No stopped source was extended artificially: in the sole saturated case being excluded, all actual low sources must continue through all $h$ paid slots. A paid wait would still occupy one of those same indices and obey the same missed-phase and even-row equations.

**证明（one actual fully paid GLOBAL attainment）。** The upper bound is credited to Chapter 73, with its full-target connection made explicit. Issue the root

$$
P_m=(10)^{(m-1)/2}1.
\tag{81.12}
$$

It has leading run one, an internal zero and terminal tail one. Exactly the original high tails $s=m$ reject; they stay absorbed for the rest of this issued complete root and return $R$ at its paid endpoint. Every low tail survives and its first-zero merger preserves its component INITIAL label. The root charge is one on all $A=W_0$ and zero at $z$. Thus low phase $z$ stops with common label $C$ at fee one, while the actual root-positive child has precisely $A$, common current scalar $v\oplus1$, common tail one and the joined table $\Gamma$. This is the actual full-positive-window archive of Definition 73.1, with $a=u=0$, and with $2^h-1\ge7$ labels.

Lemma 73.3 supplies an injective code $b:\Gamma[A]\to\mathbb F_2^h$, now with coordinates $r=1,\ldots,h$, satisfying its simultaneous restrictions

$$
\begin{aligned}
b_r(\Gamma(\widetilde e_r))&=0&&1\le r\le h,\\
b_1(\Gamma(m))&=0,\\
b_{r-1}(\Gamma(\widetilde s_r))\,b_r(\Gamma(\widetilde s_r))&=0
&&2\le r\le h,\\
\widetilde e_r&=m+1-2r,&
\widetilde s_r&=m+2-2r.
\end{aligned}
\tag{81.13}
$$

Repeated classes collect all their restrictions, as that lemma permits. Here $h\le(m+1)/2$, so all these indices lie in their stated ranges; its four-label alternative is unnecessary. For each actual issued index $r=1,\ldots,h$, prescribe

$$
\begin{aligned}
\psi_r(j)&=b_r(\Gamma(j))&&j\in A\setminus\{\widetilde e_r\},\\
\psi_r(\widetilde e_r)&=0,&&
\psi_r(z)=\bigoplus_{j\in A\setminus\{\widetilde e_r\}}
                       b_r(\Gamma(j)),\\
S_{r,i}&=\bigoplus_{a=0}^{i}
          \psi_r(rm+a\bmod T)&&0\le i<m.
\end{aligned}
\tag{81.14}
$$

The path $W_r$ misses only $\widetilde e_r$ and contains $z$. The prescribed charge at $z$ makes that one full path even. It fixes bits of the same literal word and supplies no observation. This phase has already stopped in the actual full target and is absent from the continuing positive archive. The unavailable coordinate has the intended zero by (81.13). The inverse (81.14) is exactly Construction 73.4, a complete width-$m$ word realizing the required difference on every continuing source.

Issue the single GLOBAL stream

$$
P_m\mid S_1\mid\cdots\mid S_h.
\tag{81.15}
$$

Its first suffix bit is $b_1(\Gamma(m))=0$, clearing the actual inherited root tail one. At each later suffix boundary, the preceding last vertex is the next first vertex $\widetilde s_r$, and the adjacent literal bits are

$$
S_{r-1,m-1}=b_{r-1}(\Gamma(\widetilde s_r)),\qquad
S_{r,0}=b_r(\Gamma(\widetilde s_r)).
\tag{81.16}
$$

Their product is zero by (81.13). Hence no one-run crosses any suffix boundary. Every word has length $m<k$ and is internally legal. This proves the strict seam conditions on the very same stream: the first suffix begins zero after tail one; every later seam has a zero among its adjacent bits. No wait, padding, clearing or repair word is implicit. This is the credited Lemma 73.5 attainment, valid on all the continuing original low tails.

The stopping rule is completely specified. Initial bottom returns $L_\bot$ freely. Root bottom returns $R$ after the whole root. Successful root difference zero returns $C$ there. Every root-positive source executes all $h$ suffix blocks. From its own successive scalar endpoints it obtains the vector $b(\Gamma(j))$. Injection identifies the unique ordered pair $(\lambda_0(j),\lambda_1(j))$; the remembered free INITIAL value $v$ selects its $v$-component. The same literal words serve both values. No current-phase read, another branch's endpoint or reevaluation of the INITIAL target is used.

Actual sources in $A$ exist by (81.6) and pay all $h+1$ complete blocks. Root-reject and root-zero sources pay one, initial bottom pays zero, and an endpoint stop needs no final cleanup. Every issued rejecting root still emits all $m$ bits. Thus the worst fee of this one stream is exactly $h+1$ blocks and $m(h+1)$ bits. The lower bound completes (81.5). ∎

**构造 81.3（An explicit inhabited family at every $d\ge3$）。** Choose any integer $d\ge3$ and put

$$
r=2^{d-1}\ge4,\qquad n=2r-1=2^d-1,\qquad
h=2d-1,\qquad N=2^h=2r^2,\qquad
m=N+2d-3,\quad k=m+1,\quad T=m+2.
\tag{81.17}
$$

Let $I=\{0,\ldots,2r-2\}$ and write $*=2r-2$. Use distinct row labels $a_i$ and column labels $b_i$, $i\in I$, with the two label sets disjoint. Choose fresh common $R,C$ outside both sets and independent $L_\bot$.

The following explicitly deleted rectangles define a bipartite edge set on $I\times I$:

$$
\begin{aligned}
I_0&=\{0,\ldots,r-3\},&
I_1&=\{r-2,\ldots,2r-3\},\\
J_0&=\{0,\ldots,r-1\},&
J_1&=\{r,\ldots,2r-3\},\\
\mathcal D&=(I_0\times J_0)\ \cup\ (I_1\times J_1)\
                \cup\bigl(\{0,1\}\times\{r,r+1\}\bigr),\\
\mathcal H&=(I\times I)\setminus
                 \bigl(\mathcal D\cup\{(*,*)\}\bigr).
\end{aligned}
\tag{81.18}
$$

The three rectangles in $\mathcal D$ are disjoint. Indeed the first two have disjoint row sets, and the third uses rows in $I_0$ but columns in $J_1$. All its displayed indices exist for $r\ge4$. Define three excluded pairs

$$
u=(0,r),\qquad v=(1,r+1),\qquad w=(0,r+1).
\tag{81.19}
$$

They are distinct members of the third deleted rectangle, hence absent from $\mathcal H$, and none uses row or column $*$. Set $A=\{0,\ldots,m\}$ and

$$
M=\{m+1-2t:1\le t<h\}.
\tag{81.20}
$$

Define a pair table $G:A\to I\times I$ by

$$
G(0)=G(2)=u,\qquad G(1)=G(3)=v,\qquad
G(j)=w\quad(j\in M).
\tag{81.21}
$$

On the remaining phases assign the pairs of $\mathcal H$ in lexicographic order to the remaining phases in increasing order. The cardinalities agree, as proved below, so this is a fully specified bijection, not an optimization prescription. If $G(j)=(i,\ell)$, put

$$
\lambda_0(j)=a_i,\qquad \lambda_1(j)=b_\ell.
\tag{81.22}
$$

Extend these tables to the full INITIAL target and history target exactly by (81.4).

**证明（counts, positivity, marginal parities and placements）。** The first two rectangles in $\mathcal D$ each have $r(r-2)$ edges, and its third has four. The exceptional pair $(*,*)$ lies in none of them. Therefore

$$
|\mathcal H|=(2r-1)^2-2r(r-2)-4-1
           =2r^2-4=N-4.
\tag{81.23}
$$

Every row and column of $\mathcal D$ has even degree. A row in $I_0$ has degree $r$, with two extra edges for rows $0,1$; a row in $I_1$ has degree $r-2$; row $*$ has zero. A column in $J_0$ has degree $r-2$; a column in $J_1$ has degree $r$, with two extra edges for columns $r,r+1$; column $*$ has zero. All these numbers are even.

The complete bipartite graph has odd degree $n=2r-1$ at every vertex. Deleting $\mathcal D$ preserves that odd parity everywhere. Deleting $(*,*)$ then changes parity only in row $*$ and column $*$, giving each of them the positive even degree $n-1=2r-2$. Every other degree of $\mathcal H$ is positive and odd: the largest deleted degree is $r+2$, so its remaining degree is at least $n-(r+2)=r-3\ge1$. Hence all $n$ row labels and all $n$ column labels will occur.

The $h-1=2d-2$ phases of $M$ are distinct and disjoint from $\{0,1,2,3\}$. Its least member is

$$
m+1-2(h-1)=N-2d+2\ge4;
\tag{81.24}
$$

the inequality follows from $2^{2d-1}\ge2d+2$ for $d\ge3$, by induction, and its greatest member is $m-1$. The unassigned phase count in (81.21) is consequently

$$
|A|-4-|M|=(N+2d-2)-4-(2d-2)=N-4=|\mathcal H|.
\tag{81.25}
$$

Thus the stated ordered bijection exists without changing any assignment. The joined classes consist precisely of the $N-4$ distinct pairs from $\mathcal H$, each with multiplicity one, and the three distinct pairs $u,v,w$ with respective multiplicities $2,2,2d-2$. All three latter multiplicities are positive and even. After translating pairs to labels, put

$$
U=(a_0,b_r),\qquad V=(a_1,b_{r+1}),\qquad
W=(a_0,b_{r+1}).
\tag{81.26}
$$

The join has exactly $N-1=2^h-1$ classes and obeys every condition (81.3). Adding the even multiplicities of $u,v,w$ to the degrees of $\mathcal H$ changes none of the row or column parities. Therefore $\lambda_0$ has exactly $2^d-1$ classes with unique positive even class $a_*$, and $\lambda_1$ has exactly $2^d-1$ classes with unique positive even class $b_*$. Every other component class has positive odd multiplicity. Both even classes avoid phases $0,1$, since those phases use $u,v$.

Finally $m=N+2d-3$ is odd and at least $2^h-1$, with $k=m+1$ and actual $\gcd(m,m+2)=1$. Thus Definition 81.1 holds for this entire target. The same single-history witnesses (81.6) realize every row of both component tables with every original tail; no marginal reachability assumption was introduced. ∎

**定理 81.4（Exact unbounded adaptive/GLOBAL separation on the original full reader）。** For every $d\ge3$, the entire target of Construction 81.3, and its explicit history pullback, satisfy under both original alphabets

$$
\boxed{
C_{\rm ad}(f)=C_{\rm ad}(F)=d,\qquad
C_{\rm pre}(f)=C_{\rm pre}(F)=2d.
}
\tag{81.27}
$$

The exact worst emitted-bit fees are respectively $md$ and $2md$, with $m=2^{2d-1}+2d-3$. The GLOBAL stream is the one joined-table stream (81.15), with $h=2d-1$. It is common to both INITIAL values and all original tails.

**证明（adaptive lower bound under every legal action）。** Fix either remembered INITIAL value. Its low sources carry $2^d$ distinct labels: the $2^d-1$ component classes just proved and fresh $C$. Free stopping and every root except a word beginning $10$ are excluded by the actual unequal-tail pair argument preceding (81.7). Such a root clears all low tails without losing their labels. Every subsequent low archive therefore obeys the all-literal common-tail binary restriction used in the proof of Theorem 81.2. A worst fee $H$ allows at most $2^H$ low-label leaves, even with arbitrary adaptive actions, waits, repairs, endpoint stops or attempted rejection. Hence $H\ge d$. The argument holds on each actual free-value fibre separately, so a controller choosing different roots from that free reading cannot evade it.

**证明（one value-adaptive policy and every strict seam）。** Let $L_v=\lambda_v[A]$, and let $D_0=a_*$, $D_1=b_*$. The component tables satisfy (80.1)–(80.2) at depth $d$: $m$ is odd and at least $2^d-1$, each has exactly $2^d-1$ classes and one positive even class avoiding phases $0,1$. Apply the credited physical selection of Lemma 80.2 separately to the two installed tables. It provides bijections

$$
c^{(v)}:L_v\cup\{C\}\longrightarrow\mathbb F_2^d,
\qquad c^{(v)}(D_v)=0,\qquad v\in\mathbb F_2.
\tag{81.28}
$$

With coordinates $t=0,\ldots,d-1$, these obey

$$
\begin{aligned}
c^{(v)}_0(C)&=0,&
c^{(v)}_0(\lambda_v(0))&=c^{(v)}_0(\lambda_v(1))=1,\\
c^{(v)}_t(\lambda_v(m+1-2t))&=0&&1\le t<d,\\
c^{(v)}_{t-1}(\lambda_v(m+2-2t))\,
c^{(v)}_t(\lambda_v(m+2-2t))&=0&&1\le t<d.
\end{aligned}
\tag{81.29}
$$

Define $\Lambda_v$ on the full phase cycle by $\Lambda_v|_A=\lambda_v$ and $\Lambda_v(z)=C$. The full-cube XOR and the unique even component class give

$$
\bigoplus_{j\in A\cup\{z\}}c^{(v)}(\Lambda_v(j))
=\left(\bigoplus_{y\in\mathbb F_2^d}y\right)
       \oplus c^{(v)}(D_v)=0.
\tag{81.30}
$$

Each coordinate of the cube has $2^{d-1}$ ones, an even number. At issued index $t$, the row $c^{(v)}_t(\Lambda_v(j))$ is zero at the sole phase missed by $W_t$, including $z$ at $t=0$, by (81.29). Equation (81.30) gives even full-path charge, so its literal inverse is the complete word

$$
B^{(v)}_{t,i}
=\bigoplus_{a=0}^{i}c^{(v)}_t
          \bigl(\Lambda_v(tm+a\bmod T)\bigr),
\qquad 0\le t<d,\quad0\le i<m.
\tag{81.31}
$$

The actual adaptive policy reads the free initial value $v$ and issues
$B^{(v)}_0|\cdots|B^{(v)}_{d-1}$ on that source, with the following stops and decoder. This is lawful use of the free value to choose actions in adaptive control. The GLOBAL attainment instead uses (81.15); no common-stream claim is made for the two action lists in (81.31).

The first two bits of $B^{(v)}_0$ are $10$. Thus its high band alone rejects, returns common $R$ at the whole paid root endpoint and stops. Every original low tail survives and merges with its component label preserved. For each later seam let $s_t=m+2-2t$. The two adjacent literal bits are

$$
B^{(v)}_{t-1,m-1}
  =c^{(v)}_{t-1}(\Lambda_v(s_t)),\qquad
B^{(v)}_{t,0}=c^{(v)}_t(\Lambda_v(s_t)),
\tag{81.32}
$$

and their product is zero by (81.29). Every boundary therefore contains a zero among its adjacent bits; all one-runs are confined to individual words of length $m<k$. The entire emitted concatenation is safe on all continuing low sources, with every seam strict and no extra clearing, wait or repair word. This is the credited Chapter 80 physical attainment, applied to each actual value fibre rather than presumed to make their streams compatible.

Initial bottom returns $L_\bot$ freely. Every low source, including outside phase $z$, continues through all $d$ words. Its own completed scalar outputs $v_0,\ldots,v_d$ give

$$
(v_1\oplus v_0,\ldots,v_d\oplus v_{d-1})
 =c^{(v_0)}(\Lambda_{v_0}(j)).
\tag{81.33}
$$

The inverse bijection returns that component INITIAL label, including $C$. The superscript is the remembered free INITIAL value, not the changing current scalar. No phase is observed. Every low record is actual by (81.6), so the policy has worst fee exactly $d$. Stopping at its last endpoint needs no cleanup. This gives the matching adaptive upper bound.

Construction 81.3 satisfies Definition 81.1 at $h=2d-1$. Theorem 81.2 therefore gives $C_{\rm pre}=h+1=2d$, with the same explicitly paid and seam-safe joined stream (81.15) on both values. Its root-positive sources pay $2d$ blocks; its $C$ and $R$ branches pay one; initial bottom pays zero. Multiplication by the actual block width gives $md$ and $2md$, including every bit of an issued rejecting block. This proves (81.27). ∎

**数学引文 81.5（Required suppliers, scoped overlap and the new fee content）。** [IC, Chapter 1; S1, Definitions 1.2–2.1, Convention 1.3, Proposition 2.2, Lemmas 4.2–4.3 and Note 5.3] supplies the original joint prior, immutable INITIAL factorization, absorbing rejection, destructive root constraints and semantic/effective distinction. Formula (81.6) uses one original history for value, phase and tail together; the target pullback is (81.4). [S2, Sections 13–14, Theorem 14.1] supplies the matched coefficient cycle for the original integer weights. [IC, Interface 1.4; S10, Interface 2.1 and Lemma 3.2; S15, Section 1, Definition 1.1 and Proposition 4.2] supplies the literal path equations, inverse, strict tail contract, all-action common-tail bound and full-parent preservation. A response row here is consumed only through the complete word (81.14) or (81.31), with its own seam proof.

[IC, Definition 29.1 and Theorem 29.2] is the already supplied exact value-join reduction, including arbitrary endpoint stopping and absorption. It supplies no numerical price for the joined table (81.2) under (81.3). Lemma 73.3, Construction 73.4, Lemma 73.5 and Theorem 73.6 supply the entire $(h+1)$-block upper bound after the actual alternating root. The full-source connection is the credited Chapter 74 attainment and the nonsaturated upper-bound clause of Open Problem 75.3; its power-of-two child-label equality is not applied to $2^h-1$. The root and physical two-block mechanisms of Chapter 76 are a precursor, but its three-label table has different label count from the $2^h-1\ge7$ joined table here.

Lemma 80.2 and Theorem 80.3 supply the component physical codes and their depth-$d$ attainment; these are credited reuse, not new component-price results. That chapter has precisely one even class and identical tables on both value fibres. Its theorem cannot be applied to the present three-even joined table, nor does it establish that the two lists (81.31) are one GLOBAL stream. The new reader-specific content is the saturated common-stream obstruction (81.8)–(81.11) combined with all actual missing vertices and the compulsory root, its exact whole-target price (81.5), and the explicit graph/phase family (81.18)–(81.26) realizing both component hypotheses and that joined obstruction at every $d\ge3$. This gives the unbounded exact adaptive/GLOBAL difference $d$ on the full original reader.

[IC, Definitions 36.1–36.2 and Theorems 37.1 and 38.1] already separates multiplicity-based code algebra from legal fee realization. The elementary full-cube XOR and the parity of phase multiplicities used here belong to that established algebra. The wide-reader fee realization assumes $m\ge k$, with Theorem 38.1 further requiring $a+k+2\le m$; neither holds at $k=m+1$. Algebraic even codes alone do not enforce the root values at $0,1$ or the missing coordinate at every index. In fact (81.11) by itself does not cause the contradiction; the reader-specific placements (81.3) force its third vector to vanish. The guarded independent-row laws [IC, Chapters 27 and 60–64; S15, Theorem 3.4] require $k\ge2m$ and are not used to realize this stream.

The finite Hall theorem [H], at its pinned version and symbol listed in Mathematical Citation 75.1, is used through the credited selections of Chapters 73 and 80. No new generic matching theorem, generic optimizer or finite-case fee catalogue is introduced.

The comparison source [phase-coherent full-tail minimax](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), Definitions 1.2–1.5, Theorem 2.1, Section 2.4 and Section 4, concerns one fixed random-depth source, paid Read letters, finite retained configurations, complete stopped-transcript laws and conditional total-variation minimax risk. Its two phase generators retain that original source and its update/Stop chronology; their exact attained radius is a prediction-loss conclusion. Here the object is the original deterministic KBonacci bit continuation, the observations are complete scalar endpoints, the target is an immutable INITIAL label and the optimized resource is a uniform worst emitted-block count. No source/action/observation or risk-to-fee bridge between those contracts is supplied or used. Its causal closure result is a comparison about lawful realization, not a numerical supplier for (81.5) or (81.27).

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Section 4 and Figure 3](https://arxiv.org/html/1907.11034v2), provides the mature distinguishing-test comparison: a candidate first operation can destroy the distinction it must later recover. That supports the identification contract and the use of destructive-root exclusions, with one input here a whole original block and one output its endpoint. It does not supply the three-even phase equation, the missed-vertex placements, the original inherited-tail seams or an emitted-block fee. This scoped comparison makes no source-wide absence or mathematical-priority claim.

All statements in this chapter are repo-derived ordinary mathematical proofs on the specified suppliers. Literature support, ordinary theory deduction and Lean/kernel certification are distinct grades. No Lean proof, compilation, ingestion, coverage or freezing is claimed.

**边界 81.6（Exact validity, resources and unresolved original quantifiers）。** Equation (81.5) requires all of (81.1)–(81.4): $h\ge3$, odd $m\ge2^h-1$, $k=m+1$, actual gcd one, exactly $2^h-1$ joined classes with precisely the three positive even classes $U,V,W$, their stated root and missed-phase placements, common fresh distinct $R,C$, a homogeneous high-tail band and the explicit full history pullback. It prices every pair of component tables meeting those conditions, but does not classify their adaptive prices. Equation (81.27) adds exactly the explicit family (81.17)–(81.22), which is inhabited for every integer $d\ge3$. The two equalities are whole-target prices from the free INITIAL reading, not prices conditional on an unpaid chosen parent. Different fixed targets may choose different GLOBAL streams.

Each attaining controller uses one free initial read and one subsequent complete-endpoint read for every actually issued block. Its maximum number of subsequent reads equals its stated block fee; counting the free read adds one. The emitted-bit count is the block fee multiplied by $m$, including absorbed rejection through the rest of an issued root. Offline code selection, target representation, arithmetic, comparison, storage and controller memory are separate resources. No polynomial selection bound, offline bit complexity, memory optimum or cost of obtaining an input presentation is asserted.

For arbitrary labels, the universal theorem is a semantic minimum and existence statement. A finite partition presentation or decidable label equality makes the cited finite code selections and literal inverses effective. Construction 81.3 itself gives the pair table by rectangles and ordered bijection at each finite $d$; it does not depend on a fee solver. The specified INITIAL pullback does not decide factorization of an arbitrary history expression. Unbounded $d$ ranges over different finite readers and targets, without claiming one controller for their union.

Other joined parity profiles and placements, arbitrary component-price classes, nonfresh high/outside labels, tail-dependent low labels, even widths, other orders or gcds, mixed acquired supports and unspecified history factorization remain outside these equalities. The original exact minimum worst-branch ACTUAL emitted-complete-block objective for every attainable immutable INITIAL target and all original $k\ge2,m\ge1$, separately for adaptive control and ONE GLOBAL preset stream per fixed target under both alphabets [IC, Definition 1.3 and Open Problem 9.1], remains unresolved.

## 追加锚（本行以下为增补区）

## 82. Saturated whole-target codes, automatic safe seams and five even joined classes

A saturated code must respect the compulsory root and every chronological missing phase. Those algebraic conditions do not, by themselves, justify a literal stream on a general reader. For the original reader at $k=m+1$, the additional physical relation proved here makes them sufficient at depth at least four: a rejecting boundary permits at most three phases charged by both adjacent words, whereas every adjacent coordinate pair of a saturated cube charges at least four distinct actual classes. This yields an exact whole-target criterion for arbitrary different value-fibre tables and arbitrary phase multiplicities in the stated saturated class.

**定义 82.1（Original arithmetic rows and an actual inherited-tail seam）。** Retain the original integer weights and matched reading of [IC, Definition 1.1]: $G_i=2^i$ for $i<k$, $G_i=\sum_{r=1}^kG_{i-r}$ thereafter, and $V_k(w)=\sum_iw_iG_i\bmod2$. In this chapter the width $m$ is odd, $k=m+1$ and $T=k+1=m+2$, so the actual coefficient cycle is

$$
\gamma_i=G_i\bmod2=\mathbf1_{\{0,T-1\}}(i\bmod T),
\qquad \gcd(m,T)=1.
\tag{82.1}
$$

The original complete-endpoint record is $(v,\theta,s)$, with $v\in\mathbb F_2$, $\theta\in\mathbb Z/T\mathbb Z$ and $0\le s<k$, or independently labelled absorbing bottom. A zero clears the tail and advances the phase; a one contributes $\gamma_\theta$, advances the phase and increments the tail, rejecting when that increment reaches $k$. Put $j=-\theta_{\rm INITIAL}$. For a complete literal word $B=(B_0,\ldots,B_{m-1})$ at actual issued index $t$, define its **full arithmetic row**, on all original phases, by

$$
q_{t,B}(j)=\bigoplus_{i=0}^{m-1}B_i\gamma_{-j+tm+i}.
\tag{82.2}
$$

On a successful source this is its completed scalar difference. On a rejecting source it is an arithmetic expression only, not an observed extra value: the actual completed output is bottom. The full word is still emitted and paid even if rejection occurs before its endpoint.

Write $u=tm\pmod T$. The credited literal inverse interface [IC, (1.4)–(1.5); S10, Interface 2.1; S15, Section 1] gives

$$
\begin{aligned}
q_{t,B}(u)&=B_0,\\
q_{t,B}(u+i)&=B_{i-1}\oplus B_i\quad(1\le i<m),\\
q_{t,B}(u+m)&=B_{m-1},\\
q_{t,B}(u+m+1)&=0.
\end{aligned}
\tag{82.3}
$$

Thus the row is even on its ordered path $W_t=[tm,(t+1)m]\pmod T$, and every even row on that path has the unique literal inverse $B_i=\bigoplus_{a=0}^i q_{t,B}(tm+a)$. This statement concerns one complete word and supplies no intermediate reading.

For a word $B$, let $\rho(B)$ be its trailing run of ones and $\alpha(B)$ its leading run, each equal to $m$ for $1^m$. Consider consecutive issued words $P,Q$, with $P$ actually completed successfully on a source. Its current tail is $r=\rho(P)$: if $P$ contains a zero, that follows from its last zero; if $P=1^m$, success at $k=m+1$ forces its incoming tail to be zero, so its outgoing tail is $m$. Consequently the next word rejects precisely when

$$
r+\alpha(Q)\ge m+1.
\tag{82.4}
$$

This includes the all-one words and the strict equality threshold. Both alphabets contain all width-$m$ words because $m<k$; the seam, rather than internal word legality, is the issue.

**引理 82.2（Sharp three-phase bound at every rejecting consecutive seam）。** In Definition 82.1, if the actual seam after $P$ rejects $Q$, then

$$
\bigl|\{j:q_{t,P}(j)=q_{t+1,Q}(j)=1\}\bigr|\le3.
\tag{82.5}
$$

The bound is attained for every odd $m\ge5$. At the degenerate odd widths $m=1$ and $m=3$, the respective sharp bounds are one and two. An all-zero word on either side cannot produce such a rejecting seam; if either word is all ones, the intersection has at most two phases, and if both are all ones it has exactly one.

**证明。** First let $m\ge3$. Translate phase coordinates by the known issued displacement $tm$ for this calculation only. The first path is $0,1,\ldots,m$, missing $m+1$; the next is

$$
m,m+1,0,1,\ldots,m-2,
\tag{82.6}
$$

missing $m-1$. Their common vertices are $\{0,\ldots,m-2\}\cup\{m\}$. Put $r=\rho(P)$, $\ell=\alpha(Q)$. Rejection implies $r,\ell\ge1$ and $r+\ell\ge m+1$.

All bits in the suffix of $P$ from position $m-r$ onward are one. Its consecutive differences in (82.3) therefore vanish at phases $m-r+1,\ldots,m-1$. Apart from its endpoint $m$, its charge support lies in $[0,m-r]$. The prefix of $Q$ has $\ell$ ones, so its consecutive differences vanish at local path positions $1,\ldots,\ell-1$. In the order (82.6), among the common vertices other than $m$, its charge support lies in $[\ell-2,m-2]\cap[0,m-2]$. These inclusions also hold when either run is the entire word. Hence the common charged vertices are contained in

$$
\{m\}\ \cup\
\bigl([0,m-2]\cap[\ell-2,m-r]\bigr).
\tag{82.7}
$$

The interval before clipping has $\max\{0,m-r-\ell+3\}\le2$ integer points, counting zero when it is empty. Clipping cannot increase this count, so including $m$ proves (82.5). This is a bound on the complete rows of the two actual words; it does not treat rejection as a third binary response.

For sharpness, at every $m\ge5$ use the actual consecutive words

$$
P=10\,1^{m-2},\qquad Q=1110\,1^{m-4}.
\tag{82.8}
$$

Start $P$ from tail zero. It succeeds, ends with tail $m-2$, and $Q$ has leading run three, so the next seam reaches $k=m+1$ and rejects. Their respective arithmetic supports, in the coordinates above, are

$$
\{0,1,2,m\},\qquad \{m,1,2,m-2\};
\tag{82.9}
$$

their intersection is exactly $\{1,2,m\}$. The initial tail-zero record is jointly actual by [IC, (1.3)], and the complete rejecting $Q$ remains a fully paid width-$m$ action. Thus this is physical sharpness, not just an abstract row pair.

To attain three, (82.7) must contain two actually charged points besides $m$. It requires $r+\ell=m+1$ and those points are $a-1,a$, where $a=m-r$. If $a=0$ there is only one nonnegative point; if $a=1$, the first bit of $P$ is zero, so its charge at zero vanishes. If $a=m-2$, then $\ell=m-1$ and the last bit of $Q$ is zero, so its endpoint charge at $m-2=a$ vanishes. If $a=m-1$, that point is absent from the common window. Thus three charged points require $2\le a\le m-3$. This is impossible at $m=3$. There the pair $P=101,Q=111$ rejects with $r+\ell=1+3=4$ and has common support $\{1,3\}$, proving sharp bound two.

At $m=1$ a rejecting seam after a successful block is exactly $P=Q=1$. Its two rows have supports $\{0,1\}$ and $\{1,2\}$ on the three-cycle, with intersection one. If $P=0^m$, its outgoing tail is zero and no next word of length $m<k$ rejects; if $Q=0^m$, it starts by clearing any legal inherited tail. An all-one word has a two-endpoint arithmetic support by (82.3), giving the stated bound of two. For two all-one words those supports are $\{0,m\}$ and $\{m,m-2\pmod T\}$, with intersection exactly $\{m\}$, including $m=1$. This covers zero, all-one and degenerate cases. ∎

**定义 82.3（Arbitrary two-value tables and the saturated compatibility criterion）。** Fix

$$
h\ge4,\qquad m\ge2^h-1\text{ odd},\qquad
k=m+1,\quad T=m+2,\quad g=1.
\tag{82.10}
$$

Put $A=\{0,\ldots,m\}$ and $z=m+1$. Let $\lambda_0,\lambda_1:A\to Y$ be arbitrary finite phase tables, allowing repetitions and different component images, such that

$$
\Gamma(j)=(\lambda_0(j),\lambda_1(j)),\qquad
|\Gamma[A]|=2^h-1.
\tag{82.11}
$$

Choose common distinct $R,C$ fresh relative to both component images. On the entire original INITIAL record space define

$$
\begin{aligned}
f(v,-j,s)&=
\begin{cases}
R,&s=m,\\
\lambda_v(j),&0\le s<m,\ j\in A,\\
C,&0\le s<m,\ j=z,
\end{cases}
&&v\in\mathbb F_2,\\
f(\bot)&=L_\bot,&&F(w)=f(q_{\rm INITIAL}(w)).
\end{aligned}
\tag{82.12}
$$

Initial bottom has its arbitrary independent label, possibly equal to another label. The pullback is part of the specified target, not inferred from the legality of a source history. No INITIAL label is reevaluated after control begins.

Write $\widehat C=(C,C)$, $L=\Gamma[A]\cup\{\widehat C\}$, and extend $\Gamma$ to the full low phase cycle by

$$
\Lambda(j)=\Gamma(j)\ (j\in A),\qquad
\Lambda(z)=\widehat C.
\tag{82.13}
$$

For a joined class $D\in\Gamma[A]$, let $n_D=|\Gamma^{-1}(D)|$, and put

$$
E=\{D\in\Gamma[A]:n_D>0\text{ is even}\},\qquad
e_t=m+1-2t\quad(1\le t<h).
\tag{82.14}
$$

The criterion $\mathsf K$ is the existence of a bijection $c:L\to\mathbb F_2^h$, with coordinates $0,\ldots,h-1$, satisfying exactly

$$
\begin{aligned}
\bigoplus_{D\in E}c(D)&=0,\\
c_0(\widehat C)&=0,\qquad
c_0(\Gamma(0))=c_0(\Gamma(1))=1,\\
c_t(\Gamma(e_t))&=0\quad(1\le t<h).
\end{aligned}
\tag{82.15}
$$

Repeated classes accumulate their coordinate restrictions. There are no additional seam clauses in $\mathsf K$. Its XOR is over positive even-multiplicity joined phase classes, not over INITIAL tails or separate component parities.

All prices below are the original minimum worst-branch ACTUAL emitted-complete-block fees [IC, Definition 1.3]. The free initial output gives the INITIAL scalar or initial bottom; all subsequent observations are complete endpoints. A GLOBAL controller uses ONE preset literal stream for this fixed full target, on both free-value fibres and all actual original sources, with its own endpoint stopping and decoding. Every issued block, including a wait, padding, repair or absorbed rejection, costs one. Reset, copy, intermediate reading, hidden INITIAL clock and borrowed sibling observations are excluded.

**定理 82.4（Exact whole GLOBAL price with no extra seam test）。** For every target of Definition 82.3, under both original literal alphabets,

$$
\boxed{
C_{\rm pre}(f)=C_{\rm pre}(F)=
\begin{cases}
h,&\mathsf K,\\
h+1,&\neg\mathsf K.
\end{cases}}
\tag{82.16}
$$

Its exact worst emitted-bit fee is $m$ times this block fee. If $\mathsf K$ holds, every witnessing bijection in (82.15), through the inverse below, supplies one legal attaining stream. This theorem does not assign an adaptive optimum to arbitrary component tables.

**证明（joint actual sources, immutable labels and all-action lower bounds）。** Every record in (82.12) is jointly actual. Use the credited original history [IC, (1.3); S1, Convention 1.3; S15, Section 1]: choose

$$
\begin{aligned}
\ell&\equiv0\pmod m,&\ell&\equiv-j\pmod T,&\ell&\ge s+2,\\
\eta&=\bigoplus_{i=\ell-s}^{\ell-1}\gamma_i,&
w(v,j,s)&=(v\oplus\eta)0^{\ell-s-1}1^s.
\end{aligned}
\tag{82.17}
$$

Actual gcd one supplies arbitrarily large compatible $\ell$. This one legal history has value $v$, phase $-j$ and tail $s$ together, and splits into complete internally legal source blocks. Its separating zero prevents a forbidden run and its first bit compensates the terminal run's scalar contribution. The history $1^{2m}$ realizes initial bottom because its two individual blocks are internally legal and their seam rejects. The histories' lengths are unobserved and supply no INITIAL clock. The explicit pullback in (82.12) gives equality of record and history acquisition fees by [S1, Proposition 2.2].

For either fixed free INITIAL value, at every phase the two actual tails $m-1$ and $m$ have unequal labels: a low label versus fresh $R$. Therefore no correct controller stops freely. A root beginning zero merges this pair at the first zero, with identical value and phase, so all later archives coincide on unequal INITIAL labels. A root with at least two leading ones, including $1^m$, rejects both before the first endpoint, and all their later outputs remain bottom. The credited first-zero and rejection losses [S1, Lemmas 4.2–4.3; S15, Proposition 4.2] thus force every correct root to begin $10$, irrespective of its horizon, subsequent actions or stopping rule.

Such a root rejects exactly $s=m$. Every low tail $s<m$ survives the leading one since $s+1\le m<k$, reaches the second-bit zero and finishes safely. At a fixed phase the merger preserves the component INITIAL label in (82.12). All successful low sources then have common current tail, and each root-output archive has common current scalar. By [S10, Lemma 3.2], every later literal action, including waits, all-one words and attempted repairs, either succeeds on all candidates of such an archive or rejects all. Common rejection cannot resolve a nonconstant label because absorption is permanent; successful actions have at most two completed scalar outcomes, each again with common value and tail. A child with at most $a$ further paid blocks therefore has at most $2^a$ distinct-label leaves. This applies to arbitrary adaptive words and homogeneous endpoint stops, not only to the attaining constructions.

For the GLOBAL lower bound use the credited exact preset value-join law [IC, Definition 29.1 and Theorem 29.2]. The joined full target has high label $(R,R)$, low table $\Lambda$, and independent initial bottom. Its preset price equals that of $f$, including stops and absorption. The law is a decoder symmetry on the same actual stream and its acquired endpoints, without a second experiment or borrowed observation. On either fixed scalar fibre there are $|L|=2^h$ actual low labels. The forced root gives at most two successful low children; each admits at most $2^{H-1}$ distinct labels when the whole worst fee is $H$. Hence $2^h\le2^H$, proving $C_{\rm pre}(f)\ge h$.

**证明（necessity of the criterion at saturated fee）。** Suppose a correct GLOBAL joined controller finishes in $h$ blocks. Equality in the preceding binary count forces a complete binary low-label tree of depth $h$. More explicitly, its two root children each have $2^{h-1}$ labels with disjoint images; the same equality recurses at every child. An overlapping label image, an early homogeneous stop, a uniform rejecting action or a missing useful child would reduce the total number of distinct-label leaves below $2^h$. Thus every low source continues through all $h$ slots and succeeds in every issued word.

The common literal stream induces a length-$h$ difference vector on every phase. Unequal low labels must have unequal vectors. All $2^h$ vectors are already required by the $2^h$ labels, so each label has exactly one vector: allowing two for one label leaves too few for the others. Consequently these actual differences give a bijection $c:L\to\mathbb F_2^h$.

Since $m\equiv-2\pmod T$, the full path at chronological index $t$ misses only $e_0=z$ at $t=0$ and $e_t$ of (82.14) for $1\le t<h$. These latter phases belong to $A$ and are distinct. Indeed $2^h\ge2h+2$ for $h\ge4$ and $m\ge2^h-1$ give $e_{h-1}\ge2^h-2h+2\ge4$. Formula (82.3) therefore forces $c_0(\widehat C)=0$ and $c_t(\Gamma(e_t))=0$. The first two root bits $10$ force its charges at phases zero and one to be one, giving the other root conditions in (82.15).

Each full arithmetic row is even on $W_t$ and zero at its missing vertex, so

$$
\bigoplus_{j=0}^{m+1}c(\Lambda(j))=0.
\tag{82.18}
$$

The XOR of the whole $h$-cube is zero, because each coordinate has $2^{h-1}$ ones, an even number. In (82.18), positive even classes contribute zero and odd classes, including the singleton outside class, contribute their code once. Hence

$$
0=\bigoplus_{j=0}^{m+1}c(\Lambda(j))
 =\left(\bigoplus_{y\in\mathbb F_2^h}y\right)
       \oplus\bigoplus_{D\in E}c(D)
 =\bigoplus_{D\in E}c(D).
\tag{82.19}
$$

This gives the remaining condition of $\mathsf K$. Thus every fee-$h$ GLOBAL controller yields a witness of (82.15). All paid waits occupy those same chronological windows; arbitrary stops and attempted rejection were included in the saturation argument. If $\mathsf K$ fails, the integer fee is at least $h+1$.

**证明（the actual $h$-block stream and its automatic strict seams）。** Suppose $\mathsf K$ holds and choose any witnessing $c$. On the full phase cycle put $\chi_t(j)=c_t(\Lambda(j))$. The cube XOR and (82.15) give (82.18) in the reverse direction, so every $\chi_t$ has even total charge. It is zero at the missing vertex of its actual $W_t$. The unique literal words are therefore

$$
B_{t,i}=\bigoplus_{a=0}^i
              c_t(\Lambda(tm+a\bmod T)),
\qquad 0\le t<h,\quad0\le i<m.
\tag{82.20}
$$

Issue the single fixed stream $B_0|B_1|\cdots|B_{h-1}$. The root bits are $B_{0,0}=1$ and $B_{0,1}=1\oplus1=0$, so the root has exactly the lawful high-band rejection and low-tail preservation already proved. Each word is internally legal since its length is $m<k$.

For every pair of consecutive coordinates $t-1,t$, the full cube contains exactly $2^{h-2}\ge4$ distinct vectors with both coordinates one. Bijection gives that many distinct low labels $D$ with $c_{t-1}(D)=c_t(D)=1$. Each label has at least one actual phase in the full low cycle, and distinct classes have disjoint phase sets. Consequently

$$
\bigl|\{j:\chi_{t-1}(j)=\chi_t(j)=1\}\bigr|
\ge2^{h-2}\ge4.
\tag{82.21}
$$

There is no counting of virtual phases or separate value optima here. These are the complete arithmetic rows of the very words (82.20) on the original reader.

Inductively assume the preceding words have succeeded on a low source. Its actual incoming tail for $B_t$ is $\rho(B_{t-1})$, including the all-one case described in Definition 82.1. If its next seam rejected, Lemma 82.2 would bound the left-hand side of (82.21) by three, a contradiction. Thus every seam obeys

$$
\rho(B_{t-1})+\alpha(B_t)<m+1=k.
\tag{82.22}
$$

This proves safety on all continuing low sources. It does not require a zero among the adjacent boundary bits: a boundary with two ones can have a short, strictly legal run. All-one and zero words are covered by the same argument. No clearing, waiting, repair or padding block is inserted.

The controller's complete rule is as follows. Initial bottom returns $L_\bot$ freely. Root bottom returns $R$ at the completed paid root endpoint and stops; every remaining bit of that root has already been emitted into absorption. Every low source, including outside phase $z$, emits all $h$ words. Its own successive scalar endpoints $v_0,\ldots,v_h$ yield

$$
(v_1\oplus v_0,\ldots,v_h\oplus v_{h-1})
   =c(\Lambda(j)).
\tag{82.23}
$$

The inverse bijection returns the joined low label. If it is $\widehat C$, return $C$; otherwise return the component selected by the remembered free INITIAL value $v_0$. The same literal stream serves both values and all original tails. No phase is read, no other child's output is used, and the INITIAL target is unchanged. All low records are actual by (82.17), so some sources, indeed all low sources in this displayed rule, pay exactly $h$ blocks. Stopping at the final endpoint requires no cleanup. Together with the lower bound, this proves the first case of (82.16).

**证明（the fully paid common fallback when the criterion fails）。** The $(h+1)$-block upper bound is credited reuse of Chapter 73, with its full-target connection as in Chapters 74 and 81. For completeness the actual words and stops are specified. Issue $P_m=(10)^{(m-1)/2}1$ at index zero. It rejects precisely high tails $s=m$, returning $R$ at its paid endpoint; all low tails survive its first zero with their INITIAL labels preserved. Its charge is one on $A$ and zero at $z$. Thus its successful zero-difference child is homogeneous $C$ and stops at fee one. Its positive child is exactly the actual archive of Definition 73.1 with full support $A$, common scalar, terminal tail one and joined table $\Gamma$.

Here the child has $2^h-1\ge15$ labels. Lemma 73.3 supplies an injective code $b:\Gamma[A]\to\mathbb F_2^h$, with suffix coordinates $r=1,\ldots,h$, satisfying

$$
\begin{aligned}
b_r(\Gamma(m+1-2r))&=0&&1\le r\le h,\\
b_1(\Gamma(m))&=0,\\
b_{r-1}(\Gamma(m+2-2r))b_r(\Gamma(m+2-2r))&=0
&&2\le r\le h.
\end{aligned}
\tag{82.24}
$$

All these representatives are low phases since $h\le(m+1)/2$. At actual index $r$, let $\psi_r(j)=b_r(\Gamma(j))$ on $A$, and prescribe the already stopped outside vertex by

$$
\psi_r(z)=\bigoplus_{j\in A}b_r(\Gamma(j)),\qquad
S_{r,i}=\bigoplus_{a=0}^i\psi_r(rm+a\bmod T).
\tag{82.25}
$$

The unavailable low coordinate is zero by (82.24); the charge at $z$ makes the full row even. Thus (82.25) is the supplied actual inverse, not a second experiment at $z$. The first suffix begins zero because its first vertex is $m$. For every later suffix boundary the preceding last and next first vertex are the same $m+2-2r$, and their literal bits have product zero by (82.24). All these strict seams and the initial tail-one seam are safe by the credited Lemma 73.5. Every continuing positive source issues the same $P_m|S_1|\cdots|S_h$ and decodes $b(\Gamma(j))$ from its own suffix differences, returning its INITIAL-value component. Initial bottom stops freely; root bottom and root-zero have already stopped. Actual positive sources pay all $h+1$ blocks. This supplies no novel fallback-price claim and uses no unpaid wait or repair. It proves the second upper bound; necessity of $\mathsf K$ proves its matching lower bound. Multiplying every paid complete word by its actual width $m$ gives the emitted-bit assertion. ∎

**构造 82.5（A uniformly inhabited five-even-class family）。** For every integer $d\ge2$, set

$$
h=2d,\qquad r=2^d,\qquad N=r^2=2^{2d},\qquad
m=N+2d+1=N+h+1,\quad k=m+1,\quad T=m+2.
\tag{82.26}
$$

Let $I=\mathbb F_2^d$, ordered lexicographically, with distinct unit vectors $a=(1,0,\ldots,0)$ and $b=(0,1,0,\ldots,0)$. Take disjoint row and column label sets $\{A_i:i\in I\}$ and $\{D_i:i\in I\}$, with all labels within each set distinct. Choose common fresh distinct $R,C$ outside these sets and independent $L_\bot$. The joined low pair set is

$$
\mathcal J=(I\times I)\setminus\{(0,0)\}.
\tag{82.27}
$$

Its five designated pairs are

$$
H_1=(a,0),\quad H_2=(b,0),\quad
H_3=(0,a),\quad H_4=(0,b),\quad
H_5=(a+b,a+b).
\tag{82.28}
$$

They are distinct nonzero pairs, also when $d=2$. Put $A=\{0,\ldots,m\}$ and $M=\{m+1-2t:1\le t<h\}$. Specify the actual pair table $G:A\to\mathcal J$ by

$$
\begin{aligned}
G(j)&=H_1&&j\in\{0\}\cup M,\\
G(1)=G(2)&=H_5,\\
G(3)=G(4)&=H_2,\\
G(5)=G(6)&=H_3,\\
G(7)=G(8)&=H_4.
\end{aligned}
\tag{82.29}
$$

Assign all other pairs in $\mathcal J\setminus\{H_1,\ldots,H_5\}$ in lexicographic order to all remaining phases in increasing order, each exactly once. If $G(j)=(i,\ell)$, define

$$
\lambda_0(j)=A_i,\qquad \lambda_1(j)=D_\ell,
\tag{82.30}
$$

and extend them by the entire INITIAL target and history pullback (82.12).

**证明（well-defined table, actual class counts and a witness of the criterion）。** Here $h\ge4$ is even. The $h-1$ phases of $M$ are distinct; their least member is $N-h+4\ge16$ (equality at $h=4$, and the expression increases thereafter), and their greatest is $m-1$. Thus $M$ is disjoint from $\{0,\ldots,8\}$, so no prescription in (82.29) conflicts with another. The $H_1$ class has exactly $h$ phases; each other $H_i$ has two. The remaining phase count is

$$
|A|-h-8=(N+h+2)-h-8=N-6
       =|\mathcal J\setminus\{H_1,\ldots,H_5\}|.
\tag{82.31}
$$

Consequently the ordered bijection is well defined and exhausts all pairs in (82.27). There are exactly $N-1=2^h-1$ joined low classes, precisely five with positive even multiplicity, namely the $H_i$ after translating to labels; all the other $N-6$ classes have multiplicity one. The total phase count is $h+4\cdot2+(N-6)=N+h+2=m+1$, as required.

Every row and column of $I\times I$ has $r$ pairs. Deleting $(0,0)$ leaves $r-1>0$ pairs in row zero and column zero and $r>0$ in every other row and column. All remaining pairs occur in $G$, so each component table has exactly $r=2^d$ positive classes. The two component tables are different, since their label sets are disjoint. The width $m=N+h+1$ is odd, is at least $2^h-1$, and has actual gcd $\gcd(m,m+2)=1$. Formula (82.17) realizes every phase, every original tail and both values jointly for these tables; no separate marginal realization is substituted.

Identify the joined class associated to $(i,\ell)\ne(0,0)$ with its pair of row and column labels, and assign its code by concatenation:

$$
c((A_i,D_\ell))=(i,\ell)\in\mathbb F_2^{2d},
\qquad c(\widehat C)=(0,0).
\tag{82.32}
$$

This is a bijection onto the full cube. With coordinates numbered $0,\ldots,2d-1$, the five even classes have codes

$$
e_0,\ e_1,\ e_d,\ e_{d+1},\
e_0\oplus e_1\oplus e_d\oplus e_{d+1},
\tag{82.33}
$$

where here $e_i$ denotes a unit vector, not a missed phase. Their XOR is zero. The code of $\widehat C$ has coordinate zero zero, and the codes at phases zero and one, $H_1,H_5$, have coordinate zero one. Every missed phase $m+1-2t$ for $1\le t<h$ has class $H_1$, whose only nonzero code coordinate is zero. Thus every clause of (82.15) holds. The witnessing code and the pair table are explicit finite formulas, rather than a fee solver or a choice of an unspecified validation example. ∎

**定理 82.6（Exact adaptive and GLOBAL fees of the five-even family）。** For every integer $d\ge2$, Construction 82.5 gives full original INITIAL and history targets with

$$
\boxed{
C_{\rm ad}(f)=C_{\rm ad}(F)=d+1,\qquad
C_{\rm pre}(f)=C_{\rm pre}(F)=2d.
}
\tag{82.34}
$$

Their exact worst emitted-bit fees are $m(d+1)$ and $2md$, respectively. The GLOBAL attainment is the one actual stream (82.20) with the explicit pair code (82.32), serving both free-value fibres, every original tail and initial bottom as specified in Theorem 82.4.

**证明（adaptive lower bound for all literal words and endpoint stops）。** Fix either free INITIAL value. The low source set has $2^d+1$ different component labels: all $2^d$ row or column labels and fresh $C$. Every one is actual by (82.17). The unequal low/high-tail pair again forces a $10$ root under every correct adaptive controller. After this root, each successful archive has common value and tail. The all-action common-tail binary bound in the proof of Theorem 82.4 therefore allows at most $2^H$ distinct low-label leaves at whole fee $H$. Since $2^d+1>2^d$, every such controller has $H\ge d+1$. The bound covers all waits, repairs, all-one words, attempted rejection and early homogeneous stops. A different root chosen on the other freely read value cannot remove this bound on either fibre.

**证明（a lawful value-adaptive attainment, with every complete word paid）。** Read the free INITIAL value $v$ and issue the same alternating root $P_m=(10)^{(m-1)/2}1$. Initial bottom has already stopped with $L_\bot$. The root rejects exactly the original high band $s=m$, returns $R$ at its paid endpoint and stops; low outside phase $z$ has successful difference zero, returns $C$ at that endpoint and stops. Every other low source reaches the actual positive archive of Definition 73.1, with support $A$, common current scalar, actual tail one and the component table $\lambda_v$. That table has exactly $r=2^d$ labels, allowing all the repetitions in (82.29).

Use the credited selection and attainment of Lemmas 73.3 and 73.5 and Theorem 73.6 on this one actual child. They give an injective $b^{(v)}:\lambda_v[A]\to\mathbb F_2^d$. For suffix coordinate $q=1,\ldots,d$ it obeys the unavailable-coordinate and first-suffix conditions

$$
b_q^{(v)}(\lambda_v(m+1-2q))=0,
\qquad b_1^{(v)}(\lambda_v(m))=0,
\tag{82.35}
$$

and, in the ordinary list selection, the adjacent conditions

$$
b_{q-1}^{(v)}(\lambda_v(m+2-2q))
 b_q^{(v)}(\lambda_v(m+2-2q))=0
\quad(2\le q\le d).
\tag{82.36}
$$

For $d\ge3$ these lists always suffice. At $d=2$, the same lists suffice unless the four specified labels in (73.7) are distinct; in that sole alternative use exactly (73.8). It still obeys (82.35), and its actual suffix has first-suffix leading zero, then terminal run one followed by leading run two at the relaxed seam. That seam has length three, strictly below $k$ since the present $m\ge21$. This is the supplied physical alternative, not an assumed availability of arbitrary binary queries.

To specify the actual suffix words in either selection, on $A$ put $\psi_q^{(v)}(j)=b_q^{(v)}(\lambda_v(j))$, compensate only at the already stopped outside phase, and invert:

$$
\psi_q^{(v)}(z)=\bigoplus_{j\in A}b_q^{(v)}(\lambda_v(j)),
\qquad
S^{(v)}_{q,i}=\bigoplus_{a=0}^i
                 \psi_q^{(v)}(qm+a\bmod T),
\quad0\le i<m.
\tag{82.37}
$$

The unavailable low coordinate is zero by (82.35) and each full row is even. The inverse is a complete literal word at actual index $q$. The first suffix starts zero, clearing the actual inherited root tail one. In the list case, (82.36) puts a zero among the two bits adjacent to each later suffix boundary; in the four-label alternative the single relaxed seam has the strict run length just stated. All words are internally legal because $m<k$. Thus the whole issued stream on the selected value fibre is $P_m|S_1^{(v)}|\cdots|S_d^{(v)}$, with no wait, repair or cleanup word.

Every root-positive source emits all $d$ suffix words, reads only its own completed scalar endpoints, obtains $b^{(v)}(\lambda_v(j))$ from successive differences and returns its immutable INITIAL component label. The superscript uses the remembered free initial value, not the changing current scalar. Both component policies are permitted adaptive actions; they are not asserted to be one common stream. The high and outside branches have already stopped after one paid block, initial bottom stops freely, and all root-positive records are actual and pay exactly $d+1$ complete blocks. This proves the adaptive upper bound matching the preceding lower bound.

Construction 82.5 satisfies $\mathsf K$ at $h=2d$ by (82.32)–(82.33). Theorem 82.4 supplies the common stream (82.20) at exactly $2d$ blocks; its strict physical seams follow from (82.21)–(82.22), not from composing the two adaptive suffixes. There are $2^{2d}$ actual joined low labels including $\widehat C$, so the same joined all-action capacity bound also directly gives its matching GLOBAL lower bound. The history pullback and complete-block bit conversion are those already proved. This gives (82.34). ∎

**实例 82.7（The depth-four anchor on the original reader）。** At $d=2$ one has $h=4$, $m=21$, $k=22$, $T=23$, four component classes in each value fibre, fifteen joined classes and five positive even joined classes. With the lexicographic assignment of Construction 82.5, the full phase-code table, including outside phase 22, is

$$
\begin{array}{c|rrrrrrrrrrrr}
j&0&1&2&3&4&5&6&7&8&9&10&11\\\hline
c(\Lambda(j))&1000&1111&1111&0100&0100&0010&0010&0001&0001&0011&0101&0110
\end{array}
\tag{82.38}
$$

$$
\begin{array}{c|rrrrrrrrrrr}
j&12&13&14&15&16&17&18&19&20&21&22\\\hline
c(\Lambda(j))&0111&1001&1010&1011&1000&1100&1000&1101&1000&1110&0000
\end{array}
\tag{82.39}
$$

Here the first two code digits are the row index and the last two are the column index, except that $0000$ is the fresh outside label. Thus (82.38)–(82.39) specify the component labels as well as the common code. Inverting these rows at actual starts $0,21,19,17\pmod{23}$ gives the one preset stream

$$
\begin{aligned}
B_0&=10\,1^{11}\,01010101,\\
B_1&=111010111111010000011,\\
B_2&=001110111011100100100,\\
B_3&=001111101111101011011.
\end{aligned}
\tag{82.40}
$$

Each displayed word has exactly 21 bits. The root begins $10$ and ends with tail one. The successive later leading runs are three, zero and zero, and the preceding terminal runs are one, two and zero, respectively. Hence the three seam lengths are four, two and zero, each strictly less than 22, including the first boundary whose adjacent bits are both one. High tail 21 rejects at the root's first bit and remains absorbed through the paid root endpoint. Every low source emits all four words and decodes its own vector in (82.38)–(82.39), returning the component selected by its free initial value, or $C$ at phase 22; initial bottom stops freely. The adaptive policy of Theorem 82.6 costs three blocks. Thus this anchor has exact adaptive/GLOBAL fees $3/4$ blocks and $63/84$ emitted bits. It is an instance of the uniform proof, not a finite-case substitute for it.

**数学引文 82.8（Exact supplier correspondence and the new physical fee relation）。** The six supplied mathematical volumes are compared at [immutable source revision 537dff8fb5928067ea056a7d52945355794cf6c6](https://github.com/the-omega-institute/trureturing/tree/537dff8fb5928067ea056a7d52945355794cf6c6/docs/develop/theory). The relevant results retain their own original contracts.

[IC, Definitions 1.1–1.3 and Interface 1.4; S1, Convention 1.3, Proposition 2.2, Lemmas 4.2–4.3 and Note 5.3; S2, Theorem 14.1] supplies the original integer weights, matched coefficient cycle, full joint complete-history prior, free initial value and independent absorbing bottom, immutable INITIAL pullback, first-zero loss, both literal alphabets and semantic/effective distinction. Here its source coordinates are exactly $(v,-j,s)$ in (82.17), its actions are the full words (82.20), (82.25) or (82.37), its observations are their completed endpoints, and its optimized resource is their worst actual emitted count. No source, action, INITIAL record, control operation or fee has been replaced.

[S10, Interface 2.1 and Lemma 3.2; S15, Section 1, Definition 1.1 and Proposition 4.2] supplies same-word arithmetic rows and inverse, the strict inherited-tail contract and the all-action common-tail bound. The generic source-specific response/seam certificate [S15, Theorem 3.3] does not assert (82.5) or dispense with checking the literal tail transfers. Lemma 82.2 proves the uniform bound for the specific consecutive paths at $k=m+1$, and (82.21) then discharges all those tail obligations simultaneously. The independent-row law [S15, Theorem 3.4; IC, Chapters 27 and 60–64] assumes $k\ge2m$, which fails here. It is not used as a safety premise.

[IC, Definition 29.1 and Theorem 29.2] supplies the exact preset join for different value fibres, including early stops and absorbing suffixes. It provides the ordered target $\Gamma$ without selecting a common optimum. [IC, Definitions 36.1–36.2 and Theorem 37.1] supplies the existing distinction between actual phase multiplicities, constant-label saturated codes and zero-sum code algebra. The full-cube XOR in (82.19) and the five-vector XOR in (82.33) are elementary instances of that established algebra, not new zero-sum spectrum claims. Its literal wide fee law [IC, Theorem 38.1] requires $m\ge k$ and the room condition $a+k+2\le m$; both are unavailable at $k=m+1$. It supplies no fee-$h$ realization of (82.15).

Chapters 79–80 and the saturation argument in Theorem 81.2 supply the compulsory-root and binary-capacity mechanisms used in the lower bound. Theorem 80.3 requires one positive even low class and identical value-fibre tables, not arbitrary joined parity profiles. Definition 81.1 and Theorem 81.2 require precisely three positive even joined classes with their specified root/missed-phase placements. At $h\ge4$ that old obstruction is recovered within the present criterion: its XOR forces the third code's root coordinate to be zero, and its remaining coordinates vanish at the prescribed missed phases, contradicting distinctness of the first two codes. This is credited overlap, not an added three-even-class theorem; Chapter 81's $h=3$ case retains its own proof. Neither theorem gives the automatic physical safety implication (82.21)–(82.22) for arbitrary even-class sets and placements.

Lemmas 73.3 and 73.5, Construction 73.4 and Theorem 73.6 supply the entire full-positive-child suffix used in both the $(h+1)$ GLOBAL fallback and the $(d+1)$ adaptive family attainment. Chapter 74 and Open Problem 75.3 supply their full-target connection at its stated fresh-label extensions. The fallback after a $2^h-1$-label child uses only that nonsaturated upper bound, not Chapter 74's power-of-two child equality. In the family each component child has exactly $2^d$ labels, and its two value-selected suffixes remain separate adaptive policies. The finite Hall theorem [H] is used only through the credited Chapter 73 selection, including its four-label alternative. Its pinned source and symbol are specified in Mathematical Citation 75.1; no new matching or generic optimizer theorem is claimed.

The mixed-tail companion [M, Definitions 1.1–1.3 and Theorem 2.1], the three-class companion [T3, Definition 1.2 and Theorem 2.1], and the four-label companion [F4, Definition 72.1 and Theorem 72.2] concern actual successful zero archives after an all-one root, their mixed-tail or homogeneous-band assumptions and their missed-set tests. The present full target forbids that root, and its joined low cycle has $2^h\ge16$ labels including outside. Their exact shallow fees and charged-run arguments are comparisons under different arrival contracts, not suppliers of (82.16).

The [phase-coherent full-tail minimax volume](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), Definitions 1.2–1.5, Theorem 2.1 and Sections 2.4 and 4, keeps one original random-depth source, paid Read letters, finite retained configurations and complete stopped-transcript conditional total-variation risk. Its legal same-update phase generators establish an attained prediction radius. No source/action/INITIAL/control/risk-to-emitted-fee bridge from that experiment to the original KBonacci reader is supplied or used. It therefore contributes no numerical fee or code-selection premise here.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), defines observations reaching test leaves, tests consistent with specified inputs/outputs and distinguishing graphs, and exhibits a system in which every possible first operation destroys a distinction needed for identification. Under the present correspondence an input is one complete literal block, an output is its completed scalar or bottom, and unequal immutable INITIAL labels require separation. That mature test framework supports the interpretation of destructive first operations; it does not state the consecutive-path bound (82.5), the saturated criterion (82.15), the original strict seam transfer or a KBonacci emitted-fee equality. No generic belief-game or distinguishing-graph restatement is counted as new fee content.

The added reader-specific ordinary mathematics is the sharp physical obstruction (82.5) with its all-one/zero/degenerate coverage, the automatic saturated-row safety implication (82.21)–(82.22), the resulting exact arbitrary-parity whole-target criterion (82.16), and the fully specified five-even-class pair/phase construction (82.27)–(82.33) realizing a compatible common stream at every $d\ge2$. The supplied capacity, join, parity algebra and fallback are explicitly reused. These are repo-derived deductions with scoped source and paper comparison; no exhaustive literature-absence or mathematical-priority claim is made. They are ordinary theory proofs, not Lean/kernel-certified declarations.

**边界 82.9（Scope, effectivity, resources and surviving original objective）。** The criterion law requires every condition in (82.10)–(82.12): depth $h\ge4$, odd $m\ge2^h-1$, original order $k=m+1$ and actual gcd one, exactly $2^h-1$ joined low classes, common fresh distinct $R,C$, the homogeneous high band and the explicit history pullback. It admits arbitrary repeated joined classes, arbitrary even-class sets and placements, and different component tables within that class. It replaces no arbitrary adaptive optimum with a joined optimum. For $h=3$, adjacent saturated coordinates supply only two distinct common-one classes, so the present safety proof does not apply; the already supplied Chapter 81 results retain their own narrower conditions.

For arbitrary semantic labels, existence or failure of (82.15) and the exact fee statement are set-theoretic. Effective selection requires a finite target-partition presentation or decidable equality on the finite label tables, as in [S1, Note 5.3]. With such input, one can form actual joined classes and multiplicities, test the finite code condition, invert a witnessing code or choose the credited fallback, and store its decoder. No polynomial selection bound, offline bit-complexity, input-acquisition cost or controller-memory optimum is asserted. Construction 82.5 gives a concrete finite table and common code for each parameter and needs no search to select its GLOBAL words. Offline selection is not an emitted fee.

Every attaining controller uses one free initial read and one subsequent read per actually emitted complete block. Its maximal paid read count equals the stated block fee; including the free read adds one. Root absorption still costs its whole issued block and all $m$ bits. Stops occur at complete endpoints and need no terminal repair. Known chronological indices determine relative windows, without exposing the source's unknown INITIAL history length. No observations are taken from stopped siblings, counterfactual actions or other sources.

The five-even family has exact block pair $(d+1,2d)$, difference $d-1$, and bit pair $(m(d+1),2md)$ at $m=2^{2d}+2d+1$. Its fifteen-joined-class anchor is not a three-even-class instance, and unbounded $d$ ranges over different finite readers and targets. No single stream for their union is asserted.

The original exact minimum worst-branch ACTUAL emitted-complete-block objective for every attainable immutable INITIAL target and all original $k\ge2,m\ge1$, separately for adaptive control and ONE GLOBAL preset stream per fixed target under both alphabets [IC, Definition 1.3 and Open Problem 9.1], remains unresolved. Other low-label counts, nonfresh or unequal high/outside labels, low-tail-dependent targets, even widths, other orders or gcds, arbitrary mixed acquired supports, competing roots outside this extension, adaptive prices for arbitrary component tables and history targets without supplied INITIAL factorization remain outside (82.16). No Lean, code delivery, compilation, ingestion, coverage, deposit or freezing accompanies this pure-theory chapter.

## 追加锚（本行以下为增补区）

## 83. Two even joined classes: safe unsaturated whole-target attainment

The full low cycle in this chapter has $2^h-1$ joined labels, one fewer than the saturated cycle of Chapter 82. Its two positive even classes permit a code with exactly one omitted vector. Root constraints, chronological missing coordinates and even full rows alone do not make every such code physically safe at $h=4$. The selection below omits a unit vector instead. This preserves at least four actual common charged phases at every consecutive boundary, while meeting all accumulated label restrictions. It gives an exact whole-target GLOBAL fee for arbitrary different component tables in the stated two-even class.

**定义 83.1（The original full target and the two-even unsaturated domain）。** Use the original integer weights, matched $V_k\bmod2$ reader, joint complete-history prior, record updates and complete-block fees of [IC, Definitions 1.1–1.3 and Interface 1.4]. Fix

$$
h\ge4,\qquad N=2^h,\qquad m\ge N-1\text{ odd},\qquad
k=m+1,\qquad T=m+2,\qquad \gcd(m,T)=1.
\tag{83.1}
$$

Let $A=\{0,\ldots,m\}$, $z=m+1$, and let $\lambda_0,\lambda_1:A\to Y$ be finite tables with arbitrary repetitions. Set

$$
\Gamma(j)=(\lambda_0(j),\lambda_1(j)),\qquad
\mathcal J=\Gamma[A],\qquad |\mathcal J|=N-2.
\tag{83.2}
$$

For $D\in\mathcal J$, let $n_D=|\Gamma^{-1}(D)|$. Exactly two classes, denoted $U,V$, have positive even $n_D$; every other $n_D$ is odd. These are multiplicities of ordered joined phase classes in one actual table, rather than separate component multiplicities.

Choose common distinct $R,C$ fresh relative to both component images. The entire immutable INITIAL target is

$$
\begin{aligned}
f(v,-j,s)&=
\begin{cases}
R,&s=m,\\
\lambda_v(j),&0\le s<m,\ j\in A,\\
C,&0\le s<m,\ j=z,
\end{cases}
&&v\in\mathbb F_2,\\
f(\bot)&=L_\bot,&&F(w)=f(q_{\rm INITIAL}(w)).
\end{aligned}
\tag{83.3}
$$

The label $L_\bot$ is arbitrary and independent, including possible coincidences with other labels. The history pullback in (83.3) is part of the target. It is never reevaluated on a later record. Put

$$
\widehat C=(C,C),\qquad
L=\mathcal J\cup\{\widehat C\},\qquad
\Lambda(j)=\begin{cases}\Gamma(j),&j\in A,\\\widehat C,&j=z.\end{cases}
\tag{83.4}
$$

Thus $|L|=N-1$, the outside class has multiplicity one, and the only even classes on the full low cycle are $U,V$.

Index literal words by their actual issued indices $t=0,1,\ldots$. Coordinates of an $h$-bit code are also numbered $0,\ldots,h-1$; let $\varepsilon_i$ be their unit vectors. Since $m\equiv-2\pmod T$, the path $W_t=[tm,(t+1)m]\pmod T$ misses only

$$
e_0=z,\qquad e_t=m+1-2t\quad(1\le t<h).
\tag{83.5}
$$

The latter phases are distinct members of $A$, separate from $0,1,z$: $e_{h-1}\ge N-2h+2\ge10$ at $h=4$, and the bound increases with $h$. A phase calculation uses known issued indices, without reading the unknown INITIAL history length.

Both alphabets contain all width-$m$ words since $m<k$. Only completed endpoints are observed. Every issued word costs one full block and $m$ emitted bits, including waits, padding, repair and a word absorbed before its endpoint. GLOBAL means ONE preset literal stream for this fixed target, on both free INITIAL values and all actual sources, with source-owned endpoint stopping and decoding. There is no reset, copy, intermediate read, hidden INITIAL clock or borrowed sibling observation.

**引理 83.2（Simultaneous root and missing-coordinate selection with a unit omission）。** Under Definition 83.1 there are an index $r\in\{1,\ldots,h-1\}$ and an injection

$$
c:L\longrightarrow\mathbb F_2^h\setminus\{\varepsilon_r\}
\tag{83.6}
$$

onto that set, satisfying

$$
\begin{aligned}
c(U)\oplus c(V)&=\varepsilon_r,\\
c_0(\widehat C)&=0,\qquad
c_0(\Gamma(0))=c_0(\Gamma(1))=1,\\
c_t(\Gamma(e_t))&=0\quad(1\le t<h).
\end{aligned}
\tag{83.7}
$$

In particular the omission never has two adjacent coordinates equal to one. Repeated classes accumulate every displayed restriction.

证明。 Let $K=\{\Gamma(0),\Gamma(1)\}$ be the set of root-positive classes. It has one or two members, none equal to $\widehat C$. For each $D\in L$ put

$$
Z_D=\{t:1\le t<h,\ \Gamma(e_t)=D\},\qquad
F_D=\{1,\ldots,h-1\}\setminus Z_D.
\tag{83.8}
$$

The sets $Z_D$ are pairwise disjoint and partition the suffix-coordinate set. In particular $Z_{\widehat C}=\varnothing$. Before reserving vectors, the list for $D$ consists of all $y\in\mathbb F_2^h$ with $y_t=0$ for $t\in Z_D$, additionally $y_0=1$ for $D\in K$, and $y_0=0$ for $D=\widehat C$.

First reserve the codes of $U,V$ and the omitted vector. Suppose no $D\in K\setminus\{U,V\}$ has $F_D=\varnothing$. Exclude from the choice of $r$ the unique member of $F_D$ whenever such a $D$ has $|F_D|=1$. There are at most two excluded coordinates and $h-1\ge3$ choices, so choose a remaining $r$. At most one of $U,V$ owns the coordinate-$r$ zero restriction. Interchange their names if needed so that $r\notin Z_V$, and reserve

$$
a=\varepsilon_r,\qquad
c(U)=\varepsilon_0,\qquad
c(V)=\varepsilon_0\oplus\varepsilon_r.
\tag{83.9}
$$

These codes satisfy all restrictions on these two classes, including either root-positive requirement. Their XOR is $a$. Each remaining root-positive list remains nonempty after reservation: its root-one subcube has $2^{|F_D|}$ vectors; if $|F_D|=1$, the choice of $r$ prevents both its vectors from being reserved; if $|F_D|\ge2$, removal of two vectors cannot empty it.

The other case is a $D\in K\setminus\{U,V\}$ with $F_D=\varnothing$. It owns every suffix zero restriction, so neither even class owns any, and any other root-positive class owns none. Choose distinct $p,r\in\{1,\ldots,h-1\}$ and reserve

$$
a=\varepsilon_r,\qquad
c(U)=\varepsilon_0\oplus\varepsilon_p,\qquad
c(V)=\varepsilon_0\oplus\varepsilon_p\oplus\varepsilon_r.
\tag{83.10}
$$

Again the two reserved class codes satisfy all their restrictions and have XOR $a$. The root-positive class owning every zero restriction retains $\varepsilon_0$. Any other remaining root-positive class has the whole root-one half cube before removal of two vectors and therefore retains a vector. This case includes all possible exhausted suffix restrictions, rather than assuming that every root-positive class has a free suffix coordinate.

In either case set

$$
Q=\mathbb F_2^h\setminus\{a,c(U),c(V)\},\qquad
\mathcal A_D=\{y\in Q:y\text{ satisfies the restrictions of }D\}
\quad(D\in L\setminus\{U,V\}).
\tag{83.11}
$$

The three deleted vectors are distinct; none is zero, the two reserved class vectors have root coordinate one, and $a$ has root coordinate zero. Thus $|Q|=N-3$, equal to the number of remaining classes. Every non-root-positive list contains zero, including the outside list, and the preceding reservation argument proves that every remaining root-positive list is nonempty.

We verify the union inequalities for the finite Hall theorem [H]. A subfamily containing a list equal to $Q$ has union size $N-3$, at least its number of classes. Otherwise every member owns a restriction. There are at most $h+2$ such classes: at most two root-positive owners, the outside owner, and $h-1$ suffix zero occurrences. Let $q$ be the subfamily size.

For $q=0,1$ the assertion is immediate from the nonemptiness just proved. For $q=2$ with one root-positive and one non-root-positive member, a root-one representative of the former and zero in the latter are distinct. If both are non-root-positive, zero and every $\varepsilon_i$ with $1\le i<h$, $i\ne r$, belong to the union: a suffix coordinate has only one zero owner and cannot be forbidden on both lists; all these vectors remain in $Q$. If both are root-positive, their zero-owner sets are disjoint. One has at most $\lfloor(h-1)/2\rfloor$ zero coordinates, hence a root-one subcube with at least

$$
2^{h-1-\lfloor(h-1)/2\rfloor}\ge4
\tag{83.12}
$$

vectors. At most two root-one vectors were deleted, so its remaining list alone has at least two. This proves every two-list inequality.

For $q=3$, each of the $h$ root-one vectors

$$
\varepsilon_0,\quad \varepsilon_0\oplus\varepsilon_i
\quad(1\le i<h)
\tag{83.13}
$$

is forbidden on at most two classes: the outside class and at most one suffix zero owner. Every such vector still in $Q$ therefore belongs to the three-list union. Reservation (83.9) deletes two of them, leaving $h-2$; zero is also in the union because only the at most two root-positive classes forbid it. This gives $h-1\ge3$ vectors. Reservation (83.10) deletes only one vector of (83.13), leaving $h-1\ge3$ directly.

For $q\ge4$, consider all vectors with root coordinate zero and suffix weight at most one, together with all vectors with root coordinate one and suffix weight at most two. A vector in the first set violates restrictions on at most three classes: at most two root-positive owners and one suffix zero owner. A vector in the second set also violates at most three: outside and at most two suffix zero owners. Every such vector in $Q$ therefore belongs to the union. Their number after removal is at least

$$
2h+\binom{h-1}{2}-3\ \ge\ h+2\ \ge\ q
\qquad(h\ge4).
\tag{83.14}
$$

The first inequality already holds at $h=4$, where its left side is eight; its difference from $h+2$ increases thereafter. These cases prove every Hall inequality, including arbitrary identifications among the restriction owners.

Apply the credited finite Hall distinct-representative theorem to (83.11). It assigns the remaining classes different vectors in $Q$, necessarily exhausting $Q$. Add the reserved codes. The resulting injection exhausts the cube except $a=\varepsilon_r$, and (83.7) holds. The finite matching theorem is reused; the reservation, accumulated-constraint inequalities and unit omission are the reader-specific selection proved here. ∎

**定理 83.3（Exact whole GLOBAL price of every target in the two-even class）。** For every target of Definition 83.1, under both original literal alphabets,

$$
\boxed{C_{\rm pre}(f)=C_{\rm pre}(F)=h.}
\qquad
\boxed{\text{Exact worst emitted-bit fee}=mh.}
\tag{83.15}
$$

One selected code from Lemma 83.2 gives a single actual $h$-block attaining stream for both free-value fibres and all actual sources. The statement asserts existence of a safe selection, without asserting safety of every injective algebraic witness.

证明（joint sources and all-action lower bound）。 All records in (83.3) are jointly actual by [IC, Convention 1.2; S1, Convention 1.3]. Explicitly choose arbitrarily large $\ell$ with

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad
\ell\ge s+2,
\qquad
\eta=\bigoplus_{i=\ell-s}^{\ell-1}\gamma_i,
\qquad
w(v,j,s)=(v\oplus\eta)0^{\ell-s-1}1^s,
\tag{83.16}
$$

where $\gamma_i=\mathbf1_{\{0,T-1\}}(i\bmod T)$ is the actual coefficient cycle [S2, Theorem 14.1]. Actual gcd one gives the compatible lengths. The first bit compensates the scalar contribution of the final run, the separating zero makes that run exactly $s<k$, and the length gives phase $-j$. This same legal history realizes value, phase and tail together and splits into complete source blocks under either alphabet. Initial bottom is realized by the two complete words $1^m|1^m$, whose seam rejects. None of these unobserved lengths is a control input.

At every phase and either free INITIAL value, the actual tails $m-1,m$ have different labels: a low label and fresh $R$. No controller can stop freely on that value fibre. A root starting zero merges this pair at its first bit with identical scalar and phase. A root with at least two leading ones, including the all-one word, rejects both before its first endpoint and leaves both permanently absorbed. These losses are irreversible [S1, Lemmas 4.2–4.3; S15, Proposition 4.2]. Consequently every correct root, under arbitrary later words and stopping rules, begins $10$.

Every such root rejects exactly the high band $s=m$. Every low source survives its leading one, reaches its second-bit zero and completes safely; same-phase low-tail mergers preserve the label because (83.3) is tail-independent there. After the root all low sources have the common actual terminal tail of that word. Within an acquired successful output archive they also have a common scalar. Every later complete literal word then either succeeds on the whole archive or rejects the whole archive, because rejection depends on their common tail and the issued bits [S10, Lemma 3.2]. On success there are at most two scalar endpoints, each again with common tail and scalar. Uniform rejection cannot resolve a nonconstant archive, because all later outputs remain bottom. A homogeneous archive may stop at its endpoint. Hence any such archive with $a$ remaining paid blocks can resolve at most $2^a$ different labels. This counts all legal words, all-one words, zero waits, padding, repairs, attempted rejection and endpoint stops.

For the GLOBAL lower bound apply exactly the preset value-join law [IC, Definition 29.1 and Theorem 29.2]. The full joined target has high label $(R,R)$, low table $\Lambda$ and independent initial bottom; its preset fee equals that of $f$. This law operates on the same actual emitted stream, using the value-complement symmetry of the acquired endpoint archive. It performs no copied experiment and borrows no sibling observation.

On either fixed scalar fibre of this joined target there are $N-1$ actual low labels. Its forced root has at most two successful children, and the preceding all-action bound gives at most $2^H$ low-label leaves at total worst fee $H$. Therefore

$$
N-1=2^h-1\le2^H,\qquad H\ge h.
\tag{83.17}
$$

The joined lower bound covers even adaptive choices on the joined target; its transfer to the original two-component target uses only the preset join law. It makes no claim that the arbitrary component adaptive optimum equals $h$.

证明（the selected one-stream attainment and strict physical seams）。 Choose $c$ as in Lemma 83.2. The XOR of the full $h$-cube is zero, since each coordinate has the even number $2^{h-1}$ of ones. Omitting $a=\varepsilon_r$ gives $\bigoplus_{D\in L}c(D)=a$. On the full low phase cycle only $U,V$ have even multiplicity, so

$$
\bigoplus_{j=0}^{m+1}c(\Lambda(j))
=\left(\bigoplus_{D\in L}c(D)\right)
       \oplus c(U)\oplus c(V)
=a\oplus a=0.
\tag{83.18}
$$

Thus each coordinate row $\chi_t(j)=c_t(\Lambda(j))$ has even total charge. It is zero at the sole missing phase of its actual path by (83.7). The supplied original literal inverse [IC, Interface 1.4; S10, Interface 2.1; Definition 82.1] therefore gives the complete words

$$
B_{t,i}=\bigoplus_{b=0}^i
 c_t(\Lambda(tm+b\bmod T)),
\qquad 0\le t<h,\quad0\le i<m.
\tag{83.19}
$$

Issue the one preset stream $B_0|\cdots|B_{h-1}$. Its first two bits are $1,0$ by the root restrictions. It has precisely the high-band rejection and low-tail preservation proved above. Every word has exactly $m$ bits and is internally legal since $m<k$.

For each $1\le t<h$, the cube has exactly $2^{h-2}$ vectors whose coordinates $t-1,t$ are both one. The omitted unit $a$ is none of them. All these vectors are therefore assigned to distinct classes of the actual low cycle. Each class has at least one actual phase, with disjoint supports for different classes. It follows that the full arithmetic rows of these very consecutive words satisfy

$$
\bigl|\{j:\chi_{t-1}(j)=\chi_t(j)=1\}\bigr|
\ge2^{h-2}\ge4.
\tag{83.20}
$$

Inductively suppose the preceding words have succeeded on a low source. At $k=m+1$ its current tail is $\rho(B_{t-1})$, including the all-one case: success of an all-one width-$m$ word forces incoming tail zero and leaves tail $m$. If the next boundary rejected, Lemma 82.2 would put at most three phases in the intersection in (83.20). This contradiction gives the actual strict seam inequality

$$
\rho(B_{t-1})+\alpha(B_t)<m+1=k
\quad(1\le t<h).
\tag{83.21}
$$

Thus every low source succeeds on the entire concatenation. This argument checks the literal words in (83.19), including boundaries with two adjacent one bits; it adds no clearing, waiting, repair or padding block. Its four-class margin includes $h=4$ because the single omitted vector has no adjacent ones.

The complete stopping rule is explicit. Initial bottom returns $L_\bot$ at the free read. High tails return $R$ at the completed root endpoint and stop; that whole root, including its absorbed suffix, has been issued and paid. All low sources, including phase $z$, issue all $h$ words. Their own successive scalar endpoints give

$$
(v_1\oplus v_0,\ldots,v_h\oplus v_{h-1})=c(\Lambda(j)).
\tag{83.22}
$$

Use the inverse injection to recover the joined label. Return $C$ for $\widehat C$ and otherwise the component selected by the remembered free INITIAL value $v_0$. This is a decoder of one actual archive, without a phase read or another source's outputs. Actual low histories in (83.16) pay exactly $h$ full words under this rule. Final-endpoint stopping needs no cleanup.

The lower bound and this attainment prove the record equality. Explicit factorization (83.3), record-sufficient control evolution and the joint realizations (83.16) give the same history price [S1, Proposition 2.2]. Since each actually issued word emits $m$ bits, the exact worst emitted-bit fee is $mh$. ∎

**命题 83.4（Algebraic witnesses need not be safe at four coordinates）。** Within Definition 83.1 at $(h,m,k,T)=(4,15,16,17)$, there is an injective label-constant four-coordinate code with even full rows, all root and chronological missing-coordinate restrictions, and $c(U)\oplus c(V)$ equal to its omitted vector, whose inverse rejects at the second emitted block. Both successful root children are nonconstant.

证明。 Take distinct component names $A_b,D_b$ for the nonzero bit strings $b$ below, with disjoint component alphabets. For $j\in A$ prescribe $\Gamma(j)=(A_{b(j)},D_{b(j)})$, assign that class code $b(j)$, and assign outside $\widehat C$ code $0000$. The full table is

$$
\begin{array}{c|rrrrrrrrr}
j&0&1&2&3&4&5&6&7&8\\\hline
b(j)&1000&1000&1001&1010&1011&0001&1101&1110&0100
\end{array}
\tag{83.23}
$$

$$
\begin{array}{c|rrrrrrrr}
j&9&10&11&12&13&14&15&16\\\hline
b(j)&0101&0110&0111&0100&0010&0011&1111&0000
\end{array}
\tag{83.24}
$$

There are fourteen positive joined classes. Exactly $1000$ and $0100$ have multiplicity two; all others have multiplicity one. The only omitted vector is $1100=1000\oplus0100$, so the full phase XOR is zero. The root conditions hold at phases $0,1,16$. At the missed phases $e_1=14,e_2=12,e_3=10$, the required coordinates of $0011,0100,0110$ are respectively zero. Thus every prescribed row is an available even full row.

Direct application of the same original inverse (83.19) to its first two rows gives

$$
B_0=1010110\,1^8,
\qquad B_1=1^8\,0101010.
\tag{83.25}
$$

Both words have fifteen bits. The root begins $10$, succeeds on every low source and has terminal tail eight. Its two successful difference children have respectively eight and seven distinct low joined labels; in this construction each component also separates those labels. Neither child can stop correctly at the root. The next word has leading run eight, so every continuing low source reaches

$$
8+8=16=k
\tag{83.26}
$$

and is absorbed during $B_1$. Subsequent endpoints cannot recover the lost labels. Both full words are paid, including the unobserved absorbed part of $B_1$. The common charged phases of the first two arithmetic rows are exactly $\{6,7,15\}$, consistent with the sharp three-phase bound of Lemma 82.2. These are arithmetic design rows; the rejecting block produces bottom, not its putative scalar difference.

This disproves all-witness safety in the unsaturated class. It does not contradict Theorem 83.3, whose selected witness omits a unit vector and therefore retains the fourth common charged class at this boundary. ∎

**构造 83.5（A uniformly inhabited different-value family at minimal odd width）。** For every integer $d\ge2$, put

$$
h=2d,\qquad N=2^{2d},\qquad m=N-1,\qquad k=N,\qquad T=N+1.
\tag{83.27}
$$

Use the ordered $d$-bit set $I=\mathbb F_2^d$. Choose distinct labels $A_i$ and $D_\ell$ with disjoint alphabets, and fresh common distinct $R,C$. Concatenate $(i,\ell)$ as an $h$-bit word, with coordinate zero the first row coordinate. Exclude the pairs whose concatenated words are $0$ and $a=\varepsilon_{h-1}$, and write

$$
\mathcal P=\mathbb F_2^h\setminus\{0,a\},\qquad
\nu=\varepsilon_0,\qquad w=\varepsilon_0\oplus\varepsilon_{h-1}.
\tag{83.28}
$$

Both $\nu,w$ belong to $\mathcal P$. Let $\sigma$ be the fixed-point-free cyclic permutation of $\{1,\ldots,h-2\}$ given by

$$
\sigma(t)=t+1\ (1\le t<h-2),\qquad \sigma(h-2)=1.
\tag{83.29}
$$

Prescribe the phase-pair code table $G:A\to\mathcal P$ by

$$
\begin{aligned}
G(0)&=\nu,&G(1)&=w,&G(2)&=w,&G(e_{h-1})&=\nu,\\
G(e_t)&=\varepsilon_{\sigma(t)}&&&&(1\le t\le h-2).
\end{aligned}
\tag{83.30}
$$

Assign all remaining members of $\mathcal P$ once each to the remaining phases in increasing binary/phase order. For $G(j)=(i,\ell)$ set

$$
\lambda_0(j)=A_i,\qquad\lambda_1(j)=D_\ell,
\tag{83.31}
$$

and use the entire target and history pullback (83.3), with arbitrary independent $L_\bot$.

证明（inhabitation, parity and a specified common code）。 All prescribed phase positions in (83.30) are distinct. The least missed phase is $N-2h+2\ge10$, so none conflicts with $0,1,2$. The units $\varepsilon_{\sigma(t)}$ exhaust $\varepsilon_1,\ldots,\varepsilon_{h-2}$, hence are distinct and different from $0,a,\nu,w$. There are $h+2$ prescribed positions using $h$ different pairs: $\nu,w$ each twice and the $h-2$ units once. The number of remaining positions is $N-h-2$, equal to the number of unused pairs in $\mathcal P$. The ordered bijection is therefore well defined.

The table has exactly $N-2$ joined classes, exactly two with positive even multiplicity, namely the pairs of $\nu,w$, each with two phases. Every other class has one. Each component has all $r=2^d$ labels: the excluded pairs are $(0,0)$ and $(0,(0^{d-1},1))$ in row/column coordinates. Row zero retains $r-2>0$ pairs and every other row retains $r$; each of those two columns retains $r-1>0$ pairs and all other columns retain $r$. Thus the component tables are genuinely different, with exactly $2^d$ labels per fibre. This is one jointly inhabited phase table, rather than two separately realized marginals. Formula (83.16) realizes every required value, phase and INITIAL tail together. The width is odd and actual gcd is $\gcd(N-1,N+1)=1$.

Assign to each joined class its concatenated pair code, and put $c(\widehat C)=0$. The image is exactly $\mathbb F_2^h\setminus\{a\}$, with $c(U)=\nu$, $c(V)=w$ and $\nu\oplus w=a$. Both root phases have coordinate zero one, and outside has coordinate zero zero. For $t\le h-2$, the missed phase has code $\varepsilon_{\sigma(t)}$, whose coordinate $t$ is zero because $\sigma(t)\ne t$. The last missed phase has code $\nu$, whose last coordinate is zero. Every clause of (83.7) therefore holds for this explicit code. The words (83.19) with this table are a fully specified common stream for every $d$, with strict seams supplied by (83.20)–(83.21). No code search is needed for this family. ∎

**定理 83.6（Exact adaptive/GLOBAL pair of the different-value family）。** Construction 83.5 satisfies, under both original alphabets,

$$
\boxed{
C_{\rm ad}(f)=C_{\rm ad}(F)=d+1,\qquad
C_{\rm pre}(f)=C_{\rm pre}(F)=2d.
}
\tag{83.32}
$$

The exact worst emitted-bit pair is $(m(d+1),2md)$ at $m=2^{2d}-1$. The adaptive child fee and suffix are supplied by Chapter 73; the new whole-target content is safe GLOBAL attainment at $2d$ for the two-even unsaturated table.

证明（all-action adaptive lower bound and the supplied physical attainment）。 Fix either free INITIAL value. Its component table has $r=2^d$ labels, plus fresh $C$ on the outside low phase. These $r+1$ low labels all have actual sources. The low/high-tail pair forces a $10$ root, as in the lower-bound proof of Theorem 83.3, independently of any value-dependent root choice. The successful common-tail binary bound for every literal continuation and endpoint stop gives $r+1\le2^H$ at total worst fee $H$. Since $r+1>2^d$, every correct adaptive controller has $H\ge d+1$. This covers all literal words, waits, repairs, uniform rejection and early homogeneous stopping.

For attainment remember the free INITIAL value $v$ and issue the actual alternating root

$$
P_m=(10)^{(m-1)/2}1.
\tag{83.33}
$$

Initial bottom has stopped freely. Root bottom returns $R$ after that full paid word. The successful outside phase has difference zero and returns $C$ at the same endpoint. Its other successful child is precisely the actual full positive window $A$ of Definition 73.1, with common current scalar, terminal tail one and component INITIAL table $\lambda_v$. It has $r$ labels. Lemmas 73.3 and 73.5, Construction 73.4 and Theorem 73.6 supply a lawful fixed $d$-word suffix for this one child.

To specify those physical words, let $b^{(v)}:\lambda_v[A]\to\mathbb F_2^d$ be the credited Chapter 73 selection, with coordinates $q=1,\ldots,d$. For $j\in A$ put $\psi_q^{(v)}(j)=b_q^{(v)}(\lambda_v(j))$, and prescribe the already stopped outside phase and the actual suffix inverse by

$$
\psi_q^{(v)}(z)=\bigoplus_{j\in A}b_q^{(v)}(\lambda_v(j)),
\qquad
S^{(v)}_{q,i}=\bigoplus_{b=0}^i
 \psi_q^{(v)}(qm+b\bmod T),\qquad0\le i<m.
\tag{83.34}
$$

The selected code is zero in coordinate $q$ at the missing phase $m+1-2q$, and in its first coordinate at phase $m$. The compensation in (83.34) makes each full row even; it is a design bit of this word, without an observation on outside. In the ordinary list choice, the Chapter 73 restrictions put a zero among the two adjacent literal boundary bits of every subsequent suffix seam. The first suffix begins zero and clears the actual root tail one. At $d=2$, if the four specified labels of (73.7) are distinct, use exactly the supplied alternative (73.8); its only relaxed suffix seam has terminal run one and leading run two, giving $3<k$ here. These are the two credited physical cases, and together cover this family at every $d\ge2$.

Every root-positive source issues $P_m|S_1^{(v)}|\cdots|S_d^{(v)}$, obtains its code from its own suffix endpoint differences and returns its immutable component label. Every word is complete and paid, all seams are strict, and no terminal clearing word is needed. The selected suffix depends on the remembered free INITIAL value, not a newly interpreted current value. These are lawful separate adaptive policies. The attainment costs exactly $d+1$ on actual positive sources, matching the all-action lower bound.

The explicit common code of Construction 83.5 is instead used in (83.19). Theorem 83.3 gives its GLOBAL fee $h=2d$, using the same stream on both values, with all outside sources continuing to the final decoder and all high sources stopping after the paid rejecting root. This is not a concatenation or maximum of the two adaptive suffix optima. The supplied history factorization gives both history equalities. Multiplication by the actual width gives the bit pair. ∎

**实例 83.7（The safe depth-four consumer on the original reader）。** At $d=2$, $h=4$, $m=15$, $k=16$, $T=17$, the full phase-code table of Construction 83.5 is

$$
\begin{array}{c|rrrrrrrrr}
j&0&1&2&3&4&5&6&7&8\\\hline
c(\Lambda(j))&1000&1001&1001&0011&0101&0110&0111&1010&1011
\end{array}
\tag{83.35}
$$

$$
\begin{array}{c|rrrrrrrr}
j&9&10&11&12&13&14&15&16\\\hline
c(\Lambda(j))&1100&1000&1101&0100&1110&0010&1111&0000
\end{array}
\tag{83.36}
$$

The first two digits select the row label, the last two the column label; $0000$ is the fresh outside class. The omitted vector is $0001$. Inverting at the actual starts $0,15,13,11\pmod{17}$ gives the one GLOBAL stream

$$
\begin{aligned}
B_0&=101111101010011,\\
B_1&=111111010001101,\\
B_2&=101111100101000,\\
B_3&=111100010100110.
\end{aligned}
\tag{83.37}
$$

Every word has fifteen bits. The successive pairs of preceding terminal run and next leading run are $(2,6),(1,1),(0,4)$, with seam sums $8,2,4$, all strictly less than sixteen. Every low source emits these four complete words and uses only its own endpoints to recover (83.35)–(83.36); high tails are absorbed on the root's first bit but still emit and pay that full root. Initial bottom stops freely. The exact adaptive/GLOBAL block pair is $3/4$ and the emitted-bit pair is $45/60$. This instance displays the uniform selected attainment; the counterexample (83.23)–(83.26) uses the same reader parameters but a different table and unsafe algebraic witness.

**数学引文 83.8（Exact overlap, source correspondence and the added fee content）。** The source of the reader and cost contract is [IC, Definitions 1.1–1.3, Convention 1.2 and Interface 1.4], with its cited original suppliers [S1, Definitions 1.2–2.1, Convention 1.3, Proposition 2.2, Lemmas 4.2–4.3 and Note 5.3; S2, Theorem 14.1; S10, Interface 2.1 and Lemma 3.2; S15, Section 1, Definition 1.1 and Proposition 4.2]. The relevant published continuation through Chapter 82 is [this volume at revision e3c880e657540852538de79ab2ec2553a9bd3d49](https://github.com/the-omega-institute/trureturing/blob/e3c880e657540852538de79ab2ec2553a9bd3d49/docs/develop/theory/KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md). The source equations are not replaced.

The correspondence is literal: original sources are the single histories (83.16), their INITIAL records are $(v,-j,s)$, their target is exactly (83.3), actions are the complete words (83.19), (83.33) or (83.34), observations are those actions' completed scalar or bottom endpoints, and the resource is the worst number of those actual emitted words. The actual coefficient period is $T=k+1$, the actual gcd is one, and the histories, phase and tail are jointly realized. Compensating a design row is not a control operation, source answer or extra read.

[IC, Definition 29.1 and Theorem 29.2] supplies the preset value join, including arbitrary stops and absorbed suffixes. It provides no choice of a safe common optimum. [IC, Definitions 36.1–36.2 and Theorem 37.1] supplies the established distinction between actual multiplicities and constant-label code algebra; the elementary XOR identity (83.18) is consistent with that algebra. Its wide literal realization [IC, Theorem 38.1] needs $m\ge k$ and the room-qualified common cut, both unavailable here. The critical-width parity spectra in [IC, Chapters 46–47] have $m=k$ and their own two-child aggregate constraints. None supplies the root/missing-coordinate selection (83.9)–(83.14) at $k=m+1$.

The original acquisition Lean sources `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.lean`, `original_cost_lower` and its local proof suppliers, and `NarrowWindowCost.lean`, `narrow_window_cost`, supply different statement shapes: a first-window/binary lower bound and a noncoprime monochromatic scan law with $g\ge2$, respectively. They do not supply a two-even, coprime, one-GLOBAL-stream attainment. No compilation, exact Lean application or kernel certification is claimed for the present ordinary proof.

Chapter 73 supplies finite Hall-based positive-child selection, its strict literal suffix and the exact additional child fee, including the four-label exception. Chapter 74 supplies the full-source connection at its fresh-label extension. Their consumption in the adaptive part of Theorem 83.6 is credited reuse. Chapter 80 has one even low class, a saturated full low-label set and its additional placement condition. Chapter 81 has three even classes and the stated saturated placement obstruction. Chapter 82 has $N-1$ joined classes on $A$, hence $N$ labels on the full low cycle. Its automatic safety proof uses all $N$ cube vectors. Here $A$ instead has $N-2$ joined classes and the cycle has $N-1$ labels, so none of those numerical whole-target laws applies directly. Lemma 82.2 is reused in its exact original domain, as the sharp upper bound of three common charged phases at a rejecting consecutive seam. Lemma 83.2 supplies the missing safe selection; Proposition 83.4 explains why the saturated all-witness conclusion cannot simply be copied.

The finite Hall distinct-representative theorem is the existing [H], pinned mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`, `Mathlib/Combinatorics/Hall/Finite.lean`, theorem `Finset.all_card_le_biUnion_card_iff_existsInjective'`. It is applied to the $N-3$ remaining class lists (83.11). The reservation and every union inequality are proved here. No new generic matching theorem, generic response/seam certificate or Bellman reformulation is counted as fee content.

The related mixed-tail, three-class and four-label root-zero volumes [M, Definitions 1.1–1.3 and Theorem 2.1; T3, Definition 1.2 and Theorem 2.1; F4, Definition 72.1 and Theorem 72.2] use successful archives acquired after an all-one root, with their own mixed-tail and missed-set contracts. The fresh low/high target (83.3) excludes that root. Their shallow fees do not price this two-even cycle. The [phase-coherent full-tail minimax volume](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), Definitions 1.2–1.5 and Theorem 2.1, fixes one random-depth source, paid Read letters, complete stopped-transcript laws and conditional total-variation prediction risk. Its same-update generation compatibility has no supplied source/action/INITIAL/control/risk-to-emitted-block-fee correspondence with this deterministic original reader. No numerical fee or code-selection premise is imported from it.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), supplies the mature distinction between legal tests, their actual leaf-reaching observations and simultaneous state distinction; Figure 3 exhibits the destruction of a necessary distinction by each possible first operation. Here one input is one issued complete word and one output is its completed scalar or bottom, while unequal immutable INITIAL labels must remain distinguishable. That comparison does not supply the KBonacci code reservation, strict tail transfer, selection theorem or emitted-fee equality. Finite distinct representatives are credited to [H]; no external zero-sum spectrum or general state-identification algorithm is needed for the new attainment.

The added ordinary reader-specific content is the uniformly selected unit-omission code with every root and missed-phase restriction, its safe physical realization at exactly $h$ fully paid blocks for every table in Definition 83.1, the concrete all-witness-safety counterexample, and the explicit different-value two-even family at $m=2^{2d}-1$ with safe common $2d$-block attainment. The join, binary capacity, arithmetic inverse, three-phase rejecting-seam bound and adaptive child price are reused under their exact hypotheses. These are repo-derived deductions with a scoped source and paper comparison, without exhaustive literature-absence or priority claims.

**边界 83.9（Effective presentation, exact resources and the remaining original objective）。** Theorem 83.3 requires every clause of Definition 83.1: $h\ge4$, odd $m\ge2^h-1$, original $k=m+1$, actual gcd one, exactly $2^h-2$ ordered joined classes on $A$, precisely two positive even classes with all others odd, common fresh distinct $R,C$, low-tail independence, the homogeneous high band and the explicit immutable history pullback. It permits arbitrary placements, positive even multiplicities, other odd multiplicities and different component tables within that domain. It does not classify the adaptive optimum of arbitrary component tables.

For arbitrary semantic labels the selection and price are set-theoretic existence statements. With a finite target-partition presentation or decidable equality on the finite tables, the selection is effective [S1, Note 5.3]: form the actual joined classes and restriction owners, make reservation (83.9) or (83.10), select finite distinct representatives in (83.11), invert the actual rows and store the code decoder. Construction 83.5 instead specifies its finite table and common code by formulas and ordered bijection. Neither description claims polynomial offline complexity, input-acquisition cost or optimal controller memory; offline selection does not issue a paid block.

The GLOBAL attainment observes one free initial output and exactly one completed endpoint per issued word. Every low source in the displayed rule has $h$ paid endpoint reads and emits $mh$ bits; including the free read gives $h+1$ observations. High tails emit the whole root and stop at its first paid endpoint even though absorption occurs on its first bit. All sources stop at complete endpoints, with no final repair. The adaptive family has $d+1$ worst paid endpoints, while GLOBAL has $2d$; their exact bit pair and difference are $(m(d+1),2md)$ and $m(d-1)$. The free value chooses an adaptive suffix but does not choose a GLOBAL stream. Different fixed targets may have different selected streams.

The result does not imply an arbitrary-parity cardinality theorem, a fee law at $k=m+2$ or $k=m+3$, or a generic safety certificate. Proposition 83.4 excludes the stronger all-witness-safety claim even at $h=4$. Other joined counts or parity profiles, nonfresh or unequal high/outside labels, low-tail-dependent tables, even widths, other orders and gcds, arbitrary acquired mixed supports, competing roots outside (83.3), and history targets without the supplied INITIAL factorization remain outside this equality.

The original exact minimum worst-branch ACTUAL emitted-complete-block fees for every attainable immutable INITIAL target and all original $k\ge2,m\ge1$, separately for adaptive control and ONE GLOBAL preset stream per fixed target under both alphabets [IC, Definition 1.3 and Open Problem 9.1], remain unresolved. The unbounded consumer parameter ranges over different finite readers and targets, rather than one stream for their union. All proofs here are ordinary mathematics, without Lean/kernel certification; no compilation, ingestion, coverage, deposit or freezing is asserted.

## 追加锚（本行以下为增补区）
## 84. Two chronological omissions and an exact original-reader GLOBAL family

At original order $k=m+2$, a complete arithmetic row misses two phases, and consecutive windows move by three phases. A successful all-one word can inherit tail one, so its outgoing tail need not equal its literal trailing run. The physical bound below retains that inherited tail. It makes a nearly full phase code automatically safe at $h\ge5$, while allowing different codes within one label class. A specified placement then realizes different free-value tables with exact whole-target GLOBAL fee $2d$ at every $d\ge3$. Its adaptive fee is bounded, not classified exactly.

**定义 84.1（The original two-omission full target）。** Retain [IC, Definitions 1.1–1.3 and Interface 1.4]: original integer weights $G_i$, matched $V_k\bmod2$ reading, the full joint actual complete-history prior, immutable INITIAL labels, a free initial scalar and independent absorbing bottom, and complete endpoints only. Fix

$$
m\ge7,\qquad 3\nmid m,\qquad k=m+2,\qquad T=m+3,
\qquad g=\gcd(m,T)=\gcd(m,3)=1.
\tag{84.1}
$$

Thus every phase is actual. Write $j=-\theta_{\rm INITIAL}\pmod T$, let $A=\{0,\ldots,m\}$, and take two finite tables $\lambda_0,\lambda_1:\mathbb Z/T\mathbb Z\to Y$. Choose $R$ fresh relative to both entire low images. Define the entire target, including the history pullback, by

$$
\begin{aligned}
f(v,-j,s)&=
\begin{cases}
\lambda_v(j),&0\le s<m,\\
R,&s=m\text{ or }s=m+1,
\end{cases}
&&v\in\mathbb F_2,\ j\in\mathbb Z/T\mathbb Z,\\
f(\bot)&=L_\bot,\qquad
F(w)=f(q_{\rm INITIAL}(w)),\qquad
\Lambda(j)&=(\lambda_0(j),\lambda_1(j)).
\end{aligned}
\tag{84.2}
$$

The initial-bottom label is arbitrary and independent, including possible coincidences with other labels. The low target is tail-independent separately on each INITIAL value fibre; the two tables need not agree. No target is reevaluated on a later record.

Index issued complete words by $t=0,1,\ldots$. Their ordered paths and two omitted vertices are

$$
\begin{aligned}
u_t&=tm\pmod T=-3t\pmod T,\\
W_t&=[u_t,u_t+m]\pmod T,\\
M_t&=\{u_t+m+1,u_t+m+2\}\pmod T
     =\{-3t-2,-3t-1\}\pmod T.
\end{aligned}
\tag{84.3}
$$

For any actual word $B$ define its complete arithmetic row by

$$
\begin{aligned}
q_{t,B}(j)&=\bigoplus_{i=0}^{m-1}B_i\gamma_{-j+tm+i},
&&\gamma_i=\mathbf1_{\{0,T-1\}}(i\bmod T),\\
q_{t,B}(u_t)&=B_0,\qquad
q_{t,B}(u_t+i)=B_{i-1}\oplus B_i&&1\le i<m,\\
q_{t,B}(u_t+m)&=B_{m-1},\qquad
q_{t,B}|_{M_t}=0.
\end{aligned}
\tag{84.4}
$$

These are the supplied original literal charges, not new observations. The row has even full-path charge; conversely an even row vanishing on $M_t$ has the unique width-$m$ inverse

$$
B_{t,i}=\bigoplus_{b=0}^i q_t(u_t+b),\qquad 0\le i<m.
\tag{84.5}
$$

On success the row equals that source's own completed scalar difference. On rejection its actual endpoint is bottom, and the arithmetic row is not a scalar readout. Every issued word is emitted completely and costs one block and $m$ bits, including an absorbed suffix. Both alphabets contain every width-$m$ word because $m<k$. GLOBAL means one preset stream for this fixed full target, on both values and every actual source, with endpoint stopping. There is no reset, copy, hidden INITIAL clock, intermediate read or borrowed sibling output.

**引理 84.2（Sharp rejecting-seam bound with the true all-one transfer）。** Under (84.1), let $P,Q$ be consecutive issued width-$m$ words and suppose $P$ has completed successfully on one actual source. If $Q$ rejects on that source, then

$$
\left|\{j:q_{t,P}(j)=q_{t+1,Q}(j)=1\}\right|\le3.
\tag{84.6}
$$

The bound is sharp for every $m$ in (84.1). If either word is all ones, the intersection is at most two. If both are all ones, it has exactly one phase. An all-zero word on either side cannot cause such a rejection.

证明。 Translate by the known displacement $tm$ for the calculation. The two consecutive paths are

$$
[0,m],\qquad [m,m+1,m+2,0,1,\ldots,m-3],
\tag{84.7}
$$

and their common vertices are $\{m\}\cup[0,m-3]$. Suppose first that $P$ contains a zero. Put $r=\rho(P)$ and $\ell=\alpha(Q)$, where $\rho$ and $\alpha$ denote literal trailing and leading one-run lengths. The actual outgoing tail of $P$ is then exactly $r$. Since $m<k$, $Q$ rejects precisely when $r+\ell\ge m+2$; a zero of $Q$, if reached, makes its internally shorter runs safe.

The suffix of $P$ has zero consecutive differences at phases $m-r+1,\ldots,m-1$, so its charge support, apart from endpoint $m$, lies in $[0,m-r]$. The $\ell$-one prefix of $Q$ has zero differences at its local positions $1,\ldots,\ell-1$. In the path order (84.7), its common charged vertices other than $m$ therefore lie in $[\ell-3,m-3]\cap[0,m-3]$. This remains a valid containment when $Q=1^m$: its other endpoint is $m-3$. Hence

$$
\{j:q_{t,P}(j)=q_{t+1,Q}(j)=1\}
\subseteq\{m\}\cup\bigl([0,m-3]\cap[\ell-3,m-r]\bigr).
\tag{84.8}
$$

Before clipping, the integer interval has $\max\{0,m-r-\ell+4\}\le2$ points. Adding $m$ proves (84.6) in this case.

If $P=1^m$, let $\sigma$ be its actual incoming tail. Its success implies $\sigma+m<m+2$, so $\sigma\in\{0,1\}$, and its outgoing tail is $\sigma+m$, exactly as in [S15, Definition 1.1]. Its row has only the two charged endpoints $\{0,m\}$, proving the bound of two without replacing this tail by $\rho(P)=m$. Similarly an all-one $Q$ has only the two endpoints $\{m,m-3\}$. If both words are all ones, the intersection is exactly $\{m\}$. An all-zero $P$ leaves tail zero, from which every width-$m$ word succeeds; an all-zero $Q$ clears any legal incoming tail. These cover the exceptional transfers.

For sharpness, begin at an actual tail-zero record and issue

$$
P=10\,1^{m-2},\qquad Q=11110\,1^{m-5}.
\tag{84.9}
$$

The first word succeeds, its outgoing tail is $m-2$, and the leading four ones of $Q$ reach $k=m+2$. Their complete arithmetic supports are $\{0,1,2,m\}$ and $\{m,1,2,m-3\}$, with intersection exactly $\{1,2,m\}$ since $m\ge7$. The rejecting $Q$ is nevertheless emitted and paid in full. The initial tail-zero record is a joint actual history by [IC, (1.3)].

The inherited-tail exception is physically consequential: from actual incoming tail one, $P=1^m$ succeeds with outgoing tail $m+1$, while $Q=10^{m-1}$ rejects on its first bit. The literal-run sum $m+1$ is below $k=m+2$ and would misclassify this seam. Its actual charged intersection is only $\{m\}$, consistent with (84.6). This lemma is used below to discharge every seam of the fee-attaining stream. ∎

**定理 84.3（High-capacity phase-wise bridge to the exact GLOBAL fee）。** In Definition 84.1 suppose

$$
h\ge5,\qquad N=2^h,\qquad |\Lambda[\mathbb Z/T\mathbb Z]|=N-1.
\tag{84.10}
$$

Let $\mathsf P_h$ mean that there is a phase assignment $Z:\mathbb Z/T\mathbb Z\to\mathbb F_2^h$, with coordinates numbered $0,\ldots,h-1$, satisfying

$$
\begin{aligned}
\Lambda(j)\ne\Lambda(j')&\ \Longrightarrow\ Z(j)\ne Z(j'),\\
\bigoplus_{j\in\mathbb Z/T\mathbb Z}Z(j)&=0,\\
Z_t(j)&=0&&j\in M_t,\quad0\le t<h,\\
Z_0(0)&=1,\qquad Z_0(1)=0,\qquad Z_0(2)=1.
\end{aligned}
\tag{84.11}
$$

There is no requirement that $Z$ be constant on a joined class. Then, under both original alphabets,

$$
\boxed{C_{\rm pre}(f)=C_{\rm pre}(F)=h\quad\Longleftrightarrow\quad\mathsf P_h.}
\tag{84.12}
$$

Every assignment in (84.11), through (84.5), supplies one actual $h$-block attaining stream. In particular no additional seam test is needed in this domain. The exact worst emitted-bit fee when (84.11) holds is $mh$. When it fails, the theorem concludes only $C_{\rm pre}\ge h+1$, possibly infinite, and supplies no general higher-price formula. It makes no arbitrary-placement selection claim.

证明（actual sources, compulsory root and all-action capacity）。 Every record in (84.2) has the credited joint witness, now instantiated with the actual new $m,T$:

$$
\begin{aligned}
\ell&\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,
\qquad \ell\ge s+2,\\
\eta&=\bigoplus_{i=\ell-s}^{\ell-1}\gamma_i,\qquad
w(v,j,s)=(v\oplus\eta)0^{\ell-s-1}1^s.
\end{aligned}
\tag{84.13}
$$

Actual gcd one gives arbitrarily large such $\ell$. The separating zero and compensating first bit simultaneously realize value $v$, phase $-j$ and tail $s<k$. The history is legal and divides into complete internally legal blocks under both alphabets. Its unobserved length is not a controller input. Two all-one complete source blocks, $1^{2m}$, separately realize initial bottom because $m<k<2m$.

Fix either free INITIAL value and any phase. The actual tails $m-1$ and $m$ have unequal INITIAL labels, low versus fresh $R$, so free stopping is impossible. A root with at most one leading one reaches its first zero on both records, since $m+1<k$; their values and phases agree there and the zero merges their tails. No later archive can recover their unequal labels. A root with at least three leading ones, including $1^m$, rejects both by the third one, leaving identical absorbing complete endpoints. Thus every correct root, regardless of its later horizon, has exactly two leading ones and prefix $110$. This is an application of the supplied first-zero and rejection-loss interfaces, not a new generic cut theorem.

Every such root rejects exactly the two high tails $m,m+1$. Every low tail survives its two leading ones because $s+2\le m+1<k$, reaches the zero, and completes safely. At each phase that merger preserves its INITIAL component label. All low sources then have the same actual terminal tail of this root. Within each acquired scalar-output archive, every later literal word either succeeds on all candidates or rejects all: safety depends only on their common actual tail and the issued word. On success it gives at most two scalar endpoints and again a common tail on each child, using the true transfer $\sigma+m$ for an all-one word. On common rejection all later outputs remain bottom; it cannot finish an archive with unequal labels. Endpoint stopping requires a homogeneous archive. Induction on the remaining fee therefore bounds the number of low labels resolvable with total worst fee $H$ by $2^H$. This includes all words, all-one actions, zero waits, padding, repair, attempted rejection and early stopping.

For the GLOBAL lower bound use the exact preset value-join law [IC, Definition 29.1 and Theorem 29.2]. Its target on this same phase/tail space has low table $\Lambda$, high label $(R,R)$ and independent bottom. The law uses value-complement symmetry of the same acquired endpoints; it issues no copied experiment and borrows no other source's outputs. On a fixed scalar fibre the joined target has $N-1=2^h-1$ actual low labels. The preceding all-action bound gives

$$
2^h-1\le2^H,\qquad H\ge h.
\tag{84.14}
$$

This is a joined-target lower bound transferred to the original target only for preset control. It does not identify its component adaptive optimum. The explicit pullback (84.2), deterministic record evolution and actual surjectivity (84.13) give equal record/history prices.

证明（the physical implication beyond row algebra）。 Suppose (84.11) holds. Put $q_t(j)=Z_t(j)$ and use its literal inverse

$$
B_{t,i}=\bigoplus_{b=0}^i Z_t(tm+b\bmod T),\qquad
0\le t<h,\quad0\le i<m.
\tag{84.15}
$$

The XOR and omission clauses make every row even and available on its actual path. The root bits are $1,1,0$, so this stream has precisely the previously proved high rejection and low preservation. Every block is internally legal.

The separation clause requires at least $N-1$ different phase vectors in the $N$-element cube. Therefore at most one cube vector is absent. For every consecutive coordinate pair $t-1,t$, the cube has $2^{h-2}$ vectors with both coordinates one. At least $2^{h-2}-1$ of these occur in the actual phase table, and different vectors have different actual phases. Consequently

$$
\left|\{j:Z_{t-1}(j)=Z_t(j)=1\}\right|
\ge2^{h-2}-1\ge7>3
\quad(1\le t<h).
\tag{84.16}
$$

Inductively let a low source have completed the preceding words successfully, and retain its true current tail. If the next word rejected, Lemma 84.2 would bound precisely these two complete arithmetic rows by three, contradicting (84.16). Thus every next word succeeds on every low source. In particular each actual seam is strict. This argument does not replace an all-one outgoing tail by a literal run. Moreover every row here has at least $2^{h-1}-1$ charged phases, while an all-one word has only two; the selected words all contain zero. Their actual seam inequalities can consequently also be written

$$
\rho(B_{t-1})+\alpha(B_t)<m+2=k.
\tag{84.17}
$$

The automatic implication (84.16) is specific to the original consecutive paths and rejecting-tail mechanics; even, available rows alone would not prove it. No wait, clearing, padding or repair block is added.

Initial bottom returns $L_\bot$ freely. High sources stop at the completed root endpoint with $R$; tail $m+1$ was absorbed on the first bit and tail $m$ on the second, but both emit and pay the entire root. Let every low source emit the same $h$ words. Its own endpoints $v_0,\ldots,v_h$ give

$$
(v_1\oplus v_0,\ldots,v_h\oplus v_{h-1})=Z(j).
\tag{84.18}
$$

By (84.11), this vector determines a unique joined label even if one label has several vectors. Return its component selected by the remembered free INITIAL value $v_0$. The same literal stream serves both values and all INITIAL tails. No INITIAL phase is observed. The displayed rule stops all low sources at the final complete endpoint without cleanup; all these records are actual and pay exactly $h$ blocks. Together with (84.14), this proves sufficiency and the exact emitted-bit fee.

证明（necessity with arbitrary endpoint stops and phase-wise splitting）。 Suppose a correct preset controller has worst fee $h$. Apply the supplied join law to its same stream; this permits a joined decoder with fee at most $h$. Stop every joined-homogeneous archive immediately. The root is still forced to have prefix $110$, and every low source has a common tail after it.

At a later slot, a common rejecting word would absorb every running low source. Correctness would force each of its current archive fibres to be homogeneous already, so all could stop before that slot. Such a word is unnecessary. After removing unnecessary final actions, the joined lower bound (84.14) forces some low source to reach slot $h-1$; every word through that slot succeeds on continuing sources. Because their tail trajectory depends on the words and not the phase or value, those same words also succeed if, solely for the mathematical row calculation, earlier stopped low phases are continued along the fixed stream. This fills a length-$h$ arithmetic vector $Z(j)$ on every low phase. No stopped source is observed or charged in the actual stopping rule.

Two unequal joined labels cannot have equal full vectors: they would have equal acquired scalar prefixes on a fixed free-value fibre, and at the earlier stopping time the same stopping/decoding decision would return unequal labels. Every full row has even charge and vanishes on its actual two omissions by (84.4). The root prefix supplies $Z_0(0),Z_0(1),Z_0(2)=1,0,1$. Thus all clauses of (84.11) hold. Unlike a saturated-label argument, this reasoning does not force one vector per class; it preserves all phase-wise splits that the actual stream produces. It covers paid waits at their chronological slots and early endpoint stops. This proves necessity. ∎

**构造 84.4（A specified compatible placement for every $d\ge3$）。** Set

$$
d\ge3,\quad h=2d,\quad r=2^d,\quad N=r^2=2^{2d},\quad
m=N-2,\quad k=N,\quad T=N+1.
\tag{84.19}
$$

Since $N=4^d\equiv1\pmod3$, $3\nmid m$ and the actual gcd is one. Let $\varepsilon_i$ be the coordinate-$i$ unit of $\mathbb F_2^h$, numbered $0,\ldots,h-1$, and define

$$
a=\varepsilon_{h-1},\qquad
\nu=\varepsilon_{h-2},\qquad
\omega=\varepsilon_{h-2}\oplus\varepsilon_{h-1},\qquad
\Omega=\mathbb F_2^h\setminus\{a,\omega\}.
\tag{84.20}
$$

Split every vector $z\in\Omega$ into its first and last $d$ coordinates, denoted $(i(z),\ell(z))\in I\times I$, where $I=\mathbb F_2^d$. Take disjoint label sets $\{A_i:i\in I\}$ and $\{D_\ell:\ell\in I\}$, with distinct labels within each set. Choose distinct common fresh $C,R$ outside both sets, and independent $L_\bot$.

Let $\sigma$ cycle the suffix coordinates $1,\ldots,h-1$ in that order. For $1\le t<h$ put

$$
b_t=\varepsilon_{\sigma(t)}\oplus
    \varepsilon_{\sigma^2(t)}\oplus
    \varepsilon_{\sigma^3(t)},\qquad
e_t=N-1-3t,\qquad f_t=N-3t.
\tag{84.21}
$$

Define a phase-vector table $Z$ by the following prescriptions:

$$
\begin{aligned}
Z(0)&=\varepsilon_0,&Z(1)=Z(3)&=\nu,
&Z(2)&=\varepsilon_0\oplus\varepsilon_1,\\
Z(e_t)&=b_t,&Z(f_t)&=\varepsilon_0\oplus b_t
&&1\le t<h,\\
Z(N-1)&=\omega,&Z(N)&=\omega.
\end{aligned}
\tag{84.22}
$$

Assign all unused members of $\Omega$ once each, in increasing binary order, to the unassigned phases of $A=\{0,\ldots,N-2\}$ in increasing order. Coordinate zero is the first binary digit. On $A$ set

$$
\lambda_0(j)=A_{i(Z(j))},\qquad
\lambda_1(j)=D_{\ell(Z(j))};
\qquad
\lambda_0(N-1)=\lambda_1(N-1)
=\lambda_0(N)=\lambda_1(N)=C.
\tag{84.23}
$$

Use the entire INITIAL target and history pullback (84.2), not just its low restriction. Thus $R$ labels INITIAL tails $m,m+1$, the low tables are independent of $s<m$, and initial bottom retains its separate label.

证明（well-defined placement and genuinely different component tables）。 The least missed phase is

$$
e_{h-1}=N-3h+2\ge48
\quad(h=2d\ge6).
\tag{84.24}
$$

The pairs $\{e_t,f_t\}$ are disjoint adjacent pairs, separated by one phase between consecutive pairs, lie in $A$, and avoid $0,1,2,3$. They also avoid the two outside phases. The suffix cycle has length $h-1\ge5$. Its next three coordinates are distinct and exclude $t$, so $(b_t)_t=0$. Their three-element consecutive cyclic supports have different starting points, so all $b_t$ are distinct. Each $b_t$ has root coordinate zero and weight three; each $\varepsilon_0\oplus b_t$ has root coordinate one and suffix weight three. These $2(h-1)$ vectors are distinct and avoid $a,\nu,\omega,\varepsilon_0,\varepsilon_0\oplus\varepsilon_1$.

Consequently the prescribed phases in $A$ number $2h+2$ and use $2h+1$ different members of $\Omega$, with exactly the duplicate $\nu$. The remaining number of phases is $N-2h-3$, equal to the number of unused members of the $(N-2)$-element set $\Omega$. The ordered bijection is well-defined. Every vector of $\Omega$ occurs once on $A$, except $\nu$ occurs twice. Outside, $\omega$ occurs twice and is represented by the fresh semantic label $(C,C)$, not by its binary row/column indices.

The full joined low image therefore has exactly $N-1$ classes. Precisely two have positive even multiplicity: the class coded by $\nu$ and the outside class $(C,C)$, both of size two. Every other class has multiplicity one. These count actual low phases on the full cycle, not INITIAL tails or separate component multiplicities.

The two excluded pairs represented by $a$ and $\omega$ have row index zero and distinct column indices. Row zero retains $r-2>0$ pairs and every other row retains $r$; the two affected columns retain $r-1>0$ pairs and every other column retains $r$. Thus each component table uses all $r$ of its own row or column labels on $A$, and adds the shared fresh low label $C$ outside. Each full low image has exactly $2^d+1$ labels. The components differ at every phase of $A$ because their row and column label sets are disjoint. This is one common, jointly inhabited table, not independently chosen component optima. Formula (84.13) realizes every value, phase and INITIAL tail for its actual new width and period. ∎

**定理 84.5（Exact GLOBAL family fee and supported adaptive bounds）。** For Construction 84.4, under both original alphabets,

$$
\boxed{C_{\rm pre}(f)=C_{\rm pre}(F)=2d,\qquad
\text{minimum worst GLOBAL emitted bits}=m\,2d.}
\tag{84.25}
$$

The same family has the supported adaptive bounds

$$
\boxed{d+1\le C_{\rm ad}(f)=C_{\rm ad}(F)\le2d,}
\qquad
m(d+1)\le\text{minimum worst adaptive emitted bits}\le2md.
\tag{84.26}
$$

No exact adaptive optimum is asserted.

证明（the uniform code, the actual common stream and matching lower bounds）。 Distinct joined classes have distinct codes in (84.22)–(84.23). The full phase-code image is exactly $\mathbb F_2^h\setminus\{a\}$. The XOR of the entire $h$-cube is zero, since each coordinate has the even number $2^{h-1}$ of ones. The class codes would therefore XOR to $a$ if each occurred once. The extra occurrences of $\nu$ and $\omega$ give

$$
\bigoplus_{j=0}^{N}Z(j)=a\oplus\nu\oplus\omega=0.
\tag{84.27}
$$

At slot zero the actual two omissions are $N-1,N$ and the root coordinate of $\omega$ is zero. At every slot $1\le t<h$, (84.3) gives exactly $M_t=\{e_t,f_t\}$, and both assigned codes there have coordinate $t$ zero by (84.21). There is no modular wrap in these displayed missed pairs by (84.24). At phases $0,1,2$ the root coordinate is $1,0,1$. Hence every clause of (84.11) holds.

The one stream is explicitly (84.15) with this table. Its root is $110\cdots$, rejecting precisely the two high INITIAL tails and merging all low tails with their labels preserved. Each subsequent consecutive pair has at least $2^{h-2}$ common charged phases: the only missing cube vector $a$ is a unit and has no two adjacent one coordinates. Lemma 84.2 proves every actual seam strict, including any boundary with two adjacent literal one bits. Thus these are actual fully paid complete words, without clearing or repair insertions. The same stream is used on both free values. The own-endpoint decoder (84.18) returns $C$ at code $\omega$; for any other observed code $z$, it returns $A_{i(z)}$ if the free INITIAL value was zero and $D_{\ell(z)}$ if it was one. Initial bottom stops freely; high sources return $R$ after the entire paid root; all low sources stop after the $h$th paid endpoint. Actual joint sources exist for all these branches.

The all-action joined lower bound (84.14) applies to these $N-1$ classes and rules out every shorter GLOBAL protocol, including other lawful roots, arbitrary literal words, paid waits and early stops. This proves (84.25). For the adaptive lower bound, fix either free INITIAL value. Its full low table has $r+1=2^d+1$ labels, all actual. The same compulsory-root and common-tail binary argument, now on that component rather than a joined adaptive target, gives $2^d+1\le2^H$, hence $H\ge d+1$. The common stream is an allowed adaptive protocol and gives $H\le2d$. The supplied record/history factorization establishes both history equalities. Every issued block has exactly $m$ emitted bits, proving the bit bounds. No new-width adaptive suffix theorem is borrowed from Chapter 73. ∎

**实例 84.6（The $d=3$ original-reader full target）。** Here

$$
(h,m,k,T,g)=(6,62,64,65,1),\qquad
(a,\nu,\omega)=(000001,000010,000011).
\tag{84.28}
$$

There are nine low labels per component, 63 joined low classes on 65 actual phases, and the two repeated codes are $000010$ at phases $1,3$ and $000011$ at phases $63,64$. The latter is the fresh shared label $C$. The omission pairs at slots $1,\ldots,5$ are

$$
\{60,61\},\quad\{57,58\},\quad\{54,55\},\quad
\{51,52\},\quad\{48,49\}.
\tag{84.29}
$$

Their codes, in the same order within each pair, are respectively

$$
(001110,101110),\ (000111,100111),\ (010011,110011),\
(011001,111001),\ (011100,111100).
\tag{84.30}
$$

Phases $0,1,2,3$ have codes $100000,000010,110000,000010$. Assign the remaining allowed vectors to the remaining phases by Construction 84.4. This fixes the whole target: the first three digits select $A_i$, the last three select $D_\ell$, except that phases 63 and 64 have $C$ on both fibres; INITIAL tails 62 and 63 have $R$ at every phase, and all other INITIAL tails use these low tables.

At actual starts $0,62,59,56,53,50\pmod{65}$, the prescribed inverse gives the following one stream:

$$
\begin{aligned}
B_0&=11000000000000000000000000001010101010101010101001001001001001,\\
B_1&=11111000000000000010101010101011111111111111010101010101010111,\\
B_2&=10100000000000101010111111110101011111110101010000000101010111,\\
B_3&=10101011111111010000010111101011110100001011111010001010010000,\\
B_4&=10110101010110011110001000111000100100100100011101110011101111,\\
B_5&=01010101000010111111100011001001110011101101100111001101000110.
\end{aligned}
\tag{84.31}
$$

Each word has exactly 62 bits. The consecutive terminal/leading run pairs are $(1,5),(3,1),(3,1),(0,1),(4,0)$, with sums $6,4,4,1,4$, all strictly below 64. Each common charged-phase intersection has at least sixteen phases. The own-endpoint decoder is (84.18) with the preceding table. The exact GLOBAL fee is six blocks and 372 emitted bits; the supported adaptive interval is four to six blocks and 248 to 372 bits. High sources emit and pay all 62 bits of the rejecting root; initial bottom emits none.

**数学引文 84.7（Exact overlap, source correspondence and additional physical content）。** The protected mathematical source is [revision c2ff98007f6606eb95541d26e96fd37c33c8dab8](https://github.com/the-omega-institute/trureturing/tree/c2ff98007f6606eb95541d26e96fd37c33c8dab8/docs/develop/theory), in particular this volume through Chapter 83 and the canonical [IC] and its [M], [T3], [F4] companions. The explicit-pin suppliers [S1], [S2] and [S15] retain the versions in this volume's reference definitions.

[IC, Definitions 1.1–1.3 and Interface 1.4; S1, Definition 1.2, Convention 1.3, Proposition 2.2 and Lemma 4.3; S2, Theorem 14.1] supplies the original weights, matched cycle, actual joint sources, first-zero loss and record/history factorization. Here the source is exactly (84.13), its INITIAL record is $(v,-j,s)$, its immutable target is (84.2), its actions are the actual complete words (84.15), and its observations and optimized fee are those words' own completed endpoints and actual emitted count. The free value selects only the final component of a GLOBAL decoder, not its stream. The gcd and joint histories are instantiated at the new width, rather than inherited from another reader.

[S15, Definition 1.1] supplies the true all-one transfer $\sigma\mapsto\sigma+m$, and Section 1 supplies the literal inverse. Its Theorem 3.3 is a general source-specific response/seam certificate and does not provide (84.6) or automatic safety from code cardinality. Its independent-row Theorem 3.4 requires $k\ge2m$, which fails at (84.1). [IC, Definition 29.1 and Theorem 29.2] supplies the exact preset value join, with early stops and absorption; it supplies neither the two-omission physical bridge nor the placement (84.22). Binary capacity and elementary cube XOR are credited reuse.

Chapter 73's full-positive-child theorem fixes odd $m$, $k=m+1$ and one omitted phase; it does not price an adaptive suffix here. Chapters 80–83 retain $k=m+1$, their own label counts, parity and placements. In particular Definition 82.1 identifies an all-one outgoing tail with $m$ only because its own success condition forces incoming tail zero. Lemma 82.2 is not used as a theorem at this new order. Proposition 83.4 demonstrates that available even algebraic rows can reject, and Boundary 83.9 expressly leaves $k=m+2$ unresolved. The new rejecting bound (84.6), three-phase shift with two actual omissions (84.3), root prefix $110$, high two-tail band and compatible placement are separately proved here.

[IC, Definition 4.1, Proposition 4.2 and Chapter 5] uses low INITIAL tails below $k-m$ and a forced all-one root, whereas (84.2) has a fresh high band only at tails $m,m+1$ and forbids that root. The [M, Definitions 1.1–1.3 and Theorem 2.1], [T3, Definition 1.2 and Theorem 2.1] and [F4, Definition 72.1 and Theorem 72.2] prices concern actually successful archives acquired after an all-one root. Even where their parameter inequalities include $k=m+2$, their arrival and target hypotheses do not give this full target or its $N-1$-class common stream. The independent-row material [IC, Chapters 27 and 60–64] keeps $k\ge2m$. The wide and critical laws [IC, Theorem 38.1 and Chapters 46–48] require $m\ge k$. None of those numerical slices supplies (84.25).

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), defines completed leaf-reaching observations, tests consistent with an input/output system, distinction by disjoint observed traces, and adaptive distinguishing graphs. Figure 3 exhibits destructive mergers after every possible first operation. For the present correspondence one input is an issued complete word and one output is its completed scalar or bottom; unequal immutable INITIAL labels must remain distinguishable on that actual experiment. This mature framework does not supply the KBonacci rejecting support bound, the literal two-omission calendar, its strict seams or the emitted-fee equality. No generic state-identification or Bellman reformulation is counted as added fee content.

The additional ordinary reader-specific content is the sharp actual rejecting-seam bound including inherited all-one tails, its automatic strict-seam implication for phase-wise nearly full codes at $h\ge5$, and the uniform compatible phase placement (84.22) that realizes the exact new-width whole-target fee. The full labels, actual source realization and explicit stopped stream connect that content to the original resource. The join, parity, capacity and inverse are reused under their exact hypotheses. These are repo-derived deductions with a scoped source and primary-paper comparison; no exhaustive priority or literature-absence claim is made.

**数据 84.8（Finite corroboration and its mathematical limits）。** Exhaustive pairs of width-$m$ words at $m=7,8,10,11$ gave respectively $176,384,1792,3840$ rejecting run cases, retaining both possible incoming tails of an all-one first word. Every complete arithmetic intersection had at most three phases, and each width attained three. The incoming-tail-one all-one cases numbered $64,128,512,1024$. These are local transfer checks, not a claim that every pair is part of a fee-optimal full controller.

For Construction 84.4 at $d=3,4,5,6$, direct finite row/inverse checks gave respectively $63,255,1023,4095$ joined low classes, precisely the two stated even classes, even rows, zeros on both chronological omissions, root prefix $110$, and strict seams. The minimum consecutive common-one counts were $16,64,256,1024$. At $d=3$, all $8320=2\cdot65\cdot64$ successful INITIAL records were jointly realized by (84.13) using the original integer recurrence for $G_i$. Literal execution checked all component decoders and all stops: 8060 low records emitted six words, 260 high records emitted the whole rejecting root, totaling 48620 issued blocks and 3014440 emitted bits across these separate checks. Initial bottom was separately realized by $1^{124}$ and stops freely. These finite checks corroborate the ordinary proofs; they do not replace the uniform construction, all-action lower bounds or every-parameter seam argument. No test program or dataset is part of the theory delivery.

**边界 84.9（Scoped fee result and remaining original objective）。** The bridge requires all of (84.1), (84.2) and (84.10): original $k=m+2$, actual gcd one, $h\ge5$, exactly $2^h-1$ joined full low classes, tail-independent low tables, the common fresh high label on precisely INITIAL tails $m,m+1$, and explicit immutable history factorization. Its phase criterion retains arbitrary chronological omissions, repeated classes, phase-wise splitting, complete-endpoint stopping and both free values. It does not prove that every such table has a witnessing assignment or assign the price above $h$ when the assignment fails. At $h=4$, omitting one cube vector can leave only three common-one vectors; the automatic argument (84.16) gives no safety conclusion, and no depth-four claim is made.

Construction 84.4 proves existence for its specified placements at every $d\ge3$, not for arbitrary placements or arbitrary multiplicity profiles. Its exact GLOBAL fee is $2d$ and its exact worst emitted-bit fee is $(2^{2d}-2)2d$. Its adaptive optimum remains within (84.26). Different fixed targets may have different streams; unbounded $d$ ranges over different finite readers and targets and does not assert one stream for their union. Offline ordered table formation and storage of the inverse decoder are separate resources, with no asserted optimal memory or offline complexity. A semantic criterion for arbitrary labels becomes effective with a finite target partition or decidable equality, as in [S1, Note 5.3].

Every fee counts the root and every issued full block, with one free initial read and one paid complete endpoint per block. High absorption does not truncate an issued word. Earlier homogeneous endpoint stops are allowed in the lower bounds and the criterion; the displayed attaining rule simply stops every low source at its $h$th endpoint. There is no final cleanup fee or unobserved read.

The original exact minimum worst-branch ACTUAL emitted-complete-block fees for every attainable immutable INITIAL target and all original $k\ge2,m\ge1$, separately adaptive and ONE GLOBAL preset stream per fixed target under both alphabets [IC, Definition 1.3 and Open Problem 9.1], remain open. Arbitrary $k=m+2$ placements, fewer joined classes, other high or outside coincidences, low-tail-dependent targets, other orders and gcds, unrelated acquired mixed archives and general adaptive optima are not resolved here. These are ordinary theory proofs without Lean/kernel certification; no compilation, ingestion, deposit, coverage or freezing is asserted.

## 追加锚（本行以下为增补区）
## 85. Exact adaptive attainment for the specified two-omission different-value family

The full target is exactly Construction 84.4, including its ordered completion of the phase table, both genuinely different free-value tables, all INITIAL tails and independent initial bottom. A different root from the GLOBAL witness leaves a two-label zero child and a positive child carrying all the component labels. The latter admits a uniformly safe logarithmic suffix on the actual two-omission calendar. This supplies the missing adaptive attainment; the exact GLOBAL stream and its price remain credited to Theorem 84.5.

**定理 85.1（Exact adaptive/GLOBAL fee pair on the unchanged full target）。** For every $d\ge3$, retain the entire target $f$ and history pullback $F$ of Construction 84.4 and (84.2), with exactly the phase table $Z$ of (84.20)–(84.23). Thus

$$
r=2^d,\qquad N=r^2,\qquad m=N-2,\qquad k=N,\qquad T=N+1,
\qquad g=\gcd(m,T)=1.
\tag{85.1}
$$

Under each original control alphabet,

$$
\boxed{
C_{\rm ad}(f)=C_{\rm ad}(F)=d+1,\qquad
C_{\rm pre}(f)=C_{\rm pre}(F)=2d.
}
\tag{85.2}
$$

The exact minimum worst emitted-bit fees are respectively

$$
\boxed{m(d+1)\quad\text{and}\quad 2md.}
\tag{85.3}
$$

The new assertion is the adaptive upper bound attained below. The all-literal adaptive lower bound and the separately attained one-GLOBAL-stream equality are the exact reused clauses of Theorem 84.5. The adaptive suffix is selected by the remembered free INITIAL value; it is not asserted to be one GLOBAL stream.

证明（the actual full source and a different lawful root）。 The matched integer reader and source contract are [IC, Definitions 1.1–1.3, Convention 1.2 and Interface 1.4]. Since $N=4^d\equiv1\pmod3$, $\gcd(N-2,N+1)=1$. In particular every $j\in\mathbb Z/T\mathbb Z$, both values and every $0\le s<k$ have the single actual complete-history witness (84.13). Explicitly choose

$$
\begin{aligned}
\ell&\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad \ell\ge s+2,\\
\eta&=\bigoplus_{i=\ell-s}^{\ell-1}\gamma_i,\qquad
w(v,j,s)=(v\oplus\eta)0^{\ell-s-1}1^s.
\end{aligned}
\tag{85.4}
$$

The separating zero and first-bit compensation jointly give $(v,-j,s)$ under the original recurrence for $G_i$; the whole history is legal and its length is divisible by $m$. The unobserved history length is not available to the controller. Initial bottom has its separate actual witness $1^{2m}$, comprising two internally legal complete source blocks and reaching absorption because $m<k<2m$. This is the original joint prior, rather than independently reachable phase, value and tail marginals.

If the free initial read is bottom, return $L_\bot$ immediately. Otherwise remember that INITIAL value $v$ and issue the complete word

$$
P=11(01)^{(m-2)/2}.
\tag{85.5}
$$

It has exactly $m$ bits, prefix $110$, an internal zero and terminal tail one. Every INITIAL tail $s<m$ survives its first two ones because $s+2\le m+1<k$, reaches its zero and completes safely. Every high INITIAL tail $s=m,m+1$ rejects, respectively on the second or first bit. Both high branches nevertheless emit the entire $P$, pay one full block and return $R$ only at its completed bottom endpoint. The first-zero merger of low tails is lawful because each low table in (84.2) is tail-independent at fixed INITIAL $v,j$.

Put

$$
S=\{0,\ldots,m\}\setminus\{1\}.
\tag{85.6}
$$

The consecutive-bit charge formula (84.4) gives $q_{0,P}=\mathbf1_S$: its first charges are $1,0,1$, all later path charges are one, and the two outside phases $N-1,N$ have charge zero. Here $|S|=m$ is even, as required for this actual row. At the root endpoint every low source has actual record $(v\oplus\mathbf1_S(j),-j+m,1)$. A successful root difference one therefore has exactly the INITIAL phase support $S$, common current scalar and actual current tail one. Its labels are $A_{i(Z(j))}$ for $v=0$ and $D_{\ell(Z(j))}$ for $v=1$.

The successful difference-zero child has precisely phases $\{1,N-1,N\}$. At phase one its INITIAL label is $A_0$ on value zero and $D_{\ell(\nu)}$ on value one; at both outside phases it is $C$. Give this child the one complete word

$$
U=0001\,0^{m-4}
\tag{85.7}
$$

at actual issued index one. It begins zero and safely clears its inherited tail one. Its isolated one is at local position three; since $m+3=T$, its original arithmetic support is exactly $\{0,1\}$. On this actual child its own next endpoint difference is one precisely at phase one and zero at the two outside phases. Return the corresponding $A_0$ or $D_{\ell(\nu)}$ on one, and $C$ on zero. This finishes that child at total fee two. The charge at phase zero is a bit prescription of this same word; the positive sibling supplies no observation and does not execute $U$.

证明（component labels and the actual two-omission lists）。 It remains to finish the actually acquired positive child with $d$ further blocks. Let $\mathcal Y_v=\lambda_v[S]$. Construction 84.4 places every vector of $\Omega$ once on $\{0,\ldots,m\}$ except that $\nu$ occurs twice. Removing phase one removes exactly that duplicate, so

$$
Z:S\longrightarrow\Omega
\quad\text{is a bijection}.
\tag{85.8}
$$

Consequently all $r$ row labels and all $r$ column labels occur on $S$. The only excluded vectors $a,\omega$ have row zero and two distinct columns. The multiplicities on this one actual positive support are

$$
\begin{aligned}
|\{j\in S:i(Z(j))=i\}|&=
\begin{cases}r-2,&i=0,\\r,&i\ne0,\end{cases}\\
|\{j\in S:\ell(Z(j))=\ell\}|&=
\begin{cases}r-1,&\ell=\ell(a)\text{ or }\ell(\omega),\\
r,&\text{otherwise}.
\end{cases}
\end{aligned}
\tag{85.9}
$$

In particular every component label has at least $r-2$ actual phases here. These are multiplicities of the fixed table, not new choices of its placement.

Number the suffix blocks by their actual absolute issued indices $t=1,\ldots,d$. Their omitted pairs are exactly

$$
M_t=\{e_t,f_t\}=\{N-1-3t,N-3t\}.
\tag{85.10}
$$

They are the actual pairs (84.3), without a modular wrap in this range. They belong to $S$ and are disjoint from phase one. Their prescribed table vectors are $b_t,\varepsilon_0\oplus b_t$. For a component label $L\in\mathcal Y_v$ put

$$
J_v(L)=\{t\in\{1,\ldots,d\}:L\in\lambda_v[M_t]\},\qquad
\mathcal L_v(L)=
\{c\in\mathbb F_2^d:c_t=0\text{ for every }t\in J_v(L)\}.
\tag{85.11}
$$

At each coordinate at most two labels have a zero requirement; on value one the two phases even have the same column label. No label has all $d$ requirements. To verify the latter claim uniformly, use the two slots $t=d-2,d-1$, whose three-coordinate supports do not wrap in the suffix cycle:

$$
b_{d-2}=\varepsilon_{d-1}\oplus\varepsilon_d\oplus\varepsilon_{d+1},
\qquad
b_{d-1}=\varepsilon_d\oplus\varepsilon_{d+1}\oplus\varepsilon_{d+2}.
\tag{85.12}
$$

The last index is at most $2d-1$ for $d\ge3$. The first $d$ coordinates of the two omission-pair tables are respectively

$$
\{\varepsilon_{d-1},\,\varepsilon_0\oplus\varepsilon_{d-1}\}
\quad\text{and}\quad
\{0,\,\varepsilon_0\};
\tag{85.13}
$$

these row-index sets are disjoint. Their last $d$ coordinates are respectively the distinct vectors with supports $\{d,d+1\}$ and $\{d,d+1,d+2\}$. Adding $\varepsilon_0$ changes neither column. Thus the column-label images at these slots are also disjoint. Both conclusions concern the original component indices, so every $J_v(L)$ is a proper subset of $\{1,\ldots,d\}$.

Apply the existing finite Hall theorem [H], specifically its finite indexed-list statement, to (85.11). The following verifies all of its inequalities rather than assuming distinct representatives are physically available. Fix a subfamily of $q$ label lists. The empty case is immediate. Each list contains zero and, because its requirements are proper, at least one unit vector. Therefore a union of one or two lists has at least $q$ elements.

For $3\le q\le d+1$, every unit vector belongs to the union: its coordinate is forbidden at no more than two of these labels. Along with zero these give $d+1\ge q$ elements. There are at most $2d$ constrained labels altogether. Hence any subfamily with $q>2d$ includes an unconstrained list, which is the full $r$-element cube.

Finally, for $d+2\le q\le2d$, one has $q\ge5$. A weight-two vector violates requirements at no more than four labels, since each of its two coordinates is required zero at no more than two labels. It therefore belongs to the union, as do every unit and zero. The union has at least

$$
1+d+\binom d2\ge2d\ge q
\qquad(d\ge3).
\tag{85.14}
$$

These cases exhaust all subfamilies. Hall consequently gives an injective choice

$$
c^{(v)}:\mathcal Y_v\longrightarrow\mathbb F_2^d,
\qquad c^{(v)}(L)\in\mathcal L_v(L).
\tag{85.15}
$$

There are exactly $r=2^d$ labels, so this choice is a bijection onto the entire $d$-cube. The list proof adapts the credited low-weight Hall method of Lemma 73.3, but its two omissions, proper-requirement verification and physical realization here are proved at the present reader; Theorem 73.6 is not applied outside its $k=m+1$ domain.

证明（one actual suffix and every strict seam）。 For each $v$ and $1\le t\le d$, prescribe a full phase row by

$$
\begin{aligned}
q_t^{(v)}(j)&=c_t^{(v)}(\lambda_v(j))&&j\in S,\\
q_t^{(v)}(1)&=\bigoplus_{j\in S}c_t^{(v)}(\lambda_v(j)),\\
q_t^{(v)}(N-1)&=q_t^{(v)}(N)=0.
\end{aligned}
\tag{85.16}
$$

These prescriptions exhaust the entire phase cycle. The row has even total charge, and (85.11) makes it zero on both members of its actual $M_t$. The supplied original inverse thus gives the unique width-$m$ word

$$
B_{t,i}^{(v)}
=\bigoplus_{b=0}^{i}q_t^{(v)}(tm+b\pmod T),
\qquad0\le i<m.
\tag{85.17}
$$

The parity compensation at phase one is available in every displayed suffix window, since none of (85.10) contains one. That phase has left the positive archive. Compensation is an offline choice of the actual emitted word, with no source reset, copied experiment, phase read or sibling endpoint.

Availability and even charge alone do not prove safety. The same rows have many common charged phases, so Lemma 84.2 can be used in its exact $k=m+2$ domain. For the root/first-suffix pair, $q_{0,P}=1$ throughout $S$. Bijection (85.15) makes exactly $r/2$ component labels have first code bit one. Each contributes at least $r-2$ distinct phases by (85.9), giving

$$
|\{j:q_{0,P}(j)=q_1^{(v)}(j)=1\}|
\ge\frac r2(r-2)>3.
\tag{85.18}
$$

For consecutive suffix coordinates $t-1,t$, precisely $r/4$ cube vectors have both coordinates one. Their labels again have disjoint phase sets, each of size at least $r-2$, so

$$
|\{j:q_{t-1}^{(v)}(j)=q_t^{(v)}(j)=1\}|
\ge\frac r4(r-2)\ge12>3,
\qquad2\le t\le d.
\tag{85.19}
$$

These are counts of full arithmetic rows of the very consecutive literal words (85.17), not counts assembled from different representations or different experiments. If the first suffix rejected after the successful root on any positive source, Lemma 84.2 would bound (85.18) by three. Inductively, if a later suffix rejected after its successful predecessor, the same lemma would bound (85.19) by three. Both contradictions prove that every positive source succeeds through all $d$ suffix words.

Moreover each suffix row has at least $r(r-2)/2>2$ charged phases. An all-one width-$m$ word has only its two charged endpoints by (84.4), so none of these suffix words is all ones. Every suffix contains a zero, and its actual outgoing tail is exactly its own literal terminal run; the root's outgoing tail is one. Their seam statements can therefore be written

$$
1+\alpha(B_1^{(v)})<k,\qquad
\rho(B_{t-1}^{(v)})+\alpha(B_t^{(v)})<k
\quad(2\le t\le d).
\tag{85.20}
$$

Each word is internally legal because $m<k$. The proof via Lemma 84.2 retains the true incoming tail before excluding all-one inverses; it does not assume the incorrect general transfer $\Phi_{1^m}(\sigma)=m$. The zero-child word (85.7) has its already verified strict seam $1+0<k$. No clearing, wait, padding, repair or final cleanup block has been inserted or left unpaid.

A positive source executes the one actual trace

$$
P\mid B_1^{(v)}\mid\cdots\mid B_d^{(v)}.
\tag{85.21}
$$

Write its own scalar endpoints as $v_0,\ldots,v_{d+1}$, including the free read and successful root. The observed suffix vector is

$$
(v_2\oplus v_1,\ldots,v_{d+1}\oplus v_d)
=c^{(v)}(\lambda_v(j)).
\tag{85.22}
$$

At that final complete endpoint, return the unique component label whose code is this vector. Every such endpoint archive is homogeneous for the immutable INITIAL target, even if several INITIAL phases have the same component label. The controller remembers INITIAL $v$ to choose its suffix and inverse decoder; it does not reinterpret a later scalar as the initial value. It never observes INITIAL $j$. Every actual positive source emits exactly $d+1$ complete blocks. The zero child emits exactly two, the high child exactly one, and initial bottom none. Because $d\ge3$, this is a uniform worst fee $d+1$ on the entire prescribed target.

证明（credited lower bound, GLOBAL comparison and history equality）。 The lower-bound clause of Theorem 84.5 applies to exactly these tables and actual sources. For clarity, its root obstruction uses the actual INITIAL tails $m-1,m$ with unequal low/high labels: at most one leading one merges them at the first zero, and at least three leading ones rejects both into the same absorbing archive. Every correct root on either value fibre must therefore have exactly two leading ones. All low sources then have a common tail, while each component has $r+1=2^d+1$ actual low labels on the full cycle. The supplied common-tail binary bound [S10, Lemma 3.2] gives $2^d+1\le2^H$, hence $H\ge d+1$. This argument already ranges over all legal literal words, all-one transfers, paid waits and repairs, arbitrary adaptive descendants, absorbed rejection and homogeneous endpoint stops. It is not a lower bound conditional on (85.5) or on the published GLOBAL root.

Combining that credited lower bound with (85.21) proves the adaptive equality. For GLOBAL control use exactly Theorem 84.5 and its one common stream (84.15), with the full table (84.22), under the same root/high/low/bottom stopping rule and own-endpoint decoder (84.18). Its joined all-action lower bound is (84.14), supported by [IC, Theorem 29.2]. The stream works on both free values and all sources of this one fixed target and pays $2d$ full blocks in the worst branch. The different adaptive suffixes above do not establish this GLOBAL conclusion; the existing same-stream witness does.

The explicit $F=f\circ q_{\rm INITIAL}$, deterministic original evolution and joint actual surjectivity (85.4) give the same prices for records and histories by [S1, Proposition 2.2]. Multiplying the actual paid-block counts by the unchanged width $m$ gives (85.3), including the high root's absorbed suffix and every issued word. ∎

**实例 85.2（A four-block adaptive attainment at $d=3$）。** The target is exactly Example 84.6: $(m,k,T,g)=(62,64,65,1)$, with its same phase table and nine full low labels per component. The positive-child omission pairs at actual suffix indices $1,2,3$ are $\{60,61\},\{57,58\},\{54,55\}$. Enumerate each component's eight indices in binary order $000,\ldots,111$. Valid code choices in that order are

$$
\begin{aligned}
c^{(0)}&=(000,001,010,101,100,011,110,111),\\
c^{(1)}&=(011,001,110,000,100,111,010,101).
\end{aligned}
\tag{85.23}
$$

For value zero the constrained label-index pairs are respectively $\{001,101\},\{000,100\},\{010,110\}$, with required coordinates $1,2,3$. For value one the constrained indices are respectively $110,111,011$. The codes in (85.23) obey all those zero requirements.

The actual root and zero-child word are

$$
\begin{aligned}
P&=11010101010101010101010101010101010101010101010101010101010101,\\
U&=00010000000000000000000000000000000000000000000000000000000000.
\end{aligned}
\tag{85.24}
$$

At the actual suffix starts $62,59,56\pmod{65}$, equations (85.16)–(85.17) give

$$
\begin{aligned}
B_1^{(0)}&=11100111111111111111111110101010101011111111010101010101001001,\\
B_2^{(0)}&=11011111000000000000010101011111111111110101010101010110110101,\\
B_3^{(0)}&=11101011111111111010101000000001010100000001010101111111010101,\\
B_1^{(1)}&=11111100100001101000101100110011001000011010010110010111111010,\\
B_2^{(1)}&=10111100101101001110011001001001000111010011100011011000111111,\\
B_3^{(1)}&=10111100010110011011110101110010001101111001000010111001000010.
\end{aligned}
\tag{85.25}
$$

Every displayed word has exactly 62 bits. The root/first-suffix and subsequent suffix terminal/leading pairs are $(1,3),(1,2),(1,3)$ on value zero and $(1,6),(0,1),(6,1)$ on value one. Their sums are respectively $4,3,4$ and $7,1,7$, all strictly below $k=64$. The respective common-charge counts are $32,16,16$ on each value. Phase-one compensation is $(0,0,0)$ for the row policy and $(0,0,1)$ for the column policy.

The zero child returns $A_{000}$ or $D_{010}$ on pulse difference one and $C$ on zero. The positive child decodes (85.23) from its own three suffix differences. High tails return $R$ only after the whole paid root. Thus the exact adaptive/GLOBAL block pair is $4/6$ and the emitted-bit pair is $248/372$.

Finite literal verification at this target jointly realized and executed all $2\cdot65\cdot64=8320$ successful INITIAL records using the original integer recurrence. The positive, zero and high branches contain respectively $7688,372,260$ records and pay respectively $4,2,1$ blocks in the displayed rule. Across these separate source executions this is $31756$ emitted blocks and $1968872$ emitted bits. Initial bottom was independently realized and stops freely. All 256 Hall subfamilies on each component passed their list cardinality checks.

Additional finite row, inverse, endpoint-decoder and strict-seam checks at $d=4,5,6$ gave positive-child sizes $254,1022,4094$, minimum component multiplicities $14,30,62$ and maximum numbers of required-zero coordinates $2,2,2$. The minimum consecutive suffix common-charge counts across both value policies were respectively $63,254,1022$. These finite results corroborate the ordinary uniform proof; they are not proofs for unbounded $d$, and no program or dataset is part of this delivery.

**数学引文 85.3（Exact overlap, physical increment and source correspondence）。** The five mathematical inputs are this volume through Chapter 84, the canonical [IC] and companions [M], [T3], [F4] at [revision 1692fdfbfffa21b1f73ce56cb10f2ab6aced1296](https://github.com/the-omega-institute/trureturing/tree/1692fdfbfffa21b1f73ce56cb10f2ab6aced1296/docs/develop/theory). The explicitly pinned reference suppliers [S1], [S2], [S10], [S15] and [H] retain the versions in this volume's reference definitions. Each contribution below retains its displayed hypotheses.

The source/action/INITIAL/control/resource correspondence is literal: (85.4) is a single actual original complete history; its INITIAL record is $(v,-j,s)$; its target is the unchanged full (84.2), (84.23); its actions are (85.5), (85.7) and (85.17); its outputs are their own completed scalar or bottom endpoints; and its resource is the actual number of these fully emitted width-$m$ words. The source integer recurrence and matched coefficient cycle come from [IC, Definition 1.1; S2, Theorem 14.1]. Joint realizations and history equivalence come from [IC, Convention 1.2; S1, Convention 1.3 and Proposition 2.2]. First-zero loss and rejection absorption come from [IC, Interface 1.4; S1, Lemmas 4.2–4.3]. Literal inversion and the true all-one tail transfer are [IC, (1.4)–(1.5); S10, Interface 2.1; S15, Section 1 and Definition 1.1].

Chapter 84 supplies the actual two omissions, three-phase chronological displacement, fixed table, all-action component lower bound, sharp rejecting-seam bound and exact common GLOBAL stream. Its nearly full $2d$-coordinate criterion does not supply the $d$-coordinate suffix on the component archive $S$. The new root changes the physically acquired support and counts, without changing the INITIAL target. Equations (85.10)–(85.20) prove the smaller actual attainment, with both omitted phases, available compensation, uniform code selection and every strict seam. The entire full target, not only a marginal archive, is then completed by its paid pulse and absorbed-root branches. That shorter physical protocol is the added fee content.

Chapter 73 and the adaptive part of Chapter 83 have $k=m+1$ and one omission. Their supplied suffix theorem cannot be instantiated here. The finite low-weight Hall method is reused, while the two-requirement bound and non-total requirement proof (85.12)–(85.14) are supplied at the fixed present placement. The underlying generic Hall theorem is credited to [H], pinned mathlib revision $db584cd6d46c92f209a44c0f1c829460d327499d$, statement $\texttt{Finset.all\_card\_le\_biUnion\_card\_iff\_existsInjective'}$; its proof is not repeated or counted as a new fee result.

[S15, Theorem 3.3] supplies a general response/seam certificate, not this uniform fee-attaining root and suffix. Its independent-row Theorem 3.4 and [IC, Chapters 27 and 60–64] require $k\ge2m$, which fails here. The wide and critical material [IC, Theorem 38.1 and Chapters 46–48] has $m\ge k$. The [M, Definition 1.2 and Theorem 2.1], [T3, Definition 1.2 and Theorem 2.1] and [F4, Definition 72.1 and Theorem 72.2] arrivals require an actually issued all-one root, with different surviving INITIAL tails and their respective binary, three-label or four-label hypotheses. None is a logarithmic physical suffix theorem on (85.6). The fixed-stream value-join law [IC, Theorem 29.2] is used only through the already credited GLOBAL equality, not to identify an adaptive component price.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), supplies leaf-reaching observations, tests consistent with available actions, disjoint observed traces and adaptive distinguishing graphs; Figure 3 demonstrates destructive first-action mergers. One input here corresponds to a complete literal word, one output to its completed scalar or bottom, and the distinction is between unequal immutable INITIAL labels on a single actual source. These mature semantics supply no two-omission literal rows, seam count or emitted-fee equality. No generic decision game, Bellman restatement, common-partition relabelling or bound-only wrapper is counted as new content.

The ordinary deductions are repo-derived with this scoped source, library-interface and primary-paper overlap comparison. No exhaustive priority, literature-absence, kernel-certification, independent-prior or independent-review claim is made.

**边界 85.4（Scope, finite fallback and the unchanged original objective）。** The exact adaptive attainment fixes every hypothesis and every placement of Construction 84.4, for every $d\ge3$. It imposes no new target condition. Its two code selections solve precisely the actual row and column tables inherited from that construction, with the full INITIAL tail ranges and arbitrary independent $L_\bot$. The label and code selection is finite and effective from the supplied indexed tables; offline matching, word construction, source-table storage and decoder memory are separate resources with no asserted optimum. A general semantic label table still needs a finite partition presentation or decidable equality as in [S1, Note 5.3].

The conclusion narrows (84.26) to equality for this specified target. It leaves the exact GLOBAL $2d$ witness as separate credited mathematics. Holding the particular GLOBAL root (84.15) fixed need not give the adaptive optimum: in the value-one fibre its zero-coordinate child retains all $r$ column labels together with $C$, so the common-tail binary bound forces at least $d+1$ additional blocks on that child, or total at least $d+2$. The new root (85.5) avoids that conditional obstruction. It does not turn a conditional-root lower bound into a lower bound for every first action.

For the full tail-independent target form (84.2), finite attainment outside the high-capacity criterion is already supported by the supplied phase-recovery theorem [S1, Theorem 3.1]. One common root $110^{m-2}$ rejects the prescribed high tails and safely merges the low tails with their INITIAL labels preserved; then its credited safe pulse scan at the actual post-root offset determines INITIAL phase from the source's own endpoints, after subtracting the known issued displacement. Thus the wording “possibly infinite” in Theorem 84.3 does not describe a necessary residual possibility for that full target form. This is credited finite fallback, not a new bound-only result and not an exact price above the criterion's threshold.

Arbitrary $k=m+2$ placements, arbitrary component or joined class counts, smaller-capacity physical compatibility, other gcds, other orders and widths, low-tail-dependent targets, other high-label coincidences, unrelated acquired supports, mixed-tail continuations and a general optimum over admissible roots remain unresolved. In particular the proof of proper requirements (85.12)–(85.13) uses this placement, and the safety margin (85.18)–(85.19) uses this component multiplicity. Neither clause is asserted for arbitrary tables.

The original exact minimum worst-branch ACTUAL emitted-complete-block fees for every attainable immutable INITIAL target and every original $k\ge2,m\ge1$, separately adaptive and ONE GLOBAL preset stream per fixed target under both original alphabets [IC, Definition 1.3 and Open Problem 9.1], remain open. Different $d$ give different finite readers and fixed targets, not one stream for their union. The conclusions here are ordinary complete mathematical proofs, without Lean/kernel certification; no compilation, ingestion, deposit, coverage or freezing is asserted.

## 追加锚（本行以下为增补区）
## 86. A one-block GLOBAL placement surcharge with unchanged joined multiplicities

Two distinct fixed INITIAL targets can have the same component label counts and the same joined multiplicity multiset, yet have different optimal GLOBAL fees. Here two entries of Construction 84.4 are changed. Every correct root then splits both doubled joined classes between its two successful output archives. Their total label count exceeds the capacity of $2d$ blocks. An actual common stream attains the resulting $2d+1$ bound, including its literal inverses, strict seams and paid stopping rule. The adaptive positive archive is exactly the archive already treated in Chapter 85.

**定义 86.1（The reader, the distinct fixed target and the entire source domain）。** Fix an integer $d\ge3$ and retain every parameter, label and ordered phase assignment $Z$ of Construction 84.4:

$$
h=2d,\qquad r=2^d,\qquad N=r^2=2^h,\qquad
m=N-2,\qquad k=N=m+2,\qquad T=N+1=m+3.
\tag{86.1}
$$

The reader is exactly [IC, Definition 1.1]. Its integer weights and matched coefficient cycle are

$$
G_i=2^i\ (0\le i<k),\qquad
G_i=\sum_{a=1}^kG_{i-a}\ (i\ge k),\qquad
V_k(w)=\sum_{i<|w|}w_iG_i,\qquad
\gamma_i=G_i\bmod2=\mathbf1_{\{0,T-1\}}(i\bmod T).
\tag{86.2}
$$

Bits are read in increasing weight position. Legal histories avoid $1^k$. The source prior is all actual finite histories of complete width-$m$ blocks, including rejected histories. Since $N=4^d\equiv1\pmod3$, the actual gcd is $\gcd(m,T)=1$. Every successful endpoint record is in $\mathbb F_2\times\mathbb Z/T\mathbb Z\times\{0,\ldots,k-1\}$, with an independent absorbing record $\bot$. A zero sends $(v,\theta,s)$ to $(v,\theta+1,0)$; a one sends it to $(v\oplus\gamma_\theta,\theta+1,s+1)$ if $s+1<k$, and otherwise to $\bot$. Both bits preserve $\bot$. Phase is advanced by the literal bits, without an intermediate observation.

Write $j=-\theta_{\rm INITIAL}\pmod T$. The labels are the original disjoint sets $\{A_i:i\in\mathbb F_2^d\}$ and $\{D_\ell:\ell\in\mathbb F_2^d\}$, the distinct common fresh $C,R$, and arbitrary independent $L_\bot$. Let $\lambda_v$ be exactly (84.23), including its ordered completion. Define new tables by

$$
\widetilde\lambda_v(j)=
\begin{cases}
\lambda_v(0),&j=1,\\
\lambda_v(2),&j=N,\\
\lambda_v(j),&j\notin\{1,N\},
\end{cases}
\qquad v\in\mathbb F_2.
\tag{86.3}
$$

The entire immutable INITIAL target and its history pullback are

$$
\begin{aligned}
\widetilde f(v,-j,s)&=
\begin{cases}
\widetilde\lambda_v(j),&0\le s<m,\\
R,&s=m\text{ or }s=m+1,
\end{cases}\\
\widetilde f(\bot)&=L_\bot,\qquad
\widetilde F(w)=\widetilde f(q_{\rm INITIAL}(w)),\qquad
\widetilde\Lambda(j)=(\widetilde\lambda_0(j),\widetilde\lambda_1(j)).
\end{aligned}
\tag{86.4}
$$

In particular the changed entries refer to INITIAL phase, and the high band refers to INITIAL tail. Neither is reevaluated after an action. The common label $C$ remains at low phase $N-1$, while low phase $N$ now has the original phase-two pair. The initial-bottom label may coincide with any other label.

The free initial observation is its scalar value or bottom. Each operation issues exactly one complete $m$-bit word and observes only its own completed endpoint. Every issued word costs one block and $m$ emitted bits, even when it rejects before that endpoint; waits, padding, repair and absorbed bits receive no discount. Both original alphabets are retained. Here every $m$-bit word is internally legal because $m<k$, so their literal action sets coincide, while cross-block rejection remains absorbing. Adaptive control may choose the next word from the acquired archive. GLOBAL control requires one preset literal stream on both free-value fibres and all sources of this one fixed target, with endpoint-dependent stopping and decoding. There is no reset, copy, hidden INITIAL clock, intermediate read or borrowed branch observation.

Every record used in these claims is jointly actual. For $v\in\mathbb F_2$, every phase $j$ and every $0\le s<k$, the credited witness [IC, Convention 1.2; S1, Convention 1.3] is

$$
\begin{aligned}
\ell&\equiv0\pmod m,\qquad
\ell\equiv-j\pmod T,\qquad \ell\ge s+2,\\
\eta&=\bigoplus_{i=\ell-s}^{\ell-1}\gamma_i,\qquad
w(v,j,s)=(v\oplus\eta)0^{\ell-s-1}1^s.
\end{aligned}
\tag{86.5}
$$

Coprimality supplies arbitrarily large such $\ell$. The separating zero makes this one history legal, and its first bit compensates the terminal run's contribution. Its value, phase, tail and complete-block length are simultaneously $v,-j,s,\ell$. Its blocks belong to both alphabets; its unobserved length is not an input to the controller. The history $1^{2m}$ separately realizes initial bottom, since $m<k<2m$ and both constituent source blocks are internally legal.

The two new doubled joined classes are precisely

$$
\begin{aligned}
X&=(\lambda_0(0),\lambda_1(0))
  =(A_{i(\varepsilon_0)},D_0),
&\widetilde\Lambda^{-1}(X)&=\{0,1\},\\
Y&=(\lambda_0(2),\lambda_1(2))
  =(A_{i(\varepsilon_0\oplus\varepsilon_1)},D_0),
&\widetilde\Lambda^{-1}(Y)&=\{2,N\}.
\end{aligned}
\tag{86.6}
$$

Here $\varepsilon_a$ is the coordinate-$a$ unit used in (84.20); its last $d$ coordinates are zero for $a=0,1$. Thus $X\ne Y$. Originally $\nu$ occurred at $1,3$ and the joined label $(C,C)$ occurred at $N-1,N$. Removing their occurrences at $1,N$ leaves them as singletons at $3,N-1$, respectively. The new entries add one occurrence each of the formerly singleton classes $X,Y$. Every other class remains singleton. Both full joined images therefore have $N-1$ classes and multiplicity multiset consisting of two twos and $N-3$ ones.

Each full component still has exactly $r+1=2^d+1$ low labels. Indeed on

$$
S=\{0,\ldots,N-2\}\setminus\{1\}
\tag{86.7}
$$

the tables are unchanged, and $Z:S\to\Omega$ is the bijection (85.8), so every one of the $r$ row labels and every one of the $r$ column labels remains present. Phase $N-1$ retains $C$. No additional label is introduced by (86.3). Component occurrence counts need not be unchanged. The new two tables differ at every phase except $N-1$, since all their other entries lie in the disjoint row and column label sets. These are genuinely different component tables of one jointly inhabited target.

**引理 86.2（All-action lower bounds and the compulsory splitting of both doubles）。** In Definition 86.1, every correct first action on either nonbottom free-value fibre has prefix $110$. Under either original alphabet,

$$
C_{\rm ad}(\widetilde f)\ge d+1,\qquad
C_{\rm pre}(\widetilde f)\ge 2d+1.
\tag{86.8}
$$

The GLOBAL bound includes every preset stream and endpoint stopping rule, rather than only streams constant on each joined class.

证明。 Fix either free INITIAL value and any phase. The actual tails $m-1,m$ have unequal low/high labels because $R$ is fresh. A root with at most one leading one reaches its first zero on both sources: even the larger tail then satisfies $m+1<k$. Their value and phase agree, and that zero merges their tails. Their unequal INITIAL labels cannot be recovered at any later endpoint. A root with at least three leading ones, including $1^m$, rejects both by the third bit. Both completed archives are then absorbing bottom; their unobserved rejection positions cannot distinguish them. Free stopping is also impossible. The supplied first-zero and rejection-loss interfaces therefore force exactly two leading ones, hence prefix $110$ [IC, Interface 1.4; S1, Lemmas 4.2–4.3].

Every such root rejects precisely INITIAL tails $m,m+1$. Each low tail survives because $s+2\le m+1<k$, reaches the zero and completes safely. Its first-zero merger preserves the tail-independent label. All low sources acquire the same actual current tail $\rho(B_0)$, independent of phase and initial tail. In a fixed successful scalar-output archive their current scalar is common as well.

Thereafter any literal word on such an archive either succeeds on all its candidates or rejects all, since safety depends only on the current tail and the word. A successful word gives at most two endpoint scalars, with a common tail in each child. A common rejecting word cannot finish an archive with unequal INITIAL labels, since all later endpoints are bottom; a homogeneous archive can already stop. Induction gives at most $2^a$ distinct-label leaves with $a$ further paid words [S10, Lemma 3.2]. This includes all literal words and the true all-one transfer $\sigma\mapsto\sigma+m$, zero waits, padding, repair attempts, absorbed suffixes and early homogeneous stops. It does not regard bottom as a useful third outcome on a common-tail archive.

On either component, the $r+1$ full low labels must fit below the two successful root outcomes of any controller with worst fee $H$. Hence $r+1\le2^H$ and $H\ge d+1$. The root may depend on the remembered free value; this inequality holds on each such fibre separately.

For GLOBAL control apply the exact value-join law [IC, Definition 29.1 and Theorem 29.2] to the entire target (86.4). Its scalar-independent low table is $\widetilde\Lambda$, high label is $(R,R)$ and initial bottom is separate. The law retains one actual stream and its fee, including arbitrary stops and absorption. It uses scalar complementation to decode the pair from the source's own archive; it executes no second experiment.

Let $q_0$ be the actual charge row of the compulsory root of any correct joined controller. The literal equations (84.4) give

$$
q_0(0)=1,\qquad q_0(1)=0,\qquad q_0(2)=1,\qquad
q_0(N-1)=q_0(N)=0.
\tag{86.9}
$$

Thus both $X$ and $Y$ occur in both successful root-difference children, regardless of every other bit of the root. No other joined class can occur in both, since every other class is singleton. If $L_e$ is the joined label image of child $e$, then

$$
|L_0\cup L_1|=N-1,\qquad
L_0\cap L_1=\{X,Y\},\qquad
|L_0|+|L_1|=N+1.
\tag{86.10}
$$

Each child has at most $H-1$ further paid words and therefore $|L_e|\le2^{H-1}$. Consequently $N+1\le2^H$, forcing $H\ge h+1=2d+1$. This counts distinct labels separately on the actually acquired children, allowing a repeated label to have different full codes. Early stops do not combine the two archives or return two unequal labels from one homogeneous leaf. Paid waits still occupy their chronological slots. The argument excludes a price at most $2d$ for this fixed target even with phase-wise splitting, arbitrary later words or attempted common rejection. ∎

**引理 86.3（One actual GLOBAL stream attains the extra block）。** For Definition 86.1 there is a single lawful stream of $h+1=2d+1$ complete words serving both free values and every actual source, with no extra clearing or final cleanup.

证明（available simultaneous rows）。 Use the actual root

$$
P=11(01)^{(m-2)/2}.
\tag{86.11}
$$

Its width is $m$, its prefix is $110$ and its literal terminal tail is one. By the preceding root analysis it rejects precisely the two high INITIAL tails and preserves every low label. Its actual arithmetic row is $\mathbf1_S$, where $S$ is (86.7). Thus all low sources have current tail one, with successful root-zero phases exactly $\{1,N-1,N\}$.

Number the $h$ suffix words by their actual absolute issued indices $t=1,\ldots,h$. Their omissions, including the last suffix index, are

$$
M_t=\{N-1-3t,N-3t\}.
\tag{86.12}
$$

These are (84.3) on the present calendar, since $m\equiv-3\pmod T$. There is no wrap in (86.12). The least representative is $N-1-3h\ge45$ at $h=6$, and the inequality persists for $h\ge6$. The $h$ adjacent pairs are disjoint, lie in $S$, and avoid all three root-zero phases. This verifies the domain of every unavailable coordinate actually used below.

For suffix codes use $\mathbb F_2^h$ with coordinates $1,\ldots,h$ and units $u_1,\ldots,u_h$. Put

$$
K=\mathbb F_2^h\setminus\{0,u_1\}.
\tag{86.13}
$$

Choose a bijection $\xi:S\to K$ subject to $\xi_t(j)=0$ for $j\in M_t$. Such a choice exists by the following direct finite selection. There are exactly $2h$ constrained phases and each belongs to only one $M_t$. Its allowed set $\{z\in K:z_t=0\}$ has at least $N/2-2$ members. The elementary inequality

$$
N/2-2=2^{h-1}-2\ge2h\qquad(h\ge6)
\tag{86.14}
$$

holds at six and is preserved by increasing $h$. Assign distinct allowed vectors to these $2h$ phases in any fixed order: before each assignment at most $2h-1$ vectors have been used, so one allowed vector remains. The remaining phases have no coordinate restriction and their number equals the number of unused vectors of $K$. Any bijection between those finite sets completes $\xi$. This chooses rows for a protocol; it does not alter (86.3).

Extend $\xi$ to a full suffix-vector table $Q$ by

$$
Q(j)=\xi(j)\ (j\in S),\qquad
Q(1)=u_1\oplus u_2,\qquad Q(N-1)=0,\qquad Q(N)=u_2.
\tag{86.15}
$$

The XOR of the full $h$-cube is zero. Therefore $\bigoplus_{z\in K}z=u_1$, while the XOR of the three other displayed vectors is also $u_1$. It follows that $\bigoplus_{j=0}^NQ(j)=0$. Each coordinate row $Q_t$ has even full-cycle charge and vanishes on its actual $M_t$. The supplied literal inverse consequently gives the actual width-$m$ word

$$
B_{t,i}=\bigoplus_{b=0}^{i}Q_t(tm+b\bmod T),
\qquad 1\le t\le h,\quad 0\le i<m.
\tag{86.16}
$$

Its complete arithmetic row is exactly $Q_t$. These are simultaneous full rows of these very words, with the actual chronological starts $tm\bmod T$. The values at the root-zero phases are prescriptions for emitted bits, rather than extra observations or a borrowed sibling source.

证明（strict seams and the true inherited tail）。 Available even rows alone do not establish safe execution. Here their density supplies the additional physical condition. In $K$, coordinate one has $N/2-1$ ones, and every other coordinate has $N/2$ ones. For two distinct consecutive suffix coordinates, all $N/4$ vectors with both bits one remain in $K$, because neither removed vector has two one coordinates. Since $\xi$ is a bijection onto $K$, the actual complete row intersections satisfy

$$
\begin{aligned}
|\{j:q_{0,P}(j)=Q_1(j)=1\}|&=N/2-1>3,\\
|\{j:Q_{t-1}(j)=Q_t(j)=1\}|&\ge N/4\ge16>3,
&&2\le t\le h.
\end{aligned}
\tag{86.17}
$$

The first equality uses precisely $S$, where the root charge is one; its charge is zero at the other three phases. The second inequality counts distinct actual phases of this same table. It does not assume that separately feasible rows are jointly feasible.

Every low source completes $P$. If $B_1$ rejected after that successful root on any such source, the sharp original rejecting-seam bound of Lemma 84.2 would make the first intersection in (86.17) at most three. This is a contradiction. Inductively, after successful $B_{t-1}$ the same lemma excludes rejection by $B_t$ using the second intersection. Thus the entire stream succeeds on every low source.

Lemma 84.2 retains the true incoming tail even when a preceding word is all ones; its transfer is $\sigma+m$, not the literal run $m$. In the present selected stream each suffix row has at least $N/2-1>2$ charged phases, whereas an all-one word has only its two charged endpoints. Hence every selected suffix word contains a zero. Only after this exclusion may its actual outgoing tail be identified with its literal trailing run. All the actual seams therefore satisfy

$$
1+\alpha(B_1)<k,\qquad
\rho(B_{t-1})+\alpha(B_t)<k\quad(2\le t\le h).
\tag{86.18}
$$

Every internal run is shorter than $k$ because the width is $m<k$. No wait, padding, repair or clearing word occurs between these consecutive issued indices.

证明（own-endpoint decoding and fully paid stops）。 The length-$(h+1)$ vector $(\mathbf1_S(j),Q(j))$ is injective on the entire phase cycle: on $S$ this follows from bijectivity of $\xi$, and off $S$ the three suffix vectors $u_1\oplus u_2,0,u_2$ are distinct. Codes on opposite root outcomes are already distinct. In particular the two occurrences of each doubled joined label receive different root bits, as required by Lemma 86.2.

A low source executes exactly

$$
P\mid B_1\mid\cdots\mid B_h.
\tag{86.19}
$$

From its own scalar endpoints $v_0,\ldots,v_{h+1}$ it obtains

$$
(v_1\oplus v_0,\ldots,v_{h+1}\oplus v_h)
=(\mathbf1_S(j),Q(j)).
\tag{86.20}
$$

At that completed endpoint, the inverse finite table gives the unique INITIAL phase $j$. Return $\widetilde\lambda_{v_0}(j)$, using the remembered free INITIAL value. Decoding phase from these acquired differences is not a hidden phase observation. The words in (86.19) are fixed independently of that value and all subsequent outputs.

Initial bottom stops freely with $L_\bot$. High INITIAL tails $m+1$ and $m$ are absorbed on the first and second bits of $P$, respectively; both still emit all $m$ bits of the root and stop with $R$ only at its completed paid endpoint. Every low source stops after all $h+1$ fully paid words. The joint witnesses (86.5) supply actual low sources attaining this worst fee. No terminal operation is needed. ∎

**定理 86.4（Exact new whole-target prices under both alphabets）。** For every $d\ge3$ in Definition 86.1, under each original literal alphabet,

$$
\boxed{
C_{\rm ad}(\widetilde f)=C_{\rm ad}(\widetilde F)=d+1,\qquad
C_{\rm pre}(\widetilde f)=C_{\rm pre}(\widetilde F)=2d+1.
}
\tag{86.21}
$$

The exact minimum worst emitted-bit fees are respectively $m(d+1)$ and $m(2d+1)$. The additional price result is the GLOBAL equality and its sharp compulsory-root obstruction. The adaptive positive-child construction below is credited reuse of Chapter 85.

证明（the precise reused adaptive archive）。 Issue the same actual root $P$ of (86.11), retaining the INITIAL value $v$. The high and initial-bottom rules are those already proved. A successful root difference one has exactly support $S$, current scalar $v\oplus1$, current tail one, and current phase $-j+m$. On $S$ neither modified entry occurs, so $\widetilde\lambda_v|_S=\lambda_v|_S$. This is exactly the positive archive in (85.6), with the same parameter, same joint INITIAL candidates, same component labels, same multiplicities and same chronological suffix indices. The proof of Chapter 85's positive continuation applies to this actual archive, rather than to the changed full target without checking its restriction.

Specifically (85.11)–(85.15) supplies a bijection $c^{(v)}$ of its $r$ component labels onto the $d$-cube, zero in coordinate $t$ on both phases of $M_t$ for $1\le t\le d$. The proper-requirement verification (85.12)–(85.13) uses the unchanged prescribed omission-pair labels. Use precisely the full rows and inverses

$$
\begin{aligned}
q_t^{(v)}(j)&=c_t^{(v)}(\widetilde\lambda_v(j))&&j\in S,\\
q_t^{(v)}(1)&=\bigoplus_{j\in S}c_t^{(v)}(\widetilde\lambda_v(j)),\\
q_t^{(v)}(N-1)&=q_t^{(v)}(N)=0,\\
B^{(v)}_{t,i}&=\bigoplus_{b=0}^{i}q_t^{(v)}(tm+b\bmod T)
&&1\le t\le d,\quad0\le i<m.
\end{aligned}
\tag{86.22}
$$

These are (85.16)–(85.17) on the identical positive support. Their available phase-one parity compensation is an offline bit prescription; that phase is absent from this archive even though it now has a different INITIAL label elsewhere. All full rows are even and zero on their actual omissions. The credited minimum component multiplicity on $S$ is $r-2$. Consequently their root/first-suffix and consecutive suffix charged intersections are at least $r(r-2)/2$ and $r(r-2)/4$, respectively, both strictly above three. The original Lemma 84.2 therefore gives every strict seam exactly as in (85.18)–(85.20). These same dense rows exclude all-one suffixes; no inherited tail is replaced incorrectly.

A positive source issues $P\mid B_1^{(v)}\mid\cdots\mid B_d^{(v)}$, reads its own $d$ suffix endpoint differences, inverts $c^{(v)}$, and returns its immutable component label. Its total fee is $d+1$. The suffix selection may use the free INITIAL value, so this supplies adaptive attainment and is not the GLOBAL witness.

证明（the changed zero archive is actually completed）。 Root difference zero now has three phases $\{1,N-1,N\}$ with joined labels $X,(C,C),Y$. At absolute issued indices one and two, give this archive the complete words

$$
U=0^3\,1\,0^{m-4},\qquad
V=0^5\,1\,0^{m-6}.
\tag{86.23}
$$

Their isolated ones are at local positions three and five. At index one the path starts at $m=N-2$, so $U$ has arithmetic support $\{0,1\}$ modulo $T$. At index two the start is $2m\equiv N-5\pmod T$, so $V$ has support $\{N,0\}$. Phase zero is absent from this archive; its prescribed charges belong to these same literal words and supply no observed sibling output.

Both words start and end zero. The incoming tail of $U$ is the root's actual one, so its seam sum is $1+0<k$; $U$ leaves tail zero and the next seam sum is $0+0<k$. Their only internal one-runs have length one. All these sources succeed. Their own two successive endpoint differences distinguish

$$
1\longmapsto(1,0),\qquad
N-1\longmapsto(0,0),\qquad
N\longmapsto(0,1).
\tag{86.24}
$$

Return $\lambda_v(0)$, $C$, or $\lambda_v(2)$, respectively. On value one the first and third labels are both $D_0$, which is permitted; the rule still decodes correctly. Stop at the second pulse's completed endpoint. This zero branch pays exactly three blocks including $P$, with no final cleanup. Since $d\ge3$, it does not exceed $d+1$.

Thus the adaptive worst fee is at most $d+1$ on the entire new target. Lemma 86.2 proves the matching all-action lower bound; Lemmas 86.2–86.3 similarly prove the GLOBAL equality. Deterministic record evolution, actual surjectivity (86.5) and the explicit pullback (86.4) give both record/history equalities [S1, Proposition 2.2]. Controllers receive only the specified record output archive, not the raw source history. Finally every issued word has exactly $m$ emitted bits, including the absorbed part of the high root. Multiplying both optimal worst-block fees by $m$ gives the stated bit fees. ∎

**比较 86.5（Two fixed targets, equal counts and different placement prices）。** Let $f,F$ continue to denote the original Construction 84.4 target and its original history pullback. They are distinct from $\widetilde f,\widetilde F$.

| Full low-cycle quantity | Original $f$ | New $\widetilde f$ |
| --- | --- | --- |
| Component label counts on each value | $2^d+1$ | $2^d+1$ |
| Joined class count | $2^{2d}-1$ | $2^{2d}-1$ |
| Joined multiplicity multiset | two twos; $N-3$ ones | two twos; $N-3$ ones |
| Doubled joined-class phase sets | $\{1,3\}$ and $\{N-1,N\}$ | $\{0,1\}$ and $\{2,N\}$ |
| Exact adaptive/GLOBAL block pair | $(d+1,2d)$ | $(d+1,2d+1)$ |
| Exact adaptive/GLOBAL emitted-bit pair | $(m(d+1),2md)$ | $(m(d+1),m(2d+1))$ |

The original price pair is credited to Theorems 84.5 and 85.1 on their unchanged fixed target. The new GLOBAL price is exactly one block, or $m$ emitted bits, larger. Its excess over its adaptive price is $d$ blocks; the original excess is $d-1$.

The two edits change the INITIAL equality partition. For example phases $N-1,N$ had equal labels in each old component and now have unequal labels. No bijective renaming of labels can produce that change. The edits also relocate which classes are doubled, while preserving their multiset of sizes. They are not a rearrangement of component occurrence counts claimed to be invariant.

There is no contradiction between an old GLOBAL price $2d$ and a new GLOBAL price $2d+1$: their target arguments differ. Lemma 86.2 refutes a GLOBAL bound at most $2d$ for (86.4). It neither refutes nor repairs an answer about the original $f$. The old-target equalities retain their own ordinary proofs and hypotheses, and the new-target equalities require the stream and obstruction proved here.

**数学引文 86.6（Exact-domain overlap and additional physical price content）。** The ordinary source comparison uses this volume through Chapter 85 and the canonical [IC], with [M], [T3] and [F4], at [revision 8886bf3d473ec3b91844f673c250bbc881425209](https://github.com/the-omega-institute/trureturing/tree/8886bf3d473ec3b91844f673c250bbc881425209/docs/develop/theory). The original suppliers [S1], [S2], [S10] and [S15] retain their explicit immutable reference pins. Reading those results is not a Lean application or kernel verification.

The source/action/INITIAL/control/fee correspondence is exact: a source is the one original history (86.5); its INITIAL record is $(v,-j,s)$; its target is (86.3)–(86.4); its actions are complete literal words at the displayed absolute issued indices; its observations are those words' own completed scalar or bottom endpoints; and its optimized resource is their actual emitted block or bit count. Both values and every actual low/high tail and phase are included. The full history target factors through the original INITIAL record, not a modified terminal record.

[IC, Definitions 1.1–1.3 and Interface 1.4; S1, Definition 1.2, Convention 1.3, Proposition 2.2 and Lemmas 4.2–4.3; S2, Theorem 14.1] supplies the integer reader, matched cycle, joint source witnesses, observation/cost contract and irreversible first-zero loss. [S10, Interface 2.1 and Lemma 3.2] supplies the literal arithmetic inverse and common-tail binary bound. [S15, Section 1 and Definition 1.1] supplies strict safety and the true all-one outgoing tail. [IC, Definition 29.1 and Theorem 29.2] supplies the exact preset value join, including early stops and absorption. Those ingredients are credited reuse.

Chapter 84 supplies the present two-omission calendar and the sharp rejecting-seam bound, including the inherited-tail exception. Its Theorem 84.3 retains phase-wise splitting and applies to the new $N-1$ joined classes at depth $h$. Here both doubled classes have unequal compulsory root bits, so any separating $h$-coordinate assignment would need at least $N+1$ distinct vectors in a cube of size $N$. Its criterion fails. That theorem supplies no fee-attaining $h+1$ stream after failure. Lemma 86.3 supplies this missing physical attainment, proving simultaneous availability, parity, dense intersections and strict seams on the full cycle, rather than substituting the covered criterion for a new price.

Theorem 84.5's attaining phase table and Theorem 85.1's full-target conclusion refer to the old entries at $1,N$ and cannot be substituted for the new target. Only Chapter 85's exact positive-archive continuation is reused in (86.22), after verifying equality of support, labels, multiplicities, current tail and chronological indices. The two-pulse rule completes the different zero archive. No new adaptive supplier theorem or new generic matching theorem is counted as the price contribution.

Chapter 79 already establishes a placement surcharge with unchanged class sizes on its two targets. It has original $k=m+1$, one omission, identical value tables and a saturated full low-label count, and its bad placement increases the adaptive price as well. Chapter 81 has the same one-omission order, three positive even joined classes on its stated support, a fresh singleton outside label and a saturated full joined count; its obstruction uses their XOR and specified missed-phase ownership. Chapters 80, 82 and 83 also retain $k=m+1$ and their own counts and placements. Those are honest related results, not the two-doubled-class obstruction and safe higher-depth stream at (86.1).

[S15, Theorem 3.3] is a general actual response/seam certificate, not a numerical optimum for this fixed target. Its independent-row Theorem 3.4 and [IC, Chapters 27 and 60–64] require $k\ge2m$, which would require $N\le4$ here and fails for $d\ge3$. The wide and critical results [IC, Theorem 38.1 and Chapters 46–48] have $m\ge k$ and do not apply. The actual all-one-root archives priced in [M, Definitions 1.1–1.3 and Theorem 2.1; T3, Definition 1.2 and Theorem 2.1; F4, Definition 72.1 and Theorem 72.2] retain their own mixed-tail, three-label or four-label arrival and target conditions. Even when their numerical parameter range includes $k=m+2$, their arrival is excluded for this full target by the compulsory $110$ root. Their additional archive prices do not give the whole-target optimum here.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), supplies the mature distinction between legal tests, completed leaf-reaching observations, disjoint observed traces and adaptive distinguishing graphs, together with destructive first-action mergers. Here one input is a complete emitted word, one output is its completed scalar or bottom, and the required distinction is between immutable INITIAL labels of one actual source. That framework supplies no KBonacci omission schedule, seam inequality or emitted-fee equality. Binary capacity and elementary cube XOR are likewise credited background, not new standalone results.

The added ordinary mathematics is the exact one-block whole-target GLOBAL surcharge at this changed placement, the compulsory splitting obstruction for all actions and stops, and a simultaneous lawful optimum under the actual two-omission calendar. The deductions are repo-derived with the scoped comparison above. No worldwide novelty, exhaustive literature-absence, independent-prior, independent-review or fresh Lean/kernel claim accompanies them.

**数据 86.7（Own finite mathematical corroboration and its bounds）。** Direct finite checks of the fixed tables, coordinate omissions, full charge parity, literal inverses, endpoint codes and strict seam sums give:

| $d$ | Actual phase count | Joined classes | Minimum consecutive GLOBAL common-charge count | Maximum GLOBAL seam sum | Minimum consecutive adaptive positive-trace common-charge count | Maximum adaptive positive-trace seam sum |
| --- | --- | --- | --- | --- | --- | --- |
| $3$ | $65$ | $63$ | $16$ | $6$ | $15$ | $4$ |
| $4$ | $257$ | $255$ | $64$ | $6$ | $63$ | $2$ |
| $5$ | $1025$ | $1023$ | $256$ | $6$ | $254$ | $2$ |
| $6$ | $4097$ | $4095$ | $1024$ | $6$ | $1022$ | $1$ |

The GLOBAL checks use the finite choice in Lemma 86.3 with constrained phases in increasing order, the least unused allowed binary vector at each such phase, and ordered completion on the remaining phases. Their root/first-suffix common-charge counts are $31,127,511,2047$, respectively. Each table has exactly the two new doubled phase sets in (86.6), unchanged component counts $9,17,33,65$, and compulsory-root total joined-label appearances $65,257,1025,4097$. The adaptive checks select valid distinct component representatives of the credited lists; their full rows, inverses and seam sums refer to those selected words. All $131584=2(2^8+2^{16})$ component Hall subfamilies at $d=3,4$ satisfy the list cardinality inequalities, including empty subfamilies. No exhaustive subfamily claim is made at larger $d$.

At $d=3$, integer-recurrence execution jointly realizes all $2\cdot65\cdot64=8320$ successful INITIAL records with legal complete source histories of lengths between $62$ and $4092$. The integer weights used extend through index $4525$. Every displayed controller decodes its source's own endpoint archive to the new INITIAL label. GLOBAL has $8060$ low records paying seven blocks and $260$ high records paying the whole root, for $56680$ issued blocks and $3514160$ emitted bits across these separate source executions. Adaptive has $7688$ positive records paying four blocks, $372$ zero records paying three, and the same $260$ high records paying one, for $32128$ blocks and $1991936$ bits. Initial bottom is separately realized by $1^{124}$ and stops freely.

These finite bounds concern the chosen protocols and stated parameter ranges. They do not enumerate all width-$62$ actions or prove an unbounded optimum by computation. The all-action lower bounds and the uniform $d\ge3$ physical attainment are the ordinary arguments above. No check program or dataset is part of the chapter.

**边界 86.8（Exact restricted progress and the remaining objective）。** The price theorem fixes every label, every unmodified phase entry and the two specified INITIAL edits of Construction 84.4, for every integer $d\ge3$. It includes both genuinely different value tables, all low tails $0\le s<m$, precisely the two high tails with common fresh $R$, arbitrary independent initial bottom, the actual gcd one, both original alphabets and the explicit history pullback. It counts all issued complete words and their absorbed bits. Different $d$ give different readers and fixed targets, not one stream for their union.

The finite choices for codes and decoders use the supplied indexed tables. Offline selection, storage, controller memory and source-description acquisition are separate resources with no optimality assertion. The GLOBAL rule reads the free initial output and $2d+1$ paid endpoints on every low source; the adaptive positive rule reads the free output and $d+1$ paid endpoints. High sources have one paid complete endpoint and initial bottom has none. All stops occur at endpoints, without a final clearing fee.

Arbitrary new placements or multiplicity profiles, smaller-capacity codes, arbitrary high-label coincidences, low-tail-dependent targets, other orders and widths, other gcds, unrelated acquired archives and general adaptive root selection remain outside the equality. The original exact minimum worst-branch ACTUAL emitted-complete-block fees for every attainable immutable INITIAL target and all original $k\ge2,m\ge1$, separately adaptive and ONE GLOBAL preset stream per fixed target under both alphabets [IC, Definition 1.3 and Open Problem 9.1], remain open. This chapter is a restricted exact result in that continuing objective. Its proofs are ordinary mathematics; no Lean/kernel certification, compilation, ingestion, deposit, coverage or freezing is asserted.

## 追加锚（本行以下为增补区）
## 87. A small-capacity two-omission whole target at order sixteen

At $k=16$, $m=14$, the two omitted phases move by three after each issued word. A two-coordinate component code can have only three common charged phases, so the high-capacity safety argument does not settle its physical execution. The fixed target below has different row and column equality partitions, five low labels on each free-value fibre and fifteen joined low labels. Explicit literal continuations complete both component archives in three total blocks and the whole joined target in five. The target is defined independently by its full table; no $d=2$ substitution into Construction 84.4 is used.

**定义 87.1（One full immutable target on the original reader）。** Retain the original integer reader and source semantics of [IC, Definitions 1.1–1.3 and Interface 1.4]. Here

$$
k=16,\qquad m=14,\qquad T=17,\qquad \gcd(14,17)=1.
\tag{87.1}
$$

The integer weights, scalar reading and coefficient cycle are

$$
\begin{aligned}
G_i&=2^i &&(0\le i<16),\\
G_i&=\sum_{a=1}^{16}G_{i-a} &&(i\ge16),\\
V_{16}(w)&=\sum_{i<|w|}w_iG_i,\qquad
\gamma_i=G_i\bmod2=\mathbf1_{\{0,16\}}(i\bmod17).
\end{aligned}
\tag{87.2}
$$

The last equality is the matched cycle supplied by [S2, Theorem 14.1]. It also follows directly here from $G_{i+17}=2G_{i+16}-G_i$ and the initial seventeen parities. Bits are read in increasing weight position. A legal history avoids $1^{16}$. The source prior consists of all finite actual histories of complete fourteen-bit blocks, including the empty and rejected histories. For a legal history its record and free output are

$$
q(w)=(V_{16}(w)\bmod2,\ |w|\bmod17,\ s(w)),
\qquad o(q)=v,
\tag{87.3}
$$

where $s(w)$ is its terminal one-run length. Every rejected history has record and output $\bot$, independent of the two scalar outputs. Successful records have $v\in\mathbb F_2$, every phase $\theta\in\mathbb Z/17\mathbb Z$, and every tail $0\le s<16$. A zero sends $(v,\theta,s)$ to $(v,\theta+1,0)$; a one sends it to $(v\oplus\gamma_\theta,\theta+1,s+1)$ when $s+1<16$, and otherwise to $\bot$. Both bits preserve $\bot$. These bit transitions define execution and supply no bitwise observation.

Take pairwise distinct labels $A_{00},A_{01},A_{10},A_{11},D_{00},D_{01},D_{10},D_{11},C,R$. The initial-bottom label $L_\bot$ is independently prescribed and may coincide with any of them. Write $j=-\theta_{\rm INITIAL}\pmod{17}$. The following table fixes every low-phase entry. Where a four-bit entry $z(j)$ is present, its first two bits index $A$ and its last two index $D$; $C$ is a semantic label, not a four-bit index.

| INITIAL phase $j$ | $z(j)$ | $\lambda_0(j)$ | $\lambda_1(j)$ |
| --- | --- | --- | --- |
| $0$ | $1000$ | $A_{10}$ | $D_{00}$ |
| $1$ | $1000$ | $A_{10}$ | $D_{00}$ |
| $2$ | $1100$ | $A_{11}$ | $D_{00}$ |
| $3$ | $0100$ | $A_{01}$ | $D_{00}$ |
| $4$ | $0110$ | $A_{01}$ | $D_{10}$ |
| $5$ | $0111$ | $A_{01}$ | $D_{11}$ |
| $6$ | $1001$ | $A_{10}$ | $D_{01}$ |
| $7$ | $1011$ | $A_{10}$ | $D_{11}$ |
| $8$ | $1101$ | $A_{11}$ | $D_{01}$ |
| $9$ | $0010$ | $A_{00}$ | $D_{10}$ |
| $10$ | $1010$ | $A_{10}$ | $D_{10}$ |
| $11$ | $1110$ | $A_{11}$ | $D_{10}$ |
| $12$ | $0000$ | $A_{00}$ | $D_{00}$ |
| $13$ | $0101$ | $A_{01}$ | $D_{01}$ |
| $14$ | $1111$ | $A_{11}$ | $D_{11}$ |
| $15$ | $C$ | $C$ | $C$ |
| $16$ | $1100$ | $A_{11}$ | $D_{00}$ |

Define the entire record target and its explicit history pullback by

$$
\begin{aligned}
f_{87}(v,-j,s)&=
\begin{cases}
\lambda_v(j),&0\le s<14,\\
R,&s=14\text{ or }s=15,
\end{cases}\\
f_{87}(\bot)&=L_\bot,\qquad
F_{87}(w)=f_{87}(q(w)),\qquad
\Lambda_{87}(j)=(\lambda_0(j),\lambda_1(j)).
\end{aligned}
\tag{87.4}
$$

Thus the low tables are independent of INITIAL tail, both high INITIAL tails have the same fresh $R$ at every phase and value, and all initially rejected histories have their independent label. The target is never reevaluated on an updated record.

Each full low image has exactly five labels. The tables have genuinely different equality partitions: phases $0,2$ have unequal row labels and equal column labels, while phases $0,6$ have equal row labels and unequal column labels. Renaming the labels of either component cannot remove these differences. The full joined image has fifteen classes. Exactly two classes are doubled:

$$
X=(A_{10},D_{00}),\quad\Lambda_{87}^{-1}(X)=\{0,1\},
\qquad
Y=(A_{11},D_{00}),\quad\Lambda_{87}^{-1}(Y)=\{2,16\}.
\tag{87.5}
$$

The other thirteen classes are singletons, including $(C,C)$ at phase $15$. In particular $X\ne Y$.

Both original literal alphabets are kept: all fourteen-bit words, and fourteen-bit words internally avoiding $1^{16}$. They coincide as sets here because $14<16$; rejection across a block boundary remains an actual absorbing event. The free initial observation reveals only $v$ or $\bot$. Thereafter the controller sees one scalar or bottom output at each of its own completed issued-block endpoints. Every issued block costs one and emits all fourteen bits, including the part after absorption, every wait, padding or repair block. Adaptive control may use the acquired archive. ONE GLOBAL requires prefixes of one literal stream for this fixed full target on both free values and all actual sources; stopping and decoding may use their own endpoint archives. There is no reset, copy, intermediate read, hidden initial clock or borrowed sibling output. Write $C_{\rm ad}$ and $C_{\rm pre}$ for the minimum uniform worst emitted-block fees under those two controls.

**接口 87.2（Joint actual histories and the literal two-omission calendar, credited reuse）。** The joint-history realization of [IC, Convention 1.2; S1, Convention 1.3] has the following explicit choice on this reader. Let $r_j$ be the representative of $6j\pmod{17}$ in $\{0,\ldots,16\}$ and set

$$
\ell_j=14(17+r_j),\qquad
\eta_{j,s}=\bigoplus_{i=\ell_j-s}^{\ell_j-1}\gamma_i,
\qquad
w(v,j,s)=(v\oplus\eta_{j,s})\,0^{\ell_j-s-1}1^s.
\tag{87.6}
$$

For every $v$, every $j$ and every $0\le s<16$, this is one actual legal complete-block history simultaneously realizing $(v,-j,s)$. Indeed $14\cdot6\equiv-1\pmod{17}$, so $\ell_j\equiv-j\pmod{17}$, and $\ell_j$ is divisible by fourteen and exceeds $s+1$. The first bit is separated from the final run by a zero, the final run has length below sixteen, and that first bit compensates its contribution to $V_{16}\bmod2$. Every constituent block belongs to both alphabets. The history lengths range from $238$ to $462$; none is revealed to the controller. The separate two-block history $1^{28}$ realizes initial $\bot$: its two fourteen-bit source words are internally legal, and their concatenation is absorbed at its sixteenth bit. These constructions include all $2\cdot17\cdot16=544$ successful records and independent bottom, rather than separate marginal witnesses for value, phase and tail.

For any history with a legal record the later record and endpoint archive depend only on that record and the issued words. All histories with that record therefore follow the same controller and have the same target (87.4). Actual surjectivity (87.6) gives equality between record and history fees, as in [S1, Proposition 2.2]. The source length is used only to verify existence, never as a control input.

Index issued words by $t=0,1,\ldots$. The actual ordered path and its two omissions are

$$
u_t=14t\pmod{17}=-3t\pmod{17},\qquad
W_t=[u_t,u_t+14]\pmod{17},\qquad
M_t=\{-3t-2,-3t-1\}\pmod{17}.
\tag{87.7}
$$

For a complete word $B=B_0\cdots B_{13}$ its arithmetic charge is

$$
\begin{aligned}
q_{t,B}(j)&=\bigoplus_{i=0}^{13}B_i\gamma_{-j+14t+i},\\
q_{t,B}(u_t)&=B_0,\\
q_{t,B}(u_t+i)&=B_{i-1}\oplus B_i &&(1\le i<14),\\
q_{t,B}(u_t+14)&=B_{13},\qquad q_{t,B}|_{M_t}=0.
\end{aligned}
\tag{87.8}
$$

Its full row is even. An even row $q_t$ vanishing on $M_t$ has the unique literal inverse

$$
B_{t,i}=\bigoplus_{b=0}^{i}q_t(14t+b\bmod17),
\qquad 0\le i<14.
\tag{87.9}
$$

These are the original response and inverse interfaces [IC, (1.4)–(1.5); S10, Interface 2.1; S15, Section 1], with Chapter 84's two-omission calendar. They are calculations on the same actual word. On success $q_{t,B}(j)$ is that source's own completed endpoint difference; on rejection the output is bottom, not the displayed arithmetic scalar. Availability and even parity alone do not establish safe concatenation.

**引理 87.3（All-action lower bounds on this fixed target）。** Under either original alphabet,

$$
C_{\rm ad}(f_{87})\ge3,\qquad C_{\rm pre}(f_{87})\ge5.
\tag{87.10}
$$

Every correct first word on either nonbottom free-value fibre has prefix $110$. These conclusions include arbitrary literal words, paid waits, padding, attempted repairs, rejection and endpoint stopping. The first-zero principle, common-tail binary bound and preset value join used here are credited existing facts; their target-specific consequences are spelled out to keep the price comparison on (87.4).

证明。 Fix either free value and any phase. The actual INITIAL tails $13,14$ have unequal target labels, respectively a low label and fresh $R$. They have the same free reading, so the controller cannot stop freely. Let $b$ be the leading one-run of its first word, taking $b=14$ for an all-one word. If $b\le1$, both sources reach the first zero successfully since $14+b<16$; they have the same value and phase there, and that zero merges their tails. Their entire subsequent records and acquired archives are identical. If $b\ge3$, both sources reject before any separating zero, since $13+3=16$. Their different unobserved rejection positions do not distinguish their identical completed bottom endpoints. Neither merger can be repaired at any later horizon [IC, Interface 1.4; S1, Lemmas 4.2–4.3]. Hence $b=2$, forcing prefix $110$.

Every such root rejects exactly INITIAL tails $14,15$. Every tail $0\le s<14$ survives its first two ones because $s+2\le15$, reaches the zero and safely completes its remaining internally shorter runs. The first-zero merger respects each tail-independent low label. All low sources have the same actual outgoing tail $\rho(B_0)$ of this root.

Within any later common endpoint archive their current scalar and tail are common. Every next literal word consequently succeeds on all those candidates or rejects all of them, independently of their phases. On success there are at most two scalar endpoint children, each again with a common current tail. On uniform rejection all future readings are bottom, so a child with unequal INITIAL labels cannot be completed; a homogeneous child can stop already. This gives at most $2^a$ distinct-label leaves with $a$ further paid words [S10, Lemma 3.2]. The reasoning uses the true all-one tail transfer $\sigma\mapsto\sigma+14$, rather than its literal trailing run, and permits every stopping rule. Zero waits and other uninformative blocks still consume one of these paid slots. A bottom output is not a useful third branch on a common-tail archive.

Each free-value fibre has five distinct low labels, distributed below the root's two successful scalar outputs. If a correct adaptive controller had worst fee $H$, their capacity would be at most $2^H$. Thus $5\le2^H$ and $H\ge3$, separately for both fibres even when their roots differ.

For ONE GLOBAL apply the exact preset value-join law [IC, Definition 29.1 and Theorem 29.2] to the full target (87.4). Its low table is $\Lambda_{87}$, high label is $(R,R)$ and initial bottom is independent. The law preserves one actual stream and its uniform worst fee even when the two component stopping times differ. Its decoder obtains the two value archives by complementing successful scalar endpoints of the one observed archive; bottom entries and issued words agree. This uses deterministic value symmetry, supplies no second experiment and borrows no sibling reading.

Let $q_0$ be the charge row of any correct joined controller's compulsory root. Formula (87.8) forces

$$
q_0(0)=1,\qquad q_0(1)=0,\qquad q_0(2)=1,
\qquad q_0(15)=q_0(16)=0.
\tag{87.11}
$$

Therefore both $X$ and $Y$ in (87.5) occur in both successful root-difference archives, whatever the other eleven literal root bits are. No other joined label can occur in both, because every other joined class is singleton. For the two actual child label images $L_0,L_1$,

$$
|L_0\cup L_1|=15,\qquad L_0\cap L_1=\{X,Y\},
\qquad |L_0|+|L_1|=17.
\tag{87.12}
$$

With total worst fee $H$ each child has at most $H-1$ further paid words and hence at most $2^{H-1}$ distinct labels. It follows that $17\le2^H$ and $H\ge5$. This argument allows the two occurrences of one label to have different full endpoint codes; it does not impose constant codes on joined classes. Early stopping cannot combine two archives or return unequal labels from one leaf. Common rejection cannot recover a merged label, and any issued wait advances the physical calendar only at its full charged price. Thus the obstruction applies to all legal streams and all endpoint stops, not merely the attaining stream below. ∎

**引理 87.4（A lawful three-block adaptive controller on the entire target）。** The target (87.4) is acquired adaptively with worst fee three under both alphabets. Every high source pays one whole root, initial bottom pays zero, and the displayed rule lets every low source pay exactly three blocks.

证明（one actual root and its complete children）。 Remember the free INITIAL value $v$. Issue

$$
P=11(01)^6=11010101010101.
\tag{87.13}
$$

It has fourteen bits, prefix $110$, a zero and terminal tail one. Its charge is $\mathbf1_S$, where

$$
S=\{0,2,3,\ldots,14\},\qquad S^c=\{1,15,16\}.
\tag{87.14}
$$

This follows from its charges $1,0,1$ at phases $0,1,2$, one at every subsequent phase through $14$, and zero at the two omitted phases. Each surviving low record is now exactly

$$
(v\oplus\mathbf1_S(j),-j+14,1).
\tag{87.15}
$$

High tail $15$ rejects on the root's first bit and high tail $14$ on its second, but each still emits all fourteen bits and returns $R$ only at the completed paid endpoint. Initial bottom instead returns $L_\bot$ at its free reading. The root-success children and their labels always refer back to (87.4).

For root difference zero use the complete words at absolute indices one and two

$$
U=0^3 1 0^{10}=00010000000000,
\qquad V=0^5 1 0^8=00000100000000.
\tag{87.16}
$$

Their full supports are respectively $\{0,1\}$ and $\{0,16\}$: their isolated ones are at absolute emitted positions $17$ and $33$. On this actual child phase zero is absent. The source's own two subsequent differences give

$$
1\longmapsto(1,0),\qquad
15\longmapsto(0,0),\qquad
16\longmapsto(0,1).
\tag{87.17}
$$

At the second pulse's completed endpoint return respectively $A_{10},C,A_{11}$ when $v=0$, and $D_{00},C,D_{00}$ when $v=1$. Both words start and end zero, have only one internal one, and their actual seam sums with the root and with each other are $1$ and $0$, below sixteen. No extra clearing or terminal word is issued. Prescribing their charge at absent phase zero is part of these words, not a read on another source.

证明（the small-capacity positive continuations）。 On $S$ the four-bit table is a bijection onto

$$
\Omega=\mathbb F_2^4\setminus\{0001,0011\}.
\tag{87.18}
$$

For $v=0$ let $c^{(0)}(j)$ be its first two bits, and for $v=1$ let $c^{(1)}(j)$ be its last two bits. The four component labels use the four respective two-bit codes without any further selection. At the actual suffix indices one and two the omissions are

$$
M_1=\{12,13\},\qquad M_2=\{9,10\}.
\tag{87.19}
$$

The first coordinate of both component codes is zero at phases $12,13$, since their table entries are $0000,0101$. The second coordinate of both is zero at phases $9,10$, whose entries are $0010,1010$. Thus these are simultaneous restrictions on the same row/column table at the actual chronological windows.

For $t=1,2$ prescribe a full row by

$$
\begin{aligned}
a_t^{(v)}(j)&=c_t^{(v)}(j)&&j\in S,\\
a_t^{(v)}(1)&=\bigoplus_{j\in S}c_t^{(v)}(j),\\
a_t^{(v)}(15)&=a_t^{(v)}(16)=0.
\end{aligned}
\tag{87.20}
$$

The phase-one compensation vectors are $00$ for $v=0$ and $10$ for $v=1$. Every full row is even and vanishes on its own pair (87.19); no compensation vertex is an omitted vertex. These are offline prescriptions for the same word's literal bits. The positive child observes none of the three excluded phases and receives no sibling output. Inverting each full row at its actual index by (87.9) gives

$$
\begin{aligned}
A_1^{(0)}&=11100111101001,&
A_2^{(0)}&=11011111010111,\\
A_1^{(1)}&=11110001001101,&
A_2^{(1)}&=00100000000101.
\end{aligned}
\tag{87.21}
$$

Here the letter $A$ denotes a word, while its indexed semantic labels in (87.4) retain their subscripts. Every displayed word has fourteen bits and contains zero. Their literal leading/trailing run pairs, including the inherited root, are

$$
\begin{array}{c|ccc|cc}
\text{positive value}&P&A_1^{(v)}&A_2^{(v)}&
\rho(P)+\alpha(A_1^{(v)})&
\rho(A_1^{(v)})+\alpha(A_2^{(v)})\\\hline
0&(2,1)&(3,1)&(2,3)&4&3\\
1&(2,1)&(4,1)&(0,1)&5&1
\end{array}
\tag{87.22}
$$

Every seam is strictly below $k=16$, and every internal run is shorter than sixteen because a word has only fourteen bits. Since each word contains zero, the preceding actual outgoing tail equals its displayed literal trailing run. The inherited-tail exception for all-one words is not silently discarded. Every positive candidate safely executes the entire concatenation $P\mid A_1^{(v)}\mid A_2^{(v)}$ with no wait, padding, repair or cleanup insertion.

If its own completed scalars are $v_0,v_1,v_2,v_3$, with remembered $v_0=v$, then

$$
(v_2\oplus v_1,v_3\oplus v_2)=c^{(v)}(j).
\tag{87.23}
$$

Return $A_{c^{(0)}(j)}$ for the remembered value zero and $D_{c^{(1)}(j)}$ for remembered value one. These acquired bits decode the immutable component label, without revealing or using a hidden phase. The suffix selection uses the free INITIAL value, not a reinterpreted current value. Each component's four labels occurs on $S$, so there are actual positive sources paying all three words. The separate negative, high and bottom rules complete the entire full target at the stated fee. ∎

**引理 87.5（One lawful five-block GLOBAL stream for both value fibres）。** The same full target has a single preset stream with worst fee five under both alphabets, including every low phase, both high tails and independent initial bottom.

证明（a simultaneously available full-cycle code）。 Keep the root $P$ in (87.13). The following independent four-coordinate suffix table $Q$ is a code for acquiring phase, not a change to the target table $z$ in Definition 87.1.

$$
\begin{array}{c|rrrrrrrrr}
j&0&1&2&3&4&5&6&7&8\\\hline
Q(j)&0111&1100&1011&0110&1010&1100&0100&0101&1101
\end{array}
\tag{87.24}
$$

$$
\begin{array}{c|rrrrrrrr}
j&9&10&11&12&13&14&15&16\\\hline
Q(j)&0011&1001&1110&0001&0010&1111&0000&0100
\end{array}
\tag{87.25}
$$

Coordinates are numbered $1,2,3,4$. On $S$, $Q$ is a bijection onto $\mathbb F_2^4\setminus\{0000,1000\}$. On its three-phase complement its values are $Q(1)=1100$, $Q(15)=0000$, $Q(16)=0100$. Each coordinate has eight ones on the full cube, so its cube XOR is zero; hence

$$
\bigoplus_{j\in S}Q(j)=1000,
\qquad Q(1)\oplus Q(15)\oplus Q(16)=1000,
\qquad \bigoplus_{j=0}^{16}Q(j)=0000.
\tag{87.26}
$$

For suffix indices $t=1,2,3,4$, the exact omission pairs and their table values are

$$
\begin{array}{c|c|c}
t&M_t&(Q(j):j\in M_t\text{ in increasing order})\\\hline
1&\{12,13\}&(0001,0010)\\
2&\{9,10\}&(0011,1001)\\
3&\{6,7\}&(0100,0101)\\
4&\{3,4\}&(0110,1010)
\end{array}
\tag{87.27}
$$

Both displayed vectors in each row have coordinate $t$ zero. Thus all four full rows $q_t(j)=Q_t(j)$ are even and simultaneously available at their actual chronological windows. No common partition or unrelated marginal realization is substituted for these rows. Applying (87.9) at the actual starts $14,11,8,5$ yields the one literal stream

$$
\begin{aligned}
B_0&=11010101010101,\\
B_1&=11110110111001,\\
B_2&=11100101100101,\\
B_3&=01100100011010,\\
B_4&=00101001100011.
\end{aligned}
\tag{87.28}
$$

Its words are fixed independently of the free value and every subsequent reading.

证明（actual seams, own-endpoint decoding and stops）。 The leading/trailing run pairs of these five words are respectively

$$
(2,1),\ (4,1),\ (3,1),\ (0,0),\ (0,2),
\tag{87.29}
$$

giving consecutive actual seam sums $5,4,1,0$, all strictly less than sixteen. Every word has an internal zero and length fourteen. The root has exactly the already verified low preservation and high absorption; every low source then executes the other four words safely. The same complete concatenation proves compatibility of all the rows, including adjacent literal ones at its first two suffix boundaries. None is a separate feasible experiment on a copied or reset source.

The five-bit vector

$$
Z_{\rm run}(j)=(\mathbf1_S(j),Q(j))
\tag{87.30}
$$

is injective on all seventeen phases. On $S$ this follows from the fourteen distinct $Q$ entries; on $S^c$ the entries $1100,0000,0100$ are distinct; phases on opposite sides have different root bits. In particular the two occurrences of each repeated joined label acquire different full codes, as permitted in the lower bound.

Each low source emits precisely (87.28). At its fifth completed endpoint its own six scalar readings, including the free one, give

$$
(v_1\oplus v_0,v_2\oplus v_1,v_3\oplus v_2,
 v_4\oplus v_3,v_5\oplus v_4)=Z_{\rm run}(j).
\tag{87.31}
$$

The inverse of the explicit finite table identifies $j$ from these observed differences. Return the entry $\lambda_{v_0}(j)$ of Definition 87.1, using the remembered free value. This is endpoint decoding of one source, not an intermediate phase observation. Initial bottom stops freely with $L_\bot$; a source absorbed by $B_0$ stops only at that word's paid completed bottom endpoint with $R$. All low sources stop at the fifth paid endpoint. No final clearing word is needed, and every bit of an absorbed root is charged. The actual witnesses (87.6) supply low sources reaching this worst fee. ∎

**定理 87.6（Exact small-capacity whole-target fees）。** For the one full target (87.4), under each original literal alphabet,

$$
\boxed{
C_{\rm ad}(f_{87})=C_{\rm ad}(F_{87})=3,\qquad
C_{\rm pre}(f_{87})=C_{\rm pre}(F_{87})=5.
}
\tag{87.32}
$$

The exact minimum worst actual emitted-bit fees are respectively $42$ and $70$. These are separate optima for adaptive control and ONE GLOBAL preset control on this same fixed target, on both genuinely different free-value fibres and all actual INITIAL records and histories.

证明。 Lemma 87.3 gives the all-action lower bounds. Lemmas 87.4 and 87.5 give the full-source, strictly safe, fully paid attainments with own-endpoint decoding and stopping. Interface 87.2 and the explicit pullback (87.4) give equality of record and history fees. Every issued block emits fourteen bits, so multiplying the optimal block fees by fourteen proves the exact bit prices, including absorbed suffixes. ∎

**数学引文 87.7（Exact overlap and the additional physical compatibility）。** The exact source comparison uses this volume through Chapter 86 and the four canonical mathematical inputs [IC], [M], [T3], [F4] at [revision ce3d9225453f24488e834808cfd228a67d3b21c2](https://github.com/the-omega-institute/trureturing/tree/ce3d9225453f24488e834808cfd228a67d3b21c2/docs/develop/theory). The original suppliers [S1], [S2], [S10], [S15] retain the immutable versions in this volume's reference definitions. They supply the reader, joint-history witness, deterministic history pullback, first-zero loss, binary capacity, literal inverse, strict seam rule and true all-one tail transfer. [IC, Theorem 29.2] supplies the exact preset value join, including unequal endpoint stopping times and absorption. Those facts and their applications are credited reuse, not additional mathematical content.

The correspondence is literal: a source is one original complete history such as (87.6); its INITIAL record is $(v,-j,s)$; its immutable label is (87.4); its action is a displayed complete fourteen-bit word at its actual issued index; its observation is that word's own completed scalar or bottom endpoint; its resource is the number of fully emitted words or bits. Both values, all seventeen actual phases, all sixteen successful INITIAL tails and independent initial bottom are retained. The target's two high tails refer to the INITIAL record, not an updated terminal run.

Chapters 84–86 do not assert this small-capacity attainment. Construction 84.4 and Theorems 85.1 and 86.4 require $d\ge3$, so their readers have $k=4^d\ge64$ and $m=4^d-2$. At the proposed $d=2$ substitution, the three suffix coordinates in Construction 84.4's cycle would all occur in every $b_t$, including its forbidden coordinate $t$; the prescribed vectors would also repeat. That is not the well-defined placement used in those theorems. In Lemma 86.3 the uniform greedy reserve inequality would be $2^{4-1}-2=6\ge8$, which is false. An explicit eight-phase simultaneous assignment, supplied in (87.24)–(87.27), is therefore needed. The displayed target is a new placement of fourteen distinct row/column pairs, together with its two specified repeats and shared $C$, rather than an undefined old ordered completion.

The more consequential small-capacity issue is the actual positive suffix. On $S$ its row multiplicities are $(2,4,4,4)$ and its column multiplicities are $(4,3,4,3)$ in binary index order. The two component omission pairs are satisfied simultaneously by (87.19)–(87.20). For the column suffix the two full consecutive rows have only three common charged phases, exactly $\{5,7,14\}$. Chapter 84's sharp rejecting-seam bound allows a rejecting pair with three common charges, so it cannot imply safety here. Equation (87.22) instead proves that this same pair has actual outgoing tail one followed by leading run zero, hence seam sum one. The phase-one parity prescription and these actual run lengths complete both different value tables without a paid repair. This is additional physical compatibility at two-coordinate capacity, beyond the dense $d\ge3$ component argument in Chapters 85–86. The GLOBAL suffix has consecutive full-row intersections $5,4,4$, while its root/first-suffix intersection is seven; its selected simultaneous code and actual run lengths give the five-block full attainment.

Chapter 83's order-sixteen instance has $m=15$, $T=17$, one omission, a different high-tail rule and an exact block/bit pair $3/4$, $45/60$. Changing the operation width changes both the paths and the emitted resource, so its stream is not an original fourteen-bit action here. Chapter 82's depth-four instance instead has $(k,m,T)=(22,21,23)$ and its own five-even-class placement. Chapters 79–81 likewise retain their own one-omission domains and label placements. None supplies the present two-omission, high-two-tail target or its column seam at three common charges. The original Construction 84.4 target keeps its proved pair $(d+1,2d)$, and the distinct Chapter 86 target keeps $(d+1,2d+1)$, throughout their stated $d\ge3$ domains. No entry or price of either former target is changed by (87.4).

[M, Definitions 1.1–1.3 and Theorem 2.1], [T3, Definition 1.2 and Theorem 2.1] and [F4, Definition 72.1 and Theorem 72.2] concern actual root-zero archives after an issued all-one root, with their own binary, three-label or four-label conditions. At $(16,14)$ that root would leave only INITIAL tails zero and one successful. It is inadmissible for the present full target because it absorbs the unequal labels at tails $13,14$. Thus those archive prices cannot be transported to the positive archive (87.15) by naming its four component labels. [S15, Theorem 3.3] is a general response/seam certificate, not an exact fee theorem for (87.4). Its independent-row Theorem 3.4 and [IC, Chapters 27 and 60–64] require $k\ge2m$, which here would say $16\ge28$. The wide and critical results [IC, Theorem 38.1 and Chapters 46–48] require $m\ge k$. These are failures of exact application hypotheses, not claimed failures of the credited results.

The repository declarations $\texttt{original\_cost\_lower}$ in $\texttt{OriginalNarrowCost.lean}$ and $\texttt{narrow\_window\_cost}$ in $\texttt{NarrowWindowCost.lean}$, under $\texttt{D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/}$, have distinct statement scopes. The first supplies a first-window/binary lower bound; the second requires actual gcd at least two and a monochromatic scan condition. Neither supplies a coprime two-omission attaining stream or this full target's exact GLOBAL surcharge. No current Lean application or compilation is asserted.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), is the primary literature comparison. It supplies completed leaf-reaching observations, legal compatible tests, disjoint observed traces and adaptive distinguishing graphs, with destructive first-action mergers. One input here is a full emitted literal word, one output its completed endpoint, and the distinction required is between immutable INITIAL labels of one actual source. Those mature semantics are credited background. They supply no matched KBonacci two-omission calendar, literal parity prescription, high-tail rule or $42/70$ emitted-bit equality. This scoped comparison is not an exhaustive absence or worldwide priority claim.

The added ordinary mathematics is the fully specified small-capacity joint placement and its simultaneous literal compatibility for both component continuations and one whole-target GLOBAL stream, yielding the exact original-reader fees where the existing high-capacity construction does not apply. The root-loss, capacity, join and inverse arguments are reused under their actual hypotheses. A generic Bellman or belief-game description, a common-partition restatement, a finite registry of separately supplied fees or a relabelled supplier optimum is not being presented as the price contribution. These deductions are repo-derived ordinary mathematics; no kernel, independent-review, independent-prior or literature-originality grade is claimed.

**数据 87.8（Finite corroboration on the original integers）。** Direct evaluation of the integer recurrence (87.2) through index $531$ verifies the matched cycle, every history (87.6), all full charge rows and inverses, the endpoint decoders and all literal seam sums. It jointly realizes and executes all $544$ successful INITIAL records on both displayed controllers, together with a separate initial-bottom realization. The successful source histories have lengths between $238$ and $462$. The record counts and emitted totals across these separate executions are

| Actual INITIAL branch | Records | Adaptive blocks per record | GLOBAL blocks per record |
| --- | --- | --- | --- |
| Low root-positive phases $S$ | $392$ | $3$ | $5$ |
| Low root-zero phases $\{1,15,16\}$ | $84$ | $3$ | $5$ |
| High tails $14,15$ | $68$ | $1$ | $1$ |

The adaptive executions issue $1496$ blocks and $20944$ bits in total; the GLOBAL executions issue $2448$ blocks and $34272$ bits. These aggregate sums concern separate actual sources, not one controller borrowing a combined archive. Initial bottom has acquisition fee zero. The actual worst individual fees remain three/five blocks and forty-two/seventy bits.

A separate finite check of all $2^{14}=16384$ first literal words at the actual equal-value, equal-phase tail pair $13,14$ gives $12288$ first-zero mergers, $2048$ common absorptions and $2048$ surviving prefix-$110$ candidates. On each surviving root the full joined child label counts sum to seventeen, with intersection precisely $\{X,Y\}$. These finite results corroborate the target-specific ordinary obstruction; they do not enumerate arbitrary deeper policies or replace its all-action proof. The complete-row common-charge counts for the two adaptive suffixes are four and three, respectively, and the GLOBAL consecutive counts are seven, five, four and four. All directly evaluated seam sums are those displayed in (87.22), (87.29) and the pulse proof. No check program or dataset is delivered with the chapter, and no finite computation is claimed as a kernel proof or a universal all-parameter enumeration.

**边界 87.9（One closed small-capacity edge and the remaining quantifiers）。** The equality fixes exactly $(k,m,T)=(16,14,17)$, the whole table of Definition 87.1, all low INITIAL tails below fourteen, both high INITIAL tails with common fresh $R$, both free values and an arbitrary independently prescribed initial-bottom label. It includes all actual finite complete histories through the explicit INITIAL pullback, both original alphabets, full charging of absorbed bits and own completed-endpoint stopping. Offline table formation, decoder storage and controller memory are separate resources with no optimality assertion.

This is one substantive ordinary whole-target result in the smaller-capacity region omitted by Chapters 84–86, not a classification of other placements at the same reader. It does not assign fees to arbitrary row/column placements, low-tail-dependent labels, different high-label coincidences, other gcds or other orders and widths. It neither redefines former targets nor changes their proved prices. The original exact minimum worst-branch ACTUAL emitted-complete-block fees for every attainable immutable INITIAL target and every original $k\ge2,m\ge1$, separately adaptive and ONE GLOBAL preset control [IC, Definition 1.3 and Open Problem 9.1], remain open. The chapter supplies ordinary proofs and bounded mathematical corroboration, without Lean/kernel validation, compilation, ingestion, deposit, coverage or freezing.

## 追加锚（本行以下为增补区）

## 88. The sharp two-double GLOBAL four/five placement law

At the original reader $(k,m,T)=(16,14,17)$, fix arbitrary low tables on the two free-value fibres whose ordered value join has exactly two double classes and thirteen singleton classes. The exact GLOBAL price depends on the locations of those doubles relative to the compulsory first word. Both doubles touching the forced-positive phases is an obstruction only when their union also touches a forced-negative phase. Root parity handles even the case where just one double is forced to split. On the other side, the simultaneous constructions below retain enough consecutive common charges to prove literal safety at four-block capacity. They classify this entire multiplicity stratum, including equal and different component equality partitions.

**定义 88.1（The full original INITIAL target and the two placements）。** Retain [IC, Definitions 1.1–1.3 and Interface 1.4], with precisely

$$
k=16,\qquad m=14,\qquad T=k+1=17,\qquad g=\gcd(14,17)=1.
\tag{88.1}
$$

The integer weights are $G_i=2^i$ for $0\le i<16$ and $G_i=\sum_{a=1}^{16}G_{i-a}$ thereafter. The matched original scalar is $V_{16}(w)\bmod2$, with coefficient cycle $\gamma_i=\mathbf1_{\{0,16\}}(i\bmod17)$ [S2, Theorem 14.1]. The prior is all finite actual complete-fourteen-bit histories, with legal records $(v,\theta,s)$ and independently absorbing $\bot$. Both $v\in\mathbb F_2$ and every $\theta\in\mathbb Z/17\mathbb Z$, $0\le s<16$, are jointly actual. Put $j=-\theta_{\rm INITIAL}\pmod{17}$.

Take arbitrary tables $\lambda_0,\lambda_1:\mathbb Z/17\mathbb Z\to Y$ and a label $R\notin\lambda_0[\mathbb Z/17\mathbb Z]\cup\lambda_1[\mathbb Z/17\mathbb Z]$. Define the entire target and its immutable history pullback by

$$
\begin{aligned}
f(v,-j,s)&=
\begin{cases}
\lambda_v(j),&0\le s<14,\\
R,&s\in\{14,15\},
\end{cases}\\
f(\bot)&=L_\bot,\qquad F(w)=f(q_{\rm INITIAL}(w)),\\
\Lambda(j)&=(\lambda_0(j),\lambda_1(j)).
\end{aligned}
\tag{88.2}
$$

The independent $L_\bot$ is arbitrary, including coincidences with other labels. Require the equality classes of the ordered table $\Lambda$ to consist of two disjoint two-element sets $D_1,D_2$ and thirteen singletons. Thus $|\Lambda[\mathbb Z/17\mathbb Z]|=15$. No condition identifies the two component partitions or fixes their separate class counts. Write

$$
P=\{0,2\},\qquad N=\{1,15,16\}.
\tag{88.3}
$$

These are the forced-positive and forced-negative root-charge sets; the actual phase domain is the entire seventeen-phase cycle. Observations are the free INITIAL scalar or bottom, followed only by the source's own completed issued-block endpoints. Each issued word emits and pays all fourteen bits, including a suffix after absorption and every wait, padding or repair. Both original alphabets are retained: all fourteen-bit words and those internally avoiding $1^{16}$. Since $14<16$, their word sets coincide, while cross-block rejection is still enforced. ONE GLOBAL uses prefixes of one fixed literal stream for this target on both free values and all sources, with endpoint-dependent stopping and decoding. There is no reset, copy, hidden INITIAL clock, intermediate reading or borrowed sibling archive.

**定理 88.2（Sharp symbolic GLOBAL four/five law on the whole two-double stratum）。** For every target of Definition 88.1, under each original alphabet,

$$
\boxed{
C_{\rm pre}(f)=C_{\rm pre}(F)=
\begin{cases}
5,&D_1\cap P\ne\varnothing,
   \ D_2\cap P\ne\varnothing,
   \ (D_1\cup D_2)\cap N\ne\varnothing,\\
4,&\text{otherwise}.
\end{cases}}
\tag{88.4}
$$

The exact worst emitted-bit fees are respectively $70$ and $56$. The four-block side has one completely paid same-stream attainment for both free values, every low and high INITIAL tail, and every actual original history. The five-block side uses the already supplied phase-recovering stream (87.28). The lower bounds range over all literal words and lawful endpoint stops, including waits, padding, repairs and attempted rejection. The criterion in (88.4) is a conclusion of the proof, with no compatibility assumption beyond Definition 88.1.

证明（joint actual sources and the all-action compulsory root）。 The joint witness is the supplied (87.6). For $r_j$ the representative of $6j\pmod{17}$, put

$$
\ell_j=14(17+r_j),\qquad
\eta_{j,s}=\bigoplus_{i=\ell_j-s}^{\ell_j-1}\gamma_i,
\qquad
w(v,j,s)=(v\oplus\eta_{j,s})0^{\ell_j-s-1}1^s.
\tag{88.5}
$$

This is one legal complete-block history jointly realizing $(v,-j,s)$ for every $v,j,0\le s<16$. Indeed $14\cdot6\equiv-1\pmod{17}$, so its complete-block length has the required phase. Its separating zero and terminal run below sixteen ensure legality; its first bit compensates the terminal scalar contribution. Each constituent fourteen-bit source word belongs to both alphabets. The separate history $1^{28}$ realizes initial bottom through two internally legal source blocks. No source length is observed or used as a control input. Deterministic record evolution and $F=f\circ q_{\rm INITIAL}$ imply that every history with a given record follows the same controller and has the same target. Actual record surjectivity therefore gives equal record and history prices [S1, Convention 1.3 and Proposition 2.2].

Fix either free value and any phase. The actual INITIAL tails $13$ and $14$ have unequal labels, low versus fresh $R$, and the same free reading. The controller cannot stop freely on this fibre. Let $b$ be its first word's leading one-run, with $b=14$ for an all-one word. If $b\le1$, both sources survive to the first zero, since $14+b<16$, and that zero merges their entire current records. Their remaining completed output and every later archive and stop agree. If $b\ge3$, both are absorbed by the third leading one, since $13+3=16$. Their unobserved absorption positions give no distinction at the paid completed bottom endpoint. Neither merger can be repaired [S1, Lemmas 4.2–4.3; IC, Interface 1.4]. Consequently every correct first word has $b=2$, hence prefix $110$.

Every such root rejects exactly INITIAL tails $14,15$. All tails below fourteen survive its two ones, reach its zero and complete safely, since every subsequent internal run is shorter than sixteen. Their merger respects the tail-independent low target at each INITIAL phase. The successful low sources now have one common actual terminal tail, the literal trailing run of this very root.

At every later common endpoint archive the current scalar and tail are common. An arbitrary next literal word succeeds on all its candidates or rejects all of them, because rejection depends only on the incoming tail and the word. Successful output has at most two scalar children, each again with a common tail. Uniform rejection cannot complete an archive with unequal INITIAL labels: all subsequent readings are absorbing bottom. A homogeneous archive can stop already. Induction on the remaining paid fee gives at most $2^a$ different-label leaves with $a$ more words [S10, Lemma 3.2]. This argument retains the true all-one transfer $\sigma\mapsto\sigma+14$, rather than substituting its literal trailing run. All-one words, zero waits, attempted repairs, rejection and early endpoint stopping are included.

Use the exact preset value-join law [IC, Definition 29.1 and Theorem 29.2]. For (88.2), its joined low target is $\Lambda$, its high target is $(R,R)$, and its initial bottom is independently labelled. The law preserves the same actual stream and uniform worst fee, including unequal component stopping times. From one observed archive its deterministic decoder complements successful scalar readings to form the two value archives; bottom readings and issued words agree. This supplies no second experiment or sibling observation. On either joined free-value fibre there are fifteen actual low labels. The binary bound, including the root's two successful children, gives $15\le2^H$ for total fee $H$, hence

$$
C_{\rm pre}(f)=C_{\rm pre}(\Lambda\text{ with its high and bottom entries})\ge4.
\tag{88.6}
$$

证明（root parity forces five, including a single compulsory split）。 Index issued words by $t=0,1,\ldots$. Their actual full arithmetic rows and unique inverses are the supplied (87.7)–(87.9):

$$
\begin{aligned}
u_t&=14t=-3t\pmod{17},\qquad W_t=[u_t,u_t+14]\pmod{17},\\
M_t&=\{-3t-2,-3t-1\}\pmod{17},\\
q_{t,B}(j)&=\bigoplus_{i=0}^{13}B_i\gamma_{-j+14t+i},\qquad
\bigoplus_{j=0}^{16}q_{t,B}(j)=0,\\
B_{t,i}&=\bigoplus_{b=0}^{i}q_t(14t+b\bmod17),\qquad0\le i<14.
\end{aligned}
\tag{88.7}
$$

An inverse exists exactly for an even full row vanishing on its own $M_t$. Its arithmetic row is an observed scalar difference only on a successful execution. Availability and parity will be supplemented by a safety proof below.

For every compulsory root the prefix and omissions give

$$
q_0=1\text{ on }P,\qquad q_0=0\text{ on }N.
\tag{88.8}
$$

Its positive support $A_+=q_0^{-1}(1)$ has even cardinality by (88.7); the complementary low phase support $A_-$ has odd cardinality, since there are seventeen phases. Let $L_+=\Lambda[A_+]$, $L_-=\Lambda[A_-]$. A double is split when its two phases lie on opposite sides. Only a split double contributes a label to both child images. Thus, writing $s_D\in\{0,1,2\}$ for the number of split doubles,

$$
|L_+|+|L_-|=15+s_D.
\tag{88.9}
$$

Suppose the five-block condition in (88.4) holds. Because the doubles are disjoint and each meets $P$, each contains exactly one of its two positive phases. A double meeting $N$ is forced to split by (88.8), so $s_D\ge1$ for every admissible root.

If both doubles split, (88.9) equals seventeen. At least one actual successful root child has at least nine joined labels. If exactly one splits, the other double is wholly positive, because it contains a phase of $P$. It is the only equality repetition within either child. Hence

$$
|L_+|=|A_+|-1\text{ is odd},\qquad
|L_-|=|A_-|\text{ is odd},\qquad
|L_+|+|L_-|=16.
\tag{88.10}
$$

Two odd integers summing to sixteen cannot both be at most eight: they would each be at most seven. Again some child has at least nine labels. This parity obstruction does not require both doubles to be compulsory splits.

In a controller of total worst fee at most four, either root child has at most three further paid words and therefore at most eight distinct-label leaves. The actual nine-label child contradicts the common-tail bound. Its label count also prevents early stopping; uniform rejection cannot erase this obligation. Root bits beyond $110$ were unrestricted, and future words may be arbitrary. Paid waits only consume one of those three remaining slots and move the calendar at that charged price. This proves $C_{\rm pre}(f)\ge5$ under the condition in (88.4), by the same-stream join law, against every allowed action and stop.

证明（four rows when a double misses the positive set）。 Suppose some double $D$ satisfies $D\cap P=\varnothing$. Number code coordinates $0,1,2,3$ chronologically and prescribe

$$
Z(j)=0000\quad(j\in D).
\tag{88.11}
$$

The remaining fifteen phases will receive all fifteen nonzero vectors in $U=\mathbb F_2^4\setminus\{0000\}$. For $j\notin D$, its allowed list consists of the vectors in $U$ obeying the following single restriction, when applicable:

$$
\begin{array}{c|c|c}
\text{phase group}&\text{restriction}&\text{maximum number of indexed lists}\\\hline
P&z_0=1&2\\
N&z_0=0&3\\
M_1=\{12,13\}&z_1=0&2\\
M_2=\{9,10\}&z_2=0&2\\
M_3=\{6,7\}&z_3=0&2
\end{array}
\tag{88.12}
$$

These five phase groups are disjoint. Every other phase has the unrestricted list $U$. Removing $D$ can only decrease their indexed group sizes. Assignment (88.11) respects every omission and negative requirement, since $D$ misses $P$.

We verify all finite Hall inequalities for these actual lists and then use the credited indexed-list Hall theorem [H]. Every list has at least seven vectors; the positive list has eight and an unrestricted list fifteen. A subfamily of size $q\le7$ has union of size at least $q$, with the empty case immediate. For $8\le q\le11$, an unrestricted list suffices. Otherwise there are at least two different restricted list types, because no single type has more than three indexed phases. Two different coordinate half-cubes have union of size twelve, or sixteen for the opposite root halves. Removing zero leaves at least eleven vectors, enough for this subfamily. Finally $q\ge12$ forces an unrestricted list: there are at most $2+3+2+2+2=11$ restricted indexed phases altogether. Its union is the fifteen-vector set $U$ and again has size at least $q$. These cases cover every subfamily.

Hall gives an injective choice on the fifteen remaining phases, hence a bijection onto $U$. With (88.11), every cube vector is represented, with only zero repeated. The full vector XOR is zero, since each cube coordinate has eight ones. Unequal joined labels have different vectors: the only equal vectors occur at the two phases of $D$. The other double is allowed, and here required, to use two distinct codes; equal-label phases need not share an endpoint vector. All coordinate rows obey their chronological omissions and (88.8).

证明（four rows when both doubles touch the positive set and neither touches the negative set）。 The remaining four-block case has both doubles meeting $P$ and

$$
(D_1\cup D_2)\cap N=\varnothing.
\tag{88.13}
$$

Reindex the two doubles solely for this construction as

$$
D^{(0)}=\{0,a\},\qquad D^{(2)}=\{2,b\},
\qquad a,b\in\{3,\ldots,14\},\quad a\ne b.
\tag{88.14}
$$

Write $e_t$ for the unit vector in coordinate $t$. Choose $r\in\{1,2,3\}$ with $b\notin M_r$. Such a choice exists because the three omission pairs are disjoint, so $b$ belongs to at most one of them. Set

$$
A=e_0=1000,\qquad B=e_0\oplus e_r,\qquad H=e_r,
\qquad Z|_{D^{(0)}}=A,\quad Z|_{D^{(2)}}=B.
\tag{88.15}
$$

The vector $A$ has all suffix coordinates zero; $B$ has its only nonzero suffix coordinate at an omission pair not containing $b$. These assignments respect all restrictions at their four phases and give root coordinate one on both doubles. The three vectors $A,B,H$ are distinct and nonzero.

The thirteen singleton phases receive exactly the thirteen vectors in

$$
U'=\mathbb F_2^4\setminus\{A,B,H\}.
\tag{88.16}
$$

For a singleton in $N$, restrict to $z_0=0$; for a singleton in $M_t$, $1\le t\le3$, restrict to $z_t=0$. The groups remain disjoint. Other singleton lists are all of $U'$. Each restricted list has at least $8-3=5$ vectors, with at most three indexed lists of the root type and at most two of each suffix type.

Here are all Hall inequalities. A subfamily of size $q\le5$ is supplied by any one of its lists. For $6\le q\le9$, an unrestricted list suffices. Otherwise at least two different restricted types occur, since a single type has at most three indices. Their two different zero-coordinate half-cubes have union of size twelve; deleting $A,B,H$ leaves at least nine vectors, enough for this subfamily. A subfamily of size $q\ge10$ contains an unrestricted list, because there are at most $3+2+2+2=9$ restricted singleton phases. Its union has all thirteen vectors of $U'$. The empty case is immediate. Applying [H] yields an injective choice on the thirteen singleton phases, hence a bijection onto $U'$.

The fifteen distinct assigned vectors are exactly the cube with $H$ omitted. Each double is constant, on $A$ and $B$, and different joined classes have different vectors. Accounting for the two repetitions gives

$$
\bigoplus_{j=0}^{16}Z(j)=H\oplus A\oplus B=0.
\tag{88.17}
$$

Indeed the whole cube XOR is zero; the distinct-code XOR after removing $H$ is $H$; the extra occurrences of $A,B$ supply the remaining terms. These are even, available full rows with the compulsory root constraints. Omitting the unit vector $H$, rather than an arbitrary missing code, will establish safety of the same words.

证明（simultaneous literal realization, every strict seam and lawful Stop）。 Either construction gives four full rows $q_t(j)=Z_t(j)$, $0\le t<4$. They have even parity and vanish on the actual $M_t$, so define the four actual words by the single inverse

$$
B_{t,i}=\bigoplus_{b=0}^{i}Z_t(14t+b\bmod17),
\qquad0\le t<4,\quad0\le i<14.
\tag{88.18}
$$

These words are fixed before execution and serve both free values. Equation (88.8) makes their root bits $B_{0,0}=1$, $B_{0,1}=1$, $B_{0,2}=0$. This is one of the proved compulsory roots: all low sources survive, the two high tails are absorbed and pay its entire fourteen bits, and its successful terminal tail is common.

In the first construction every cube vector occurs. In the second every cube vector except a unit occurs. For each consecutive coordinate pair $(t-1,t)$ the four-cube has four distinct vectors with both coordinates one. A missing unit never has that pair of ones. Consequently, for the actual full rows of the very words (88.18),

$$
\left|\{j:Z_{t-1}(j)=Z_t(j)=1\}\right|\ge4,
\qquad t=1,2,3.
\tag{88.19}
$$

This counts actual phase entries, including any repeated code, rather than combining rows from separate experiments. The sharp original rejecting-seam bound, Lemma 84.2, applies at $m=14$, $k=m+2=16$. After a successful word, rejection by its next word would bound the intersection of these full rows by three, with the true incoming tail retained. Equation (88.19) rules it out. Starting from the successful compulsory root and applying this implication inductively proves that every low source safely executes all four words of (88.18).

Each row has at least seven charged phases, since all cube vectors, or all except one, are represented. An all-one fourteen-bit word has just two charged endpoints, so none of these inverses is all ones. Every word contains a zero and its actual outgoing tail is its literal trailing one-run. The proved seams can therefore also be written as the strict inequalities

$$
\rho(B_{t-1})+\alpha(B_t)<16,\qquad t=1,2,3.
\tag{88.20}
$$

Every internal run is shorter than sixteen because a word has only fourteen bits. No wait, padding, repair, clearing word or final cleanup has been inserted. The inherited-tail exception for all-one words was retained in the lower bound and in Lemma 84.2 before the construction excluded those words.

Initial bottom stops freely with $L_\bot$. A high source stops with $R$ only at the root's paid completed bottom endpoint; all fourteen bits are charged despite absorption at its first or second bit. Let every low source issue exactly $B_0|B_1|B_2|B_3$. Its own scalar archive $v_0,\ldots,v_4$ supplies

$$
(v_1\oplus v_0,v_2\oplus v_1,v_3\oplus v_2,v_4\oplus v_3)=Z(j).
\tag{88.21}
$$

The code determines one joined label by the separation proved in the relevant construction. At this fourth completed endpoint return its component selected by the remembered free INITIAL value $v_0$. This is a well-defined endpoint decoder even where a double has different codes. Its stopped archive is homogeneous for the INITIAL target, so Stop is lawful. A source never reads its INITIAL phase or its current intermediate state. All low records are actual by (88.5), and this rule makes each pay four whole words. With (88.6), this proves the four-block and fifty-six-bit equalities.

证明（the credited five-block attainment and exact fees）。 For the five-block condition, use exactly the supplied stream (87.28), with root $11010101010101$, the same four suffix words, and the strict seam sums $5,4,1,0$ proved in (87.29). Its five-coordinate endpoint-difference map (87.30)–(87.31) is injective on all seventeen phases. That map and its safety depend on the original reader and literal words, not on the low target labels. On (88.2), its decoder recovers $j$ from its own five completed differences and returns $\lambda_{v_0}(j)$. Initial bottom stops freely; high tails stop with $R$ after the fully paid absorbed root; low sources all pay five words. This is the existing phase-recovering five-block fallback with the present table as its consumer. It is not a new fifth-block construction or a composition of separate component optima.

The all-action lower bound gives five exactly under the condition in (88.4). Its complement is exhausted by a double missing $P$, or by both doubles meeting $P$ with their union missing $N$, so the two four-block constructions cover every other placement. Equal record and history fees follow from the joint witnesses and immutable pullback. Multiplication by the unchanged width fourteen gives $70$ or $56$, with every absorbed suffix included. This proves all assertions of the theorem. ∎

### 88.3. Concrete streams and the one-split obstruction

**实例 88.3（Both four-block mechanisms on entire targets）。** For the first example choose doubles $\{0,1\}$ and $\{3,4\}$. Enumerate its fifteen joined classes by increasing least phase and write $\ell(j)\in\{0,\ldots,14\}$ for the class index. Take pairwise distinct labels $L_0,\ldots,L_{14}$ and put $\lambda_0(j)=\lambda_1(j)=L_{\ell(j)}$. This has equal component partitions and exactly the required joined classes. Give tails $14,15$ a fresh common $R$ and bottom any independent label, as in (88.2). The double $\{3,4\}$ misses $P$, so the zero-double construction applies.

For the second example choose doubles $\{0,3\}$ and $\{2,4\}$, and enumerate its classes in the same way. Take mutually distinct $A_0,\ldots,A_3,B_0,\ldots,B_3$ and put

$$
\lambda_0(j)=A_{\lfloor\ell(j)/4\rfloor},\qquad
\lambda_1(j)=B_{\ell(j)\bmod4}.
\tag{88.22}
$$

The fifteen ordered pairs are distinct. Its component partitions differ: class indices zero and one agree only in the first component; zero and four agree only in the second. Again use the entire low/high/bottom target (88.2), with fresh $R$. Both doubles meet $P$ and neither meets $N$, so the second construction applies with $r=1$, $A=1000$, $B=1100$, $H=0100$.

Full chronological code assignments for these examples are:

| $j$ | $Z^{\rm I}(j)$ | $Z^{\rm II}(j)$ |
| --- | --- | --- |
| $0$ | $1011$ | $1000$ |
| $1$ | $0111$ | $0111$ |
| $2$ | $1111$ | $1100$ |
| $3$ | $0000$ | $1000$ |
| $4$ | $0000$ | $1100$ |
| $5$ | $0100$ | $1111$ |
| $6$ | $1000$ | $1110$ |
| $7$ | $1110$ | $0110$ |
| $8$ | $0011$ | $0010$ |
| $9$ | $1100$ | $1101$ |
| $10$ | $1101$ | $1001$ |
| $11$ | $0010$ | $0001$ |
| $12$ | $1010$ | $1011$ |
| $13$ | $1001$ | $1010$ |
| $14$ | $0001$ | $0000$ |
| $15$ | $0110$ | $0101$ |
| $16$ | $0101$ | $0011$ |

证明。 In the first column the zero-double phases have the only repeated code; the other fifteen phases exhaust the nonzero cube. In the second, codes $1000$ and $1100$ are repeated exactly on the doubles and $0100$ is the only absent cube vector. These descriptions prove full XOR zero and separation between unequal joined labels. The displayed entries give coordinate zero one on $P$ and zero on $N$, and every later coordinate zero on its own omission pair (88.12). Thus both columns satisfy the full-row restrictions. Their literal inverses (88.18) are respectively

$$
\begin{aligned}
B_0^{\rm I}&=11000010010010,&B_0^{\rm II}&=11010100010010,\\
B_1^{\rm I}&=01001000110010,&B_1^{\rm II}&=01110110101100,\\
B_2^{\rm I}&=10001101000001,&B_2^{\rm II}&=01000110000101,\\
B_3^{\rm I}&=11000100101000,&B_3^{\rm II}&=01010001001111.
\end{aligned}
\tag{88.23}
$$

Their leading/trailing run pairs are

$$
\begin{aligned}
(\alpha,\rho)^{\rm I}&=((2,0),(0,0),(1,1),(2,0)),\\
(\alpha,\rho)^{\rm II}&=((2,0),(0,0),(0,1),(0,4)).
\end{aligned}
\tag{88.24}
$$

Both roots reject precisely the two high tails and preserve every low tail. The same actual low-source seams have sums $(0,1,3)$ and $(0,0,1)$, all strictly below sixteen. Each word contains zero and has fourteen bits. These are two safe four-word concatenations on both free values. Their completed differences are the displayed column, so (88.21) returns the correct immutable component at fee four; high tails pay one whole root and initial bottom pays zero. The all-action lower bound makes both worst fees exactly four and fifty-six bits. These examples exhibit both mechanisms; their finite tables are not the classification proof. ∎

**实例 88.4（One compulsory double split already costs five）。** Choose doubles $D_1=\{0,1\}$ and $D_2=\{2,3\}$. Take both component tables equal to the fifteen distinct class labels indexed by increasing least phase, and keep the full target (88.2), including fresh high $R$ and independent bottom. Every compulsory root splits $D_1$, but it need not split $D_2$. The whole GLOBAL fee is nevertheless five, or seventy bits.

证明。 Both doubles meet $P$ and their union meets $N$ at phase one. If the root also splits $D_2$, its child label counts sum to seventeen. If it keeps $D_2$ together, that double is positive, and even root charge gives the two odd child label counts in (88.10), summing to sixteen. Either alternative leaves at least nine labels in one common-tail child, requiring at least four more words. The credited stream (87.28) attains five by its phase decoder. Thus the fee is exactly five. Counting only compulsory splits and ignoring literal full-row parity would miss this obstruction. The Chapter 87 placement $\{0,1\},\{2,16\}$ has two compulsory splits and remains a five-block instance of the same law. ∎

### 88.4. Exact suppliers and the physical compatibility increment

**数学引文 88.5（Bounded source comparison and literal correspondence）。** The comparison fixes this volume through Chapter 87, [IC], [M], [T3], [F4], and the two mathematical Lean sources with their Blueprint statements at [revision 54a7583b8680eff7a8cb21bd42ed2d538aaf5b70](https://github.com/the-omega-institute/trureturing/tree/54a7583b8680eff7a8cb21bd42ed2d538aaf5b70). The original suppliers [S1], [S2], [S10], [S15] retain the immutable versions in this volume's reference definitions. [H] is the finite indexed-list Hall theorem at mathlib revision $db584cd6d46c92f209a44c0f1c829460d327499d$, statement $\texttt{Finset.all\_card\_le\_biUnion\_card\_iff\_existsInjective'}$.

[S1, Convention 1.3 and Proposition 2.2] supplies actual joint complete-history realization and record/history equivalence. Its Lemmas 4.2–4.3 supply first-zero merger and unobserved absorbing rejection. [S2, Theorem 14.1] supplies the matched coefficient cycle. [S10, Interface 2.1 and Lemma 3.2] and [S15, Section 1 and Definition 1.1] supply the full-row inverse, common-tail binary bound, strict safety and true all-one tail transfer. [IC, Theorem 29.2] supplies preset value joining on one actual stream, including unequal stopping times. These facts are credited reuse.

The correspondence is the original one: a source is one full actual history such as (88.5); its INITIAL record is $(v,-j,s)$; its immutable target is (88.2); an action is a literal fourteen-bit inverse at its actual issued index; its observation is that source's own completed scalar or bottom endpoint; its fee counts every fully emitted word or bit. Other histories with the same record follow the same deterministic continuation. The code assignment prescribes these same words offline; it supplies neither an operation nor a separate source model. No intermediate phase or literal bit is observed.

Theorem 84.3 supplies a phase-wise criterion at $h\ge5$, allowing different codes within one joined class. Boundary 84.9 explicitly leaves the $h=4$ safety gap: an arbitrary omitted four-cube vector may leave just three common-one vectors at a consecutive pair. Lemma 84.2 supplies the sharp rejecting-seam bound of three. The present constructions ensure that all cube vectors occur, or that the only missing vector is a unit, so four common charged phases always remain. Their Hall inequalities retain every actual omission and the same-stream parity. Chapter 87 supplies one fixed two-double five-block result and the safe phase-injective stream (87.28); Boundary 87.9 leaves other placements outside that equality. Its phase-injective stream is exactly the reused five-block fallback here.

The additional price content is the complete symbolic placement obstruction (88.9)–(88.10), including the one-split parity case, and its matching four-word physical attainments (88.11)–(88.21) for every complementary placement. Fifteen joined labels alone give only the four-block capacity lower bound. The compulsory root fixes positive and negative phase locations, and its actual literal-row parity raises that bound at the obstructed placements. On the four-block side, neither even available rows nor independently feasible component codes discharge physical compatibility; the represented-cube geometry proves every seam of the single inverse stream. This extends the placement scope, rather than only increasing a label quantifier on an already supplied stream.

The [M, Definition 1.2 and Theorem 2.1], [T3, Definition 1.2 and Theorem 2.1] and [F4, Definition 72.1 and Theorem 72.2] fees concern their actually paid all-one-root archives, with mixed incoming tails and their respective binary, three-label or four-label conditions. Here every correct full root has prefix $110$, so those fee formulas are not applied to the present whole target. Their original source and irreversible-loss semantics remain compatible background.

The pinned $\texttt{CoprimeSingletonLower.singleton\_tree\_obstruction}$ and $\texttt{CoprimeSingletonCost.coprime\_nonzero\_singleton\_cost}$, under $\texttt{D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/}$, concern a binary INITIAL phase singleton versus its complement, with one phase-table label across all legal INITIAL tails. The latter has exact cost $\max(2,\lceil j/m\rceil)$ for $2\le m<k$, actual coprimality and $1\le j\le k$. Their endpoint semantics, rejection quantifiers and actual-history scope are relevant source evidence. Their binary, tail-independent whole targets differ from (88.2), whose high tails have fresh $R$ and whose joined low image has fifteen classes. Neither statement supplies the two-double whole-target placement equality. The associated Blueprint statements delimit the same hypotheses.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), supplies the primary experiment-semantics comparison: leaf-reaching completed observations, tests consistent with available inputs and outputs, disjoint distinguishing observations and adaptive distinguishing graphs, including destructive first-action mergers. Here an input is a complete emitted word and an output its completed scalar or bottom endpoint; the required distinction is between unequal immutable INITIAL labels. The paper supplies this semantic background, not a fee bridge to (88.4). The matched cycle, compulsory-root parity, omission-specific code choices and original literal seam proofs provide the reader-specific price argument. This comparison is bounded to the named sources and hypotheses; it asserts neither exhaustive absence nor priority.

### 88.5. The exact scope and the continuing original objective

**边界 88.6（Whole-stratum equality and retained unresolved obligations）。** The law covers exactly $(k,m,T,g)=(16,14,17,1)$, arbitrary component tables whose ordered join has multiplicity profile $(2,2,1^{13})$, every low INITIAL tail $0\le s<14$, both high INITIAL tails with a common label fresh from both low images, both free values and independently prescribed initial bottom. Component partitions may agree or differ, with arbitrary label coincidences consistent with that joined profile. All actual immutable INITIAL histories are included through (88.2), and every absorbed suffix and issued calendar advance is paid. The constructions require no extra compatibility hypothesis. Offline list matching, table storage, decoder memory and source-description length are different resources, without an optimum asserted here.

The theorem identifies the exact ONE GLOBAL fee throughout this stratum. It does not classify the separate adaptive fees of arbitrary component tables, other joined multiplicity profiles, low-tail-dependent targets, high-label coincidences with low labels, different orders or widths, other gcds or unrelated acquired archives. Former targets and supplied prices remain unchanged. The original objective of exact minimum worst-branch ACTUAL emitted-complete-block fees for every attainable immutable INITIAL target and every original $k\ge2,m\ge1$, separately adaptive and ONE GLOBAL preset control [IC, Definition 1.3 and Open Problem 9.1], remains active and unresolved. This restricted equality advances its GLOBAL placement part without completing that original objective.

## 追加锚（本行以下为增补区）

## 89. One triple joined class: the exact GLOBAL four/five placement law

A three-phase joined class has a different full-row parity budget from two double classes. If its three phases share a four-coordinate code, their two extra occurrences cancel, forcing zero to be the omitted cube vector. If it splits, its repeated code must instead be zero. These two alternatives give a symbolic law for every triple placement on the original order-sixteen reader. The compulsory positive phases and a compulsory negative phase cannot all lie in the triple at four-block fee; every other placement admits one physically safe four-word stream.

**定义 89.1（The full original target with one triple）。** Retain the original integer weights, matched $V_{16}\bmod2$ scalar and bit transitions of [IC, Definitions 1.1–1.3 and Interface 1.4; Definition 87.1], with exactly

$$
k=16,\qquad m=14,\qquad T=k+1=17,\qquad
g=\gcd(14,17)=1,\qquad
\gamma_i=\mathbf1_{\{0,16\}}(i\bmod17).
\tag{89.1}
$$

The prior is all finite actual complete-fourteen-bit histories, including the empty history and rejected histories. Successful INITIAL records are $(v,-j,s)$, with $v\in\mathbb F_2$, $j\in\mathbb Z/17\mathbb Z$ and $0\le s<16$ jointly actual; $\bot$ is separately absorbing. The source length is unobserved. Take arbitrary tables $\lambda_0,\lambda_1:\mathbb Z/17\mathbb Z\to Y$, and write

$$
\Lambda(j)=(\lambda_0(j),\lambda_1(j)).
\tag{89.2}
$$

Require the equality classes of this ordered join to be one three-element class $D$ and fourteen singleton classes. Thus $|\Lambda[\mathbb Z/17\mathbb Z]|=15$. The component tables need not have equal partitions, disjoint images or prescribed individual class counts. Choose $R$ fresh from both entire low images and any independent $L_\bot$, allowing $L_\bot$ to coincide with any other label. Define the complete immutable target and its history pullback by

$$
\begin{aligned}
f(v,-j,s)&=
\begin{cases}
\lambda_v(j),&0\le s<14,\\
R,&s\in\{14,15\},
\end{cases}\\
f(\bot)&=L_\bot,\qquad
F(w)=f(q_{\rm INITIAL}(w)),\\
P&=\{0,2\},\qquad N=\{1,15,16\}.
\end{aligned}
\tag{89.3}
$$

Here $P,N$ are root-charge sets, not restrictions on the actual phase prior. All seventeen phases and all sixteen successful INITIAL tails are present. The target is never reevaluated on an updated record.

Keep both original alphabets, all fourteen-bit words and the fourteen-bit words internally avoiding $1^{16}$. They coincide as literal word sets because $14<16$, while rejection at a block boundary is still enforced. The free initial output is $v$ or $\bot$; later observations are only that source's own completed issued-block endpoints. ONE GLOBAL requires prefixes of one preset literal stream for this fixed full target on both values and every actual source, with its own endpoint decoder and stopping rule. Each issued complete word costs one block and fourteen emitted bits, including every wait, padding, repair and the whole suffix after absorption. No reset, copy, hidden INITIAL clock, intermediate reading or borrowed archive is allowed.

**定理 89.2（Exact whole-triple GLOBAL placement price）。** For every semantic label assignment and triple placement of Definition 89.1, under either original alphabet,

$$
\boxed{
C_{\rm pre}(f)=C_{\rm pre}(F)=
\begin{cases}
5,&\{0,2\}\subseteq D\text{ and }D\cap\{1,15,16\}\ne\varnothing,\\
4,&\text{otherwise}.
\end{cases}}
\tag{89.4}
$$

The corresponding exact worst emitted-bit fees are $70$ and $56$. The attaining controller uses one actual stream for both free values, every low and high INITIAL tail, independently labelled initial bottom, and every history realizing these records. Its worst fee is reached by an admissible source. The lower bounds cover all literal words and endpoint stops, including rejection and every paid calendar advance; they impose no constant-code requirement on the triple.

证明（exact reuse and the all-action root obligations）。 The joint actual sources are precisely those of (87.6), or equivalently (88.5): for $r_j$ representing $6j\pmod{17}$, the history

$$
\ell_j=14(17+r_j),\qquad
w(v,j,s)=(v\oplus\eta_{j,s})0^{\ell_j-s-1}1^s,
\qquad
\eta_{j,s}=\bigoplus_{i=\ell_j-s}^{\ell_j-1}\gamma_i
\tag{89.5}
$$

jointly realizes $(v,-j,s)$ under both alphabets. This is credited use of Interface 87.2 and [S1, Convention 1.3], rather than a new reachability assertion. In particular the full actual source prior includes both tails $13,14$ at each fixed phase and free value, and includes the independent rejected history $1^{28}$. Deterministic evolution and the specified factorization $F=f\circ q_{\rm INITIAL}$ give equality of record and history prices [S1, Proposition 2.2]. Neither (89.5) nor the controller reveals source length.

The low/high separation in (89.3) is exactly the hypothesis of the compulsory-root argument in the proof of Theorem 88.2. Applying its first-zero and absorbing-loss suppliers [IC, Interface 1.4; S1, Lemmas 4.2–4.3] to the actual tails $13,14$ forces every correct first word to have leading run two, hence prefix $110$. A shorter leading run merges these unequal INITIAL labels at its zero; a longer one absorbs both before a separating zero. Their unobserved internal events cannot be distinguished at the completed endpoint or repaired later. Free stopping on either scalar fibre is impossible because $R$ is fresh. Every such root rejects exactly tails $14,15$, preserves every tail below fourteen, and leaves all low sources with the common literal terminal tail of that same word. Tail independence in (89.3) makes its first-zero merger lawful.

At an ensuing common scalar archive, current value and tail are common. The exact common-tail bound [S10, Lemma 3.2] therefore permits at most $2^a$ different INITIAL labels with $a$ further paid words. A word either succeeds on all candidates of that archive or rejects them all. Uniform rejection cannot complete an archive with unequal labels, and homogeneous archives can already stop. This supplied bound covers arbitrary future words, waits, repairs and stopping rules, with the true all-one transfer $\sigma\mapsto\sigma+14$. An absorbing endpoint is not a useful third child on this archive.

For the two arbitrary component tables use exactly [IC, Definition 29.1 and Theorem 29.2]. Its value-independent joined target has low table $\Lambda$, high label $(R,R)$ and an independent initial-bottom pair. The law preserves one literal stream and its worst paid depth, even when the component decoders stop at different endpoints. Complementing successful scalar readings computes both value archives from one observed archive; bottom entries and issued words agree. This is deterministic decoding, without a second experiment or another source's observations. Since the joined low table has fifteen actual labels and a compulsory root with two successful scalar children, the supplied binary bound gives

$$
C_{\rm pre}(f)=C_{\rm pre}(\text{joined target})\ge4.
\tag{89.6}
$$

This is the four-block lower bound for every placement, regardless of individual component class counts.

证明（the triple-specific sharp five-block obstruction）。 Every actual word at issued index $t$ has the full arithmetic row and unique inverse of (87.7)–(87.9). In particular its row is even, vanishes on

$$
M_t=\{-3t-2,-3t-1\}\pmod{17},
\tag{89.7}
$$

and the compulsory root row satisfies $q_0=1$ on $P$, $q_0=0$ on $N$. These are constraints on the very root word, with all other root bits unrestricted.

Suppose the five-block condition in (89.4) holds. Since $D$ has three elements, it is $\{0,2,n\}$ for one $n\in N$. Thus every compulsory root places exactly two of its triple phases on the positive side and the third on the negative side. Let $A_+=q_0^{-1}(1)$, $A_-=q_0^{-1}(0)$ and let $L_+,L_-$ be their joined low label images. The positive side has the sole internal repetition, from those two triple phases; every negative-side phase has a different joined label. Even full-row parity and the seventeen-phase prior consequently give

$$
\begin{aligned}
|A_+|&\text{ is even},& |A_-|&\text{ is odd},\\
|L_+|&=|A_+|-1\text{ is odd},&
|L_-|&=|A_-|\text{ is odd},\\
|L_+|+|L_-|&=16.
\end{aligned}
\tag{89.8}
$$

Both child images are nonempty. Two odd integers summing to sixteen cannot both be at most eight; at least one actual successful root archive has at least nine joined labels. With total worst fee at most four it would have at most three further paid words, hence at most eight different-label leaves, contrary to the supplied common-tail bound. A homogeneous early stop cannot remove this nonconstant child; common rejection cannot recover its labels. Every wait or repair occupies one of those same three charged slots and advances the actual calendar at that price. This proves the all-action lower bound $C_{\rm pre}(f)\ge5$, by the same-stream value-join law. The argument allows the three occurrences of the triple label to acquire different complete endpoint vectors.

证明（the four-coordinate parity alternatives）。 The new code choice concerns physical phase rows, rather than separate component optima. Let $K=\mathbb F_2^4$, with coordinates $0,1,2,3$ in issued order, and consider a full map $Z:\mathbb Z/17\mathbb Z\to K$ separating unequal joined labels and satisfying

$$
\bigoplus_{j=0}^{16}Z(j)=0.
\tag{89.9}
$$

The fourteen singleton phases must have fourteen different codes, none equal to any code used on $D$. Thus $D$ can use at most two different codes. If it uses one code $A$, fifteen distinct vectors occur, with two extra occurrences of $A$. Let $H$ be the single absent cube vector. The whole cube XOR is zero, and the two extra copies cancel, so (89.9) gives $H=0$. Therefore $A\ne0$, all fifteen nonzero vectors occur, and $A$ occurs three times. If $D$ uses two codes, one code $A$ occurs twice and another once. All sixteen cube vectors then occur, with one extra copy of $A$, so (89.9) gives $A=0$. These exhaust the alternatives:

$$
\begin{array}{c|c|c}
\text{codes on }D&\text{represented cube vectors}&\text{extra multiplicity}\\\hline
A,A,A\ (A\ne0)&K\setminus\{0\}&\text{two extra copies of }A\\
0,0,B\ (B\ne0)&K&\text{one extra copy of }0.
\end{array}
\tag{89.10}
$$

The identity $\bigoplus_{z\in K}z=0$ follows because each coordinate has eight ones. This parity dichotomy applies to any such separating even full-row map; it is not assumed as a restriction on controllers in the preceding lower bound. We now realize the appropriate alternative with the exact chronological omissions and root constraints.

证明（credited zero-pair construction when the triple does not contain both positive phases）。 Suppose $P\not\subseteq D$. There are at least two triple phases outside $P$. Choose any two-element set

$$
E\subseteq D\setminus P.
\tag{89.11}
$$

Reuse the precise zero-pair list construction (88.11)–(88.12): prescribe $Z=0000$ on $E$, and on its fifteen-phase complement choose bijectively all fifteen nonzero vectors, respecting

$$
Z_0=1\text{ on }P,\qquad Z_0=0\text{ on }N,\qquad
Z_t=0\text{ on }M_t\quad(1\le t\le3).
\tag{89.12}
$$

Its Hall argument requires exactly that the prescribed zero pair misses $P$: the five disjoint restricted phase groups are $P,N,M_1,M_2,M_3$, of sizes at most $2,3,2,2,2$, and all other lists are unrestricted in the nonzero cube. Those are unchanged here. This step uses that existing construction and its verified list inequalities, not Theorem 88.2 with an incorrect multiplicity hypothesis. In the present target the only code equality is on $E$, whose two phases belong to the same triple class; its third phase may have a different nonzero code. Therefore unequal joined labels are separated. The complete cube occurs with one extra zero, exactly the second alternative in (89.10), so (89.9) holds. No new price content is attributed to this reused matching step.

证明（the new constant-triple construction when both positive phases lie in it）。 It remains on the four-block side that $P\subseteq D$ and $D\cap N=\varnothing$. Write

$$
D=\{0,2,a\},\qquad a\in\{3,\ldots,14\},\qquad
A=e_0=1000.
\tag{89.13}
$$

Assign $Z=A$ on all three phases of $D$. This meets their root constraints and every suffix omission, since $A$ has all suffix coordinates zero. The fourteen singleton phases must receive bijectively

$$
U=K\setminus\{0000,A\},\qquad |U|=14.
\tag{89.14}
$$

For a singleton in $N$ allow the list $U\cap\{z:z_0=0\}$, of size seven. For a singleton in $M_t$, $1\le t\le3$, allow $U\cap\{z:z_t=0\}$, of size six. Every remaining singleton has list $U$. These phase groups are disjoint; at most three lists have the root-negative type and at most two have each suffix type. Removing $a$ can only decrease these counts. Both forced-positive phases have already been assigned to $D$.

Here are all indexed-list Hall inequalities for this new fourteen-vector assignment. The empty subfamily has union size zero. A nonempty subfamily of size $q\le6$ has union size at least six from any of its lists. For $7\le q\le9$, an unrestricted list suffices; if there is none, at least two different restricted types occur because one type has at most three indices. Two different zero-coordinate half-cubes have union size twelve; deleting $0000,A$ leaves at least ten vectors, hence at least $q$. For $q\ge10$, an unrestricted list is compulsory because there are at most $3+2+2+2=9$ restricted indices. It supplies the fourteen-vector union $U$, again of size at least $q$. These cases prove every inequality. The existing finite indexed-list Hall theorem [H] therefore gives the desired bijection on the fourteen singleton phases.

All assigned vectors are nonzero, and every nonzero vector occurs, with exactly two extra copies of $A$ at its triple. The singleton-vector XOR is $A$, since it is the whole cube with $0,A$ removed. The triple-vector XOR is also $A$, since it consists of three copies. Their sum is zero, proving (89.9). Different joined classes have different codes, and all rows meet (89.12). This is the first alternative in (89.10), with zero, rather than a unit vector, omitted from the represented cube. It supplies the missing physical four-block attainment for every $a$ in (89.13), uniformly in the semantic component labels.

证明（the same literal stream, every strict seam and its own decoder）。 In either four-block construction define four fixed actual words by the supplied chronological inverse

$$
B_{t,i}=\bigoplus_{b=0}^{i}Z_t(14t+b\bmod17),
\qquad 0\le t<4,\quad0\le i<14.
\tag{89.15}
$$

Equation (89.9) makes each full row even. At $t=0$ it vanishes on $M_0=\{15,16\}$; at the three later indices (89.12) gives its exact omissions $M_1=\{12,13\}$, $M_2=\{9,10\}$ and $M_3=\{6,7\}$. Hence (87.8)–(87.9) make (89.15) their actual literal inverses. The root charges at $0,1,2$ are $1,0,1$, yielding root bits $110$. All low sources safely complete this root, while both high tails are absorbed and nevertheless pay all fourteen root bits.

For every adjacent coordinate pair $(t-1,t)$ the four-cube has four distinct vectors with both coordinates one. All occur in both constructions: the only possibly absent vector is zero. Thus the full arithmetic rows of the very words in (89.15) obey

$$
\left|\{j:Z_{t-1}(j)=Z_t(j)=1\}\right|\ge4,
\qquad t=1,2,3.
\tag{89.16}
$$

The exact hypotheses of Lemma 84.2 hold: $m=14\ge7$, $3\nmid14$, $k=m+2$ and actual coprimality. After a successful word any rejecting next word would make this full-row intersection at most three, including the supplied true all-one transfer. Equation (89.16) rules rejection out. Starting at the successful compulsory root, induction proves that every low source safely executes this same four-word concatenation.

Each coordinate row has at least eight charged phases: all cube vectors with that coordinate one occur. A fourteen-bit all-one word has only two charged endpoints by (87.8), so none of these words is all ones. Each contains zero and has actual outgoing tail equal to its literal trailing run. The proved safety therefore gives every actual strict seam

$$
\rho(B_{t-1})+\alpha(B_t)<16,\qquad t=1,2,3.
\tag{89.17}
$$

Internal runs are shorter than sixteen because each word has fourteen bits. The argument uses the same rows and their same literal inverses throughout, rather than choosing favourable representatives from different experiments. There is no inserted wait, clearing, padding or repair word and no final cleanup.

Initial bottom stops freely with $L_\bot$. At a completed bottom endpoint after the root, a previously successful INITIAL source returns $R$ and stops; absorption inside the root does not reduce its fee. Every low source issues all four words. Its own five scalar readings, including the free one, give

$$
(v_1\oplus v_0,v_2\oplus v_1,v_3\oplus v_2,v_4\oplus v_3)=Z(j).
\tag{89.18}
$$

Separation defines a unique joined label for each observed code, even when the triple uses two different codes. Return its component selected by the remembered free INITIAL value $v_0$ and stop at this fourth completed endpoint. All compatible INITIAL records then have that component label. Neither phase nor tail is read, and another value fibre's actual archive is never consulted. The exact actual history $0^{238}=w(0,0,0)$ is admissible under both alphabets and is low; the displayed rule makes it emit all four words. Thus the worst fee is actually reached and is $4$ blocks, or $56$ bits, by (89.6).

证明（credited five-word phase fallback and exact upper fee）。 On the obstructed placements use exactly the supplied phase-recovering stream (87.28):

$$
\begin{aligned}
B_0&=11010101010101,\\
B_1&=11110110111001,\\
B_2&=11100101100101,\\
B_3&=01100100011010,\\
B_4&=00101001100011.
\end{aligned}
\tag{89.19}
$$

Its leading/trailing run pairs are the supplied $(2,1),(4,1),(3,1),(0,0),(0,2)$, so its strict seam sums are $5,4,1,0<16$. Its root has the required $110$ prefix; every low tail survives, both high tails are absorbed, and every word contains a zero. The already proved phase map (87.24)–(87.31) is injective on all seventeen phases and is realized by these same five completed words. Its applicability requires this reader, its actual calendar and the common low-root continuation, all exactly present in Definition 89.1; it imposes no low-label-table hypothesis.

At the fifth endpoint use that phase inverse on the source's own five scalar differences and return $\lambda_{v_0}(j)$. This consumes the supplied decoder with the present immutable table; it adds no phase observation or new mathematical phase-recovery result. Initial bottom returns $L_\bot$ freely, high sources return $R$ after the fully paid root, and all low sources pay five whole words. Again the admissible source $0^{238}$ reaches that worst fee. The upper fee is $5$ blocks and $70$ bits, matching (89.8). Together with the four-block construction and (89.6), this proves (89.4) for every placement and semantic label assignment. ∎

### 89.3. Exact supplier correspondence and the added fee content

**数学引文 89.3（Covered reuse and the triple increment）。** The scoped mathematical comparison is this volume through Chapter 88, [IC], [M], [T3], [F4], and the two $\texttt{CoprimeSingletonLower}$ and $\texttt{CoprimeSingletonCost}$ mathematical sources with their Blueprint statements at [revision 3ae8362b33cb1609bfc0beffb15cda0300a16744](https://github.com/the-omega-institute/trureturing/tree/3ae8362b33cb1609bfc0beffb15cda0300a16744). [S1], [S2], [S10], [S15] and [H] retain the immutable versions in this volume's reference definitions.

[IC, Definitions 1.1–1.3 and Interface 1.4; S1, Convention 1.3 and Proposition 2.2] supply the original scanner, all joint actual histories and immutable record/history pullback. [S1, Lemmas 4.2–4.3] supplies first-zero loss and indistinguishable absorption; [S2, Theorem 14.1] supplies the matched coefficient cycle; [S10, Interface 2.1 and Lemma 3.2; S15, Section 1] supplies literal charges, their inverse, the common-tail binary bound and the true all-one tail transfer. [IC, Theorem 29.2] supplies one-stream value joining, including unequal component stopping times. Interface 87.2 supplies the displayed joint witnesses and two-omission calendar, Lemma 84.2 the sharp rejecting-seam bound, and (87.24)–(87.31) the exact five-word phase fallback. These are reused with their stated source, archive and resource hypotheses.

The correspondence uses one actual history as source, its INITIAL record $(v,-j,s)$ as the target argument, and its own completed scalar or bottom outputs as the archive. Its actions are the actual fourteen-bit words (89.15) or (89.19), at their issued indices. Its cost is the full emitted word count, multiplied by fourteen for emitted bits. Offline code choices prescribe those very words, without supplying a source transformation, reset or extra observation. The joined target is the ordered pair of the two semantic low tables on that same phase/tail trajectory, not two separately optimal value experiments.

Chapter 88's exact theorem assumes two double classes; Definition 89.1 has one triple, so that theorem is not instantiated as the present equality. Its zero-pair construction and list inequalities are reused only under the precise hypothesis (89.11). The new price content is the triple's parity obstruction (89.8), the exhaustive four-coordinate parity alternatives (89.10), and the constant-triple assignment (89.13)–(89.14) with its full Hall inequalities and same-stream realization. Two extra copies of a constant triple code cancel, forcing the absent vector to be zero. This differs from the two-double construction's extra codes and omitted unit. The represented-cube geometry then proves all physical seams at four-word capacity. These arguments settle exactly the remaining placements rather than attributing new content to a broader label quantifier on the phase fallback or the reused zero-pair stream. The finite indexed-list matching theorem itself is [H], $\texttt{Finset.all\_card\_le\_biUnion\_card\_iff\_existsInjective'}$, and is credited existing mathematics.

The fees of [M, Definition 1.2 and Theorem 2.1], [T3, Definition 1.2 and Theorem 2.1] and [F4, Definition 72.1 and Theorem 72.2] start at already paid all-one-root archives, with their own mixed tails and low-label conditions. Every correct full root here starts $110$, so none is used as a fee bridge to (89.4). The pinned $\texttt{singleton\_tree\_obstruction}$ has $2\le m<k$, $1\le j\le k$, distinct binary labels and a phase-singleton label across all successful INITIAL tails; its lower bound does not require coprimality. The pinned $\texttt{coprime\_nonzero\_singleton\_cost}$ adds actual coprimality and gives $\max(2,\lceil j/m\rceil)$ for that binary full-tail target, with free value and independent bottom. Their Blueprint statements delimit the same respective hypotheses. Neither is the fresh-high, fifteen-joined-label triple target (89.3); their original endpoint and absorbing semantics supply no additional placement fee theorem here.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), supplies the same bounded experiment-semantics comparison used in Mathematical Citation 88.5: completed observations reaching leaves, tests consistent with available inputs and outputs, disjoint distinguishing observations, and destructive first-action mergers. Here an input is a complete emitted word and its output is a completed scalar or bottom endpoint; the required distinction concerns unequal INITIAL labels. This primary source supplies that semantic comparison, without a reader-specific exact-fee transport. The triple-placement law and its physical code argument are repository-derived ordinary mathematics; no literature-priority claim, exhaustive-search claim, independent-review claim or kernel certification is made.

### 89.4. Conditions, effectivity and the continuing original objective

**边界 89.4（Exact restricted outcome and unresolved scopes）。** Equation (89.4) covers exactly $(k,m,T,g)=(16,14,17,1)$, one triple joined phase class and fourteen singleton classes, arbitrary component equality partitions and label coincidences consistent with that join, low-tail independence for every $0\le s<14$, fresh common high label for both tails $14,15$, and arbitrary independent initial bottom. It covers the full actual history target only through the explicitly specified immutable INITIAL factorization (89.3). No additional compatibility condition is imposed on these targets, and all actually issued complete blocks, including absorbed suffixes, are charged.

For arbitrary $Y$ the theorem is a semantic existence and minimum statement. A supplied finite equality-partition presentation or decidable equality on the finite table entries makes selection effective: determine $D$, test (89.4), select the indicated finite matching or the fixed five-word fallback, and use its endpoint decoder. Offline label comparison, matching time, memory, integer arithmetic and source-description length are separate resources with no optimum asserted here. The symbolic proof uses no finite-case catalogue or numerical corroboration as evidence for universality. This text is an ordinary authoring result, without Lean compilation or kernel verification.

The separate adaptive prices of arbitrary component tables, other joined multiplicity profiles, low-tail dependence, high-label coincidences with low labels, other parameters or gcds, and unrelated acquired supports remain outside this equality. Prior targets, prices and hypotheses are retained. The original objective [IC, Definition 1.3 and Open Problem 9.1] remains active: exact minimum worst-branch ACTUAL emitted-complete-block fees for every attainable immutable INITIAL target and every original $k\ge2,m\ge1$, separately adaptive and ONE GLOBAL preset control. The restricted triple-placement outcome does not complete that objective.

## 追加锚（本行以下为增补区）

## 90. A uniform rejecting-seam obstruction and full INITIAL capacity at arbitrary omission length

The original consecutive arithmetic rows have at most three common charged phases whenever the second word rejects after the first succeeds. This bound holds at every proper-narrow width, retaining the actual inherited tail and actual gcd. It removes the physical seam predicate from a near-full-cube capacity boundary for entire INITIAL targets with three or more chronological omissions. A coprime three-omission family supplies an inhabited consumer with exact GLOBAL fee $h$ and exact emitted-bit fee $h(2^h-3)$ for every $h\ge5$.

**定义 90.1（Ambient arithmetic and the actual tail）。** Use exactly [IC, Definitions 1.1–1.3 and Interface 1.4; S15, Section 1]: original integer weights, matched $V_k\bmod2$ scalar, $T=k+1$, $g=\gcd(m,T)$ and actual endpoint phases $P=g\mathbb Z/T\mathbb Z$. Fix $1\le m<k$ and write $b=k-m$. INITIAL indices are $j=-\theta_{\rm INITIAL}$; actual sources have $j\in P$. At actual issued index $t$, a complete word $B$ has the full arithmetic row

$$
q_{t,B}(j)=\bigoplus_{i=0}^{m-1}B_i\gamma_{-j+tm+i},\qquad
\gamma_i=\mathbf1_{\{0,T-1\}}(i\bmod T),\qquad
W_t=[tm,tm+m]\pmod T.
\tag{90.1}
$$

On this ordered path the credited charges are $B_0$ at its start, $B_{i-1}\oplus B_i$ at its internal vertex $i$, and $B_{m-1}$ at its end; they vanish outside $W_t$. The full row is even. An even row supported on $W_t$ has the unique complete literal inverse

$$
B_i=\bigoplus_{a=0}^i q(tm+a\bmod T),\qquad 0\le i<m.
\tag{90.2}
$$

These are arithmetic identities on the ambient cycle. Only a successful actual source observes their value as its completed scalar difference. A rejecting source observes bottom; a nonactual phase supplies no observation or source. Both original alphabets contain every width-$m$ word here, since $m<k$.

Let $\alpha(B)$ and $\rho(B)$ be the leading and trailing one-run lengths, both equal to $m$ for $1^m$. From actual incoming tail $\sigma<k$, success is exactly $\sigma+\alpha(B)<k$. Its outgoing tail is $\rho(B)$ if it contains zero, and $\sigma+m$ if it is all ones. Every complete word, including its absorbed suffix, is emitted and paid in full. These true transfers are [S15, Definition 1.1], not a choice of favourable word representatives.

**引理 90.2（Uniform sharp three-phase obstruction）。** For every $1\le m<k$, every actual issued index $t$ and the actual $g=\gcd(m,k+1)$, suppose $P_0$ completes successfully on an actual source and the consecutive complete word $Q_0$ rejects on it. Then

$$
\left|\{j\in\mathbb Z/T\mathbb Z:
q_{t,P_0}(j)=q_{t+1,Q_0}(j)=1\}\right|\le3.
\tag{90.3}
$$

The constant three is sharp uniformly over these parameters. If either word is all ones, the intersection is at most two; if $k\ge2m$, it is at most one. No coprimality or omission-length bound is imposed.

证明。 Translate coordinates by the known issued displacement $tm$ for the arithmetic calculation. This is not a phase observation or physical rotation. The two paths are $[0,m]$ and $[m,2m]\pmod T$. If $k\ge2m$, then $2m<T$ and their only common vertex is $m$, proving the stronger bound one.

Otherwise $1\le b<m$ and the second path wraps exactly once. Its order is $m,m+1,\ldots,T-1,0,\ldots,m-b-1$, and the common vertices are

$$
\{m\}\cup[0,m-b-1].
\tag{90.4}
$$

If $P_0$ contains zero, set $r=\rho(P_0)$ and $\ell=\alpha(Q_0)$. Its actual outgoing tail is $r$; rejection of $Q_0$ requires $r+\ell\ge k=m+b$. Outside the endpoint $m$, the suffix of $r$ ones makes the first row's charge support a subset of $[0,m-r]$. The leading $\ell$ ones make the second row vanish at its local path positions $1,\ldots,\ell-1$. A common wrapped vertex $j$ has local position $b+1+j$, so the second row can charge it only when $j\ge\ell-b-1$. This also covers the final endpoint when $Q_0=1^m$. Consequently

$$
\{j:q_{t,P_0}(j)=q_{t+1,Q_0}(j)=1\}
\subseteq\{m\}\cup
\bigl([0,m-b-1]\cap[\ell-b-1,m-r]\bigr).
\tag{90.5}
$$

Before clipping, that integer interval has $\max(0,m-r-\ell+b+2)\le2$ points. Including the boundary vertex gives (90.3). This argument counts full arithmetic rows, without exposing a rejection time or an intermediate scalar.

If $P_0=1^m$, its row has only the two endpoints $0,m$, so the bound two follows directly. Its actual incoming tail is retained: success gives $\sigma+m<k$, hence outgoing tail $\sigma+m$, and rejection of $Q_0$ means $\sigma+m+\alpha(Q_0)\ge k$. Substituting $m$ for this outgoing tail is unnecessary and can be false. For example, whenever $b\ge2$, incoming tail $b-1$ lets $1^m$ succeed with tail $k-1$, after which a word beginning one rejects although $m+1<k$. These incoming records are jointly actual by [IC, (1.3)]. If $Q_0$ is all ones, its row likewise has only two endpoints. Zero words have empty charge support; moreover an all-zero predecessor leaves tail zero and an all-zero successor clears any legal tail.

Sharpness is credited evidence from Lemma 82.2: at $(k,m,T,g)=(6,5,7,1)$, the actual tail-zero arrival followed by $10111\mid11101$ succeeds in its first word, rejects in its second and has common charged phases $\{1,2,5\}$. Lemma 84.2 also supplies sharp two-omission witnesses. These establish sharpness of the uniform constant, rather than a claim that it is the best bound at every fixed reader. ∎

**定义 90.3（Full INITIAL tables and the algebraic capacity condition）。** Assume

$$
h\ge5,\qquad 3\le m<k<2m,\qquad
b=k-m\ge3,\qquad T=k+1,\qquad \gcd(m,T)=1.
\tag{90.6}
$$

Take arbitrary tables $\lambda_0,\lambda_1:\mathbb Z/T\mathbb Z\to Y$, a common $R$ fresh from both low images, and any independently observed initial-bottom label $L_\bot$. On the entire original INITIAL space set

$$
\begin{aligned}
f(v,-j,s)&=
\begin{cases}
\lambda_v(j),&0\le s<m,\\
R,&m\le s<k,
\end{cases}\qquad
f(\bot)=L_\bot,\\
F(w)&=f(q_{\rm INITIAL}(w)),\qquad
\Lambda(j)=(\lambda_0(j),\lambda_1(j)),\qquad
n=|\Lambda[\mathbb Z/T\mathbb Z]|\in\{2^h-1,2^h\}.
\end{aligned}
\tag{90.7}
$$

Every actual phase, every INITIAL tail $s<k$, both free values and all complete histories realizing them are included. The low tables are separately independent of INITIAL tail; their component partitions, images and decoder stopping times need not agree. $L_\bot$ may coincide with any other label. Targets are never reevaluated on current records.

Let $\mathsf A_h$ assert the existence of a phase assignment $Z:\mathbb Z/T\mathbb Z\to\mathbb F_2^h$, with coordinates $0,\ldots,h-1$, satisfying exactly

$$
\begin{aligned}
\Lambda(j)\ne\Lambda(j')&\ \Longrightarrow\ Z(j)\ne Z(j'),\\
\bigoplus_{j\in\mathbb Z/T\mathbb Z}Z(j)&=0,\\
Z_t(j)&=0&&j\notin W_t,\quad0\le t<h,\\
Z_0(0)&=Z_0(b)=1,\qquad
Z_0(i)=0&&1\le i<b.
\end{aligned}
\tag{90.8}
$$

Different vectors within one joined class are allowed. The XOR and support clauses mean that every full row is even and supported on its actual chronological path, whose complement has $b$ vertices. The final line is exactly the charge prefix corresponding to first literal zero at position $b$. There is no further seam condition in $\mathsf A_h$.

**定理 90.4（Exact full INITIAL GLOBAL capacity boundary）。** Under Definition 90.3 and either original alphabet,

$$
\boxed{C_{\rm pre}(f)=C_{\rm pre}(F)=h
\quad\Longleftrightarrow\quad\mathsf A_h.}
\tag{90.9}
$$

Every assignment satisfying (90.8) gives one lawful full INITIAL stream attaining $h$ complete blocks and $mh$ emitted bits. If the condition fails, $C_{\rm pre}\ge h+1$, possibly infinite; no exact price above capacity or arbitrary adaptive value-join equality is asserted.

证明（joint actual sources and the compulsory root）。 The original joint-history supplier [IC, (1.3); S1, Convention 1.3] applies with this actual $m,T$: choose

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad
\ell\ge s+2,\qquad
\eta=\bigoplus_{i=\ell-s}^{\ell-1}\gamma_i,\qquad
w(v,j,s)=(v\oplus\eta)0^{\ell-s-1}1^s.
\tag{90.10}
$$

Coprimality gives arbitrarily large such lengths. The separating zero and compensating first bit jointly realize value $v$, phase $-j$ and tail $s<k$, with complete internally legal blocks under both alphabets. History lengths are unobserved. Independently, $1^{2m}$ realizes initial bottom because $m<k<2m$. Deterministic evolution and the specified immutable pullback give equal record/history fees by [S1, Proposition 2.2].

At each phase and either fixed free value, the actual tails $m-1,m$ have unequal labels, low versus fresh $R$. Free stopping is impossible. If a root has its first zero after $a<b$ ones, both records survive to that zero and merge with identical value and phase. If $a>b$, both reject before the first endpoint; a zero-free root also rejects both since $m>b$. These losses are irreversible by [S1, Lemmas 4.2–4.3]. Thus every correct root has exactly $b$ leading ones, followed by zero, irrespective of later horizon or actions.

Such a root rejects exactly the high INITIAL tails $s\ge m$. Every low tail survives because $s+b\le k-1$, reaches the zero and completes safely; its phase-wise merger preserves its tail-independent INITIAL label. All low sources then have the common terminal tail of that same word. Within any scalar archive, every later word either succeeds on all its candidates or rejects all, and success has at most two scalar children with common value and tail. Uniform rejection cannot resolve unequal INITIAL labels; homogeneous archives may stop before acting. The supplied common-tail bound [S10, Lemma 3.2] therefore gives at most $2^H$ different low labels with total worst fee $H$, including the root, arbitrary waits, padding, repairs, all-one transfers and endpoint stops.

For GLOBAL control apply exactly [IC, Definition 29.1 and Theorem 29.2]. The ordered joined target has low table $\Lambda$, high label $(R,R)$ and independent bottom. Complement symmetry computes its two component archives from the same actual completed endpoints and preserves the same stream and worst paid bound, including unequal component stopping times. It creates no second experiment or borrowed observation. On a fixed value fibre the joined target has $n\ge2^h-1>2^{h-1}$ actual low labels, hence every correct preset controller has $H\ge h$. This joining step and binary bound are credited reuse.

证明（necessity, including phase splits and early stops）。 Suppose a correct preset controller has worst fee $h$. Transfer its very same stream to the joined target and stop joined-homogeneous archives immediately. This is the early-stop normalization of [S15, Theorem 3.3]. Some low source still reaches slot $h-1$, by the preceding lower bound. Every running archive is nonconstant. After the root, a rejecting word would uniformly absorb a running archive and could never resolve it; thus every word through that slot succeeds on continuing low sources.

Safety is independent of phase and value. Since the root contains zero, all low tails have the same trajectory along the fixed words. The successful words therefore also succeed if earlier stopped low phases are continued solely for the mathematical row calculation. This gives their full $h$-coordinate arithmetic vectors $Z(j)$, without charging or observing stopped actual sources. Unequal joined labels cannot have equal full vectors: on a fixed initial value they would have equal scalar prefixes at the earlier stopping time and the same deterministic stopping/decoding decision. The full rows are even and vanish outside their exact $W_t$ by (90.1)–(90.2). The compulsory root $1^b0$ forces its charges $1,0,\ldots,0,1$ at $0,1,\ldots,b$. These are all clauses of (90.8). No constancy on a joined class was inferred. Every paid wait retains its actual slot; no calendar advance is omitted.

证明（same literal sufficiency and automatic strict seams）。 Choose any $Z$ satisfying (90.8) and prescribe the one fixed stream by

$$
B_{t,i}=\bigoplus_{a=0}^i Z_t(tm+a\bmod T),\qquad
0\le t<h,\quad0\le i<m.
\tag{90.11}
$$

Evenness and support make these the actual full-row inverses. The root has prefix $1^b0$ and therefore exactly the established high rejection and low preservation. Every word is internally legal since $m<k$.

At least $2^h-1$ distinct vectors occur in the actual phase table, so at most one cube vector is absent. For any two consecutive coordinates $t-1,t$, at least $2^{h-2}-1\ge7$ distinct represented vectors have both coordinates one. Distinct vectors require distinct actual phases. Thus the complete rows of these very words satisfy

$$
|\{j:Z_{t-1}(j)=Z_t(j)=1\}|
\ge2^{h-2}-1>3,\qquad1\le t<h.
\tag{90.12}
$$

Inductively, if a low source successfully completes the preceding word but the next rejects, Lemma 90.2 contradicts (90.12), with its true incoming tail retained. Hence every next word succeeds on every low source. Furthermore every coordinate row charges at least $2^{h-1}-1>2$ phases, whereas an all-one word has only two charged endpoints. All selected words contain zero; their outgoing tails are their literal trailing runs. The proved safety gives every actual strict seam

$$
\rho(B_{t-1})+\alpha(B_t)<k,\qquad1\le t<h.
\tag{90.13}
$$

This discharges the physical constraint on the same literal words. No clearing, wait, padding or repair block is inserted, and no final cleanup is needed.

Initial bottom returns $L_\bot$ freely. High sources emit the entire root, including all absorbed bits, return $R$ at its completed bottom endpoint and stop. Every low source emits all $h$ words. Its own scalar readings $v_0,\ldots,v_h$ yield $(v_{t+1}\oplus v_t)_{t<h}=Z(j)$. Separation makes the joined label determined by that vector even if its class uses several codes. Return its component selected by the remembered free INITIAL value $v_0$ and stop at endpoint $h$. The same stream serves both values and every tail/history of this fixed target. Every low record is actual by (90.10) and reaches fee $h$ in this displayed rule. Together with the all-action lower bound this proves (90.9), its exact bit fee, and the failure implication $C_{\rm pre}\ge h+1$. ∎

**构造 90.5（An infinite three-omission full INITIAL consumer）。** For every integer $h\ge5$ put

$$
N=2^h,\qquad k=N,\quad m=N-3,\quad T=N+1,\quad b=3,\qquad
M_t=\{N-2-4t,N-1-4t,N-4t\},\quad0\le t<h.
\tag{90.14}
$$

The actual gcd is $\gcd(N-3,N+1)=\gcd(N-3,4)=1$. The chronological path starts at $u_t=-4t\pmod T$ and misses exactly $M_t$. The induction $N\ge4h+12$ starts at $h=5$ and persists on doubling $N$; consequently the least listed omission is $N-4h+2\ge14$. The $M_t$ are disjoint triples separated by one phase, avoid $0,1,2,3$, and do not wrap in this representative list. No virtual phase is used.

Assign $Z(1)=Z(2)=0$. On the remaining $N-1$ phases assign bijectively all $N-1$ nonzero vectors of $K=\mathbb F_2^h$, with these indexed lists:

$$
\mathcal L_j=
\begin{cases}
\{z\in K:z_0=1\},&j\in\{0,3\},\\
\{z\in K\setminus\{0\}:z_t=0\},&j\in M_t,\quad0\le t<h,\\
K\setminus\{0\},&\text{otherwise}.
\end{cases}
\tag{90.15}
$$

The phase groups are disjoint, so each constrained phase has exactly the indicated single restriction. Here is a complete Hall check. A subfamily containing an unrestricted list has union size $N-1$, at least its number of indices. A nonempty subfamily of $q\le N/2-1$ lists has union size at least $N/2-1$ from any member. A larger subfamily without an unrestricted list has $q\le3h+2$, the total number of restricted indices. It has at least two different types, since one type has at most three indices and $q\ge N/2\ge16$. Opposite root half-cubes have union $K\setminus\{0\}$. Two types on different coordinates have union of size at least $3N/4-1\ge3h+2$, using $N\ge4h+12$. Thus in every case the union has at least $q$ members; the empty inequality is immediate. The credited finite indexed-list Hall theorem [H] supplies the required bijection. Matching is used to inhabit this application, not asserted as a new mathematical mechanism.

All cube vectors now occur, zero exactly twice and every nonzero vector once. Each coordinate of the cube has the even number $2^{h-1}$ of ones, so its XOR is zero. The full table XOR is therefore also zero, since its one extra occurrence is zero. Its rows vanish on $M_t$; its root charges at $0,1,2,3$ are $1,0,0,1$, so it satisfies the algebraic prefix for $1110$.

For a fixed choice of this table let $a=\lceil h/2\rceil$, write $Z(j)=(I(j),J(j))\in\mathbb F_2^a\times\mathbb F_2^{h-a}$, and take disjoint sets of labels $\{A_i:i\in\mathbb F_2^a\}$ and $\{D_l:l\in\mathbb F_2^{h-a}\}$, distinct within each set. Choose a common $R$ fresh from both sets and any independent $L_\bot$. Specify the entire immutable target, before any experiment, by

$$
\begin{aligned}
f_h(0,-j,s)&=A_{I(j)},&f_h(1,-j,s)&=D_{J(j)}&&0\le s<N-3,\\
f_h(v,-j,s)&=R&&&&N-3\le s<N,\\
f_h(\bot)&=L_\bot,\qquad F_h(w)=f_h(q_{\rm INITIAL}(w)).
\end{aligned}
\tag{90.16}
$$

The low component images have sizes $2^a$ and $2^{h-a}$, and their partitions differ: all cube vectors occur, so holding either coordinate projection fixed leaves multiple values of the other. The ordered join has exactly $N$ classes, its only double being phases $\{1,2\}$. No two separate value optima or separately realized marginals were combined.

**定理 90.6（Exact fee of the inhabited three-omission family）。** For every $h\ge5$, every table chosen in Construction 90.5 and either original alphabet,

$$
\boxed{C_{\rm pre}(f_h)=C_{\rm pre}(F_h)=h,\qquad
\text{minimum worst emitted-bit fee}=h(2^h-3).}
\tag{90.17}
$$

证明。 Equations (90.14)–(90.16) verify every hypothesis and every clause of (90.8): the joined labels are in bijection with the represented cube vectors, all full rows are even and have their exact chronological support, and the root first-zero prefix is $1110$. This is a consumer of Theorem 90.4, with its same-literal inversion (90.11), automatic strict seams and own-endpoint decoder; its application is not a separate novelty claim.

For explicit jointly realized sources, $m^{-1}=N/4\pmod T$. Let $r_j$ be the representative of $-(N/4)j\pmod T$ in $\{0,\ldots,T-1\}$, and use (90.10) with $\ell_j=m(T+r_j)$. Then $\ell_j$ is divisible by $m$, congruent to $-j\pmod T$, and larger than $s+1$ for every $s<N$. The credited separating history jointly realizes every value, phase and tail under both alphabets. Initial bottom is separately realized by $1^{2m}$. No source length enters the decoder.

The one fixed literal stream obtained from this chosen $Z$ has $h$ complete words. Initial bottom stops freely, high tails $N-3,N-2,N-1$ stop with $R$ only after their fully paid root, and all low sources stop after their own $h$ scalar differences decode $Z(j)$ and its remembered-value component. In particular the actual low history $0^{mT}=w(0,0,0)$ reaches that last endpoint and pays exactly $h$ blocks and $mh$ bits. The joined target has $N$ actual low labels, so the all-action capacity lower bound in Theorem 90.4 rules out every smaller GLOBAL fee, including all other roots, words, waits, repairs, rejection and early-stop rules. This proves the exact attained price. ∎

### 90.7. Supplier correspondence, mathematical increment and boundaries

**数学引文 90.7（Exact reuse and scope of the added reduction）。** The scoped comparison comprises [IC], this volume through Chapter 89, [M], [T3], [F4], and the $\texttt{CoprimeSingletonLower}$/$\texttt{CoprimeSingletonCost}$ mathematical sources and Blueprint statements at [revision e23df943779556edf1d488df6c29bf6483b0a818](https://github.com/the-omega-institute/trureturing/tree/e23df943779556edf1d488df6c29bf6483b0a818). The immutable [S1], [S2], [S10], [S15] and [H] references defined in this volume supply the primary mathematical interfaces used here.

[S2, Theorem 14.1] supplies the original matched coefficient cycle. [IC, Definitions 1.1–1.3 and Interface 1.4; S1, Convention 1.3 and Proposition 2.2] supplies the full joint prior, actual histories, immutable pullback, complete endpoints and emitted fees. [S1, Lemmas 4.2–4.3] supplies irreversible first-zero and rejection losses; [S10, Interface 2.1 and Lemma 3.2; S15, Section 1, Definition 1.1 and Theorem 3.3] supplies literal charge inversion, true inherited-tail transfer, the binary common-tail bound and preset early-stop normalization. [IC, Theorem 29.2] supplies the exact value join on one actual stream. [H], $\texttt{Finset.all\_card\_le\_biUnion\_card\_iff\_existsInjective'}$, supplies only finite indexed-list matching. None of these applications or bit-unit conversions is counted as new content.

The new physical step is (90.4)–(90.5) for every omission length and actual gcd, including nonwrapping windows and all-one arrivals. Lemmas 82.2 and 84.2 supply its sharp witnesses, but their respective reader hypotheses $k=m+1$ and $k=m+2$ do not cover (90.6). The full INITIAL consequence (90.9) uses that uniform obstruction to remove every extra seam predicate from every witnessing near-full-cube phase assignment at $b\ge3$, preserving phase-wise splitting and both component stopping rules. It reduces this capacity question to the explicit algebraic restrictions (90.8), rather than reissuing [S15]'s response/seam certificate with a new name. The Hall construction supplies a real full-target consumer at new readers $(2^h,2^h-3)$; it is not a scaled old construction offered as an independent new mechanism.

[IC, Theorem 33.2 and Open Problem 35.2] already covers arbitrary INITIAL preset targets throughout the noncoprime proper-narrow region $3\le m<k$, $g\ge2$, including $k<2m$. The present capacity theorem and consumer have $g=1$ and do not reclassify that covered region as missing. Chapters 86–89 have their specified two-omission readers and multiplicity/placement hypotheses; their attaining words are not transported to the new three-omission reader. [M, Definition 1.2 and Theorem 2.1], [T3, Definition 1.2 and Theorem 2.1] and [F4, Definition 72.1 and Theorem 72.2] price already paid all-one-root archives, with mixed inherited tails and at most their specified lower-label images. Here the full target instead forces first zero at $b$, so none supplies a full-fee bridge without a different proved correspondence. The singleton Lean statements concern distinct binary phase-singleton labels on all successful INITIAL tails; neither is the fresh-high, near-full ordered-join target (90.7). Their existence or Blueprint prose is not a compilation check of this chapter.

The source/action/target/fee correspondence throughout is one actual original history, its immutable INITIAL record, the prescribed actual complete words at their issued indices, and that source's own completed scalar or bottom endpoints. Offline vector choice prescribes those very words. Ambient rows become scalar differences only on successful actual records. No reset, copy, hidden clock, intermediate Read or borrowed archive is introduced. Authorship uses the two stated skills under pure-theory authorization, with repository prior exposed; the proofs are repository-derived ordinary mathematics, without compilation, kernel certification, independent-review or literature-priority claims. This scoped supplier search is not global novelty certification.

**边界 90.8（Exact restricted settlement and the active original objective）。** Lemma 90.2 covers every proper-narrow original reader and actual gcd. Theorem 90.4 covers exactly (90.6)–(90.7), with $2^h-1$ or $2^h$ ordered joined classes, arbitrary phase multiplicities, low-tail independence, fresh common high label and arbitrary independent bottom. It gives an exact price only at capacity and a lower bound when its algebraic condition fails. It neither chooses a feasible assignment for every such table nor gives exact above-capacity prices. The infinite application (90.17) fixes one full target after its finite offline assignment and one preset stream for that target; it does not optimize offline computation or memory.

The universal obstruction and the symbolic Hall inequalities are ordinary proofs. Finite direct evaluations of full arithmetic rows and original bit updates corroborate the stated seams and full-target decoder at $h=5,6,7$; they are regression evidence, not the justification for the universal claims. No Lean or kernel validation is asserted. Arbitrary adaptive optima, adaptive value joining, smaller joined images, mixed low INITIAL tails, nonfresh high labels, other full target forms, critical/wide readers and the original all-parameter exact-fee objective remain outside this restricted capacity result. The original goal remains ACTIVE, with all previous targets, hypotheses and prices retained.

## 追加锚（本行以下为增补区）

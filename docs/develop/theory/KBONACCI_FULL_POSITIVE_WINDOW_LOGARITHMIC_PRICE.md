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

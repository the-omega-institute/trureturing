# KBonacci coprime INITIAL phase-target fees

> This is an append-only theory volume using the `generic-v1` convention. Corrections and extensions belong after the final append anchor in newly numbered sections. The mathematics consists of ordinary proofs and finite exact checks; it has not been compiled or verified by the Lean kernel.

## 1. Fixed reader, actual sources and charged observations

Fix the original forbidden-run order $k\ge2$ and complete-block width $m\ge1$. Bits are read in increasing weight order. A legal word avoids $1^k$. The matched integer weights and value are

$$
G_i=2^i\quad(0\le i<k),\qquad
G_i=\sum_{h=1}^kG_{i-h}\quad(i\ge k),\qquad
V_k(w)=\sum_{i<|w|}w_iG_i.
$$

The reader reports $V_k(w)\bmod2$, with independent absorbing rejection $\bot\notin\mathbb F_2$. Write $T=k+1$. The supplied matched coefficient law is $c_i=G_i\bmod2=\mathbf1_{\{0,-1\}}(i\bmod T)$, of exact period $T$ [S2, §§13–14]. This is the original matched $\Phi_k=X^k-\sum_{i<k}X^i$ reader, rather than a freely selected linear sensor.

The two control alphabets remain separately fixed:

$$
\mathcal A_{\rm all}=\{0,1\}^m,\qquad
\mathcal A_{\rm loc}=\{B\in\{0,1\}^m:B\text{ internally avoids }1^k\}.
$$

The prior is all finite actual complete-block histories in the chosen alphabet, including already rejected histories. A legal endpoint record is $(v,\theta,s)$, where $v\in\mathbb F_2$, $\theta=|w|\bmod T$, and $0\le s<k$ is the terminal run of ones. Generally $\theta\in P=g\mathbb Z/T\mathbb Z$, where $g=\gcd(m,T)$. This volume concerns $g=1$, so $P=\mathbb Z/T\mathbb Z$, indexed by

$$
\theta_j=-j\pmod T,\qquad 0\le j\le k.
$$

The initial output $v$ or $\bot$ is free. Afterwards only complete-block endpoints are visible. A controller chooses its next literal $m$-bit word from its actual archive, or stops with an INITIAL label. Every emitted block costs one, including all-zero displacement blocks and blocks containing padding. No reset, copy, intermediate observation, unknown initial clock or combination of different branches is available. The controller knows its own paid displacement $tm$ after $t$ blocks. Offline search time and controller memory are separate resources.

Fix one free initial-value fiber $v$. All four laws concern targets

$$
f(v,\theta_j,s)=\lambda(j),\qquad 0\le s<k,
$$

independent of the INITIAL tail. The label set can be arbitrary; its image on the finite phase set is finite. Let $C_v(\lambda)$ be the minimum worst-case number of actually emitted blocks. Labels in the other value fiber may differ and are handled independently. The total cost is $\max\{C_0,C_1\}$; the initial $\bot$ branch returns its prescribed label for free. Constants on either legal value fiber also stop for free. Successful protocols in this volume never reject a legal source.

The supplied actual joint-source interface [S3, Lemma 15.1; S1, Convention 1.3; S4, §1] gives a concrete history for every lower-bound representative. Choose

$$
N\equiv0\pmod m,\qquad N\equiv-j\pmod T,\qquad N\ge s+2,
\qquad D=\bigoplus_{i=N-s}^{N-1}c_i,
$$

and take the single word

$$
W(v,j,s)=(v\oplus D)\,0^{N-s-1}1^s.
$$

Coprimality makes the congruences compatible, and increasing $N$ provides the indicated zero separator. Its initial bit contributes $v\oplus D$, its terminal run contributes $D$, its length phase is $-j$, and its actual tail is $s$. It is legal and cuts into locally legal complete blocks. Thus the full-tail sources used at the root and the tail-zero representatives used below are joint realizations, rather than a product of unrelated marginal reachability assertions. The chosen $N$ is a source witness, never information given to the controller.

All displayed protocols have $m<k$. Consequently every $m$-bit word is internally legal and the two alphabets coincide here. This does not make a cross-block seam safe: a run reaching $k$ still rejects in either alphabet. The general equivalence of optimal costs in the two alphabets is already supplied by [S1, Proposition 2.3].

## 2. The cost mechanism inherited from the literal reader

We use the first-zero, actual path-mask and finite adaptive-tree interfaces of [S1, §§2, 4–5] and [S4, §§1–3], not a new mask or Bellman framework. A one at absolute continuation position $t$ has INITIAL phase mask $\{t,t+1\}\pmod T$. The successful endpoint difference of a whole block is the XOR of its literal one-position masks. Rejection is an independent observation, not an additional parity value. Differences mean $y_{t+1}\oplus y_t$ between consecutive visible successful endpoints; knowing the free initial value makes these equivalent to the endpoint archive.

For a nonconstant phase-only target, any successful root word starts with zero [S4, Lemma 3.1]. Indeed, if it starts with one, choose two differently labelled phases, each with actual INITIAL tail $k-1$ using $W$. Both immediately enter the same absorbing rejection record and have identical archives forever. This argument applies to the full joint prior and both alphabets. It does not impose root zero on a target that depends on INITIAL tails.

Root zero sacrifices the earliest edge while clearing every old tail. Thereafter candidates sharing an archive have a common current value and the same literal current tail. On such a set, any next block either rejects all these candidates or succeeds on all of them. Uniform rejection cannot distinguish different INITIAL labels. A nonzero phase $j$ first has active positions $j-1,j$; after those pass, its interior distinction is silent until cyclic reactivation. Phase zero has its position zero suppressed by the root zero and next becomes active at $T-1=k$.

The lower-bound pair $j=0,J$, both initially of tail zero, therefore remains on one common archive before block $\lceil J/m\rceil$: every earlier block ends before position $J-1$, and also before phase zero reactivates. Adaptation cannot create a difference while both sources are silent; their common tail also makes any rejection uniform. When their labels differ, this proves the paid-arrival lower bound. It is an application of actual transition semantics, not a free displacement to a favorable phase.

An excluded phase can supply parity on the same actual branch. A literal mask of even total charge may restrict to an odd mask on the surviving candidates because its other endpoint has already been excluded. Whether that endpoint is accessible, and whether the same word's leading run is legal with the actual terminal tail, determines the fee. The four laws below make this dependence explicit.

## 3. Unit blocks: every INITIAL phase labeling

**Theorem 3.1 (exact unit-block law).** Let $m=1$ and $k\ge2$. In a specified free value fiber, let $\lambda:\{0,\ldots,k\}\to Y$ be any phase labeling, independent of INITIAL tail. Put

$$
A=\lambda(0),\qquad
J=\max\bigl(\{j\in\{1,\ldots,k\}:\lambda(j)\ne A\}\cup\{0\}\bigr).
$$

A constant labeling has cost zero. For $k\ge3$ and $J>0$,

$$
C_v(\lambda)=\max\bigl\{J,\ 2+\mathbf1_{\{\lambda(1)\ne\lambda(2)\}}\bigr\}.
\tag{3.1}
$$

For $k=2$, the exact costs are

$$
C_v(\lambda)=
\begin{cases}
0,&J=0,\\
3,&J=1,\\
2,&J=2\text{ and }\lambda(1)=\lambda(2),\\
4,&J=2\text{ and }\lambda(1)\ne\lambda(2).
\end{cases}
\tag{3.2}
$$

Every bit in the proof is one paid complete block.

**Proof.** First suppose $k\ge3$. For $3\le H\le k$, emit the literal stream $0\,1^{H-1}$ and retain all endpoint differences $d_0,\ldots,d_{H-1}$. The full signatures are

$$
\begin{array}{c|c}
\text{INITIAL index}&\{t:d_t=1\}\\ \hline
j=1&\{1\}\\
1<j<H&\{j-1,j\}\\
j=H&\{H-1\}\\
j=0\text{ or }j>H&\varnothing.
\end{array}
\tag{3.3}
$$

The two singleton positions are distinct because $H\ge3$, and every listed pair is distinct from them and from every other pair. These signatures follow directly from the literal active positions; the root at position zero is zero and no wrap occurs. The root clears all actual old tails, and the longest subsequent run is $H-1\le k-1$, so the whole stream is legal.

When $J\ge3$, use $H=J$, return $\lambda(j)$ on each identified nonzero signature, and return $A$ on the zero signature. Every phase beyond $J$ has label $A$, so these are correct INITIAL leaf labels. When $J\le2$ and $\lambda(1)\ne\lambda(2)$, use $H=3$; index three and every later index have label $A$, giving the same correct rule in three blocks. When $J=2$ and $\lambda(1)=\lambda(2)$, emit $01$. Its differences are $(0,1)$ at indices $1,2$ and $(0,0)$ elsewhere; return their common label or $A$, respectively. These protocols prove all upper bounds in (3.1). In particular, taking $H=k$ identifies every phase for $k\ge3$ within this same proof.

For $k=2$, emit $01$ in the equal-pair case. If $J=1$, emit $001$. Its full difference signatures, ordered by INITIAL index, are

$$
j=0:(0,0,1),\qquad
j=1:(0,0,0),\qquad
j=2:(0,0,1).
$$

Return $\lambda(1)$ on the zero signature and $A=\lambda(2)$ otherwise. If $J=2$ and the pair labels differ, emit $0101$. The full signatures are

$$
j=0:(0,0,0,1),\qquad
j=1:(0,1,0,1),\qquad
j=2:(0,1,0,0).
\tag{3.4}
$$

They identify all three INITIAL indices and permit their own labels. All runs after the first zero have length at most one; each displayed stream is legal for every INITIAL tail.

For the adaptive lower bounds, a nonconstant target forces root bit zero by §2. One block therefore yields a constant output and cannot succeed. In a two-block tree, the second bit zero gives no information, and the second bit one splits precisely $\{1,2\}$ from the remaining indices. Both sets must have constant labels to stop. Since $A=\lambda(0)$ and $J$ is the last non-$A$ index, a nonconstant labeling admits two blocks exactly when $J=2$ and $\lambda(1)=\lambda(2)$. This proves the three-block lower bounds for the other small cases. For $J\ge3$, the actual tail-zero pair $0,J$ from §2 proves the additional lower bound $J$. These arguments cover every adaptive tree, not just the displayed stream.

It remains to exclude three blocks for $k=2,J=2,\lambda(1)\ne\lambda(2)$. Following root zero, if the second bit is zero then the third bit one queries $\{0,2\}$, whose labels differ; third bit zero queries nothing. Thus neither third choice succeeds. If the second bit is one, its positive child consists of $\{1,2\}$ with different labels and common terminal tail one. Third bit zero gives no new value difference; third bit one rejects both and merges them permanently. This child cannot finish. The root has no other possible first bit, so all three-block adaptive trees fail. Stream (3.4) attains four, completing (3.2). $\square$

The endpoint stream used in this theorem is available specifically at $m=1$. Its signatures cannot be treated as observations inside a larger complete block; §7 gives an actual failure of such grouping.

## 4. Width two: every binary INITIAL phase target

**Theorem 4.1 (exact binary width-two law).** Let $m=2$, $T=k+1$ odd with $T\ge5$, so $k\ge4$, $g=1$ and $m<k$. Fix distinct labels $A,B$ and a binary phase target with $\lambda(0)=A$. Write

$$
D=\{j\in\{1,\ldots,k\}:\lambda(j)=B\},\qquad J=\max(D\cup\{0\}).
$$

Then, on the full joint actual-history prior,

$$
C_v(\lambda)=
\begin{cases}
0,&D=\varnothing,\\
1,&D=\{1,2\},\\
\max\{2,\lceil J/2\rceil\},&\text{otherwise}.
\end{cases}
\tag{4.1}
$$

**Proof.** The empty case stops free. For $J\le2$ and a nonempty target, emit $01$. Difference zero has only $A$ labels. Difference one retains exactly $\{1,2\}$; if their labels agree, return the common label immediately. Otherwise emit the whole next block $10$. Its one is at absolute position two, with mask $\{2,3\}$, and so singles out index two within that actual pair. Return $\lambda(2)$ on difference one and $\lambda(1)$ on zero. This costs at most two, and exactly one for $D=\{1,2\}$.

For $d=\lceil J/2\rceil\ge2$, scan on the continuing zero branch by emitting $01$ in block slots $t=0,\ldots,d-2$. The mask in slot $t$ is the literal pair

$$
\{2t+1,2t+2\}.
$$

A zero difference excludes that whole pair. A positive difference retains exactly that pair, since all earlier pairs were excluded on this path. If its two INITIAL labels agree, stop with that label. If they differ, emit $10$ in the next slot: its leading edge is $\{2t+2,2t+3\}$, restricting to the right member of the pair. Return the right label on one and the left label on zero, then stop. The repair branch ends by block $t+2\le d$; it never rejoins or reads the continuing scan branch.

After $d-1$ zero scans, put $a=2d-1$, $b=2d$, and $z_j=\mathbf1_D(j)$. The final literal block is

$$
(z_a\oplus z_b)\,z_b.
\tag{4.2}
$$

Its two positions are $2d-2$ and $2d-1$. The full mask assigns coefficients $z_a\oplus z_b$ to $2d-2$, $z_a$ to $a$, and $z_b$ to $b$. Index $2d-2$ has already been excluded by the preceding scan. All indices $1,\ldots,2d-2$ are absent from this actual child; every index above $b$ has label $A$ because $J\le b$. Thus the mask restricted to survivors equals $D$, and the final difference returns $B$ on one and $A$ on zero. Also $b\le k$, so no modular wrap is being hidden in this argument.

The first $01$ clears all INITIAL tails. Each further scan starts zero. A scan leaves tail one, and a repair $10$ joins at most two consecutive ones. The worst final block in (4.2) is $11$, which joins that tail to a run of three. Since $k\ge4$, every such seam is legal. The full second bit of each block, including zero padding, is emitted and charged. The constructed worst fee is at most $d$.

For optimality, the actual pair $0,J$ supplies $C_v\ge\lceil J/2\rceil$ by §2. A nonconstant one-block solution must start zero; the only root words are $00$ and $01$, and their masks are respectively empty and $\{1,2\}$. Because index zero lies outside the mask and has label $A$, a nonconstant binary target can finish in one block exactly when $D=\{1,2\}$. All other nonempty cases require at least two. These lower bounds hold for all adaptive continuations and coincide with the upper bounds, proving (4.1). $\square$

The case $k=2,m=2$ belongs to the supplied critical-width theory [S5, Theorem 5.1]; it is outside the proper-narrow hypotheses here.

## 5. First-window charge and the boundary obstruction

**Theorem 5.1 (exact first-window binary classification).** Let $m\ge2$, $T=k+1\ge2m+1$ and $\gcd(m,T)=1$. Fix distinct $A,B$ and any $H\subseteq\{1,\ldots,m\}$. Give INITIAL index $j$ label $B$ exactly when $j\in H$, and label $A$ otherwise, at every INITIAL tail in a specified free value fiber. Then

$$
C_v(H)=
\begin{cases}
0,&H=\varnothing,\\
1,&|H|>0\text{ is even},\\
2,&|H|\text{ is odd and }(m\notin H\text{ or }H=\{m\}),\\
3,&|H|\text{ is odd},\ m\in H,\ |H|\ge3.
\end{cases}
\tag{5.1}
$$

**Proof: literal upper bounds.** For an even set $E\subseteq\{1,\ldots,m\}$, write the root-zero representative supplied by consecutive-edge inversion as

$$
R(E)_i=\bigoplus_{j=0}^{i}\mathbf1_E(j),\qquad 0\le i<m,
\qquad L=1\,0^{m-1}.
\tag{5.2}
$$

Here $0\notin E$. Reading the two endpoints of every selected literal edge shows that the root mask is exactly $E$: at $1\le j<m$ its coefficient is $R(E)_{j-1}\oplus R(E)_j$, at $m$ it is $R(E)_{m-1}=\mathbf1_E(m)$, and at zero it is zero. This applies the supplied path inversion to an actual word; no abstract span is substituted for a block. Every representative starts zero and is internally legal since $m<k$.

For nonempty even $H$, emit $R(H)$ and return $B$ on difference one, $A$ on zero. For odd $H$ with $m\notin H$, emit $R(H\cup\{m\})$. Difference zero returns $A$. Its positive child consists of $H\cup\{m\}$, where $H$ has label $B$ and $m$ has label $A$. Emit the whole block $L$ next. Its edge at absolute position $m$ has mask $\{m,m+1\}$, restricting to $\{m\}$ in this child. Return $A$ on one and $B$ on zero.

For $H=\{m\}$, emit $0^{m-1}1$. Its positive child is $\{m-1,m\}$, and its zero child is all $A$. On the positive child emit $L$; return $B$ on one and $A$ on zero. In both two-block constructions the root terminal run is at most $m-1$, so the single leading one of $L$ joins a run of length at most $m<k$. Its remaining $m-1$ zeros are actually emitted.

For the remaining odd case let $K=H\setminus\{m\}$. This is a nonempty even set. First emit $R(K)$; difference one returns $B$. The representative ends zero, because $m\notin K$. On difference zero emit the whole $1^m$. From actual tail zero this is legal and has mask $\{m,2m\}$. Difference zero returns $A$, since the only remaining $B$ index is $m$. Its positive child is exactly $\{m,2m\}$, labelled $B,A$ respectively. Emit $L$ in block three, whose mask is $\{2m,2m+1\pmod T\}$. On this child it selects only $2m$, including the endpoint case $T=2m+1$, when the other endpoint is zero. Return $A$ on one and $B$ on zero.

The second block leaves tail $m$; the third leading one joins exactly $m+1$ ones. The hypotheses give

$$
m+1<2m\le k
$$

because $m\ge2$, so this seam is safe. If $T=2m+1$, the wrap at the third edge has no effect on its stated positive child. The full words in this proof all have length $m$; no subsequent tail clearing is required after a stop.

**Proof: all-adaptive lower bounds.** Root zero is necessary by §2. A root $m$-bit word starting zero has mask supported on $\{1,\ldots,m\}$, excludes zero, and has even cardinality: it is the XOR of the actual edges at positions $1,\ldots,m-1$ along that path. A nonconstant binary target can stop after it only if its mask equals $H$, since index zero remains in the $A$ child. Thus every odd $H$ needs at least two blocks; a nonempty target needs at least one. Together with the upper bounds this settles the first three cases of (5.1).

For the last case, consider any proposed successful tree of depth at most two. Its root starts zero; denote its mask by $E$. This is any allowable root mask, not one chosen by the upper-bound protocol. Restrict attention to the actual tail-zero histories $W(v,j,0)$. After the root, all these sources have its common literal terminal tail. Throughout block two, every interior index $1\le j<m$ is silent: its first activity $j-1,j$ was in block one and its next activity is at $T+j-1\ge2m+1$. Index zero is also silent, because its next activity $T-1\ge2m$ lies after block two's last position $2m-1$. Within either root child these silent sources have a common current value and tail. Every second block therefore gives them the same endpoint output or the same absorbing rejection.

Every $B$ interior belongs to $K=H\setminus\{m\}$ and must lie in $E$: otherwise it remains indistinguishable from the $A$ source at index zero on the zero child. Since $K$ is nonempty, the positive child contains a $B$ interior. No $A$ interior can belong to $E$, since it would share that positive child's silent second-block archive with the $B$ interior. Hence

$$
E\cap\{1,\ldots,m-1\}=K.
$$

The root mask has even size and $K$ is even, so $m\notin E$, forcing $E=K$. In particular the zero child contains index zero and the entire next window $\{m,m+1,\ldots,2m\}$; its only $B$ index is $m$.

Every literal second-block mask is supported on that next window and has even cardinality. Its edges run from absolute position $m$ through $2m-1$, and $2m<T$, so there is no wrap or accessible earlier filler. Index zero is outside the mask and receives difference zero if the block succeeds. Therefore every surviving $A$ candidate must also receive difference zero, while $m$ must receive one: the required mask on the fully present next window is the odd singleton $\{m\}$. The complementary orientation fails because it would put some $A$ candidates on the same endpoint as $m$, while zero fixes the other orientation. An even literal mask cannot realize this singleton. If the second block rejects, the common actual tail makes rejection uniform and again cannot finish. This contradiction excludes every depth-two adaptive tree, including every action in the larger alphabet. The three-block construction attains the lower bound. $\square$

At $T=7,m=3,H=\{1,2,3\}$ the exact cost is three. The literal protocol is $010$: difference one returns $B$; otherwise emit $111$: difference zero returns $A$; otherwise emit $100$, returning $A$ on one and $B$ on zero. On its longest branch the terminal seam joins four ones, below $k=6$. This is a nonwrapping witness for the last case, with every leaf accounted for.

## 6. Proper-narrow nonzero singleton targets

**Theorem 6.1 (exact nonzero singleton fee).** Let $k\ge2$, $2\le m<k$ and $\gcd(m,k+1)=1$. Fix $1\le j\le k$ and distinct labels $A,B$. In a specified free value fiber give INITIAL index $j$ label $B$ and every other index label $A$, independently of INITIAL tail. Then

$$
C_v(j)=\max\{2,\lceil j/m\rceil\}.
\tag{6.1}
$$

For $m=2$ this is already implied by Theorem 4.1. The wider-block content is the following literal helper construction and its actual seam.

**Proof.** If $j<m$, first emit $0^j1^{m-j}$, whose mask is $\{j,m\}$. Difference zero returns $A$. On the positive child emit the whole $L=1\,0^{m-1}$ at the next block boundary. Its mask is $\{m,m+1\}$, selecting only $m$ within the actual child $\{j,m\}$. Return $A$ on one and $B$ on zero. The root begins zero and leaves tail $m-j$; the repair joins $m-j+1\le m<k$ ones.

If $j=m$, first emit $0^{m-1}1$, with mask $\{m-1,m\}$. Difference zero returns $A$; on one emit $L$, returning $B$ on one and $A$ on zero. The actual seam joins two ones, which is safe because $m\ge2$ and $m<k$ imply $k\ge3$.

If $j>m$, write

$$
d=\lceil j/m\rceil\ge2,\qquad a=(d-1)m,\qquad r=j-a\in\{1,\ldots,m\}.
$$

Emit $d-2$ whole zero blocks, then the whole penultimate pulse $0^{m-1}1$. This pulse lies at absolute position $a-1$ and has mask $\{a-1,a\}$. Both are $A$ indices: $a<j\le k$. Difference one therefore returns $A$ immediately. On difference zero, both candidates have been excluded on this actual path, in particular the boundary helper $a$ is unavailable as a source. Emit the final literal block

$$
1^r0^{m-r}.
\tag{6.2}
$$

Its selected consecutive edges telescope to $\{a,a+r\}=\{a,j\}$. Since $a$ has actually been excluded, its restricted mask is the desired singleton $j$. Return $B$ on one and $A$ on zero. All waiting is paid: the long branch uses $(d-2)+1+1=d$ blocks. If $d=2$, the wait is empty and the penultimate pulse itself starts with zero and clears every INITIAL tail; for $d>2$ the first zero block does so.

The penultimate terminal tail is one. If $m\le k-2$, (6.2) joins a run of at most $1+r\le m+1\le k-1$. If $m=k-1$ and $j>m$, necessarily $j=k$, $d=2$ and $r=1$, so the seam joins two ones and $2<k$. These are all parameter cases. The final padding consists of precisely $m-r$ emitted zeros; when $r=m$ there is no padding and the safe all-one final block simply ends the experiment. No additional free or paid cleanup is implicit.

For every adaptive protocol, root zero is necessary. The actual tail-zero pair at indices zero and $j$ remains indistinguishable before block $\lceil j/m\rceil$, proving that lower bound by §2. One block cannot suffice either: its root-zero mask is even, avoids index zero, and is supported on $\{1,\ldots,m\}$, whereas separating this singleton target in the orientation fixed by index zero requires the odd singleton $\{j\}$. Uniform rejection cannot help. The upper bounds meet both lower bounds, proving (6.1). $\square$

The index-zero singleton is outside this statement. Unit-width singletons are already part of Theorem 3.1. Width $m=k$ is supplied critical overlap [S5], and no case with $k=2$, $2\le m<k$ exists.

## 7. Two precise failures of scope transfer

**Counterexample 7.1 (wrap makes an excluded filler accessible earlier).** Take $k=4,T=5,m=3$ and $H=\{1,2,3\}$, with label $B$ on $H$ and $A$ elsewhere. This violates $T\ge2m+1$. Emit $010$, with root mask $\{1,2\}$. Difference one returns $B$. On zero the surviving INITIAL indices are $\{0,3,4\}$; emit $111$. Its actual mask is

$$
\{3,6\}\pmod5=\{3,1\}.
$$

Index one has already been excluded on this branch, so the restricted query selects only index three. Return $B$ on one and $A$ on zero. The first block ends zero; the second run has length three below $k=4$. Thus the protocol costs two and is safe for every INITIAL tail. A one-block solution is impossible because the root mask is even, excludes zero, and would have to equal the odd set $H$; hence two is exact.

This refutes dropping the nonwrapping width hypothesis from Theorem 5.1. It does not reverse that theorem or a supplied theorem: its own pair $T=5,m=3$ is outside the stated hypothesis, whereas $T=7,m=3,H=\{1,2,3\}$ in §5 has exact fee three.

**Counterexample 7.2 (unit signatures disappear at block endpoints).** Take $k=6,m=2,T=7$. The grouped literal continuation

$$
01\mid11\mid10
\tag{7.1}
$$

has identical endpoint archives for the actual sources $W_0=0^{14}$ and $W_3=0^4$. They have the same value zero and actual INITIAL tail zero, but length phases respectively $0$ and $4=-3\pmod7$, hence INITIAL indices zero and three. Each initial history and each continuation in (7.1) is a sequence of complete two-bit blocks, and the longest continuation run is four, below $k=6$.

For $W_0$, the selected continuation positions $1,2,3,4$ are all inactive. For $W_3$, only positions two and three are active, and both lie in the middle complete block $11$, canceling in its endpoint difference. Both archives, including the free initial output, are therefore

$$
(y_0,y_1,y_2,y_3)=(0,0,0,0).
$$

A binary target with $B$ at INITIAL indices $3,5$ and $A$ elsewhere assigns these two actual sources different labels. Thus the particular grouped protocol cannot acquire that target. This is a failure of protocol transfer, not target unattainability or a numerical optimum assertion. A wider query must establish actual complete-block separation using the current exclusions, paid position and literal terminal tail; retaining the hidden unit signatures is not legal.

## 8. Finite exact checks and their limits

**Data 8.1 (actual integer-history protocol execution).** Literal protocol execution was checked on both initial values, every INITIAL phase and every INITIAL tail for each target in the following finite scopes. For each record, a complete history $W(v,j,s)$ was constructed, and its legality, integer-recurrence value, length phase and actual tail were checked together. Continuations were then executed bit by bit with integer $G_i$ weights and forbidden-run detection; only complete-block endpoint values were passed to the controller. Each leaf was compared to its preserved INITIAL label. The check required the observed maximum branch length to equal the stated fee, not merely to lie below it.

| Family | Exact finite input scope | Target patterns | Actual-history executions | Emitted complete blocks |
| --- | --- | ---: | ---: | ---: |
| Unit-width labels | $k=2,3,4,5,6$; all set partitions of $k+1$ phases | 1,152 | 88,348 | 484,332 |
| Width-two binary labels | $T=5,7,9$; all subsets $D\subseteq\{1,\ldots,T-1\}$ | 336 | 42,880 | 117,348 |
| First-window binary labels | $(T,m)=(5,2),(7,3),(8,3),(9,4),(10,3),(11,5),(12,5),(13,5)$; every $H\subseteq\{1,\ldots,m\}$ | 140 | 30,944 | 38,040 |
| Nonzero singletons | Every $3\le k\le12$, $2\le m<k$, $\gcd(m,k+1)=1$, $1\le j\le k$ | 318 | 72,600 | 123,728 |
| Wrapped first-window counterexample | $T=5,m=3,H=\{1,2,3\}$ | 1 | 40 | 64 |

The table contains 234,812 executions and 763,512 actually emitted blocks, using 7,204 distinct parameterized joint-source records across 39 distinct $(k,m)$ pairs. There were no wrong INITIAL leaves, unexpected rejections, unsafe seams or fee mismatches. Constants, the $k=2$ two/three/four-block distinctions, odd/even first-window sets, boundary repairs, remote singleton waits, and the $m=k-1,r=1$ corner are included. Arbitrary names of labels are represented by their equality partitions; the protocols use no other structure on those labels. A separate integer-history execution of the two explicit histories in Counterexample 7.2 returned the stated identical archives.

For each of the 39 parameter pairs, a rejected complete-block history was constructed using a sufficient number of locally legal $1^m$ blocks. Its output was checked to be the independent symbol $\bot$, and absorption was checked under all $2^m$ literal next blocks: 5,710 action checks in total. Two assigned INITIAL bottom labels per pair gave 78 depth-zero stopping checks. These checks distinguish the rejected prior from either value fiber; constants in the legal fibers are included in the table and stop at zero fee.

**Data 8.2 (separate unrestricted adaptive-tree check).** A second computation enumerated the actual complete-block transitions and all endpoint branches, retaining INITIAL labels paired with current records after destructive updates. It allowed every literal action, including constant-output displacement actions and actions causing rejection. It imposed no root-zero or proposed-protocol restriction. A node could stop exactly when its INITIAL labels were constant; candidates merged into one current record with different INITIAL labels were rejected as unsolvable. The two alphabets were compared as actual action sets, which coincide at every tested $m<k$. Both initial values and both alphabet choices were evaluated.

| Tree-check family | Exhaustively compared targets | Value/alphabet cases | Budget feasibility checks |
| --- | ---: | ---: | ---: |
| Every unit-width partition in Data 8.1 | 1,152 | 4,608 | 29,308 |
| Every width-two binary pattern in Data 8.1 | 336 | 1,344 | 5,916 |
| Every first-window pattern in Data 8.1 | 140 | 560 | 1,476 |
| Singletons at $(k,m)=(4,2),(4,3),(6,2),(6,3),(7,3)$, all $1\le j\le k$ | 27 | 108 | 336 |
| Counterexample 7.1 | 1 | 4 | 12 |

Each case tested every budget from zero through its claimed optimum. Every smaller budget was infeasible, and the claimed budget admitted a successful tree. In total, 6,624 value/alphabet cases and 37,048 budget checks agreed with the formulas. In particular this independently tests the three-block obstruction at $T=7,m=3,H=\{1,2,3\}$ and the two-block wrapped falsifier.

The combined finite execution and tree-check program exited with code zero. Source retrieval and interface extraction also exited with code zero; all six pinned repository texts cited below and all four primary papers were retrieved with HTTP 200. The pinned repository texts matched their supplied SHA256 seals. The PDF's prose definitions 11–15 and 18 were readable; PDF mathematical-symbol extraction was not used to prove a cost law. No test program or execution log is part of this volume. The larger singleton pairs received protocol checks, not exhaustive optimal-tree claims. Finite results are regression evidence; the universal fees depend on the ordinary proofs in §§3–6, and no Lean/kernel result is claimed.

## 9. Pinned reuse and primary literature interfaces

**Sources 9.1 (repository interfaces and overlap).** The following sources are fixed to immutable commits. Their statements remain the supplied definitions and results; this volume adds target-specific fees, literal optimal protocols and lower bounds.

| Pinned source | Reused interface and scope limit |
| --- | --- |
| [S1: Irreversible Target Acquisition](https://github.com/the-omega-institute/trureturing/blob/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md) | §§1–2 fix complete histories, INITIAL labels, actual fee and the two-alphabet equivalence; Lemmas 4.2–4.3 and Theorem 5.2 give first-zero acquisition semantics. Its existence bounds do not determine the four fees here. |
| [S2: Minimal Modular Observer](https://github.com/the-omega-institute/trureturing/blob/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md) | §§13–14 give the original matched weights and exact period $k+1$. Autonomous state counts and future windows are different resources from emitted blocks. |
| [S3: Self-Calibrating Boundaries](https://github.com/the-omega-institute/trureturing/blob/84aeabc092530002a1a9f17079c15a8c803e38cd/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md) | Lemma 15.1 supplies simultaneous actual value/phase/tail witnesses and independent reachable rejection. Its arbitrary-length joint prior does not supply a hidden length clock. |
| [S4: Narrow Query Window Cost](https://github.com/the-omega-institute/trureturing/blob/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md) | §§1–3 supply joint histories, actual transitions, consecutive path masks and forced root zero. The $g\ge2$ singleton scans, first-window $n\ge3$ lower bound, guarded waiting and five-label seam families do not settle these $g=1$ binary fees. The short-path inversion is reused background, not a separate contribution. |
| [S5: Critical Width Target Cost](https://github.com/the-omega-institute/trureturing/blob/0e51d0ec80c86e888fcdde78982665a7c5c17c79/docs/develop/theory/KBONACCI_CRITICAL_WIDTH_TARGET_COST.md) | Theorem 2.2 supplies cyclic-edge inversion; Theorem 5.1 settles $m=k$ phase labels. Those critical-width fees are overlap outside the proper-narrow statements, including $k=m=2$. |
| [S6: Target Acquisition Cost](https://github.com/the-omega-institute/trureturing/blob/3fa4d2325f1e8bcf3f4f9813f83fdf4c1156fdd0/docs/develop/theory/KBONACCI_TARGET_ACQUISITION_COST.md) | Theorem 3.1 supplies wide-block exact costs under its stated query-space condition. That condition is unavailable at the widths proved here; the general all-width question remains its own objective. |

The new deductions relative to these inspected suppliers are the exact unit-width small exceptions, width-two scan/repair completion, first-window binary boundary obstruction, and wider-block paid-helper singleton protocol. Generic adaptive trees, parity incidence, source saturation and source-encoding shortest-word results are reused interfaces, not new delivered frameworks. These are `repo-derived` ordinary cost results. Inspection of these sources is not an exhaustive absence or mathematical priority claim.

**Sources 9.2 (original papers and migration limits).** A whole block is one action of a finite deterministic input/output machine, with its endpoint as the response and INITIAL labels attached to sources. This supplies a direct testing-tree interpretation. It does not import another machine's action availability, free transfers or optimum.

| Primary source | Checked interface and precise limit |
| --- | --- |
| Petra van den Bos and Frits Vaandrager, [State Identification for Labeled Transition Systems with Inputs and Outputs, arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), adaptive distinguishing graphs, Definition 11 and Figure 3 | `literature-attested`: adaptive state-identification tests and a root-action obstruction caused by irreversible state merging. Figure 3 explicitly merges states 1,2 after input $a$ and states 2,3 after $b$. The local retirement and charged-calendar proofs here remain reader-specific. |
| Anastasiya Chistopolskaya and Vladimir V. Podolskii, [Parity Decision Tree Complexity is Greater Than Granularity, arXiv:1810.08668v1](https://arxiv.org/html/1810.08668v1), Introduction and §2.2 | `literature-attested`: queries of arbitrary-subset parity on one fixed unknown Boolean input, with query-count complexity. Encoding a phase as a one-hot vector does not supply arbitrary subset access in a moving literal block window or remove terminal-tail constraints; those minimax numbers are not imported. |
| Michał Szyfelbein and Dariusz Dereniowski, [Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312v1](https://arxiv.org/html/2602.21312v1), §2 and §3.1 | `literature-attested`: static predecessor constraints on tests, including worst-case tree height. A predecessor relation alone does not represent the actual cyclic position, branch exclusions and tail legality of this reader. No cost-preserving reduction is assumed. |
| Uraz Cengiz Türker, Robert M. Hierons, Mohammad Reza Mousavi and Khaled El-Fakih, [Efficient State Identification for Finite State Machine-Based Testing, accepted manuscript](https://eprints.whiterose.ac.uk/id/eprint/230260/1/Ordered_Wset_Accepted.pdf), [DOI 10.1109/TSE.2025.3604472](https://doi.org/10.1109/TSE.2025.3604472), Definitions 11–15 and 18 | `literature-attested`: state-identifying paths, coverage of every state/characterising-word pair, transfer-free identification paths, pairwise shortest-prefix minimality, ordered characterising sets and bounded transfer variants. These methods include paths needing no reset or added transfer; they cannot uniformly be described as reset-dependent. Their specified-start coverage and pairwise minimality differ from the worst actual branch for one unknown INITIAL target label. No equivalence of those optimization contracts is proved here. |

The literature check establishes these interfaces and limits, not originality or a comprehensive negative search result. No external generic algorithm is being reimplemented as a claimed new cost theorem.

## 10. The unchanged all-width objective and the remaining obstruction

**Open problem 10.1 (arbitrary attainable INITIAL-record fees).** For every $k\ge2,m\ge1$ in the fixed original matched reader and full joint actual-history prior, determine the exact minimum worst-case actual emitted-block fee and an optimal protocol for every attainable arbitrary INITIAL-record target $f(v,\theta,s)$. This all-width problem remains open. The supplied wide and critical laws and the four families proved here do not replace its quantifiers.

The unit-width law settles every phase labeling, and the proper coprime width-two law settles every binary phase labeling. The first-window classification and nonzero singleton law give wider-block exact fees, including a precise failure of a two-block strategy when no accessible parity helper exists. For general coprime $m\ge3$, arbitrary binary multi-window patterns and multilabel phase patterns beyond these scopes remain unresolved; so do the index-zero singleton in that general regime and the full mixed INITIAL-tail objective. Cyclic reactivation can change both available fillers and retired distinctions and must be accounted for on the same charged actual path.

The remaining structural task is to coordinate which INITIAL distinctions must be settled before their active positions retire, which excluded phase can supply charge in a later actual window, and which literal word realizes that query with the branch's actual terminal tail. Different branches cannot contribute a common filler unless each has actually excluded it, and a safe tail from one representative cannot be combined with a mask from another. Counterexamples 7.1–7.2 exhibit these two constraints concretely. Any extension needs an actual cost-preserving protocol and an all-adaptive lower bound; a generic belief recursion, an algebraic span, a finite table or a weaker prefix-deadline candidate alone does not close the original objective. No unproved general deadline formula is asserted in this volume, and the root-zero restriction is not extended to mixed-tail targets.

## 追加锚（本行以下为增补区）

## 11. Exact price of requiring every block to start zero

**Definition 11.1 (one fixed table and four block-fee optima).** Let $m\ge2$, $Q\ge2$, $k=Qm$ and $T=Qm+1$. Then $m<k$ and $\gcd(m,T)=1$. Fix $j\in\{1,\ldots,m\}$ and distinct labels $A,B$. On both free initial-value fibers define the single INITIAL table

$$
f_j(v,\theta_\ell,s)=
\begin{cases}
B,&\ell=j,\\
A,&\ell\ne j,
\end{cases}
\qquad
v\in\mathbb F_2,\quad 0\le\ell\le k,\quad 0\le s<k,
\qquad f_j(\bot)=\beta,
\tag{11.1}
$$

where $\theta_\ell=-\ell\pmod T$ and $\beta$ is any prescribed label, possibly equal to $A$ or $B$. This table is fixed independently of the controller and of every INITIAL tail. Its argument is the original record, not the record after a paid continuation.

Use the complete-history prior, literal actions, endpoint archive and unit charge of §§1–2. Write $C_{\rm ad}$ for the minimum worst fee over all successful adaptive controllers. Write $C_{\rm pre}$ for the minimum with the additional GLOBAL requirement: every actual emitted sequence is a prefix of one fixed literal block stream, common to all sources and both free values; stopping and label decoding may use the actual endpoint archive. Write $C_{0\rm ad}$ and $C_{0\rm pre}$ for the corresponding minima when **every issued block**, at every depth and on every branch, must begin with zero. All four costs below have the same target $f_j$ and the same original source prior. They count every emitted complete block, including all-zero waits and padding, and permit the initial $\bot$ branch to return $\beta$ for free. No bound on controller memory is imposed.

**Theorem 11.2 (exact whole-policy restriction price).** For Definition 11.1, separately in each of the two original alphabets,

$$
C_{\rm ad}(f_j)=C_{\rm pre}(f_j)=2,
\qquad
C_{0\rm ad}(f_j)=C_{0\rm pre}(f_j)=Q+1.
\tag{11.2}
$$

These equalities also hold separately on each free value fiber. The unrestricted value two reuses Theorem 6.1 and its first-window literal protocol. The additional content is the exact price of restricting the entire policy, including a lower bound for every restricted adaptive controller and a single GLOBAL stream attaining it on this same table.

**Proof.** Every source record used here has the actual joint witness $W(v,\ell,s)$ of §1: choose one $N\equiv0\pmod m$, $N\equiv-\ell\pmod T$, $N\ge s+2$, put $D=\bigoplus_{i=N-s}^{N-1}c_i$, and use the one history $(v\oplus D)0^{N-s-1}1^s$. Coprimality gives such an $N$. Its value, length phase and terminal tail are jointly the specified ones; the history is legal and cuts into locally legal complete blocks. This supplies every phase at both values and every tail, including the tail-zero pairs below. Initial lengths may differ and are never revealed. Since $m<k$, every length-$m$ word is internally legal, so the two action alphabets coincide for these parameters; all seams must still obey the original forbidden-run rule.

For the unrestricted costs, all hypotheses of Theorem 6.1 hold and $\lceil j/m\rceil=1$, giving the inherited adaptive optimum two. To make its common-stream realization explicit, put

$$
r=\min\{j,m-1\},\qquad
R_r=0^r1^{m-r},\qquad L=1\,0^{m-1}.
\tag{11.3}
$$

Emit $R_r\mid L$ on every legal source. These are the first-window words of Theorem 6.1, with its early $A$ leaves allowed to receive the same second block as the other leaves. Their full INITIAL masks are $\{r,m\}$ and $\{m,m+1\}$. If $j<m$, return $B$ exactly on difference pair $(1,0)$; if $j=m$, return $B$ exactly on $(1,1)$; return $A$ otherwise. The root starts zero, clearing every old tail, and leaves tail $m-r$. The second block joins only $m-r+1\le m<k$ ones and ends with its $m-1$ actual zeros. Both complete endpoint differences are obtained from the free initial value and the two actual endpoint values. Thus the very same two-block stream works on both free values and all tails. The inherited lower bound and $C_{\rm ad}\le C_{\rm pre}\le2$ give the first equality in (11.2); no new unrestricted singleton law is asserted.

Now fix either free value $v$ and any proposed correct restricted adaptive controller. It cannot stop at the root because (11.1) is nonconstant on this fiber. Let its arbitrary first block be $x_0\cdots x_{m-1}$, with $x_0=0$. For the root-mask calculation only, set $x_m=0$. Its difference-one set $E$ is supported on $\{1,\ldots,m\}$, with

$$
\mathbf1_E(\ell)=x_{\ell-1}\oplus x_\ell
\quad(1\le\ell\le m),
\qquad
\bigoplus_{\ell=1}^m\mathbf1_E(\ell)=x_0\oplus x_m=0.
\tag{11.4}
$$

Thus $E$ has even cardinality and excludes phase index zero. If $j\notin E$, choose $h=0$. If $j\in E$, evenness supplies some $h\in E\setminus\{j\}$. In both cases $h\in\{0,\ldots,m\}\setminus\{j\}$ and the actual sources $W(v,j,0)$ and $W(v,h,0)$ have different INITIAL labels but the same first endpoint difference. They also share the free initial value. The root zero makes their current literal tails equal, so they have one common archive after block one.

Their remaining possible activity before the end of block $Q$ can be listed completely. For any index $1\le\ell<m$, the first active positions $\ell-1,\ell$ have both passed within block one; its next active position is $T+\ell-1=k+\ell>k-1$. Index $m$ has one remaining first-period active position at $m$, but that is exactly the first bit of block two and must be zero. Its next activity is later than $k-1$. Index zero had its position zero suppressed at the root and next becomes active at $k$, just after the first $Q$ blocks. Consequently, for every possible restricted sequence, each index in $\{0,\ldots,m\}$ contributes zero throughout continuation positions $m,\ldots,k-1$.

Along the pair's common archive the adaptive controller issues the same next word on both sources. Each such word starts zero, so it clears their common incoming tail and has no run longer than $m-1<k$; neither source rejects. The listed inactivity makes their next endpoint differences both zero, and their terminal tails remain equal. Induction therefore keeps their entire actual archives equal through all $Q$ paid blocks. Stopping on this archive at any earlier or equal depth would give the same leaf to their different INITIAL labels. Every correct restricted controller must have worst fee at least $Q+1$. The partner $h$ can depend on the controller's root word; the fixed table (11.1) does not. This proves the universal adaptive lower bound on each fiber, rather than merely excluding the unrestricted protocol.

For the matching GLOBAL upper bound, retain $r$ and $R_r$ from (11.3) and define the complete words

$$
Z=0^m,\qquad F_r=0\,1^r0^{m-r-1}.
\tag{11.5}
$$

Use the one stream

$$
R_r\ \mid\
\underbrace{Z\mid\cdots\mid Z}_{Q-1\text{ paid blocks}}
\ \mid\ F_r.
\tag{11.6}
$$

Here $1\le r\le m-1$, so every exponent is nonnegative and each displayed word has exactly $m$ bits. Zero exponents denote empty substrings, not omitted endpoints. Every block starts zero. The root mask is $\{r,m\}$, all waiting differences are zero, and the last block starts at paid position $Qm=k=T-1$. Its ones occupy precisely the actual positions $k+1,\ldots,k+r$. Their literal edges telescope modulo $T$ to

$$
\bigtriangleup_{a=1}^{r}\{k+a,k+a+1\}\pmod T
=\{k+1,k+r+1\}\pmod T
=\{0,r\}.
\tag{11.7}
$$

Write $a$ for the root difference and $b$ for the final difference. The entire endpoint record on a legal source is

$$
y_0=v,\qquad
 y_1=y_2=\cdots=y_Q=v\oplus a,\qquad
 y_{Q+1}=v\oplus a\oplus b.
\tag{11.8}
$$

The full signatures, including all $Q-1$ intervening zero differences, are determined by

$$
\begin{array}{c|cc}
\text{INITIAL index }\ell&a&b\\ \hline
0&0&1\\
r&1&1\\
m&1&0\\
\ell\notin\{0,r,m\}&0&0.
\end{array}
\tag{11.9}
$$

The three distinguished indices are distinct. When $j<m$, $r=j$ and the INITIAL $B$ label is exactly signature $(1,1)$. When $j=m$, $r=m-1$ and that label is exactly $(1,0)$. These rules assign $A$ to every other source, including every phase outside the first window; no current-phase label is substituted for the INITIAL one. All entries and both differences come from this same actual stream on each source. The rule uses $v$ only to recover differences, so (11.6) is common to both free values.

The first zero clears any prescribed old tail, including $k-1$. The root's terminal run is $m-r\le m-1$; the next block starts zero. Every waiting block has actual terminal tail zero. The last block again starts zero and has a run of $r\le m-1<k$ ones. It ends with tail zero if $r<m-1$, and with tail $m-1$ if $r=m-1$; this latter endpoint is legal and needs no cleanup. Thus every legal source, at every INITIAL tail, survives all complete blocks. Every bit of the final padding is emitted. The total charge is exactly $1+(Q-1)+1=Q+1$ on the legal branches of this fixed-length protocol. The initially rejected sources instead return their freely decoded $\beta$ before any block, using the empty prefix of the same GLOBAL stream. There is no reset, intermediate observation, free displacement or branch combination. Together with the adaptive lower bound and $C_{0\rm ad}\le C_{0\rm pre}$, this proves the remaining equalities in (11.2).

On each one of these fixed tables the additive and multiplicative losses are therefore

$$
\begin{aligned}
C_{0\rm ad}-C_{\rm ad}
&=C_{0\rm pre}-C_{\rm pre}=Q-1,\\
\frac{C_{0\rm ad}}{C_{\rm ad}}
&=\frac{C_{0\rm pre}}{C_{\rm pre}}=\frac{Q+1}{2}.
\end{aligned}
\tag{11.10}
$$

For fixed $m\ge2$ and fixed $j\in\{1,\ldots,m\}$, letting $Q$ increase makes both losses unbounded. Each comparison keeps one original reader and one immutable table on the two sides; varying $Q$ varies the reader only between comparisons. In particular, the original two-block upper bound and the all-restricted-policy lower bound at least three apply to the same table for every $Q\ge2$. $\square$

The exact restricted optimum and same-table losses are repo-derived ordinary mathematics. The actual-record, literal-mask, first-zero and source-realization interfaces are reused from §§1–2 and the pinned suppliers of §9.1; Theorem 6.1 owns the unrestricted singleton fee. The state-identification and parity-query interfaces cited in §9.2 supply terminology and comparison boundaries, not a transferred optimum: arbitrary subset queries do not supply the paid cyclic positions or the actual words in (11.6). This result concerns $k=Qm$, $Q\ge2$, $m\ge2$ and only the first-window singleton indices $1\le j\le m$, with the same phase table on all INITIAL tails and both free values. It does not settle arbitrary phase layouts, mixed-tail tables or Open Problem 10.1, and it makes no worldwide novelty or exhaustive-absence claim.

## 追加锚（本行以下为增补区）

## 12. The phase-zero singleton on every proper coprime width

**Definition 12.1 (the immutable phase-zero table).** Retain the original matched reader, complete actual-history prior, independent absorbing bottom, alphabets and paid endpoint observations of §§1–2. Suppose

$$
k\ge2,\qquad 2\le m<k,\qquad T=k+1,\qquad \gcd(m,T)=1.
\tag{12.1}
$$

For distinct labels $A,B$ and any prescribed label $\beta$, fix the one INITIAL table

$$
f_0(v,\theta_j,s)=
\begin{cases}
B,&j=0,\\
A,&1\le j\le k,
\end{cases}
\qquad
v\in\mathbb F_2,\quad 0\le s<k,\qquad
f_0(\bot)=\beta.
\tag{12.2}
$$

Here $\theta_j=-j\pmod T$ is the original history's phase. The table is the same on both free values and every INITIAL tail; $\beta$ need not differ from either legal label. Let $C_{\rm ad}(f_0)$ be the minimum worst actual emitted-complete-block fee over all successful adaptive controllers. Let $C_{\rm pre}(f_0)$ impose the additional requirement that every emitted sequence be a prefix of one fixed literal block stream, common to both free values and every actual source. Stopping and decoding may depend on the source's own chronological endpoint archive, including its free initial value. These are the unrestricted adaptive and GLOBAL meanings of Definition 11.1, applied to (12.2). Every issued block, including every wait and every padding bit in its complete word, is charged. Initial bottom can stop freely with $\beta$.

**Theorem 12.2 (closed phase-zero fee and common literal attainment).** For Definition 12.1, separately for both original alphabets,

$$
\boxed{\displaystyle
C_{\rm ad}(f_0)=C_{\rm pre}(f_0)=\left\lceil\frac{k}{m}\right\rceil.}
\tag{12.3}
$$

The same minimum holds on each free-value fibre separately. A single stream attaining it is specified below using only $k,m$, with a decoder using only complete endpoints. Its legality includes all actual INITIAL tails and all cross-block seams. The adaptive lower bound includes arbitrary literal actions, rejecting words, waits and early stopping.

**Proof (actual sources and the all-adaptive lower bound).** Put

$$
d=\left\lceil\frac{k}{m}\right\rceil\ge2,\qquad
a=(d-1)m,\qquad r=k-a\in\{1,\ldots,m\}.
\tag{12.4}
$$

Every original record used in the proof is jointly attainable by the history $W(v,j,s)$ in §1. In particular, for each specified $v,j,s$, that one legal complete-block history realizes its value, length phase and tail together. Its witnessing length is not revealed to the controller. Since $m<k$, every literal $m$-bit word is internally legal, so the two original action alphabets coincide; their common cross-block forbidden-run rule still applies.

Fix either free initial value $v$ and any correct adaptive controller. Its root cannot stop, since the actual records at indices zero and $k$ have unequal labels $B,A$. Its first literal bit must be zero: otherwise the actual sources $W(v,0,k-1)$ and $W(v,k,k-1)$ both reject immediately. They then have the same completed root output $\bot$, the same remembered free value and the same issued word. Absorption makes every future endpoint archive identical. Neither early stopping nor any further words can return their different immutable INITIAL labels. This is the forced-root-zero interface of §2 applied to (12.2), including the possibility of a rejecting root in the larger alphabet.

Now use the actual tail-zero pair $W(v,0,0)$ and $W(v,k,0)$. Index zero's active continuation positions begin with $0,k,k+1$, and index $k$ first becomes active at $k-1,k$. The forced root zero suppresses position zero. For any integer $b<d$,

$$
bm\le(d-1)m<k,\qquad bm-1\le k-2.
\tag{12.5}
$$

Thus, throughout the first $b$ whole blocks, every emitted one has coefficient zero at both sources. They have the same initial value and tail; along equal archives the adaptive controller issues the same next whole word. Their current tails remain equal bit by bit. Every successful endpoint therefore has the same value at both sources, and any forbidden run rejects both simultaneously. A common rejection remains absorbing and cannot distinguish their labels. Induction keeps the entire available chronological archives equal through every depth below $d$. Stopping there returns the same label on two differently labelled actual sources. No correct controller can have worst fee below $d$. This is precisely the paid-arrival argument of §2 with $J=k$; it does not assume a predetermined continuation or give free displacement. It proves $C_{\rm ad}(f_0)\ge d$ on each value fibre, and hence on their union. The initial-bottom label plays no role in this legal-source obstruction.

**Proof (the nondivisible case and its chronological decoder).** Suppose $m\nmid k$, so $1\le r<m$. The coprime hypothesis excludes $r=m-1$: that equality would give $T=k+1=dm$ and hence $\gcd(m,T)=m>1$. Consequently

$$
m\ge3,\qquad 1\le r\le m-2.
\tag{12.6}
$$

Define the complete literal words

$$
Z=0^m,\qquad P=0^{m-1}1,\qquad
F=1^{r+1}0^{m-r-1},
\tag{12.7}
$$

and issue the one stream

$$
\underbrace{Z\mid\cdots\mid Z}_{d-2\text{ whole blocks}}
\ \mid\ P\ \mid\ F.
\tag{12.8}
$$

When $d=2$ the displayed waiting part is empty and $P$ is the root. All three words in (12.7) have length exactly $m$. The final zeros have positive length by (12.6), and are actually emitted before observing its endpoint. The charge is $(d-2)+1+1=d$, including every uninformative waiting block.

Each $Z$ has empty mask. The sole one of $P$ is at absolute continuation position $a-1$, giving the full INITIAL mask $\{a-1,a\}$. The ones of $F$ occupy the actual consecutive positions $a,a+1,\ldots,k$. Their same-block edge XOR is

$$
\mathop{\triangle}_{t=a}^{k}\{t,t+1\}\pmod T
=\{a,k+1\}\pmod T
=\{a,0\}.
\tag{12.9}
$$

Its trailing zeros add no charge. This computation uses precisely the actual final block, including its wrap at position $k$, rather than observations of its constituent bits. The indices $0,a-1,a$ are distinct, with $1\le a-1<a\le k-1$.

Let $y_b$ denote the actual successful endpoint after $b$ emitted blocks, with $y_0=v$, and retain

$$
p=y_{d-1}\oplus y_{d-2},\qquad
q=y_d\oplus y_{d-1}.
\tag{12.10}
$$

Every earlier endpoint equals $v$. Equations (12.7)–(12.9) give the full two final differences on each original phase:

$$
\begin{array}{c|cc}
\text{INITIAL index }j&p&q\\ \hline
0&0&1\\
a-1&1&0\\
a&1&1\\
j\notin\{0,a-1,a\}&0&0.
\end{array}
\tag{12.11}
$$

Return $B$ exactly when $(p,q)=(0,1)$, and $A$ otherwise. Equivalently, after the actually recorded penultimate difference zero, the helper $a$ has been excluded on that same archive, and the final mask restricts to the singleton zero. On penultimate difference one both candidates already have label $A$. The fixed stream may nevertheless issue $F$ there too; (12.11) decodes these sources correctly. All entries come from the one stream on each source; no observation or exclusion is borrowed from another branch. Only the free value and complete endpoints are used, so the rule is identical on both free-value fibres.

The use of the chronological archive in (12.10) is essential for this stream. At indices zero and $a-1$, the final scalar is the same $v\oplus1$, while the penultimate scalars are $v$ and $v\oplus1$, respectively. The actual sources $W(v,0,0)$ and $W(v,a-1,0)$ supply the two different INITIAL labels. Thus replacing (12.10) by a decoder of the final scalar alone would be false. For a concrete literal instance, $k=7,m=5$ gives $00001\mid11100$: the actual histories $0^{40}$ and $0^{20}$ have INITIAL indices zero and four, respectively, and their endpoint pairs are $(0,1)$ and $(1,1)$. Both histories have free value zero, tail zero and complete five-bit cuts. This witness concerns the displayed stream's decoder.

It remains to check its actual seams. The first issued bit is zero, whether it belongs to a waiting $Z$ or to $P$, and clears every old tail, including $k-1$. Each waiting block ends zero. The word $P$ has terminal tail one. Its final one and the leading run of $F$ form exactly $r+2$ consecutive ones, and

$$
r+2\le m<k.
\tag{12.12}
$$

The remaining $m-r-1\ge1$ actual zeros of $F$ clear that tail. All earlier runs after the root zero are shorter. This proves legality for every actual source and every INITIAL tail, including $d=2$ and $m=k-1$ without a different seam convention. Both original alphabets admit these internally legal whole words. No post-stop cleanup or extra endpoint is required.

**Proof (divisible widths and complete-mask coverage).** Suppose $m\mid k$. Write $k=dm$, where $d\ge2$, so $r=m$ in (12.4). The stream below has exactly $d$ complete words and length $k$ bits. Since it starts zero, phase zero's position zero is suppressed and its next active position $k$ is not emitted. Its entire difference signature is therefore zero.

If $m$ is even, set

$$
U=(01)^{m/2}
\quad\text{and issue}\quad
\underbrace{U\mid\cdots\mid U}_{d\text{ whole blocks}}.
\tag{12.13}
$$

At block index $t\in\{0,\ldots,d-1\}$, its actual one positions are $tm+1,tm+3,\ldots,(t+1)m-1$. Their disjoint edges give exactly

$$
E_t=\{tm+1,tm+2,\ldots,(t+1)m\}.
\tag{12.14}
$$

These masks are pairwise disjoint and their union is $\{1,\ldots,k\}$. Every nonzero INITIAL index therefore gives a one difference at one of the recorded endpoints. Every word starts zero and ends one, so the root clears every INITIAL tail and no subsequent seam joins two ones. All runs are legal.

If $m$ is odd, then $m\ge3$. Define

$$
R=(01)^{(m-1)/2}0,\qquad
S=(10)^{(m-1)/2}1,
\quad\text{and issue}\quad
R\ \mid\ \underbrace{S\mid\cdots\mid S}_{d-1\text{ whole blocks}}.
\tag{12.15}
$$

The root ones occur at $1,3,\ldots,m-2$, giving

$$
E_0=\{1,\ldots,m-1\}.
\tag{12.16}
$$

For $1\le t<d$, the ones of its one actual word $S$ occur at $tm,tm+2,\ldots,(t+1)m-1$. Their edges are disjoint within that word and give

$$
E_t=\{tm,tm+1,\ldots,(t+1)m\}.
\tag{12.17}
$$

Thus the root covers indices $1,\ldots,m-1$, the next word covers $m,\ldots,2m$, and all later words continue the coverage through $k=dm$. Every $E_t$ excludes zero, and

$$
\bigcup_{t=0}^{d-1}E_t=\{1,\ldots,k\}.
\tag{12.18}
$$

Adjacent $S$ masks overlap at their shared boundary index. Such an index gives difference one at two separate endpoints; those readings are both retained, not XORed into one final observation. There is no cancellation between different chronological coordinates. The root starts and ends zero; each $S$ alternates internally and starts and ends one. The root-to-$S$ seam is safe, and any later $S$-to-$S$ seam forms a run of exactly two ones. Since $k=dm\ge2m\ge6$, these runs are strictly below $k$. The final tail one is legal and requires no further block.

For either parity of $m$, compute the actual differences $\delta_b=y_b\oplus y_{b-1}$ for $1\le b\le d$. Return $B$ precisely when all these differences are zero; otherwise return $A$. Phase zero has that all-zero signature, and (12.14) or (12.18) supplies at least one nonzero chronological coordinate for each other phase. This proves the decoder for every INITIAL phase on both values. The first zero has cleared every old tail, and the seam calculations cover every word actually issued. Exactly $d$ whole blocks are charged. In particular the divisibility case is not obtained by substituting $r=m$ into (12.7), whose padding exponent would be negative.

Finally, on initially rejected histories return their assigned $\beta$ before issuing any word. This is the empty prefix of the same GLOBAL stream. Rejected prior histories actually exist in both alphabets: sufficiently many consecutive $1^m$ complete blocks reach a forbidden cross-block run, even though each such block is internally legal. Their free output is the independent symbol $\bot$, not either legal value. Every legal history instead survives the displayed $d$-word stream and receives its immutable label. Consequently $C_{\rm pre}(f_0)\le d$. Combining this with the all-adaptive lower bound and $C_{\rm ad}\le C_{\rm pre}$ proves (12.3) and the corresponding equalities on each free-value fibre. $\square$

## 13. Source correspondence and the remaining INITIAL objective

**Mathematical citation 13.1 (exact overlap and the closed evaluation).** The actual-history witnesses, forced root zero, charged arrival and actual path masks in Theorem 12.2 are the interfaces of §§1–2 and their pinned suppliers in Sources 9.1. The proof uses the original matched coefficient law and original whole words on their actual joint prior.

For comparison with binary laws normalized to have label $A$ at index zero, exchange the label names: take their baseline $A_{\rm source}=B$, their other label $B_{\rm source}=A$, and hence their nonbaseline set $H=\{1,\ldots,k\}$ and last index $J=k$. This is the same immutable table, not a different target. The exact correspondences are as follows.

- At $m=2$, coprimality makes $k$ even and properness gives $k\ge4$. Theorem 4.1 with that label exchange already gives the adaptive value $\max\{2,k/2\}=k/2$. Its adaptive value is credited reuse. Stream (12.13) additionally exhibits the required one GLOBAL stream on both free values and all INITIAL tails.
- When $m\mid k$, write $k=dm$, $d\ge2$. The [prefix-deadline law, Theorem 3.1](https://github.com/the-omega-institute/trureturing/blob/785db9da5282938375cc4c1b917fcac6ce311af9/docs/develop/theory/KBONACCI_PREFIX_DEADLINE_AND_WRAP_COST.md) already gives the adaptive value $d$. In its notation $h=D=d$, $b_0=m-1$, $b_t=m$ for $1\le t<d$, and $z=1$. If $m$ is even the first count is odd and releases its earlier-window condition; if $m$ is odd and $d\ge3$, count $b_1=m$ releases it. For odd $m$ and $d=2$, the last count is odd and equals $z$ modulo two. In every case its $\varepsilon=0$ and its guardrail includes depth $d$. Equations (12.13)–(12.18) give simultaneous GLOBAL attainment, rather than treating a branch-dependent deadline tree as a common stream.
- In the strip $m<k<2m$, equality $k=2m-1$ is excluded by $\gcd(m,k+1)=1$. Hence $2m>k+1$, $m\ge3$, and the [same source's Theorem 6.1](https://github.com/the-omega-institute/trureturing/blob/785db9da5282938375cc4c1b917fcac6ce311af9/docs/develop/theory/KBONACCI_PREFIX_DEADLINE_AND_WRAP_COST.md) already gives adaptive value two for this table: $H$ contains $k>m$, so its one-block clause does not apply. Formula (12.8) with no waiting blocks gives one common optimal stream here, including the near-critical case.
- On $m\ge3$, $k\ge2m$ and $\gcd(m,k+1)=1$, [Theorem 62.2 of the INITIAL target theory](https://github.com/the-omega-institute/trureturing/blob/785db9da5282938375cc4c1b917fcac6ce311af9/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md) already supplies the exact adaptive structural minimum for arbitrary immutable INITIAL targets. Its table here is $F_v(j,s)=B$ at $j=0$ and $A$ otherwise, for both $v$ and all $s$. Theorem 12.2 evaluates that minimum in closed form as $\min\mathcal C_0=\min\mathcal C_1=\lceil k/m\rceil$. The structural minimum's arbitrary-target adaptive scope is credited in full; it is not an unresolved existence problem. Its independent child choices do not by themselves supply the one GLOBAL stream, which is proved here by the literal constructions.

The phase-zero result is a repo-derived closed evaluation with a single optimal GLOBAL realization across all the stated proper coprime widths. Its width-two, divisible-width and upper-strip adaptive values have the direct source specializations just listed; the remaining guarded adaptive values are evaluations of the supplied structural minimum. The ordinary proof adds the simultaneous literal masks, charged calendar and seams needed for (12.3), without a worldwide priority or exhaustive literature-absence claim. Sources 9.2 retain their original state-identification and parity-query comparison boundaries; no optimum from a machine with different action access or costs is transferred.

Theorem 3.1 of this volume owns the unit-width phase-label law, outside (12.1). Theorem 6.1 owns the nonzero singleton indices and is not restated as a companion result. Critical widths, wider widths and noncoprime phase orbits retain their supplied hypotheses. At $k=2$ no integer $m$ satisfies $2\le m<k$. The full-history and mask arguments here require (12.1); no all-phase coprime source witness is asserted for a noncoprime orbit.

The phase-zero singleton gap described in §10 is resolved on (12.1) by (12.3). The arbitrary attainable INITIAL-record objective of Open Problem 10.1 remains broader: arbitrary tail-dependent tables, arbitrary multilabel layouts, the remaining parameter regions, and exact GLOBAL compatibility for arbitrary targets are not consequences of this singleton law. The arbitrary-target adaptive structural slice of the cited Theorem 62.2 and all other already settled source slices retain their scope. The same-table equality here does not identify $C_{\rm ad}$ with $C_{\rm pre}$ for those broader targets.

## 追加锚（本行以下为增补区）

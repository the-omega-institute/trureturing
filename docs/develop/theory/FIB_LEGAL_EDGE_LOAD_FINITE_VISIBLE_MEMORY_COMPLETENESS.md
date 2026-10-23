# Fibonacci harmonic-edge load: finite visible memory completeness

## 1. The original domain and the completeness statement

**Definition 1.1 (Complete open-path word graphs).** For every integer $n\ge1$, let

$$
B_n=\{b\in\{0,1\}^n:b_jb_{j+1}=0\text{ for }1\le j<n\}.
$$

The graph $\Gamma_n$ has all of $B_n$ as vertices and all legal Hamming-distance-one pairs as edges. There is no constraint between the first and last coordinates. Write $b_0=b_{n+1}=0$ when testing whether an insertion is legal. Thus every all-zero word and every legal word with a $1$ at either endpoint is retained. Set

$$
h(s,t)=
\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
\qquad
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu(b),\mu(c))
\tag{1.1}
$$

for every probability vector $\mu$ on the whole of $B_n$. Zero masses do not change the vertex or edge sets.

**Convention 1.2 (Owned suppliers).** The harmonic duality, attained finite-volume maximum and growth constant are the results of [Growth], Theorems 3.2 and 5.2:

$$
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_{n\to\infty}\frac{\kappa_n}{n}
=\inf_{n\ge1}\frac{\kappa_n}{n},\qquad
c_\star n\le\kappa_n\le c_\star(n+1).
\tag{1.2}
$$

Its Lemma 3.1 supplies continuity, concavity and nonnegative homogeneity of $h$ and hence of $\Phi_n$. The completed [TwoStep], §§2–3, supplies its coherent positive stationary pair law and full-word ratio grouping; its Theorem 4.1 owns the strict bulk separation from the one-activity comparator. These statements retain their source ownership. No numerical certificate from [Growth], §11, is needed.

**Definition 1.3 (Permitted visible laws).** Let

$$
X=\{x\in\{0,1\}^{\mathbb Z}:x_jx_{j+1}=0\text{ for every }j\in\mathbb Z\}.
$$

A permitted law $Q$ is a stationary probability law on $X$ having some finite visible Markov order at most $m\ge1$. This means that, almost surely, its conditional next-bit probabilities given the entire visible past depend only on its last $m$ bits. Every legal $m$-context has positive probability, and every legal extension of every such context has positive conditional probability. Equivalently, all legal finite cylinders are positive and its visible order-$m$ kernel is positive on every legal extension. Denote its length-$n$ cylinders by $Q_n$.

**Theorem 1.4 (Finite visible memory completeness).** For every permitted law $Q$ the limit

$$
d(Q)=\lim_{n\to\infty}\frac{\Phi_n(Q_n)}n
\tag{1.3}
$$

exists. On exactly the graphs of Definition 1.1,

$$
c_\star=\sup_{\substack{m\ge1\text{ finite}\\Q\text{ permitted of order at most }m}}d(Q).
\tag{1.4}
$$

For each $\epsilon>0$, §§3–5 specify one finite $m$ and one normalized stationary full-support law $Q$, used at every length, with $d(Q)>c_\star-\epsilon$. Both limits also hold on $n=3N$, $N\ge1$.

The proof is ordinary mathematics. This source carries no Lean kernel verification. The additional conclusion over the owned suppliers is (1.4), with its visible-memory and full-support bridges; the finite-probability, conditional-risk and delimiter tools are supporting machinery.

## 2. Exact densities from actual full-word probabilities

**Definition 2.1 (Stationary context products).** A legal order-$m$ kernel consists of numbers $k(z\mid s)\ge0$, $s\in B_m$, $z\in\{0,1\}$, summing to one over legal $sz$ and vanishing on illegal extensions. It gives the context transition $s\longmapsto s_2\cdots s_mz$. If $\pi$ is a stationary context distribution, its stationary visible cylinders, for $n\ge m$, are

$$
Q_n(b)=\pi(b_1\cdots b_m)
\prod_{j=m+1}^n k(b_j\mid b_{j-m}\cdots b_{j-1}).
\tag{2.1}
$$

Here the displayed expression is a product of the initial factor and the transition product. Shorter cylinders are its marginals. Rows on zero-mass contexts may be chosen arbitrarily among legal probability rows. Stationary laws of visible order at most $m$ have this representation by successive conditioning; the tower property replaces conditioning on a finite past of length at least $m$ by the same last-$m$ kernel.

**Definition 2.2 (Coordinate sums and the finite-window expression).** Put

$$
\Phi_{n,i}(\mu)=
\sum_{\substack{b\in B_n\\b_{i-1}=b_i=b_{i+1}=0}}
h(\mu(b),\mu(b+e_i)),\qquad
\Phi_n(\mu)=\sum_{i=1}^n\Phi_{n,i}(\mu).
\tag{2.2}
$$

For a stationary order-$m$ law, including one with zero cylinders, define

$$
D_m(Q)=
\sum_{\substack{a,v\in B_m\\a_m=v_1=0}}
h\bigl(Q_{2m+1}(a0v),Q_{2m+1}(a1v)\bigr).
\tag{2.3}
$$

**Lemma 2.3 (Matching bound).** For every probability vector on $B_n$,

$$
0\le\Phi_{n,i}(\mu)\le\frac14,\qquad
0\le\Phi_n(\mu)\le\frac n4.
\tag{2.4}
$$

Proof. The edges at a fixed coordinate form a matching: each vertex belongs to at most one such edge. The inequality $h(s,t)\le(s+t)/4$ is equivalent to $(s-t)^2\ge0$. The masses of the matching's endpoints sum to at most one. Summing over coordinates proves the second bound. In particular $0\le c_\star\le1/4$ by (1.2). $\square$

**Lemma 2.4 (Exact full-word grouping, including zeros).** For every stationary law represented by (2.1), every $n\ge2m+1$ and every $m+1\le i\le n-m$,

$$
\Phi_{n,i}(Q_n)=D_m(Q).
\tag{2.5}
$$

Proof. Fix $a,v\in B_m$ with $a_m=v_1=0$, and write $w^z=azv$ for $z=0,1$. Let

$$
A_z=\prod_{j=m+1}^{2m+1}
k(w^z_j\mid w^z_{j-m}\cdots w^z_{j-1}).
\tag{2.6}
$$

Then $Q_{2m+1}(w^z)=\pi(a)A_z$. In a full-word pair differing at $i$, precisely the transition factors with indices $j=i,\ldots,i+m$ can change. They have product $A_z$. The initial factor and all other transition factors have a common nonnegative product $C_\omega$, depending on the outside completion $\omega$. The legal outside completions are identical for the two central words: their first and last bits agree, and the center's two neighbors are zero. Thus the actual endpoint masses are $C_\omega A_0,C_\omega A_1$.

Summing $C_\omega$ over all such completions gives $\pi(a)$. Indeed, summing the right-side transition products gives one by row normalization, while summing the left-side products gives the stationary probability of the context $a$ immediately before position $i$. Therefore homogeneity gives

$$
\begin{aligned}
\sum_\omega h(C_\omega A_0,C_\omega A_1)
&=\pi(a)h(A_0,A_1)\\
&=h\bigl(Q_{2m+1}(a0v),Q_{2m+1}(a1v)\bigr).
\end{aligned}
\tag{2.7}
$$

This argument divides by no probability and includes $\pi(a)=0$ and $A_0=A_1=0$. Summing the contexts proves (2.5). It is a grouping of actual paired full words, justified by their common factors. $\square$

**Proposition 2.5 (Density and all endpoints).** Every stationary visible order-$m$ law, even an auxiliary law with zero cylinders, satisfies

$$
\begin{aligned}
\Phi_n(Q_n)&=(n-2m)D_m(Q)+E_n,\quad 0\le E_n\le m/2 &&(n\ge2m+1),\\
\bigl|\Phi_n(Q_n)-nD_m(Q)\bigr|&\le m/2 &&(n\ge1).
\end{aligned}
\tag{2.8}
$$

For $n\ge2m+1$, $E_n$ is exactly the sum of the original coordinate contributions at $1,\ldots,m,n-m+1,\ldots,n$. In particular $d(Q)=D_m(Q)$ exists and $d(Q)\le c_\star$.

Proof. Lemma 2.4 gives the $n-2m$ interior terms. Lemma 2.3 bounds each remaining term by $1/4$, so $E_n\in[0,m/2]$. Applying that lemma to the central coordinate at length $2m+1$ also gives $D_m(Q)\in[0,1/4]$. Thus $E_n-2mD_m(Q)\in[-m/2,m/2]$. If $n\le2m$, both $\Phi_n(Q_n)$ and $nD_m(Q)$ lie in $[0,n/4]$, giving the same remainder bound. Dividing by $n$ proves existence, including along $n=3N$. Finally $\Phi_n(Q_n)\le\kappa_n$ by (1.2), so the growth limit proves the upper bound. $\square$

**Proposition 2.6 (Positive full-word flip ratios at every cut).** For a permitted law, $n\ge m$ and any original upward edge $c=b+e_i$,

$$
\frac{Q_n(c)}{Q_n(b)}
=\frac{\pi(c_1\cdots c_m)}{\pi(b_1\cdots b_m)}
\prod_{j=\max(m+1,i)}^{\min(n,i+m)}
\frac{k(c_j\mid c_{j-m}\cdots c_{j-1})}
{k(b_j\mid b_{j-m}\cdots b_{j-1})}.
\tag{2.9}
$$

Again the initial ratio multiplies the transition product. Empty products equal one. At $n<m$, the ratio is the ratio of the corresponding $\pi$-marginals.

Proof. Divide the two products in (2.1). A factor changes only if its symbol or its history contains $i$, that is, $j-m\le i\le j$. Every denominator is positive. The initial factor is retained even when the flip lies in its context. No endpoint, seam or transition at an arbitrary cut is omitted. $\square$

## 3. Guarded payloads with a visible delimiter

**Definition 3.1 (One stationary marked law).** Fix $L\ge2$ and a probability vector $\mu$ on $B_L$. Set

$$
r=L+3,\qquad T=(L+2)^2,\qquad m=2T.
\tag{3.1}
$$

For each $j\in\mathbb Z$, sample $L$ mutually independent payloads $W_{j,1},\ldots,W_{j,L}$ of law $\mu$, independently also across $j$. Its cell is

$$
C_j=1\,0^r\,
(1\,0\,W_{j,1}\,0)
(1\,0\,W_{j,2}\,0)\cdots
(1\,0\,W_{j,L}\,0).
\tag{3.2}
$$

Parentheses denote concatenation units. The length is $1+r+L(L+3)=T$. Concatenate these cells in both directions with cell $j$ starting at $jT$, obtaining $Y$. Independently choose $A$ uniformly in $\{0,\ldots,T-1\}$ and set $X_t=Y_{t+A}$. Call its law $S$.

Its cylinders also have an entirely finite formula. For an offset $a$ and length $q\ge1$, let $I(a,q)$ be the finite set of payload indices $(j,\ell)$ whose positions meet the observed interval $[1+a,q+a]$ of $Y$. Let $V_{a,q}$ extract that interval from the fixed cell bits and the assigned payload words. Then, for $b\in B_q$,

$$
S_q(b)=\frac1T\sum_{a=0}^{T-1}
\sum_{(w_\alpha)\in B_L^{I(a,q)}}
\left(\prod_{\alpha\in I(a,q)}\mu(w_\alpha)\right)
\mathbf1\{V_{a,q}((w_\alpha))=b\}.
\tag{3.3}
$$

An empty assignment has product one. The formulas for $S_m$ and $S_{m+1}$ in §4 are precisely these finite sums, from this same payload law and offset.

**Lemma 3.2 (Legality, stationarity and actual visible memory).** The construction gives one normalized stationary law on $X$ of visible order at most $m=2T$. It need not have full support.

Proof. Every payload is legal, its two neighboring guard bits are zero, every fixed $1$ has zero neighbors, and the last bit of a cell is zero before the next cell's initial $1$. Hence every concatenation is legal. The iid payload array and the independent finite uniform offset define a probability law, so all its cylinders are normalized and consistent.

Shifting by one cycles $A$. When it wraps from $T-1$ to zero, it also shifts the iid cell indices by one; that array has unchanged distribution. Consequently the visible law is stationary at every integer shift.

The marked zero run has length exactly $r$ and is flanked by fixed ones. Between consecutive fixed ones elsewhere, there are at most $L+2$ zeros, including when a payload is all zero. A fixed one separates each such interval from its neighbors. Therefore occurrences of $0^r$ are exactly the designated runs, one per cell, with their ending positions spaced exactly $T$ apart. There is only one length-$r$ occurrence inside each run of length exactly $r$.

Consider the past positions $-m,\ldots,-1$. The most recent completed marked run ends at some $e\in[-T,-1]$, and starts at $e-r+1\ge-2T+1$, since $r\le T$. Thus the suffix contains a complete marked run. Its visible ending position determines the cell phase modulo $T$ uniquely. At a payload position, the suffix also contains that payload's entire already observed prefix, of length at most $L-1$.

For a prefix $v$ of a payload, put

$$
\mu[v]=\sum_{\substack{b\in B_L\\b\text{ begins with }v}}\mu(b),
\qquad \mu[\varnothing]=1.
\tag{3.4}
$$

Given a supported past, the next-bit probability is either prescribed by the fixed cell positions or, inside the current payload, equals $\mu[vz]/\mu[v]$. Its denominator is positive for a prefix actually observed with positive probability. At the beginning of a new payload this uses the empty prefix. Independence of the other payloads makes earlier visible history irrelevant once the phase and this prefix are known.

Both phase and prefix are functions of the last $m$ visible bits. The same conditional rule holds when conditioning on any finite longer past and on the whole past. Hence $S$ has actual visible order at most $m$. On zero-mass contexts one can complete the kernel, for example by appending zero deterministically. Its stationary context distribution remains $S_m$, and (2.1) applies. This proves the visible-memory claim directly. $\square$

**Lemma 3.3 (Full-word harmonic packing bound).** The marked law satisfies

$$
\Phi_n(S_n)\ge\frac{L(n-L+1)}T\,\Phi_L(\mu)
\quad(n\ge L),\qquad
d(S)\ge\frac{L\Phi_L(\mu)}T.
\tag{3.5}
$$

Proof. First condition on a particular offset $A=a$. For any complete payload contained in positions $1,\ldots,n$, fix all outside visible coordinates in that word. Their distribution is independent of this payload. For an original edge $\{b,c\}$ in $\Gamma_L$, the two full-word endpoint masses are consequently $\rho_\omega\mu(b)$ and $\rho_\omega\mu(c)$, with the same outside probability $\rho_\omega$.

Both concatenations are legal. At a payload boundary the neighboring coordinate inside the observation, if present, is its zero guard; if absent, the original observation has an open endpoint. Thus this pairing includes every coordinate of the payload, including either endpoint and every legal endpoint one. Summing over outside completions, homogeneity and $\sum_\omega\rho_\omega=1$ give exactly $\Phi_L(\mu)$ for its payload-coordinate edges. Complete payloads use disjoint coordinates, so these contributions do not count any edge twice. Every other original edge remains in the objective and has a nonnegative contribution.

There are $L$ payload-start residues in a period of length $T$. Under the uniform offset, each integer position has probability $L/T$ of being a payload start. A length-$L$ payload is wholly contained precisely when its start is in $1,\ldots,n-L+1$. The expected number of complete payloads is therefore $L(n-L+1)/T$.

Write $S_n^a$ for the offset-conditioned cylinder vector, extended by zero on all other vertices of $B_n$. Concavity from [Growth], Lemma 3.1, gives

$$
\Phi_n(S_n)
=\Phi_n\left(\frac1T\sum_{a=0}^{T-1}S_n^a\right)
\ge\frac1T\sum_{a=0}^{T-1}\Phi_n(S_n^a)
\ge\frac{L(n-L+1)}T\Phi_L(\mu).
\tag{3.6}
$$

The first expression is evaluated at the average vector; the subsequent inequalities average objective values. The existence of $d(S)$ follows from Lemma 3.2 and Proposition 2.5. Taking the limit proves the second assertion. Marker, guard, seam and observation-end edges have only been omitted from the lower-bound sum, never from $\Phi_n$. Their coordinates are all charged in the length $T$. $\square$

## 4. Positive stationary flows at one fixed visible order

**Convention 4.1 (Owned positive reference law).** Let $R$ be exactly the stationary pair law of [TwoStep], Definition 2.1 and Proposition 2.2, with pair-state order $(00,01,10)$ and

$$
P=\begin{pmatrix}7/10&3/10&0\\0&0&1\\2/3&1/3&0\end{pmatrix},
\qquad \pi^R=(10/19,9/38,9/38).
\tag{4.1}
$$

The supplier proves row normalization, $\pi^RP=\pi^R$, positive mass on every legal cylinder and stationary consistency at every window. Those are precisely the reference hypotheses used here. Its strict density comparison is not used to prove the completeness bridge.

**Lemma 4.2 (An explicit coherent full-support law).** Fix any stationary legal law $S$ of visible order at most $m$. For $0<\delta<1$ define, on all legal words of the indicated lengths,

$$
\begin{aligned}
\pi_\delta(s)&=(1-\delta)S_m(s)+\delta R_m(s),\\
F_\delta(sz)&=(1-\delta)S_{m+1}(sz)+\delta R_{m+1}(sz),\\
k_\delta(z\mid s)&=\frac{F_\delta(sz)}{\pi_\delta(s)}.
\end{aligned}
\tag{4.2}
$$

Set $k_\delta(z\mid s)=0$ for illegal extensions. These data specify one stationary two-sided visible order-$m$ law $Q^\delta$ through (2.1), with shorter cylinders given by $\pi_\delta$-marginals. This law has full support and positive probabilities for every legal next-bit extension.

Proof. Stationarity and cylinder consistency of both source laws give the two balance identities

$$
\sum_{z:sz\text{ legal}}F_\delta(sz)=\pi_\delta(s),
\qquad
\sum_{a:as\text{ legal}}F_\delta(as)=\pi_\delta(s).
\tag{4.3}
$$

Thus the rows of $k_\delta$ sum to one. For the overlapping context transition $s\mapsto s_2\cdots s_mz$, the incoming mass of a target $s$ is the second sum in (4.3), so $\pi_\delta$ is invariant. It is normalized because both source $m$-word distributions are normalized.

The products (2.1) now have total mass one by summing their last transitions and then their initial distribution. Summing a final symbol proves right consistency. Summing an initial symbol uses the incoming identity in (4.3), then leaves exactly the product for the remaining word, proving left consistency. At lengths below $m$ the marginals of $\pi_\delta$ inherit both consistency identities; they are $(1-\delta)S_n+\delta R_n$. Hence the products assign consistent probabilities to every translated finite interval.

These consistent probabilities give a finitely additive probability on the algebra of finite unions of cylinder sets in $\{0,1\}^{\mathbb Z}$. This product space is compact, and every such cylinder-algebra set is closed. A decreasing sequence of these sets with empty intersection must therefore have an empty member. The assignment is consequently continuous at the empty set, which makes it countably additive on that algebra. The measure extension theorem produces its unique law on the cylinder sigma-algebra. The verified consistency and finite-alphabet compactness are the hypotheses of the usual probability extension step.

The equal left and right consistency formulas make this two-sided law stationary. Successive products give the conditional next-bit kernel $k_\delta$ for every finite past of length at least $m$; conditioning on the whole past yields that same kernel, so its memory is visible.

Since $\delta>0$ and every legal $R$-cylinder is positive, $\pi_\delta(s)>0$ and $F_\delta(sz)>0$ for every legal $sz$. All legal transition probabilities are therefore positive. The full-word products and their shorter marginals give positive mass to every word of every $B_n$. Illegal adjacent ones have probability zero. This proves every assertion about the final process.

Only stationary block flows are mixed in (4.2). Longer cylinders of $Q^\delta$ are their Markov products; no claim that a mixture of whole processes is Markov is involved. $\square$

**Lemma 4.3 (The fixed-order support limit controls the original density).** For the laws of Lemma 4.2 with $m$ fixed,

$$
Q^\delta_n(b)\longrightarrow S_n(b)\quad(\delta\downarrow0)
\text{ for every fixed legal word }b,\qquad
d(Q^\delta)\longrightarrow d(S).
\tag{4.4}
$$

Proof. On each context $s$ with $S_m(s)>0$, (4.2) gives

$$
k_\delta(z\mid s)\longrightarrow
\frac{S_{m+1}(sz)}{S_m(s)}=k_S(z\mid s).
\tag{4.5}
$$

For a word of positive $S$-mass, its initial context and every traversed context and transition have positive supporting mass. Its finite product therefore converges to the $S$-product.

For a word of zero $S$-mass and length at least $m$, either its initial context has zero $S_m$-mass, in which case the initial factor tends to zero, or there is a first extension of a positive-mass prefix which makes its mass zero. At that extension the context has positive $S_m$-mass, while its $(m+1)$-word mass is zero. The corresponding transition factor tends to zero by (4.5). All other factors are between zero and one, so the whole product tends to zero. This also handles paths which subsequently visit zero-mass contexts. Shorter words converge by their explicit marginal formula.

In particular the finitely many $(2m+1)$-word masses converge. By (2.3), continuity of $h$ on the entire nonnegative quadrant, including $h(0,0)=0$, implies

$$
d(Q^\delta)=D_m(Q^\delta)\longrightarrow D_m(S)=d(S).
\tag{4.6}
$$

Proposition 2.5 establishes these density identities before the support limit is taken. The convergence is at one fixed $m$, so no uncontrolled interchange with the growing observation length is used. Formula (2.9) applies to every original edge of $Q^\delta$, including former deterministic seams. $\square$

## 5. The epsilon witness and the equality

Proof of Theorem 1.4. Proposition 2.5 already proves density existence and $d(Q)\le c_\star$ for every permitted law.

For each $L\ge2$, choose one maximizing vector $\mu_L^\star$ on all of $B_L$, whose existence is [Growth], Theorem 3.2. Let $u_L$ be the uniform probability vector on $B_L$ and set

$$
\mu_L=(1-L^{-2})\mu_L^\star+L^{-2}u_L.
\tag{5.1}
$$

This is a normalized strictly positive payload law. Concavity and nonnegativity give

$$
\Phi_L(\mu_L)\ge(1-L^{-2})\kappa_L.
\tag{5.2}
$$

Construct $S^{(L)}$ by Definition 3.1 with this payload law. Lemmas 3.2–3.3 give an actual visible order at most $m_L=2(L+2)^2$ and

$$
d(S^{(L)})\ge
\frac{L(1-L^{-2})\kappa_L}{(L+2)^2}
=:g_L.
\tag{5.3}
$$

The owned limit $\kappa_L/L\to c_\star$ and

$$
g_L=
\frac{\kappa_L}{L}(1-L^{-2})\frac{L^2}{(L+2)^2}
\longrightarrow c_\star
\tag{5.4}
$$

show that, for a given $\epsilon>0$, there exists $L\ge2$ with $g_L>c_\star-\epsilon/2$. Choose one such $L$ and fix the maximizing vector, payload law, cells, marked process and finite visible order $m=m_L$.

Use Lemma 4.2 for this $S=S^{(L)}$ and the owned reference $R$. Lemma 4.3 supplies a positive $\delta$ with

$$
D_m(Q^\delta)>D_m(S)-\epsilon/2.
\tag{5.5}
$$

For a definite selection, $\delta$ may be $2^{-j}$ for the least integer $j\ge1$ satisfying (5.5); the proved limit ensures this set is nonempty. Equations (4.2) and (2.1) are the actual normalized producer for this choice, on every original legal context and every word length.

The single permitted law $Q=Q^\delta$ consequently satisfies

$$
d(Q)>d(S)-\epsilon/2\ge g_L-\epsilon/2>c_\star-\epsilon.
\tag{5.6}
$$

All parameters are fixed independently of $n$. The auxiliary marked law is used only to establish the lower bound; the witness has full support on the original shift. The upper bound proved for every permitted law and the arbitrary $\epsilon$ prove (1.4). The all-length remainder (2.8) proves the same limits along $n=3N$.

Every observation remains an open path, and every arbitrary cut retains its transitions in (2.1). The guards protect payload endpoints only in the auxiliary construction; they impose no extra word restriction on the final law. Allzero, endpoint-one and seam cylinders of that law are positive by Lemma 4.2. $\square$

## 6. Two precisely scoped shortcut boundaries

**Proposition 6.1 (Local marginals need a common-factor bridge).** A harmonic term of window marginals need not equal the sum of the corresponding full-word harmonic terms, even on the original legal domain.

Proof. On $B_4$ place mass $1/2$ at each of $0000$ and $0101$, and zero at all other vertices. At coordinate two the original edge pairs are $0000$–$0100$ and $0001$–$0101$. Each has a zero-mass endpoint, so their harmonic sum is zero. The marginal on positions one through three instead has masses $1/2$ at $000$ and $010$, whose harmonic term is $1/4$. This is a finite-prior counterexample to unproved marginal grouping, not a counterexample to (1.4). Lemma 2.4 supplies the specific equality missing in that shortcut. $\square$

**Proposition 6.2 (Finite hidden state does not imply finite visible order).** There is a stationary legal full-support process with a finite hidden-state presentation and no finite visible Markov order.

Proof. For $0<a<1$, let $R^a$ be the stationary first-order bit chain with transitions $0\to1$ of probability $a$, $0\to0$ of probability $1-a$, and $1\to0$ of probability one. Its stationary bit distribution is $(1/(1+a),a/(1+a))$, as direct multiplication verifies. Its legal cylinders are positive.

Choose once, with equal probabilities, between $a=1/3$ and $b=2/3$, then use the chosen stationary chain forever. The resulting law $M=(R^a+R^b)/2$ is stationary, legal and full-support. A hidden state records the chosen parameter and the current bit, giving four states.

For $q\ge1$, put $A_q=(1-a)^{q-1}/(1+a)$ and $B_q=(1-b)^{q-1}/(1+b)$. Direct conditional probability gives

$$
M(X_0=1\mid X_{-q}\cdots X_{-1}=0^q)
=\frac{aA_q+bB_q}{A_q+B_q}
=a+(b-a)\frac{t_q}{1+t_q},
\quad
t_q=\frac45\,2^{-(q-1)}.
\tag{6.1}
$$

This quantity strictly decreases with $q$. If $M$ had visible order at most any finite $m$, the tower property would make it the same value $k(1\mid0^m)$ for every $q\ge m$, a contradiction. The example explains why Lemma 3.2 proves bounded visible phase recovery rather than relying on a cell or hidden-state count. $\square$

## 7. Citation scope and remaining limits

**Citation scope 7.1 (Established machinery and the uncovered delta).** The source dependencies and their hypotheses are as follows.

| Source | Exact scope and use |
| --- | --- |
| [Growth], Lemma 3.1 and Theorems 3.2, 5.2 | Owned harmonic concavity, continuity and homogeneity; finite simple-graph duality and attained maximum; growth on the complete open-path Fibonacci graphs. Every graph here has exactly that domain. No code-dependent numerical conclusion is borrowed. |
| [TwoStep], Definition 2.1, Proposition 2.2, Proposition 2.4 and Theorems 3.1, 4.1 | Owned normalized stationary positive pair law, actual full-word ratio grouping, its density and strict bulk comparison. The reference law in (4.1) is that same law. The general-order calculation consumes the existing grouping mechanism; it does not rediscover the pair separation. |
| S. Gallo, M. Lerasle and D. Y. Takahashi, [Markov approximation of chains of infinite order in the d-bar-metric][GLT], arXiv:1107.4353v2, Definitions 2.1–2.3 | Literature-attested finite-past conditional kernel for a stationary process and the distinction between finite visible dependence and dependence on an entire past. The block-conditional construction is established machinery. Its stationary-flow normalization and treatment of zero contexts on the present grammar are proved explicitly in §4; no quantitative approximation theorem from this paper is imported. |
| Cesar Maldonado and Raúl Salgado-García, [Markov approximations of Gibbs measures for long-range potentials on 1D lattices][MSG], arXiv:1306.6104v1, §§2.1–2.4, Condition 1 and Theorem 3.1 | Literature-attested alternative: a finite-alphabet full shift with a real pair potential $\phi(x)=\sum_r\psi_r(x_0,x_r)$, satisfying $\sum_r p(r)\|\psi_r\|<\infty$ for a weight with $p(r)/r\to\infty$, has projectively convergent finite-range Gibbs/Markov approximations. No such potential or regularity is assumed or established for harmonic optimizers here. The theorem is not applied to the forbidden-$11$ shift. |
| Aernout van Enter and Evgeny Verbitskiy, [Erasure entropies and Gibbs Measures][EV], arXiv:1001.3122v1, Definition 4 and Theorems 5–6 | Literature-attested conditional-uncertainty background. Theorem 5 assumes a translation-invariant finite-alphabet random field and concerns Shannon erasure entropy; Theorem 6 additionally assumes a Gibbs measure for the stated interaction. Neither supplies this harmonic functional or its finite-order supremum. No Shannon or Gibbs conclusion is substituted for (1.4). |

The projective estimate in [MSG], Definition 2.1, compares length-$n$ cylinder ratios by $\exp(\pm n\eta_r)$ with $\eta_r\to0$. Even an endpointwise comparison of that form, at a fixed $r$, supplies through monotonicity and homogeneity only a lower bound with factor $\exp(-n\eta_r)$. This factor gives no positive asymptotic density lower bound at fixed $\eta_r>0$. The missing bridge for this objective is therefore not supplied merely by that estimate or by matching defining Markov marginals. Here it is (2.7), followed by the full-word packing bound (3.6) and the fixed-$m$ density continuity (4.6).

For completeness, coordinatewise monotonicity used in this comparison follows directly from the formula for $h$: at fixed $t>0$, the derivative in $s$ is $t^2/(s+t)^2\ge0$, and at $t=0$ the function is constant zero. Symmetry handles the other coordinate. The comparison is a limitation of that lower-bound inference, not a disproof of any stronger result under additional Gibbs hypotheses.

Theorem 1.4 is a repo-derived synthesis on the fixed domain. The cited Markov, Gibbs and conditional-uncertainty literature supplies established frameworks with the indicated boundaries, not a primary-source theorem asserting (1.4). The cited scope is bounded; no worldwide originality or exhaustive absence assertion follows. Delimiter coding, independent products, probability extension and conditional-risk grouping are not claimed as separate new discoveries.

**Boundary 7.2 (What the equality does not decide).** The result gives neither attainment at a fixed finite order nor the exact numerical value of $c_\star$. It does not prove strict improvement at every memory order or identify an optimal approximation rate. The choices of a finite maximizing payload prior and a sufficiently small positive $\delta$ are existential; no efficient acquisition or transition-table construction is established.

A table on $B_m$ has $|B_m|=F_{m+2}$ context rows and at most two legal outgoing entries per row, where $F_0=0$, $F_1=1$ and $F_{j+2}=F_{j+1}+F_j$. With $B_0$ consisting of the empty word, this count follows by splitting a legal word according to whether it ends in $0$ or $01$, with $|B_0|=1$, $|B_1|=2$. Acquiring and describing its probabilities, and storing its contexts, are separate costs from the density $\Phi_n/n$. The theorem asserts no actual machine-learning benefit, physical or quantum advantage, or kernel-verified statement.

[Growth]: https://github.com/the-omega-institute/trureturing/blob/409f27ebed169a35fa000f22ed56a2f154cb9c93/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[TwoStep]: https://github.com/the-omega-institute/trureturing/blob/348bfc85a973f021d8e3e79df589b335b5407ee7/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_TWO_STEP_BULK_SEPARATION.md
[GLT]: https://arxiv.org/html/1107.4353v2
[MSG]: https://arxiv.org/html/1306.6104v1
[EV]: https://arxiv.org/html/1001.3122v1

## 追加锚（本行以下为增补区）

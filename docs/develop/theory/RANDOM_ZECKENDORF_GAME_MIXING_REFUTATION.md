# Random Zeckendorf games: a temporal non-mixing theorem

## 1. Exact model and the target

Let $F_1=1,F_2=2$, and $F_{j+1}=F_j+F_{j-1}$ for $j\ge2$.  A configuration is a finite multiset of the $F_j$.  The legal labels are

$$
 C_1:\;2F_1\longrightarrow F_2,\qquad
 C_j:\;F_{j-1}+F_j\longrightarrow F_{j+1}\quad(j\ge2),
$$

and

$$
 S_2:\;2F_2\longrightarrow F_1+F_3,\qquad
 S_j:\;2F_j\longrightarrow F_{j-2}+F_{j+1}\quad(j\ge3).
$$

At each nonterminal configuration $s$, every available label is chosen with probability

$$
 q(s,M)=\frac1{d(s)},\qquad d(s)=\#\{\text{available labels at }s\}.
$$

Thus a complete word $g=(M_1,\ldots ,M_{L(g)})$ has probability

$$
 P_N(g)=\prod_{r=1}^{L(g)}
 \frac1{d(s_{r-1})},
$$

where $s_{r-1}$ is the configuration before $M_r$.  This is the measure $P_N$ of Cheigh et al. [1, Definition 1.2 and §1.2].

For input $N$, let

$$
 d_N=\max\{L(g):g\text{ is a complete legal game from }N F_1\}.
$$

For a random complete game, put $X_{N,i}=1$ when the $i$-th actual move is a split and $X_{N,i}=0$ when it is a combine; set $X_{N,i}=0$ after the game terminates, up to the fixed row endpoint $d_N$.  For $1\le a\le b\le d_N$, write

$$
 \mathcal F^{(N)}_{a,b}=\sigma(X_{N,a},\ldots ,X_{N,b}),
 \qquad
 \mathcal F^{(N)}_{0,m}=\sigma(X_{N,1},\ldots ,X_{N,m}).
$$

When the original notation uses $\mathcal F^{(N)}_{m+k,\infty}$, extend the row by $X_{N,i}=0$ for $i>d_N$; the resulting sigma-algebra is exactly $\mathcal F^{(N)}_{m+k,d_N}$.
For $k\ge0$, define

$$
 \alpha_N(k)=
 \sup_{\substack{m\ge1\\m+k\le d_N}}
 \ \sup_{\substack{A\in\mathcal F^{(N)}_{0,m}\\
                    B\in\mathcal F^{(N)}_{m+k,d_N}}}
 \left|P_N(A\cap B)-P_N(A)P_N(B)\right|,
$$

and put $\alpha_N(k)=0$ if the outer supremum has no admissible $m$.  This is the absolute-covariance convention in [1, equation (7)].

The question is whether there are $\delta,C>0$ such that, for every $N$,

$$
 \sum_{k=0}^{\infty}(k+1)^2
 \alpha_N(k)^{\delta/(4+\delta)}<C. \tag{Q}
$$

We prove the negation of (Q) for the actual locally uniform label law.

## 2. Fibonacci rows and deterministic bounds

Fix $N=F_n$, with $n\ge 6$, and write

$$
 M=2n,\qquad C=N-1.
$$

A combine reduces the number of tokens by one and a split preserves it.  The terminal Zeckendorf decomposition of $F_n$ is the one token $F_n$, so every complete game has exactly $C=N-1$ combines.  Consequently, if $L$ is its length and $S=\sum_{i=1}^{d_N}X_{N,i}$ is its total number of splits, then

$$
 L=C+S. \tag{2.1}
$$

No occupied index can exceed $n$, because $F_{n+1}>F_n$ and the weighted sum of the configuration is conserved.  Hence the only possible labels are

$$
 C_1,\ldots ,C_{n-1},\quad S_2,\ldots ,S_{n-1},
$$

at most $2n-3<M$ labels.  Every prescribed legal next label therefore has conditional probability at least $M^{-1}$.  Also, after $t$ moves the number $h_1(t)$ of $F_1$-tokens satisfies

$$
 h_1(t)\ge N-2t, \tag{2.2}
$$

because a move removes at most two $F_1$-tokens.

We use the linear longest-game estimate of Cheigh et al. [1, Theorem 1.6].  On $N=F_n$ it gives

$$
 d_N<3N \tag{2.3}
$$

for all $n\ge6$.

## 3. A stopped-prefix product law

For $1\le c\le C$, let $\tau_c$ be the time of the $c$-th combine.  Since $L\ge C$, $\tau_c$ is defined on every game.

**Lemma 3.1 (the $C_2\leftrightarrow(S_2,C_1)$ interchange).**
Suppose a configuration has heights $(a,b,d)$ in bins $1,2,3$.  If $C_2$ is legal and $b\ge2$, then both words $C_2$ and $S_2,C_1$ are legal and have the same endpoint:

$$
 (a,b,d)\xrightarrow{C_2}(a-1,b-1,d+1)
$$

and

$$
 (a,b,d)\xrightarrow{S_2}(a+1,b-2,d+1)
 \xrightarrow{C_1}(a-1,b-1,d+1).
$$

Conversely, legality of $S_2,C_1$ implies legality of $C_2$ and $b\ge2$.

*Proof.*  The displayed height changes are the definitions of the three labels.  The first route requires $a,b\ge1$.  The second requires $b\ge2$ and, after $S_2$, $a+1\ge2$, hence $a\ge1$.  These are exactly the stated conditions. ∎

For a legal word ending at $\tau_c$, sum the probabilities of all complete continuations.  The conditional continuation probability is one, so the word's probability is exactly the product of its local reciprocal denominators, including when the word itself is terminal.

Contract every consecutive occurrence of $S_2,C_1$ in such a word to $C_2$, repeatedly from left to right.  The occurrences cannot overlap.  By Lemma 3.1, contraction preserves every subsequent configuration.  The resulting representative $R$ contains no $S_2,C_1$.  Conversely, an occurrence of $C_2$ in $R$ is *eligible* when the alternative $S_2,C_1$ is legal; expanding any set of eligible occurrences gives a legal word ending at the same $c$-th combine.  Since each expansion creates its own $S_2,C_1$ and the endpoint after the pair is unchanged, expansions at distinct eligible occurrences do not alter one another's eligibility and create no boundary pair.  Thus the stopped prefixes are partitioned by their unique representative $R$ and independent expansion choices. This representative partition is the locally uniform stopped-prefix adaptation of Cheigh et al. [1, Lemma 4.1], with the present legality and stopping-time details proved here.

Let $t_j$ be the configuration immediately after the $S_2$ in the long route at eligible slot $j$, and put $d_j=d(t_j)$.  The denominator before the first move is the same for $C_2$ and $S_2$; all later denominators are shared because the endpoints agree.  Therefore replacing the short route by the long route multiplies the prefix probability by exactly $d_j^{-1}$.  Conditional on $R$, the expansion indicators $B_j$ are independent Bernoulli variables with

$$
 p_j=P(B_j=1\mid R)=\frac1{1+d_j},
 \qquad
 \frac1{M+1}\le p_j\le\frac12. \tag{3.1}
$$

If $T(R)$ is the number of eligible slots, then

$$
 \tau_c=|R|+\sum_{j=1}^{T(R)}B_j
 \quad\text{conditional on }R. \tag{3.2}
$$

This is a conditional product law for stopped prefixes; it asserts no independence for the original time-indexed sequence $(X_{N,i})$. The conditional Bernoulli calculation adapts Cheigh et al. [1, Lemma 4.2 and Corollary 4.3] to the actual locally uniform label law. ∎

## 4. Many slots and anti-concentration of $\tau_c$

We first record the adapted lower-tail estimate used twice below.

**Lemma 4.1 (adapted Bernoulli lower tail).**
Let $I_1,\ldots ,I_r\in\{0,1\}$ be adapted to $(\mathcal G_j)$, and suppose

$$
 P(I_j=1\mid\mathcal G_{j-1})\ge u
$$

almost surely, where $0<u\le1$.  Then

$$
 P\!\left(\sum_{j=1}^r I_j\le\frac{ru}{2}\right)
 \le e^{-ru/8}. \tag{4.1}
$$

*Proof.*  With $\lambda=\log2$,

$$
 E(e^{-\lambda I_j}\mid\mathcal G_{j-1})
 \le1-u+ue^{-\lambda}=1-\frac u2\le e^{-u/2}.
$$

Iterating and applying Markov's inequality gives

$$
 P\!\left(\sum I_j\le ru/2\right)
 \le e^{\lambda ru/2}e^{-ru/2}
 =e^{-ru(1-\log2)/2}\le e^{-ru/8}.
$$

∎

**Lemma 4.2 (slot abundance).**
For $6\le c\le N/4$,

$$
 P_N\!\left(T(R)<\frac{c}{12M^3}\right)
 \le \exp\!\left(-\frac{c}{48M^3}\right), \tag{4.2}
$$

for all sufficiently large $n$, where $R$ is the representative of the prefix ending at $\tau_c$. The triple-counting construction is the locally uniform counterpart of Cheigh et al. [1, Lemma 4.4]; the displayed tail bound is proved here from Lemma 4.1.

*Proof.*  The first $c$ moves exist because $\tau_c\ge c$.  By (2.2), throughout those moves

$$
 h_1\ge N-2c\ge N/2.
$$

For large $N$, each disjoint triple among the first $\lfloor c/3\rfloor$ triples can therefore realize

$$
 C_1,C_1,C_2:
$$

after the two $C_1$'s there are at least two new $F_2$-tokens and at least one $F_1$-token remains, so $C_2$ is legal.  Conditional on the preceding moves, the probability of this triple is at least

$$
 u=M^{-3}. \tag{4.3}
$$

Let $I_j$ indicate success of the $j$-th triple.  By Lemma 4.1 and $\lfloor c/3\rfloor\ge c/6$,

$$
 P_N\!\left(\sum I_j<\frac{c}{12M^3}\right)
 \le e^{-c/(48M^3)}.
$$

A successful triple contributes a distinct $C_2$ to the representative: it cannot be the contracted member of an $S_2,C_1$ pair, and contractions before it preserve the state before its $C_2$.  Hence $T(R)\ge\sum I_j$. ∎

**Lemma 4.3 (Poisson-binomial point bound).**
If $Z=\sum_{j=1}^r B_j$ is a sum of independent Bernoulli variables and $V=\sum_jp_j(1-p_j)>0$, then

$$
 \sup_{z\in\mathbb Z}P(Z=z)\le\frac{K_0}{\sqrt V},
 \qquad K_0=\frac1{2}\sqrt{\frac\pi2}. \tag{4.4}
$$

This is the standard independent Bernoulli point-mass estimate; see Baillon, Cominetti, and Vaisman [2, Theorem 1]. The weaker constant displayed here is proved directly.

*Proof.*  Fourier inversion and

$$
 |1-p+pe^{it}|^2
 =1-4p(1-p)\sin^2(t/2)
$$

give

$$
 |\mathbb E e^{itZ}|
 \le\exp\!\left(-2V\sin^2(t/2)\right).
$$

For $|t|\le\pi$, $\sin(|t|/2)\ge |t|/\pi$.  Therefore

$$
 P(Z=z)\le\frac1{2\pi}\int_{-\pi}^{\pi}
 e^{-2Vt^2/\pi^2}\,dt
 \le\frac1{2}\sqrt{\frac\pi{2V}},
$$

which is (4.4). ∎

**Proposition 4.4 (anti-concentration at a combine time).**
There is a universal $K$ such that, for $6\le c\le N/4$, every integer interval $I$ containing at most $h$ integers satisfies

$$
 P_N(\tau_c\in I)
 \le e^{-c/(48M^3)}
   +K\,h\,\frac{M^2}{\sqrt c}. \tag{4.5}
$$

*Proof.*  Conditional on a representative $R$, Lemma 3.1 gives (3.2).  On the event $T(R)\ge c/(12M^3)$, (3.1) implies

$$
 V=\sum_jp_j(1-p_j)
 \ge\frac{T(R)}{2(M+1)}
 \ge\frac{c}{48M^4}
$$

for $M\ge2$.  Lemma 4.3 bounds the conditional probability of each integer value by $K_0\sqrt{48}\,M^2/\sqrt c$, and hence the probability of $I$ by $K_0h\sqrt{48}\,M^2/\sqrt c$.  The exceptional representatives have total probability bounded by (4.2), which is paid once, not once per point of $I$.  Enlarging the universal constant gives (4.5). ∎

## 5. The early split count has polynomial-window small mass

Put

$$
 m=\lfloor N/8\rfloor,\qquad
 S_m=\sum_{i=1}^{m}X_{N,i},\qquad
 D_m=m-S_m.
$$

There is no termination before move $m$, because $L\ge C=N-1>m$.  By (2.2), $C_1$ is available throughout the first $m$ moves, and the conditional probability of a combine at each such move is at least $M^{-1}$.  Lemma 4.1 gives

$$
 P_N\!\left(D_m<\frac{m}{2M}\right)
 \le e^{-m/(8M)}. \tag{5.1}
$$

Let $v=M^2$.  The probability that the last $v$ moves before $m$ contain no combine is at most

$$
 (1-M^{-1})^v\le e^{-M}. \tag{5.2}
$$

If $D_m=c$ and there is a combine in that interval, then $\tau_c\in(m-v,m]$.  Thus, for any integer interval $J$ with at most $h$ points, (4.5), (5.1), and a union over the possible $c\in J\cap[m/(2M),m]$ yield

$$
\begin{aligned}
 P_N(D_m\in J)
 &\le e^{-m/(8M)}+e^{-M}\\
 &\quad+h\left[
 e^{-m/(96M^4)}
 +K(v+1)\frac{M^2}{\sqrt{m/(2M)}}\right]. \tag{5.3}
\end{aligned}
$$

For large $n$, the values $c$ in the union satisfy $6\le c\le m\le N/4$, so Proposition 4.4 applies.  Since $N=F_n$ grows exponentially in $n$, while $M=2n$, the right side of (5.3) tends to zero whenever $h$ is bounded by any fixed power of $M$.  Because $S_m=m-D_m$, the same is true with $D_m$ replaced by $S_m$:

$$
 \sup_{\substack{J\subset\mathbb Z\\ |J|\le H_n}}
 P_N(S_m\in J)\longrightarrow0
 \quad\text{for every fixed polynomial }H_n\text{ in }M. \tag{5.4}
$$

## 6. A suffix statistic recovers the early count

Let $L$ be the actual length, let

$$
 J=\max\{i\le d_N:X_{N,i}=1\},
$$

with $J=0$ if there is no split, and define the trailing combine run $R=L-J$.  At a configuration with $H>n+2$ tokens, either a bin $i\ge2$ contains at least two tokens, in which case a split is available, or every such bin has height at most one and then $h_1\ge4$; in the latter case $C_1,C_1,S_2$ is legal.  Hence, from every configuration with $H>n+2$, the conditional probability of seeing a split within the next three moves is at least $M^{-3}$.

If $R\ge r+n+2$, then at the beginning of the final combine run there are $1+R\ge r+n+3$ tokens.  During the first $r$ combines, each three-move block begins with more than $n+2$ tokens.  For a fixed possible beginning time, conditional multiplication bounds the probability of those $r$ combines by

$$
 (1-M^{-3})^{\lfloor r/3\rfloor}.
$$

A union over the at most $d_N+1$ possible beginning times is valid even though $J$ is not a stopping time.  Consequently

$$
 P_N(R\ge r+n+2)
 \le(d_N+1)(1-M^{-3})^{\lfloor r/3\rfloor}. \tag{6.1}
$$

Choose $r=M^5$ and put

$$
 b=M^5+n+2.
$$

Using (2.3),

$$
 P_N(R>b)\le(3N+1)(1-M^{-3})^{\lfloor M^5/3\rfloor}
 \longrightarrow0. \tag{6.2}
$$

Set

$$
 k=M^6,\qquad q=m+k.
$$

For large $n$, $q<C-b$, and $q\le d_N$.  From the future coordinates alone define

$$
 V=\sum_{i=q}^{d_N}X_{N,i},\qquad
 J_q=\max\{i\ge q:X_{N,i}=1\},
$$

where $J_q=q-1$ if the set is empty, and then

$$
 U=J_q-C-V. \tag{6.3}
$$

Thus $U$ is measurable with respect to $\mathcal F^{(N)}_{q,d_N}$.

On $R\le b$, (6.2) and $J=L-R\ge C-b>q$ imply $J_q=J$.  Let

$$
 G=\sum_{i=m+1}^{q-1}X_{N,i}.
$$

Using zero padding and (2.1),

$$
 J+R=L=C+S_m+G+V,
$$

so

$$
 U=S_m+G-R,\qquad |U-S_m|\le(q-m-1)+b\le k+b. \tag{6.4}
$$

## 7. Covariance at a polynomially diverging lag

Choose the least integer $a_n$ with

$$
 P_N(S_m\le a_n)\ge\frac12,
$$

and put

$$
 A_n=\{S_m\le a_n\},\qquad B_n=\{U\le a_n\}.
$$

Then $A_n\in\mathcal F^{(N)}_{0,m}$ and $B_n\in\mathcal F^{(N)}_{q,d_N}$.  By (5.4), the largest atom of $S_m$ tends to zero, hence

$$
 P_N(A_n)\longrightarrow\frac12. \tag{7.1}
$$

If $A_n\triangle B_n$ occurs on $R\le b$, (6.4) implies

$$
 |S_m-a_n|\le k+b.
$$

Therefore

$$
 P_N(A_n\triangle B_n)
 \le P_N(R>b)+P_N(|S_m-a_n|\le k+b)
 \longrightarrow0, \tag{7.2}
$$

because $k+b=O(M^6)$ and (5.4) applies.

For events $A,B$, writing $p=P_N(A)$, one has

$$
 \left|
 [P_N(A\cap B)-P_N(A)P_N(B)]-p(1-p)
 \right|
 \le2P_N(A\triangle B). \tag{7.3}
$$

Indeed, $|P_N(A\cap B)-p|\le P_N(A\triangle B)$ and
$|P_N(B)-p|\le P_N(A\triangle B)$.  Equations (7.1)--(7.3) give

$$
 \left|P_N(A_n\cap B_n)-P_N(A_n)P_N(B_n)\right|
 \longrightarrow\frac14. \tag{7.4}
$$

Since the absolute covariance of two events is at most $1/4$, (7.4) and the definition of $\alpha_N$ imply

$$
 \alpha_{F_n}((2n)^6)\longrightarrow\frac14. \tag{7.5}
$$

## 8. Negative answer to the original weighted condition

**Theorem 8.1 (refutation of Question 6.5 / chapter Question 3).**
For every $\delta>0$,

$$
 \sup_{N\ge1}\sum_{k=0}^{\infty}(k+1)^2
 \alpha_N(k)^{\delta/(4+\delta)}=\infty. \tag{8.1}
$$

Consequently, there do not exist $\delta,C>0$ satisfying (Q).

*Proof.*  Fix $\delta>0$, and set $p=\delta/(4+\delta)>0$.  By (7.5), for all sufficiently large $n$,

$$
 \alpha_{F_n}((2n)^6)\ge\frac18.
$$

The single summand at $k=(2n)^6$ is therefore at least

$$
 \bigl((2n)^6+1\bigr)^2\,8^{-p},
$$

which tends to infinity.  Hence the supremum in (8.1) is infinite, proving the exact negation of (Q). ∎

**Corollary 8.2.**  For each fixed $k\ge0$,

$$
 \sup_N\alpha_N(k)=\frac14.
$$

*Proof.*  The upper bound is the universal event-covariance bound.  Given fixed $k$, choose $n$ so large that $(2n)^6\ge k$.  For any row, $\alpha_N(k)\ge\alpha_N((2n)^6)$, because enlarging the future sigma-algebra by moving its first coordinate left cannot decrease the supremum.  Apply (7.5) along $N=F_n$. ∎

The conclusion concerns the original locally uniform label law, the longest complete-game row endpoint, zero padding, and the full generated past and future event sigma-algebras.  It does not concern the uniform measure on complete games, accelerated move rules, atom-only events, or the Gaussian limit conjecture.

## References

[1] Cheigh, Dantas e Moura, Jeong, Lehmann Duke, Milgrim, Miller, and Ngamlamai, *Towards the Gaussianity of Random Zeckendorf Games*, arXiv:2210.11038v1, Definition 1.2, §1.2, Theorem 1.6, Lemma 4.1, Lemma 4.2, Corollary 4.3, Lemma 4.4, equations (7) and (11), Question 6.5; author chapter version, Chapter Question 3 and Theorem 11.

[2] J.-B. Baillon, R. Cominetti, and J. Vaisman, *A sharp uniform bound for the distribution of sums of Bernoulli trials*, arXiv:0806.2350v4, Theorem 1.

## 追加锚（本行以下为增补区）

## 9. Complete-word $R_2$ fibres and quantitative $P_N$ fluctuations

**Definition 9.1 (the original complete-word laws).** Let $\Omega_N$ be the set of all complete legal words from $N F_1$, let

$$
 P_N(g)=\prod_{t=1}^{L(g)}d(s_{t-1})^{-1},\qquad
 \mu_N(g)=|\Omega_N|^{-1}\quad(g\in\Omega_N),
$$

and choose the unique $n=n(N)$ with $F_n\le N<F_{n+1}$. These are exactly the laws of [1, Definition 1.2 and §1.2]; each available label, rather than each pair of tokens, has one chance to be chosen. At $N=1$, the sole complete word is empty and $L=0$.

**Theorem 9.2 (all-integer fluctuations under $P_N$).** Let $R_2$ be the complete-word contraction defined in §9.1 and put $V=\operatorname{Var}_{P_N}(L\mid R_2)$. There are absolute constants $a,b_0,c,K>0$ and an integer $N_0$ such that, for every integer $N\ge N_0$,

$$
 P_N(V<cN)\le e^{-aN}+2e^{-b_0N/n(N)},\qquad
 \operatorname{Var}_{P_N}(L)\ge cN/2,\qquad
 \sup_{\ell\in\mathbb Z}P_N(L=\ell)\le K/\sqrt N.
$$

The complete-word partition and both pushforward identities in §9.1 hold for every positive integer $N$. The quantitative estimates concern $P_N$.

*Proof.* We use the exchange and conditional Bernoulli mechanism of [1, Lemmas 4.1–4.2], the adapted bound in Lemma 4.1 above, and the independent-trial bound in Lemma 4.3 above and [2, Theorem 1]. The construction below supplies the particular $R_2$ partition, its actual weights, and the game-specific estimates needed for the three conclusions.

### 9.1. The complete-word contraction and its exact pushforward law

For a configuration write $h_i$ for the height of bin $i$. Contract every consecutive occurrence of $S_2,C_1$ in a complete word, scanning from left to right, to one symbol $C_2$; call the resulting complete word $R_2=\rho_2(g)$. At a $C_2$ in $R_2$, call the slot eligible when its pre-move heights satisfy

$$
 h_1\ge1,\qquad h_2\ge2.
$$

Let $T(R_2)$ be the number of eligible slots, and for an eligible slot $j$ let $s_j$ be its pre-move configuration and

$$
 d_j=d(S_2s_j).
$$

Here $d(S_2s_j)$ is the number of legal labels after the counterfactual $S_2$ move; it is at least one because $C_1$ is then legal. The following endpoint identity is the local reason that this is an exact partition. If the relevant heights are $(a,b,c)$, then

$$
 (a,b,c)\xrightarrow{C_2}(a-1,b-1,c+1)
$$

and

$$
 (a,b,c)\xrightarrow{S_2}(a+1,b-2,c+1)
 \xrightarrow{C_1}(a-1,b-1,c+1).
$$

Thus both routes are legal exactly when $a\ge1$ and $b\ge2$, and they have the same endpoint. The pattern $S_2,C_1$ cannot overlap itself. Replacing it by $C_2$ cannot create a new such pattern across either boundary, because the new symbol is $C_2$ and the old second symbol was $C_1$. Consequently every subset of the eligible slots of a representative $R_2$ expands to a legal complete word with contraction $R_2$. Conversely, each word with this contraction is recovered by expanding exactly the slots created by its removed pairs. An expansion starts with $S_2$ and ends with $C_1$, so no extra $S_2,C_1$ occurs across an expansion boundary, including between two expanded slots. These operations are inverse. In particular,

$$
 \rho_2^{-1}(R_2)\cong\{0,1\}^{T(R_2)}.                         \tag{9.1}
$$

Write $X_j=1$ when slot $j$ is expanded. If $g_E$ is the expansion indexed by $E\subseteq\{1,\ldots,T(R_2)\}$, the endpoint identity makes all factors outside the expanded slots identical, while the long route has one additional denominator $d_j$. Hence

$$
 P_N(g_E)=P_N(R_2)\prod_{j\in E}d_j^{-1},\qquad
 P_N(\rho_2=R_2)=P_N(R_2)\prod_{j=1}^{T(R_2)}(1+d_j^{-1}).             \tag{9.2}
$$

It follows, with no completion-count assumption, that under $P_N$ and conditionally on $R_2$ the variables $X_j$ are independent and

$$
 p_j:=P_N(X_j=1\mid R_2)=\frac1{1+d_j},\qquad
 L=|R_2|+\sum_jX_j.                                                   \tag{9.3}
$$

Under the separate law $\mu_N$, the same fibre has $2^{T(R_2)}$ words and therefore

$$
 \mu_N(\rho_2=R_2)=\frac{2^{T(R_2)}}{|\Omega_N|},\qquad
 \mu_N(X_j=1\mid R_2)=\frac12.                                    \tag{9.4}
$$

The representative weights in (9.2) and (9.4) are different pushforward laws. The estimates below use (9.2) only. The local exchange and Bernoulli mechanism are those of [1, Lemmas 4.1–4.2]; that paper allows exchanges at all indices with an additional predecessor condition, whereas this $R_2$ contracts only $S_2,C_1$. The endpoint and boundary argument above establishes this particular partition without identifying the two representative spaces.

### 9.2. Uniform deterministic bounds needed for all integer inputs

The deterministic inputs are [1, Theorems 1.1, 1.3, 1.6 and §2]. The following potential calculation records their correspondence to the present move labels within the proof. The terminal configuration has distinct nonconsecutive Fibonacci summands: the lexicographically decreasing potential $(U,h_2)$, with $U=\sum_i(i+2)h_i$, decreases under every move (under $S_2$ it preserves $U$ and decreases $h_2$). Write its terminal digits as $z_i\in\{0,1\}$. For a complete word $g$, let $c_k(g)$ and $s_k(g)$ count its $C_k$ and $S_k$ moves, respectively, suppressing $g$ in these counts when convenient, and put

$$
 D_N=2N-\sum_iF_{i+1}z_i,\qquad
 B_N=3N-\sum_i(i+2)z_i,\qquad
 W(g)=\sum_{k\ge2}(k-1)c_k(g).
$$

The potential $Q=\sum_iF_{i+1}h_i$ decreases by $1$ under $C_1$, increases by $1$ under $S_2$, and is unchanged by every other label. The potential $U$ decreases by $2$ under $C_1$, by $k$ under $C_k$ for $k\ge2$, by $1$ under $S_k$ for $k\ge3$, and is unchanged under $S_2$. Therefore

$$
 c_1-s_2=D_N,\qquad B_N-L=D_N+W(g),\qquad
 L=A_N-W(g),\quad A_N:=B_N-D_N.                              \tag{9.5}
$$

Since $\sum_iF_i z_i=N$ and $F_{i+1}\le2F_i$,

$$
 A_N=N+\sum_i(F_{i+1}-i-2)z_i
 \le3N-\sum_i(i+2)z_i<3N.                                          \tag{9.6}
$$

Thus every complete word has $L<3N$. A configuration of weight $N$ has no occupied bin $i\ge n+1$. For $n\ge2$, $C_n$ would consume $F_{n+1}>N$ and $S_n$ would consume $2F_n>F_{n+1}>N$, leaving only $C_1,\ldots,C_{n-1}$ and $S_2,\ldots,S_{n-1}$. At $N=1$, there are no legal labels. Hence

$$
 d(s)\le\max\{0,2n-3\},\qquad d_j+1\le2n=:b.                                \tag{9.7}
$$

The number of combines is $N-\sum_i z_i\le N-1$, and a contracted $C_2$ slot is one combine, so $T(R_2)\le N-1$.

### 9.3. Linear abundance of eligible slots under the actual $P_N$ law

Put $r=\lfloor N/12\rfloor$ and observe only the four labels

$$
 \mathcal A=\{C_1,C_2,C_3,S_2\}.
$$

Every label outside $\mathcal A$ weakly increases both $h_1$ and $h_2$. In a complete word $h_1$ ends at $z_1\le1$, and one observed label lowers $h_1$ by at most two. Therefore at least $(N-1)/2$ observed labels occur. For $N\ge24$, the first $3r$ observed labels exist and before each of them $h_1\ge N/2$.

If a prescribed label in $\mathcal A$ is legal and stays legal while no label in $\mathcal A$ is played, then its conditional probability of being the next observed label is at least $1/4$. Indeed, condition on the current full history. For every finite intervening word $h$ with no label in $\mathcal A$, let $w(h)$ be its conditional path probability, let $s_h$ be its endpoint, and let $a(s_h)$ count the available labels in $\mathcal A$. Persistence makes the prescribed label legal at every $s_h$. The game terminates, so persistence also ensures that some observed label occurs before termination. The disjoint events specifying $h$ and the first subsequent observed label therefore give

$$
 P_N(\text{next observed label is the prescribed one}\mid\text{history})
 =\sum_h\frac{w(h)}{d(s_h)}
 \ge\frac14\sum_h\frac{w(h)a(s_h)}{d(s_h)}=\frac14.
$$

The sums are finite by (9.6). This conditions on the actual history and assumes no independence between observation times.

Partition the first $3r$ observed labels into $r$ consecutive blocks. On the history before each block, $C_1$ remains legal until the next observed label; after one prescribed $C_1$ it remains legal for the second, and after two prescribed $C_1$'s the label $C_2$ is legal and the slot is eligible. The lower bound $h_1\ge N/2$ and $N\ge24$ cover all these intermediate states; the two prescribed $C_1$ moves add two tokens to bin 2, and all intervening unobserved moves weakly increase that height. Thus each block equals $C_1,C_1,C_2$ conditionally with probability at least $u=4^{-3}=1/64$. Let $I_j$ be the indicator of this event, using the full history through block $j$ as the block filtration. The adapted Bernoulli lower-tail lemma already proved in Section 4 gives

$$
 P_N\!\left(T(R_2)<\frac r{128}\right)
 \le P_N\!\left(\sum_{j=1}^rI_j<\frac{ru}{2}\right)
 \le \exp(-r/512).                                                \tag{9.8}
$$

A successful block contributes a distinct $C_2$ which is not contracted and whose pre-state has $h_2\ge2$, so it contributes an eligible slot of $R_2$.

### 9.4. A linear-probability degree bound for the actual representative

Let $D(R_2)=\sum_jd_j$, and let $\mathcal F_i$ be the sigma-algebra generated by the first $i$ actual move labels, with one absorbing symbol repeated after termination. For the original word define, with zero padding after termination up to the endpoint $3N$ from (9.6),

$$
 Y_i=\begin{cases}
       d(S_2s_{i-1})+1,&\text{if the $i$th move is an eligible }C_2,\\
       0,&\text{otherwise},
      \end{cases}\qquad
 W_*:=\sum_{i=1}^{3N}Y_i.                                           \tag{9.9}
$$

Applying $S_2$ changes only bins $1,2,3$, so only the six labels
$C_1,C_2,C_3,C_4,S_2,S_3$ can change availability. On a nonterminal state with $d(s)\ge1$, the conditional expectation of $Y_i$ is therefore at most

$$
 \frac{d(s)+7}{d(s)}\le8.                                          \tag{9.10}
$$

At a terminal state $Y_i=0$, so the same expectation bound holds without a denominator. Since $0\le Y_i\le b$, convexity of the exponential on $[0,1]$ gives

$$
 E\left(e^{Y_i/b}\mid\mathcal F_{i-1}\right)
 \le\exp\!\left(\frac{8(e-1)}b\right)\le e^{16/b}.
$$

Iterating through $3N$ padded positions and applying Markov's inequality yields

$$
 P_N(W_*\ge96N)\le e^{-48N/b}.                                    \tag{9.11}
$$

Conditionally on $R_2$, (9.3) shows that the eligible $C_2$ moves in the original word are exactly the unexpanded slots, and hence

$$
 W_*\ =\sum_j(d_j+1)(1-X_j),\qquad E[W_*\mid R_2]=D(R_2).             \tag{9.12}
$$

For completeness, if $Z_j=(d_j+1)(1-X_j)$, then $0\le Z_j\le b$ and $E[Z_j\mid R_2]=d_j$. Convexity gives

$$
 E(e^{-Z_j/b}\mid R_2)\le
 1-(1-e^{-1})d_j/b.
$$

Independence and $1/2-e^{-1}>1/8$ therefore imply

$$
 P_N\!\left(W_*<\frac{D(R_2)}2\mid R_2\right)
 \le\exp\!\left(-\frac{D(R_2)}{8b}\right).                         \tag{9.13}
$$

Combining (9.11)--(9.13),

$$
 P_N(D(R_2)\ge192N)
 \le e^{-48N/b}+e^{-24N/b}
 \le2e^{-12N/n}.                                                     \tag{9.14}
$$

### 9.5. The all-integer fluctuation bounds

Define the selected conditional variance

$$
 V(R_2):=\operatorname{Var}_{P_N}(L\mid R_2)
       =\sum_jp_j(1-p_j)=\sum_j\frac{d_j}{(1+d_j)^2}.               \tag{9.15}
$$

For every $d_j\ge1$, the inequality $1+d_j\le2d_j$ gives the first bound below. When $T(R_2)>0$, Cauchy–Schwarz applied to $T(R_2)=\sum_j\sqrt{d_j}\sqrt{1/d_j}$ gives the second:

$$
 \frac{d_j}{(1+d_j)^2}\ge\frac1{4d_j},\qquad
 \sum_j\frac1{d_j}\ge\frac{T(R_2)^2}{D(R_2)}.                       \tag{9.16}
$$

For $N\ge24$, put

$$
 G_N=\{T(R_2)\ge r/128,\ D(R_2)<192N\}.
$$

On $G_N$, the slot set is nonempty and (9.16) gives

$$
 V(R_2)\ge v_N:=\frac{r^2}{768\,128^2N}.                            \tag{9.17}
$$

The union bound in (9.8) and (9.14) gives

$$
 P_N(G_N^c)\le e^{-r/512}+2e^{-12N/n}.
$$

For $N\ge24$, $r\ge N/24$. Set

$$
 c=\frac1{768\,128^2\,24^2},\qquad a=\frac1{12288},\qquad b_0=12.
$$

Since $v_N\ge cN$, for every integer $N\ge24$ we have

$$
 P_N(V(R_2)<cN)\le P_N(G_N^c)\le e^{-aN}+2e^{-b_0N/n}.                            \tag{9.18}
$$

The inequality $F_{j+2}\ge2F_j$ gives $n(N)\le2\log_2N+2$ for every $N$. Put $C=2/\log 2+2$. For $N\ge e$, this implies $n(N)\le C\log N$. If $x=\log N$, then $N/(\log N)^2=e^x/x^2\ge x/6\to\infty$, using $e^x\ge x^3/6$. Consequently

$$
 \frac12\log N-aN\longrightarrow-\infty,\qquad
 \frac12\log N-\frac{12N}{n(N)}
 \le\frac12\log N-\frac{12N}{C\log N}\longrightarrow-\infty.
$$

Thus $N^{1/2}(e^{-aN}+2e^{-12N/n(N)})\to0$ through all integers. Fix an absolute integer $N_0\ge24$ beyond which this expression is at most one and the unmultiplied sum is at most $1/2$. This supplies both bounds used below with one finite threshold.

The law of total variance and (9.15) now give, for every integer $N\ge N_0$,

$$
 \operatorname{Var}_{P_N}(L)
 =\operatorname{Var}_{P_N}(E[L\mid R_2])+E_{P_N}V(R_2)
 \ge cN/2.                                                         \tag{9.19}
$$

Finally, use $K_0=\tfrac12\sqrt{\pi/2}$ from Lemma 4.3 above; [2, Theorem 1] supplies a stronger constant. Applying this existing independent-Bernoulli point-mass bound to (9.3) gives
$\sup_\ell P_N(L=\ell\mid R_2)\le K_0/\sqrt{V(R_2)}$ whenever $V(R_2)>0$. Splitting according to $G_N$ and $G_N^c$, which depend only on $R_2$, and using (9.17)--(9.18),

$$
 \sup_{\ell\in\mathbb Z}P_N(L=\ell)
 \le N^{-1/2}+\frac{K_0}{\sqrt{v_N}}
 \le \frac{K}{\sqrt N},\qquad
 K:=1+24\,128\sqrt{768}\,K_0.                                     \tag{9.20}
$$

Equations (9.18)--(9.20) prove Theorem 9.2, with $a,c$ as specified above, $b_0=12$, and $K$ as in (9.20), through every integer $N\ge N_0$. The exact $\mu_N$ fibre law remains (9.4); no $P_N$ degree or tail estimate is transferred to it. The exchange, conditional product calculation, deterministic bounds, adapted lower-tail inequality, and independent-trial point bound are reused inputs [1, Lemmas 4.1–4.2, Corollary 4.3 and Theorem 1.6; 2, Theorem 1; Lemmas 4.1 and 4.3 above]. The game-specific additions are the four-label observed-block estimate (9.8), the representative-degree estimate (9.14), and their consequences (9.18)--(9.20). ∎

## 追加锚（本行以下为增补区）

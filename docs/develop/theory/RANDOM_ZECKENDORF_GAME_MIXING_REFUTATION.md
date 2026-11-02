# Random Zeckendorf games: a temporal non-mixing theorem

## 1. Exact model and the target

Let \(F_1=1,F_2=2\), and \(F_{j+1}=F_j+F_{j-1}\) for \(j\ge2\).  A configuration is a finite multiset of the \(F_j\).  The legal labels are
\[
 C_1:\;2F_1\longrightarrow F_2,\qquad
 C_j:\;F_{j-1}+F_j\longrightarrow F_{j+1}\quad(j\ge2),
\]
and
\[
 S_2:\;2F_2\longrightarrow F_1+F_3,\qquad
 S_j:\;2F_j\longrightarrow F_{j-2}+F_{j+1}\quad(j\ge3).
\]
At each nonterminal configuration \(s\), every available label is chosen with probability
\[
 q(s,M)=\frac1{d(s)},\qquad d(s)=\#\{\text{available labels at }s\}.
\]
Thus a complete word \(g=(M_1,\ldots ,M_{L(g)})\) has probability
\[
 P_N(g)=\prod_{r=1}^{L(g)}
 \frac1{d(s_{r-1})},
\]
where \(s_{r-1}\) is the configuration before \(M_r\).  This is the measure \(P_N\) of Cheigh et al. [1, Definition 1.2 and §1.2].

For input \(N\), let
\[
 d_N=\max\{L(g):g\text{ is a complete legal game from }N F_1\}.
\]
For a random complete game, put \(X_{N,i}=1\) when the \(i\)-th actual move is a split and \(X_{N,i}=0\) when it is a combine; set \(X_{N,i}=0\) after the game terminates, up to the fixed row endpoint \(d_N\).  For \(1\le a\le b\le d_N\), write
\[
 \mathcal F^{(N)}_{a,b}=\sigma(X_{N,a},\ldots ,X_{N,b}),
 \qquad
 \mathcal F^{(N)}_{0,m}=\sigma(X_{N,1},\ldots ,X_{N,m}).
\]
For \(k\ge0\), define
\[
 \alpha_N(k)=
 \sup_{\substack{m\ge1\\m+k\le d_N}}
 \ \sup_{\substack{A\in\mathcal F^{(N)}_{0,m}\\
                    B\in\mathcal F^{(N)}_{m+k,d_N}}}
 \left|P_N(A\cap B)-P_N(A)P_N(B)\right|,
\]
and put \(\alpha_N(k)=0\) if the outer supremum has no admissible \(m\).  This is the absolute-covariance convention in [1, equation (7)].

The question is whether there are \(\delta,C>0\) such that, for every \(N\),
\[
 \sum_{k=0}^{\infty}(k+1)^2
 \alpha_N(k)^{\delta/(4+\delta)}<C. \tag{Q}
\]

We prove the negation of (Q) for the actual locally uniform label law.

## 2. Fibonacci rows and deterministic bounds

Fix \(N=F_n\), with \(n\ge 6\), and write
\[
 M=2n,\qquad C=N-1.
\]
A combine reduces the number of tokens by one and a split preserves it.  The terminal Zeckendorf decomposition of \(F_n\) is the one token \(F_n\), so every complete game has exactly \(C=N-1\) combines.  Consequently, if \(L\) is its length and \(S=\sum_{i=1}^{d_N}X_{N,i}\) is its total number of splits, then
\[
 L=C+S. \tag{2.1}
\]
No occupied index can exceed \(n\), because \(F_{n+1}>F_n\) and the weighted sum of the configuration is conserved.  Hence the only possible labels are
\[
 C_1,\ldots ,C_{n-1},\quad S_2,\ldots ,S_{n-1},
\]
at most \(2n-3<M\) labels.  Every prescribed legal next label therefore has conditional probability at least \(M^{-1}\).  Also, after \(t\) moves the number \(h_1(t)\) of \(F_1\)-tokens satisfies
\[
 h_1(t)\ge N-2t, \tag{2.2}
\]
because a move removes at most two \(F_1\)-tokens.

We use the linear longest-game estimate of Cheigh et al. [1, Theorem 1.6].  On \(N=F_n\) it gives
\[
 d_N<3N \tag{2.3}
\]
for all \(n\ge6\).

## 3. A stopped-prefix product law

For \(1\le c\le C\), let \(\tau_c\) be the time of the \(c\)-th combine.  Since \(L\ge C\), \(\tau_c\) is defined on every game.

**Lemma 3.1 (the \(C_2\leftrightarrow(S_2,C_1)\) interchange).**
Suppose a configuration has heights \((a,b,d)\) in bins \(1,2,3\).  If \(C_2\) is legal and \(b\ge2\), then both words \(C_2\) and \(S_2,C_1\) are legal and have the same endpoint:
\[
 (a,b,d)\xrightarrow{C_2}(a-1,b-1,d+1)
\]
and
\[
 (a,b,d)\xrightarrow{S_2}(a+1,b-2,d+1)
 \xrightarrow{C_1}(a-1,b-1,d+1).
\]
Conversely, legality of \(S_2,C_1\) implies legality of \(C_2\) and \(b\ge2\).

*Proof.*  The displayed height changes are the definitions of the three labels.  The first route requires \(a,b\ge1\).  The second requires \(b\ge2\) and, after \(S_2\), \(a+1\ge2\), hence \(a\ge1\).  These are exactly the stated conditions. ∎

For a legal word ending at \(\tau_c\), sum the probabilities of all complete continuations.  The conditional continuation probability is one, so the word's probability is exactly the product of its local reciprocal denominators, including when the word itself is terminal.

Contract every consecutive occurrence of \(S_2,C_1\) in such a word to \(C_2\), repeatedly from left to right.  The occurrences cannot overlap.  By Lemma 3.1, contraction preserves every subsequent configuration.  The resulting representative \(R\) contains no \(S_2,C_1\).  Conversely, an occurrence of \(C_2\) in \(R\) is *eligible* when the alternative \(S_2,C_1\) is legal; expanding any set of eligible occurrences gives a legal word ending at the same \(c\)-th combine.  Since each expansion creates its own \(S_2,C_1\) and the endpoint after the pair is unchanged, expansions at distinct eligible occurrences do not alter one another's eligibility and create no boundary pair.  Thus the stopped prefixes are partitioned by their unique representative \(R\) and independent expansion choices.

Let \(t_j\) be the configuration immediately after the \(S_2\) in the long route at eligible slot \(j\), and put \(d_j=d(t_j)\).  The denominator before the first move is the same for \(C_2\) and \(S_2\); all later denominators are shared because the endpoints agree.  Therefore replacing the short route by the long route multiplies the prefix probability by exactly \(d_j^{-1}\).  Conditional on \(R\), the expansion indicators \(B_j\) are independent Bernoulli variables with
\[
 p_j=P(B_j=1\mid R)=\frac1{1+d_j},
 \qquad
 \frac1{M+1}\le p_j\le\frac12. \tag{3.1}
\]
If \(T(R)\) is the number of eligible slots, then
\[
 \tau_c=|R|+\sum_{j=1}^{T(R)}B_j
 \quad\text{conditional on }R. \tag{3.2}
\]
This is a conditional product law for stopped prefixes; it asserts no independence for the original time-indexed sequence \((X_{N,i})\). ∎

## 4. Many slots and anti-concentration of \(\tau_c\)

We first record the adapted lower-tail estimate used twice below.

**Lemma 4.1 (adapted Bernoulli lower tail).**
Let \(I_1,\ldots ,I_r\in\{0,1\}\) be adapted to \((\mathcal G_j)\), and suppose
\[
 P(I_j=1\mid\mathcal G_{j-1})\ge u
\]
almost surely, where \(0<u\le1\).  Then
\[
 P\!\left(\sum_{j=1}^r I_j\le\frac{ru}{2}\right)
 \le e^{-ru/8}. \tag{4.1}
\]

*Proof.*  With \(\lambda=\log2\),
\[
 E(e^{-\lambda I_j}\mid\mathcal G_{j-1})
 \le1-u+ue^{-\lambda}=1-\frac u2\le e^{-u/2}.
\]
Iterating and applying Markov's inequality gives
\[
 P\!\left(\sum I_j\le ru/2\right)
 \le e^{\lambda ru/2}e^{-ru/2}
 =e^{-ru(1-\log2)/2}\le e^{-ru/8}.
\]
∎

**Lemma 4.2 (slot abundance).**
For \(6\le c\le N/4\),
\[
 P_N\!\left(T(R)<\frac{c}{12M^3}\right)
 \le \exp\!\left(-\frac{c}{48M^3}\right), \tag{4.2}
\]
for all sufficiently large \(n\), where \(R\) is the representative of the prefix ending at \(\tau_c\).

*Proof.*  The first \(c\) moves exist because \(\tau_c\ge c\).  By (2.2), throughout those moves
\[
 h_1\ge N-2c\ge N/2.
\]
For large \(N\), each disjoint triple among the first \(\lfloor c/3\rfloor\) triples can therefore realize
\[
 C_1,C_1,C_2:
\]
after the two \(C_1\)'s there are at least two new \(F_2\)-tokens and at least one \(F_1\)-token remains, so \(C_2\) is legal.  Conditional on the preceding moves, the probability of this triple is at least
\[
 u=M^{-3}. \tag{4.3}
\]
Let \(I_j\) indicate success of the \(j\)-th triple.  By Lemma 4.1 and \(\lfloor c/3\rfloor\ge c/6\),
\[
 P_N\!\left(\sum I_j<\frac{c}{12M^3}\right)
 \le e^{-c/(48M^3)}.
\]
A successful triple contributes a distinct \(C_2\) to the representative: it cannot be the contracted member of an \(S_2,C_1\) pair, and contractions before it preserve the state before its \(C_2\).  Hence \(T(R)\ge\sum I_j\). ∎

**Lemma 4.3 (Poisson-binomial point bound).**
If \(Z=\sum_{j=1}^r B_j\) is a sum of independent Bernoulli variables and \(V=\sum_jp_j(1-p_j)>0\), then
\[
 \sup_{z\in\mathbb Z}P(Z=z)\le\frac{K_0}{\sqrt V},
 \qquad K_0=\frac1{2}\sqrt{\frac\pi2}. \tag{4.4}
\]

*Proof.*  Fourier inversion and
\[
 |1-p+pe^{it}|^2
 =1-4p(1-p)\sin^2(t/2)
\]
give
\[
 |\mathbb E e^{itZ}|
 \le\exp\!\left(-2V\sin^2(t/2)\right).
\]
For \(|t|\le\pi\), \(\sin(|t|/2)\ge |t|/\pi\).  Therefore
\[
 P(Z=z)\le\frac1{2\pi}\int_{-\pi}^{\pi}
 e^{-2Vt^2/\pi^2}\,dt
 \le\frac1{2}\sqrt{\frac\pi{2V}},
\]
which is (4.4). ∎

**Proposition 4.4 (anti-concentration at a combine time).**
There is a universal \(K\) such that, for \(6\le c\le N/4\), every integer interval \(I\) containing at most \(h\) integers satisfies
\[
 P_N(\tau_c\in I)
 \le e^{-c/(48M^3)}
   +K\,h\,\frac{M^2}{\sqrt c}. \tag{4.5}
\]

*Proof.*  Conditional on a representative \(R\), Lemma 3.1 gives (3.2).  On the event \(T(R)\ge c/(12M^3)\), (3.1) implies
\[
 V=\sum_jp_j(1-p_j)
 \ge\frac{T(R)}{2(M+1)}
 \ge\frac{c}{48M^4}
\]
for \(M\ge2\).  Lemma 4.3 bounds the conditional probability of each integer value by \(K_0M^2/\sqrt c\), and hence the probability of \(I\) by \(K_0hM^2/\sqrt c\).  The exceptional representatives have total probability bounded by (4.2), which is paid once, not once per point of \(I\).  Enlarging the universal constant gives (4.5). ∎

## 5. The early split count has polynomial-window small mass

Put
\[
 m=\lfloor N/8\rfloor,\qquad
 S_m=\sum_{i=1}^{m}X_{N,i},\qquad
 D_m=m-S_m.
\]
There is no termination before move \(m\), because \(L\ge C=N-1>m\).  By (2.2), \(C_1\) is available throughout the first \(m\) moves, and the conditional probability of a combine at each such move is at least \(M^{-1}\).  Lemma 4.1 gives
\[
 P_N\!\left(D_m<\frac{m}{2M}\right)
 \le e^{-m/(8M)}. \tag{5.1}
\]
Let \(v=M^2\).  The probability that the last \(v\) moves before \(m\) contain no combine is at most
\[
 (1-M^{-1})^v\le e^{-M}. \tag{5.2}
\]
If \(D_m=c\) and there is a combine in that interval, then \(\tau_c\in(m-v,m]\).  Thus, for any integer interval \(J\) with at most \(h\) points, (4.5), (5.1), and a union over the possible \(c\in J\cap[m/(2M),m]\) yield
\[
\begin{aligned}
 P_N(D_m\in J)
 &\le e^{-m/(8M)}+e^{-M}\\
 &\quad+h\left[
 e^{-m/(96M^4)}
 +K(v+1)\frac{M^2}{\sqrt{m/(2M)}}\right]. \tag{5.3}
\end{aligned}
\]
For large \(n\), the values \(c\) in the union satisfy \(6\le c\le m\le N/4\), so Proposition 4.4 applies.  Since \(N=F_n\) grows exponentially in \(n\), while \(M=2n\), the right side of (5.3) tends to zero whenever \(h\) is bounded by any fixed power of \(M\).  Because \(S_m=m-D_m\), the same is true with \(D_m\) replaced by \(S_m\):
\[
 \sup_{\substack{J\subset\mathbb Z\\ |J|\le H_n}}
 P_N(S_m\in J)\longrightarrow0
 \quad\text{for every fixed polynomial }H_n\text{ in }M. \tag{5.4}
\]

## 6. A suffix statistic recovers the early count

Let \(L\) be the actual length, let
\[
 J=\max\{i\le d_N:X_{N,i}=1\},
\]
with \(J=0\) if there is no split, and define the trailing combine run \(R=L-J\).  At a configuration with \(H>n+2\) tokens, either a bin \(i\ge2\) contains at least two tokens, in which case a split is available, or every such bin has height at most one and then \(h_1\ge4\); in the latter case \(C_1,C_1,S_2\) is legal.  Hence, from every configuration with \(H>n+2\), the conditional probability of seeing a split within the next three moves is at least \(M^{-3}\).

If \(R\ge r+n+2\), then at the beginning of the final combine run there are \(1+R\ge r+n+3\) tokens.  During the first \(r\) combines, each three-move block begins with more than \(n+2\) tokens.  For a fixed possible beginning time, conditional multiplication bounds the probability of those \(r\) combines by
\[
 (1-M^{-3})^{\lfloor r/3\rfloor}.
\]
A union over the at most \(d_N+1\) possible beginning times is valid even though \(J\) is not a stopping time.  Consequently
\[
 P_N(R\ge r+n+2)
 \le(d_N+1)(1-M^{-3})^{\lfloor r/3\rfloor}. \tag{6.1}
\]
Choose \(r=M^5\) and put
\[
 b=M^5+n+2.
\]
Using (2.3),
\[
 P_N(R>b)\le(3N+1)(1-M^{-3})^{\lfloor M^5/3\rfloor}
 \longrightarrow0. \tag{6.2}
\]

Set
\[
 k=M^6,\qquad q=m+k.
\]
For large \(n\), \(q<C-b\), and \(q\le d_N\).  From the future coordinates alone define
\[
 V=\sum_{i=q}^{d_N}X_{N,i},\qquad
 J_q=\max\{i\ge q:X_{N,i}=1\},
\]
where \(J_q=q-1\) if the set is empty, and then
\[
 U=J_q-C-V. \tag{6.3}
\]
Thus \(U\) is measurable with respect to \(\mathcal F^{(N)}_{q,d_N}\).

On \(R\le b\), (6.2) and \(J=L-R\ge C-b>q\) imply \(J_q=J\).  Let
\[
 G=\sum_{i=m+1}^{q-1}X_{N,i}.
\]
Using zero padding and (2.1),
\[
 J+R=L=C+S_m+G+V,
\]
so
\[
 U=S_m+G-R,\qquad |U-S_m|\le(q-m-1)+b\le k+b. \tag{6.4}
\]

## 7. Covariance at a polynomially diverging lag

Choose the least integer \(a_n\) with
\[
 P_N(S_m\le a_n)\ge\frac12,
\]
and put
\[
 A_n=\{S_m\le a_n\},\qquad B_n=\{U\le a_n\}.
\]
Then \(A_n\in\mathcal F^{(N)}_{0,m}\) and \(B_n\in\mathcal F^{(N)}_{q,d_N}\).  By (5.4), the largest atom of \(S_m\) tends to zero, hence
\[
 P_N(A_n)\longrightarrow\frac12. \tag{7.1}
\]
If \(A_n\triangle B_n\) occurs on \(R\le b\), (6.4) implies
\[
 |S_m-a_n|\le k+b.
\]
Therefore
\[
 P_N(A_n\triangle B_n)
 \le P_N(R>b)+P_N(|S_m-a_n|\le k+b)
 \longrightarrow0, \tag{7.2}
\]
because \(k+b=O(M^6)\) and (5.4) applies.

For events \(A,B\), writing \(p=P_N(A)\), one has
\[
 \left|
 [P_N(A\cap B)-P_N(A)P_N(B)]-p(1-p)
 \right|
 \le2P_N(A\triangle B). \tag{7.3}
\]
Indeed, \(|P_N(A\cap B)-p|\le P_N(A\triangle B)\) and
\(|P_N(B)-p|\le P_N(A\triangle B)\).  Equations (7.1)--(7.3) give
\[
 \left|P_N(A_n\cap B_n)-P_N(A_n)P_N(B_n)\right|
 \longrightarrow\frac14. \tag{7.4}
\]
Since the absolute covariance of two events is at most \(1/4\), (7.4) and the definition of \(\alpha_N\) imply
\[
 \alpha_{F_n}((2n)^6)\longrightarrow\frac14. \tag{7.5}
\]

## 8. Negative answer to the original weighted condition

**Theorem 8.1 (refutation of Question 6.5 / chapter Question 3).**
For every \(\delta>0\),
\[
 \sup_{N\ge1}\sum_{k=0}^{\infty}(k+1)^2
 \alpha_N(k)^{\delta/(4+\delta)}=\infty. \tag{8.1}
\]
Consequently, there do not exist \(\delta,C>0\) satisfying (Q).

*Proof.*  Fix \(\delta>0\), and set \(p=\delta/(4+\delta)>0\).  By (7.5), for all sufficiently large \(n\),
\[
 \alpha_{F_n}((2n)^6)\ge\frac18.
\]
The single summand at \(k=(2n)^6\) is therefore at least
\[
 \bigl((2n)^6+1\bigr)^2\,8^{-p},
\]
which tends to infinity.  Hence the supremum in (8.1) is infinite, proving the exact negation of (Q). ∎

**Corollary 8.2.**  For each fixed \(k\ge0\),
\[
 \sup_N\alpha_N(k)=\frac14.
\]

*Proof.*  The upper bound is the universal event-covariance bound.  Given fixed \(k\), choose \(n\) so large that \((2n)^6\ge k\).  For any row, \(\alpha_N(k)\ge\alpha_N((2n)^6)\), because enlarging the future sigma-algebra by moving its first coordinate left cannot decrease the supremum.  Apply (7.5) along \(N=F_n\). ∎

The conclusion concerns the original locally uniform label law, the longest complete-game row endpoint, zero padding, and the full generated past and future event sigma-algebras.  It does not concern the uniform measure on complete games, accelerated move rules, atom-only events, or the Gaussian limit conjecture.

## References

[1] Cheigh, Dantas e Moura, Jeong, Lehmann Duke, Milgrim, Miller, and Ngamlamai, *Towards the Gaussianity of Random Zeckendorf Games*, arXiv:2210.11038v1, Definition 1.2, §1.2, Theorem 1.6, Lemma 4.1, Lemma 4.2, Corollary 4.3, Lemma 4.4, equations (7) and (11), Question 6.5; author chapter version, Chapter Question 3 and Theorem 11.

## 追加锚（本行以下为增补区）

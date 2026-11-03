# 1. Nonbinary mutual abelian-border joint limits

**Definition 1.1 (Words and Parikh vectors).** Let $q\ge3$ be an integer and let $A$ be a finite alphabet of cardinality $q$. Write $e_a$ for the coordinate vector of $a\in A$ in $\mathbb Z^A$. For a word $w=w_1\cdots w_m$, put

$$
\operatorname{Par}(w)=\sum_{j=1}^m e_{w_j}.
$$

The words $w$ and $w'$ are abelian equivalent precisely when their Parikh vectors agree. For $0\le t\le m$, let $\operatorname{pre}_t(w)=w_1\cdots w_t$ and $\operatorname{suf}_t(w)=w_{m-t+1}\cdots w_m$; the factors of length zero are empty.

**Definition 1.2 (The two border events).** For each integer $n\ge1$, let $U_n=u_1\cdots u_n$ and $V_n=v_1\cdots v_n$ be independent uniform words in $A^n$. Within this finite model all $2n$ letter coordinates $u_j,v_j$ are independent and uniform on $A$. Denote its probability law by $\mathbb P_n$. Define

$$
\begin{aligned}
I_n&=\left\{\exists r\in\{1,\ldots,n-1\}:
\operatorname{Par}(\operatorname{suf}_r(U_n))
=\operatorname{Par}(\operatorname{pre}_r(V_n))\right\},\\
E_n&=\left\{\exists s\in\{1,\ldots,n-1\}:
\operatorname{Par}(\operatorname{pre}_s(U_n))
=\operatorname{Par}(\operatorname{suf}_s(V_n))\right\}.
\end{aligned}
$$

The two existential quantifiers are separate. No restriction is placed on $r+s$, and no relation between the witnesses is required. Every witness is nonempty and proper. These are the internal and external abelian-border conditions of Maity–Krishna [MK, Definition 1.1], with the alphabet allowed to have $q$ letters.

**Definition 1.3 (Return parameter).** On an infinite product probability space, let $(X_j)_{j\ge1}$ and $(Y_j)_{j\ge1}$ be independent sequences of independent uniform $A$-valued letters. Put

$$
S_0=0,\qquad S_t=\sum_{j=1}^t(e_{X_j}-e_{Y_j}),\qquad
T=\inf\{t\ge1:S_t=0\},
$$

where $\inf\varnothing=\infty$. Write

$$
r_q=\mathbb P(T<\infty),\qquad
F_q(k)=\mathbb P(T\le k)\quad(k\ge0),\qquad
p_q(1)=r_q,\quad p_q(0)=1-r_q.
$$

In particular $F_q(0)=0$. The increment law is

$$
\mathbb P(e_{X_j}-e_{Y_j}=z)=
\begin{cases}
q^{-1},&z=0,\\
q^{-2},&z=e_a-e_b\text{ for distinct }a,b\in A,\\
0,&\text{otherwise}.
\end{cases}
$$

Thus equal letters give a zero increment and a return at time one. They are included in $T$ and $r_q$. Relabeling the alphabet permutes coordinates and preserves returns, so $r_q$ depends only on $q$.

## 2. The joint law on the same word pair

**Theorem 2.1 (Opposite abelian-border indicators).** For every integer $q\ge3$, every alphabet $A$ of cardinality $q$, and every $a,b\in\{0,1\}$, the events in Definition 1.2 satisfy

$$
\lim_{n\to\infty}
\mathbb P_n\bigl(\mathbf 1_{I_n}=a,\ \mathbf 1_{E_n}=b\bigr)
=p_q(a)p_q(b).
$$

Consequently, if $M_q(n)$ counts ordered pairs in $A^n\times A^n$ having both kinds of proper abelian border, and $\overline M_q(n)$ counts those having neither kind, then

$$
\lim_{n\to\infty}\frac{M_q(n)}{q^{2n}}=r_q^2,
\qquad
\lim_{n\to\infty}\frac{\overline M_q(n)}{q^{2n}}=(1-r_q)^2.
$$

**Proof.** Fix $q$ and $A$. For each $n$, define from the actual pair $(U_n,V_n)$

$$
D_j^{(n)}=e_{u_{n+1-j}}-e_{v_j}\qquad(1\le j\le n).
$$

Distinct indices $j$ use disjoint letter coordinates, so the increments $D_1^{(n)},\ldots,D_n^{(n)}$ are independent and have exactly the law in Definition 1.3. For $1\le r<n$,

$$
\sum_{j=1}^r D_j^{(n)}
=\operatorname{Par}(\operatorname{suf}_r(U_n))
-\operatorname{Par}(\operatorname{pre}_r(V_n)).
$$

For $1\le s<n$ the opposite end of this very same increment sequence satisfies

$$
\begin{aligned}
\sum_{j=n-s+1}^nD_j^{(n)}
&=\sum_{i=1}^s(e_{u_i}-e_{v_{n+1-i}})\\
&=\operatorname{Par}(\operatorname{pre}_s(U_n))
-\operatorname{Par}(\operatorname{suf}_s(V_n)).
\end{aligned}
$$

It follows that $I_n$ is existence of a zero prefix sum of length between $1$ and $n-1$, whereas $E_n$ is existence of a zero suffix sum in that range. Reversing the finite independent increment sequence preserves its law. In particular,

$$
\mathbb P_n(I_n)=\mathbb P_n(E_n)=F_q(n-1).
$$

For an integer $k\ge1$ and $n\ge2k$, define $I_{n,k}$ and $E_{n,k}$ by restricting the respective witnesses in Definition 1.2 to $1\le r\le k$ and $1\le s\le k$. These are proper witnesses since $k<n$. The event $I_{n,k}$ depends only on $D_1^{(n)},\ldots,D_k^{(n)}$, and $E_{n,k}$ depends only on $D_{n-k+1}^{(n)},\ldots,D_n^{(n)}$. These two index sets are disjoint, including when $n=2k$. Hence $I_{n,k}$ and $E_{n,k}$ are independent, and each has probability $F_q(k)$.

Put $p_{q,k}(1)=F_q(k)$ and $p_{q,k}(0)=1-F_q(k)$. For all $a,b\in\{0,1\}$ and $n\ge2k$,

$$
\mathbb P_n\bigl(\mathbf 1_{I_{n,k}}=a,\ \mathbf 1_{E_{n,k}}=b\bigr)
=p_{q,k}(a)p_{q,k}(b).
$$

The truncation events are contained in their respective full events. The probability of losing an internal event is therefore exactly

$$
\mathbb P_n(I_n\setminus I_{n,k})
=F_q(n-1)-F_q(k)\le r_q-F_q(k).
$$

The same equality and bound hold with $E$ in place of $I$. In particular, these differences require absence of every witness of length at most $k$. They are controlled by the first-return distribution, rather than by the event that some return occurs after $k$.

Outside

$$
B_{n,k}=(I_n\setminus I_{n,k})\cup(E_n\setminus E_{n,k}),
$$

both full indicators equal their truncated indicators. Thus for every $a,b\in\{0,1\}$,

$$
\left|
\mathbb P_n\bigl(\mathbf 1_{I_n}=a,\ \mathbf 1_{E_n}=b\bigr)
-p_{q,k}(a)p_{q,k}(b)
\right|
\le\mathbb P_n(B_{n,k})
\le2\bigl(r_q-F_q(k)\bigr).
$$

This bounds every discrepancy, including those whose full witnesses have overlapping letter sets or whose two lengths sum to more than $n$. No independence of such full witnesses has been used.

The events $\{T\le k\}$ increase to $\{T<\infty\}$. Countable additivity, through continuity of probability from below, gives $F_q(k)\to r_q$. For fixed $k$ the displayed bound holds for every $n\ge2k$. The triangle inequality yields

$$
\begin{aligned}
\limsup_{n\to\infty}
\left|
\mathbb P_n\bigl(\mathbf 1_{I_n}=a,\ \mathbf 1_{E_n}=b\bigr)
-p_q(a)p_q(b)
\right|
\le{}&2\bigl(r_q-F_q(k)\bigr)\\
&+\left|p_{q,k}(a)p_{q,k}(b)-p_q(a)p_q(b)\right|.
\end{aligned}
$$

Letting $k\to\infty$ makes the right-hand side zero, proving the joint limit for all four choices of $(a,b)$. Finally, every ordered word pair has probability $q^{-2n}$, so the cells $(1,1)$ and $(0,0)$ give the two counting limits. $\square$

## 3. Mathematical sources and extent

**Mathematical citation 3.1 (Border definitions and counting question).** [MK] Anuran Maity and K. V. Krishna, *Mutually Abelian-Bordered Binary Words*, [arXiv:2509.20773v1](https://arxiv.org/html/2509.20773v1), Definitions 1.1–1.2 and Section 4, Conclusion, item 3; published in SOFSEM 2026, [DOI 10.1007/978-3-032-17801-5_6](https://doi.org/10.1007/978-3-032-17801-5_6). The definitions of internal and external borders, mutually bordered pairs and pairs with neither border are `literature-attested`. The source treats binary words and asks for the number of mutually abelian-bordered pairs of nonbinary words. Theorem 2.1 supplies asymptotic densities for the latter setting; exact finite counts and unequal word lengths are outside its conclusion.

**Mathematical citation 3.2 (Return interpretation and joint inference).** N. Rampersad, M. Rigo and P. Salimov, *On the Number of Abelian Bordered Words*, DLT 2013, LNCS 7907, pp. 420–432, [DOI 10.1007/978-3-642-38771-5_37](https://doi.org/10.1007/978-3-642-38771-5_37), Section 4, Definition 3 and Propositions 4–5, describes letter-difference paths in the coordinate-sum-zero lattice, with equal letters represented by colored loops, for a single word. That single-word dictionary is `literature-attested`. The same-pair prefix/suffix identities, first-witness truncation and resulting joint indicator law in Theorem 2.1 are `repo-derived`; the two-boundary inference is given in its proof. No claim of worldwide originality is attached to this designation. The proof uses neither a recurrence classification nor removal of zero increments, and it asserts no rate uniform in $q$.

## 追加锚（本行以下为增补区）

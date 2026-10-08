# Pauli-weight geometry of the SIC k-fidelities of qubit maps

This volume is reference input; nothing in it is kernel-verified. Its text is append-only: corrections and additions belong after the final append anchor.

## 1. Scope

The $k$-fidelities of an $n$-qubit map are obtained by truncating the expansion of the process fidelity over tensor products of single-qubit SIC states. This volume shows that every $k$-fidelity is a fixed linear functional of the Pauli-weight distribution of the map, with an explicit binomial coefficient for each weight. From this formula it derives the alternating sign of the truncation error, the exact set of pairs ($k$-fidelity, process fidelity) realised by $n$-qubit channels, a linear relation among all $k$-fidelities valid for every trace-preserving map, and the joint range of $(F_0,\dots,F_{n-1})$ as an explicit simplex.

## 2. Notation and cited facts

**Cited facts.** (a) J. M. Renes, R. Blume-Kohout, A. J. Scott and C. M. Caves, *Symmetric informationally complete quantum measurements*, J. Math. Phys. 45 (2004) 2171, arXiv:quant-ph/0310075, Section 2: every SIC-POVM in dimension $d$ is a spherical 2-design, so that $\sum_{k=1}^{d^2}(\lvert\phi_k\rangle\langle\phi_k\rvert)^{\otimes 2}=d^2K_2$ with $K_2=\frac{2}{d(d+1)}\Pi_{\mathrm{sym}}$, where $\Pi_{\mathrm{sym}}$ is the projector onto the symmetric subspace. For $d=2$ and $\Pi_{\mathrm{sym}}=\frac12(I\otimes I+S)$, with $S$ the swap operator, this reads

$$
\sum_{a=1}^{4}\rho_a\otimes\rho_a=\frac23\,(I\otimes I+S)
$$

for every qubit SIC $\lbrace\rho_a\rbrace$. Taking the partial trace over the second factor gives $\sum_{a}\rho_a=2I$.

(b) S. Greenaway, F. Sauvage, K. E. Khosla and F. Mintert, *Efficient assessment of process fidelity*, Phys. Rev. Research 3 (2021) 033031, arXiv:2102.08101, Section II B: the process fidelity of an $n$-qubit map is written through the inverse of the overlap matrix of the $4^n$ product SIC states; the inverse is expanded by the number of factors of a single-qubit matrix $A$, and truncating this expansion defines the $k$-fidelities, the $0$-fidelity being the leading term and the $n$-fidelity coinciding with the process fidelity. Section VI (Outlook) of the same paper lists as a potentially valuable route for further work to investigate any relationship between the hierarchy of $k$-fidelities and the efficient evaluation of the process fidelity of Pauli channels from the eigenvalues of the superoperator matrix, noting that the $k$-fidelities are not restricted to Pauli channels.

(c) K. Mayer, *A short note on the 0-fidelity*, arXiv:2109.09629. Section I: the $0$-fidelity does not depend on the choice of single-qubit SIC-POVMs, which follows from the facts that $F_0$ is quadratic in the SIC projectors and that SIC-POVMs are 2-designs. Theorem 1: for every $n$-qubit CPTP map, $1-\frac32(1-F_0)\le F\le F_0$. In Section III the minimum and the maximum of $F$ over CPTP maps with prescribed $F_0$ are posed as semidefinite programs; the minimum is reported to equal $1-\frac32(1-F_0)$ for $n\le4$, followed by the sentence "This leads us to conjecture that the lower bound in Th. 1 is tight for all $n$", the maximum is computed numerically and shown in a figure, and for $n=1$ the value of $F$ is stated to be determined by $F_0$.

(d) Used here as cited steps and not as load-bearing items of this volume: in the notation of Convention 2.1, $F_0=\sum_\beta 3^{-\lvert\beta\rvert}q_\beta$; and the lower bound of (c) is attained for every $n\ge2$ and every $F_0\in[\frac13,1]$. Stance: repo-derived (used as a cited step; not a load-bearing item of this volume). The first statement is recovered below as the case $k=0$ of Theorem 4.1, the second as part of Theorem 5.1.

(e) A. N. Korotkov, *Error matrices in quantum process tomography*, arXiv:1309.6405, Section II, Eqs. (1)–(3) and the following paragraph: the process matrix $\chi$ of a quantum operation in the (unnormalised) Pauli basis, $\rho\mapsto\sum_{m,n}\chi_{mn}E_m\rho E_n^\dagger$, is Hermitian with non-negative eigenvalues, and the operation is trace-preserving if and only if $\sum_{m,n}\chi_{mn}E_n^\dagger E_m=I$. Section II, Eq. (5), and Section III, Eqs. (12)–(13): the process fidelity of a trace-preserving operation relative to a desired unitary is $\operatorname{Tr}(\chi_{\mathrm{des}}\chi)$, and when the desired operation is the identity, $\chi_{\mathrm{des}}$ has the single non-zero entry $1$ at the identity label, so the process fidelity is $\chi_{00}$.

**Convention 2.1 (Pauli labels and Pauli-weight distribution).** Write $P_0=I$, $P_1=X$, $P_2=Y$, $P_3=Z$ for the single-qubit Pauli matrices. Fix $n\ge1$ and $d=2^n$. For $\beta=(\beta_1,\dots,\beta_n)\in\lbrace0,1,2,3\rbrace^n$ put $P_\beta=P_{\beta_1}\otimes\cdots\otimes P_{\beta_n}$ and let $\lvert\beta\rvert$ be the number of indices $i$ with $\beta_i\ne0$. The $d^4$ maps $X\mapsto P_\beta XP_\gamma$ form a basis of the space of linear maps on $M_d(\mathbb C)$, so every linear map $\Lambda$ on $M_d(\mathbb C)$ has a unique expansion

$$
\Lambda(X)=\sum_{\beta,\gamma}\chi_{\beta\gamma}\,P_\beta XP_\gamma .
$$

Put $q_\beta=\chi_{\beta\beta}$ (the Pauli-twirl weights of $\Lambda$) and $Q_w=\sum_{\lvert\beta\rvert=w}q_\beta$ for $0\le w\le n$. The following standard facts are used: if $\Lambda$ is completely positive, the matrix $\chi$ is positive semidefinite, so $q_\beta\ge0$; if $\Lambda$ is trace-preserving, then $\sum_{\beta,\gamma}\chi_{\beta\gamma}P_\gamma P_\beta=I$, and taking the trace gives $\sum_\beta q_\beta=1$; conversely, for every probability vector $(q_\beta)_\beta$ the Pauli channel $X\mapsto\sum_\beta q_\beta P_\beta XP_\beta$ is completely positive and trace-preserving with Pauli-twirl weights $q_\beta$. Moreover, for the process fidelity $F$ of Definition 2.3 one has $F(\Lambda)=q_0=Q_0$; used as a cited step: since $\langle\Phi\rvert(I\otimes P_\beta)\lvert\Phi\rangle=d^{-1}\operatorname{Tr}P_\beta=\delta_{\beta0}$, one gets $F(\Lambda)=\sum_{\beta,\gamma}\chi_{\beta\gamma}\delta_{\beta0}\delta_{\gamma0}=\chi_{00}$, and this computation holds for every linear map $\Lambda$. Stance: repo-derived for the notation $q_\beta$, $Q_w$; literature-attested for the three facts on the process matrix and for $F=\chi_{00}$ (cited fact (e); the converse fact holds because the Pauli channel has diagonal $\chi$ with entries $q_\beta\ge0$, which is positive semidefinite and satisfies the trace-preservation condition of cited fact (e) as $\sum_\beta q_\beta=1$).

**Definition 2.2 (Qubit SIC, overlap matrix, the matrix $A$).** A qubit SIC is a family $\lbrace\rho_a\rbrace_{a=1}^4$ of rank-one projectors on $\mathbb C^2$ with $\operatorname{Tr}(\rho_a\rho_b)=\frac13$ for $a\ne b$. Its overlap matrix is $B=\big(\operatorname{Tr}(\rho_a\rho_b)\big)_{a,b}=\frac23I_4+\frac13J_4$, where $J_4$ is the all-ones $4\times4$ matrix. Put

$$
A=\frac14J_4-\frac12I_4 .
$$

Since $J_4^2=4J_4$, one has $B(I_4-A)=\big(\frac23I_4+\frac13J_4\big)\big(\frac32I_4-\frac14J_4\big)=I_4-\frac16J_4+\frac12J_4-\frac13J_4=I_4$, so $B^{-1}=I_4-A$; entrywise $A_{ab}=\frac14(1-2\delta_{ab})$. Stance: literature-attested for the notion of qubit SIC and its overlap matrix (cited facts (a), (b)); repo-derived for the explicit matrix $A$ (computed in this volume).

**Definition 2.3 (Process fidelity and $k$-fidelities).** Let $\Lambda$ be a linear map on $M_d(\mathbb C)$, $d=2^n$. Its process fidelity is $F(\Lambda)=\langle\Phi\rvert(\mathrm{id}\otimes\Lambda)(\lvert\Phi\rangle\langle\Phi\rvert)\lvert\Phi\rangle$ with $\lvert\Phi\rangle=d^{-1/2}\sum_{x=1}^{d}\lvert x\rangle\otimes\lvert x\rangle$. For each qubit $i\in\lbrace1,\dots,n\rbrace$ fix a qubit SIC $\lbrace\rho^{(i)}_a\rbrace_{a=1}^4$, and for $a=(a_1,\dots,a_n)\in\lbrace1,2,3,4\rbrace^n$ put $\rho_a=\rho^{(1)}_{a_1}\otimes\cdots\otimes\rho^{(n)}_{a_n}$. For $T\subseteq\lbrace1,\dots,n\rbrace$ let $M_T=M_1\otimes\cdots\otimes M_n$ with $M_i=A$ for $i\in T$ and $M_i=I_4$ for $i\notin T$, so that $(I_4-A)^{\otimes n}=\sum_T(-1)^{\lvert T\rvert}M_T$. For an integer $k\ge0$ the $k$-fidelity of $\Lambda$ is

$$
F_k(\Lambda)=\frac{1}{4^n}\sum_{\lvert T\rvert\le k}(-1)^{\lvert T\rvert}\sum_{a,b}(M_T)_{ab}\operatorname{Tr}\big(\rho_b\,\Lambda(\rho_a)\big),
$$

that is, the truncation of $4^{-n}\sum_{a,b}\big[(I_4-A)^{\otimes n}\big]_{ab}\operatorname{Tr}(\rho_b\Lambda(\rho_a))$ to the terms carrying at most $k$ factors of $A$. In particular $F_0(\Lambda)=4^{-n}\sum_a\operatorname{Tr}(\rho_a\Lambda(\rho_a))$, and $F_k=F_n$ for $k\ge n$. Stance: literature-attested for $F$ and $F_0$ (cited facts (b), (c)) and for the truncation scheme (cited fact (b)); repo-derived for this precise normalisation of $F_k$, $1\le k\le n-1$ (Remark 2.4 records the differences from the printed text of (b)).

**Remark 2.4 (The printed form of the expansion in cited fact (b)).** Section II B of the paper in cited fact (b) prints $A_{ij}=\frac14(1-5\delta_{ij})$. With this matrix, $I_4-A$ has diagonal entries $2$ and off-diagonal entries $-\frac14$, and $B(I_4-A)$ has diagonal entries $2-\frac14=\frac74$, so it is not the inverse of $B$; the inverse is $I_4-A$ with $A$ as in Definition 2.2. The same section prints $B^{-1}=\sum_{k=0}^{n}(-1)^k\Omega_k$ with $\Omega_k$ the sum over arrangements of $k$ factors $I_4$ and $n-k$ factors $A$; with this labelling $\sum_k(-1)^k\Omega_k=(A-I_4)^{\otimes n}=(-1)^n(I_4-A)^{\otimes n}$, and $\Omega_k$ counts identity factors, whereas the accompanying text states that after truncation at the $k$-th term "only pairs of input states differing by at most $k$ single qubit states will have non-zero contributions to the $k$-fidelity". Since every factor $I_4$ is diagonal, a term with at most $k$ factors of $A$ is supported on such pairs; Definition 2.3 follows the text and counts factors of $A$. The printed coefficient $c_m=(-1)^m5^{n-m}/4^n$ for a pair differing in $m$ single-qubit states equals the corresponding entry of $(I_4-A)^{\otimes n}$ with $A$ as in Definition 2.2, whose single-qubit entries are $\frac54$ on and $-\frac14$ off the diagonal. Stance: literature-attested for the printed expressions (cited fact (b)); repo-derived for the comparison.

## 3. The per-qubit functionals

**Lemma 3.1 (Per-qubit functionals act diagonally on Pauli labels).** Let $\lbrace\rho_a\rbrace_{a=1}^4$ be any qubit SIC, $A$ as in Definition 2.2, and for $\beta,\gamma\in\lbrace0,1,2,3\rbrace$ put

$$
e(\beta,\gamma)=\frac14\sum_{a}\operatorname{Tr}\big(\rho_aP_\beta\rho_aP_\gamma\big),\qquad \alpha(\beta,\gamma)=\frac14\sum_{a,b}A_{ab}\operatorname{Tr}\big(\rho_bP_\beta\rho_aP_\gamma\big).
$$

Then $e(\beta,\gamma)=\alpha(\beta,\gamma)=0$ for $\beta\ne\gamma$, and on the diagonal

$$
e(0,0)=1,\quad e(\beta,\beta)=\tfrac13,\quad \alpha(0,0)=0,\quad \alpha(\beta,\beta)=\tfrac13\qquad(\beta\ne0).
$$

Consequently, for every $n\ge1$, every $k\ge0$, every choice of the qubit SICs in Definition 2.3 and every linear map $\Lambda$ on $M_{2^n}(\mathbb C)$,

$$
F_k(\Lambda)=\sum_{\beta}q_\beta\sum_{\lvert T\rvert\le k}(-1)^{\lvert T\rvert}\prod_{i\in T}\alpha(\beta_i,\beta_i)\prod_{i\notin T}e(\beta_i,\beta_i).
$$

In particular $F_k(\Lambda)$ depends only on the Pauli-twirl weights $q_\beta$ of $\Lambda$, coincides with $F_k$ of the Pauli channel $X\mapsto\sum_\beta q_\beta P_\beta XP_\beta$, and does not depend on the choice of the qubit SICs.

**Proof.** For operators $X,Y$ on $\mathbb C^2$ one has $\operatorname{Tr}((X\otimes Y)S)=\operatorname{Tr}(XY)$, hence $\operatorname{Tr}(\rho P\rho Q)=\operatorname{Tr}((\rho P\otimes\rho Q)S)=\operatorname{Tr}((\rho\otimes\rho)(P\otimes Q)S)$. By cited fact (a), and since $S(P\otimes Q)S=Q\otimes P$,

$$
\sum_a\operatorname{Tr}(\rho_aP_\beta\rho_aP_\gamma)=\frac23\big(\operatorname{Tr}(P_\beta P_\gamma)+\operatorname{Tr}P_\beta\operatorname{Tr}P_\gamma\big)=\frac23\big(2\delta_{\beta\gamma}+4\delta_{\beta0}\delta_{\gamma0}\big),
$$

which gives the stated values of $e$. Using $\sum_a\rho_a=2I$ (cited fact (a)),

$$
\frac14\sum_{a,b}\frac14\operatorname{Tr}(\rho_bP_\beta\rho_aP_\gamma)=\frac1{16}\operatorname{Tr}\big(2P_\beta\,2P_\gamma\big)=\frac12\delta_{\beta\gamma},
$$

so $\alpha(\beta,\gamma)=\frac12\delta_{\beta\gamma}-\frac12e(\beta,\gamma)$, which is $0$ off the diagonal, $0$ at $\beta=\gamma=0$ and $\frac12-\frac16=\frac13$ at $\beta=\gamma\ne0$.

For $n$ qubits and the product states of Definition 2.3, the map $X\mapsto P_\beta XP_\gamma$ is the tensor product of the single-qubit maps $X_i\mapsto P_{\beta_i}X_iP_{\gamma_i}$, the trace of a tensor product is the product of the traces, and $(M_T)_{ab}=\prod_i(M_i)_{a_ib_i}$. Hence

$$
\frac1{4^n}\sum_{a,b}(M_T)_{ab}\operatorname{Tr}\big(\rho_bP_\beta\rho_aP_\gamma\big)=\prod_{i\in T}\alpha_i(\beta_i,\gamma_i)\prod_{i\notin T}e_i(\beta_i,\gamma_i),
$$

where $e_i,\alpha_i$ are formed with the SIC on qubit $i$. By the single-qubit statement this product vanishes unless $\beta=\gamma$ and takes on the diagonal values that do not depend on the SICs. Inserting the expansion of Convention 2.1 into Definition 2.3 and using linearity gives the displayed formula. $\square$

Stance: literature-attested for the values of $e$ (a direct evaluation of the 2-design identity of cited fact (a)) and for the independence of $F_0$, the case $k=0$, from the choice of the qubit SICs (cited fact (c), Section I); suspected-novel for the values of $\alpha$ and for the formula and the SIC-independence for $k\ge1$.

## 4. The Pauli-weight formula and the sign of the truncation error

**Theorem 4.1 (Pauli-weight formula).** For every $n\ge1$, every $k\ge0$ and every linear map $\Lambda$ on $M_{2^n}(\mathbb C)$, with $Q_w$ as in Convention 2.1 and $\binom{m}{k}=0$ for $k>m$,

$$
F_k(\Lambda)=Q_0+(-1)^k\sum_{w=1}^{n}3^{-w}\binom{w-1}{k}Q_w .
$$

In particular $F_k(\Lambda)=Q_0=F(\Lambda)$ for every $k\ge n$, and $F_0(\Lambda)=\sum_\beta3^{-\lvert\beta\rvert}q_\beta$.

**Proof.** Fix $\beta$ with $\lvert\beta\rvert=w$ and support $W=\lbrace i:\beta_i\ne0\rbrace$. In the formula of Lemma 3.1, a subset $T$ containing an index $i\notin W$ contributes $0$, since $\alpha(0,0)=0$. For $T\subseteq W$ every factor equals $\frac13$ at indices of $W$ and $1$ elsewhere, so the term equals $3^{-w}$. Hence the coefficient of $q_\beta$ is $3^{-w}\sum_{j=0}^{k}(-1)^j\binom{w}{j}$, which is $1$ for $w=0$. For $w\ge1$ and every integer $m\ge0$,

$$
\sum_{j=0}^{m}(-1)^j\binom{w}{j}=(-1)^m\binom{w-1}{m},
$$

by induction on $m$: both sides equal $1$ at $m=0$, and Pascal's rule $\binom{w}{m}=\binom{w-1}{m}+\binom{w-1}{m-1}$ gives $(-1)^{m-1}\binom{w-1}{m-1}+(-1)^m\binom{w}{m}=(-1)^m\binom{w-1}{m}$. Summing over $\beta$ by weight gives the formula. For $k\ge n$ and $1\le w\le n$ one has $\binom{w-1}{k}=0$; together with Convention 2.1 this gives $F_k=F$. For $k=0$, $\binom{w-1}{0}=1$. $\square$

Stance: suspected-novel for $1\le k\le n-1$; the case $k=0$ is cited fact (d), and the equality $F_n=F$ is stated in cited fact (b). Section VI of the paper in cited fact (b) lists a relationship between the $k$-fidelities and Pauli channels as a route for further work; Theorem 4.1 gives one such relation, expressing every $F_k(\Lambda)$ through the Pauli-twirl weights of $\Lambda$, equivalently through the Pauli channel with the same weights (Lemma 3.1). No claim is made that this settles the question posed there.

**Theorem 4.2 (Alternating sign of the truncation error).** Let $\Lambda$ be a completely positive map on $M_{2^n}(\mathbb C)$ and $k\ge0$. Then

$$
(-1)^k\big(F_k(\Lambda)-F(\Lambda)\big)=\sum_{w=k+1}^{n}3^{-w}\binom{w-1}{k}Q_w\ \ge\ 0,
$$

with equality if and only if $Q_w=0$ for every $w\ge k+1$, that is, if and only if $q_\beta=0$ whenever $\lvert\beta\rvert>k$. Consequently $F_k\le F$ for odd $k$ and $F\le F_k$ for even $k$; in particular $F_j\le F\le F_i$ for all odd $j$ and even $i$.

**Proof.** Theorem 4.1 and Convention 2.1 give the identity, the terms with $w\le k$ vanishing because $\binom{w-1}{k}=0$. Complete positivity gives $q_\beta\ge0$, hence $Q_w\ge0$, and every coefficient $3^{-w}\binom{w-1}{k}$ with $w\ge k+1$ is strictly positive. $\square$

Stance: suspected-novel for $k\ge1$; the inequality for $k=0$ is the upper bound $F\le F_0$ of cited fact (c), literature-attested.

## 5. The realised pairs ($k$-fidelity, process fidelity)

**Theorem 5.1 (Achievable region).** Fix $n\ge1$ and $k\ge0$, and let $R_k\subseteq\mathbb R^2$ be the set of pairs $(F_k(\Lambda),F(\Lambda))$ with $\Lambda$ ranging over the completely positive trace-preserving maps on $M_{2^n}(\mathbb C)$.

(i) $k=0$. For $n\ge2$, $R_0$ is the closed triangle with vertices $(1,1)$, $(3^{-n},0)$ and $(\frac13,0)$; equivalently $(F_0,F)\in R_0$ if and only if

$$
F\ge0,\qquad 1-\tfrac32(1-F_0)\ \le\ F\ \le\ \frac{F_0-3^{-n}}{1-3^{-n}} .
$$

For $n=1$, $R_0$ is the segment $F=1-\frac32(1-F_0)$, $\frac13\le F_0\le1$. The upper bound is attained by $X\mapsto pX+(1-p)Z^{\otimes n}XZ^{\otimes n}$, $0\le p\le1$, and the lower bound by $X\mapsto pX+(1-p)P_\beta XP_\beta$ with $\lvert\beta\rvert=1$.

(ii) $1\le k\le n-1$. Let $g(w)=3^{-w}\binom{w-1}{k}$, put $w^*=\min\big(n,\lfloor3k/2\rfloor+1\big)$ and $x_k=(-1)^kg(w^*)$. Then $g(w^*)=\max_{1\le w\le n}g(w)>0$, and $R_k$ is the closed triangle with vertices $(1,1)$, $(0,0)$ and $(x_k,0)$; equivalently, for odd $k$ (where $x_k<0$),

$$
(F_k,F)\in R_k\iff F\ge0,\qquad F_k\ \le\ F\ \le\ \frac{F_k-x_k}{1-x_k},
$$

and for even $k$ (where $x_k>0$),

$$
(F_k,F)\in R_k\iff F\ge0,\qquad \frac{F_k-x_k}{1-x_k}\ \le\ F\ \le\ F_k .
$$

In both cases these inequalities imply $0\le F\le1$. The maximiser of $g$ on $\lbrace1,\dots,n\rbrace$ is unique and equal to $w^*$, except when $k$ is even and $3k/2+1\le n$, in which case $g$ attains its maximum exactly at $w=3k/2$ and $w=3k/2+1=w^*$. The vertex $(x_k,0)$ is attained by $X\mapsto P_\beta XP_\beta$ with $\lvert\beta\rvert=w^*$, the vertex $(0,0)$ by the same map with $\lvert\beta\rvert=1$, and $(1,1)$ by the identity map.

(iii) $k\ge n$. $R_k$ is the segment from $(0,0)$ to $(1,1)$ on the diagonal $F_k=F$.

**Proof.** By Convention 2.1 the vector $(Q_0,\dots,Q_n)$ of a CPTP map is a probability vector, and every probability vector arises, for instance from a Pauli channel that puts weight $Q_w$ on one label of weight $w$. By Theorem 4.1 and Convention 2.1 the pair $(F_k,F)$ is a linear function of $(Q_0,\dots,Q_n)$, so $R_k$ is the convex hull of the images of the vertices of the simplex: $(1,1)$ for $w=0$ and $\big((-1)^kg(w),0\big)$ for $1\le w\le n$.

For $k=0$, $g(w)=3^{-w}$, so the points on the axis $F=0$ fill the interval $[3^{-n},\frac13]$, which is a single point when $n=1$. The convex hull of $(1,1)$ and this interval is the stated triangle (a segment for $n=1$). Its two upper edges are the lines through $(1,1)$ and $(\frac13,0)$, namely $F=\frac{3F_0-1}{2}=1-\frac32(1-F_0)$, and through $(1,1)$ and $(3^{-n},0)$, namely $F=(F_0-3^{-n})/(1-3^{-n})$. The given mixtures have $(Q_0,Q_n)=(p,1-p)$, respectively $(Q_0,Q_1)=(p,1-p)$, and run along these two edges.

For $k\ge1$, $g(w)=0$ for $1\le w\le k$, and $g(k+1)=3^{-k-1}>0$ since $k+1\le n$. For $w\ge k+1$,

$$
\frac{g(w+1)}{g(w)}=\frac{1}{3}\cdot\frac{\binom{w}{k}}{\binom{w-1}{k}}=\frac{w}{3(w-k)},
$$

which exceeds $1$ for $w<3k/2$, equals $1$ for $w=3k/2$ and is less than $1$ for $w>3k/2$. Hence $g$ strictly increases from $w=k+1$ up to $w=\lfloor3k/2\rfloor+1$ when $k$ is odd, and up to $w=3k/2$ when $k$ is even, with $g(3k/2)=g(3k/2+1)$ in the even case, and strictly decreases afterwards. Restricting to $w\le n$ yields the stated maximiser and its uniqueness pattern. All the points $\big((-1)^kg(w),0\big)$ lie on the same side of the origin, so they fill the segment between $(0,0)$ and $(x_k,0)$, and the convex hull with $(1,1)$ is the stated triangle; its edges through $(1,1)$ are $F=F_k$ and $F=(F_k-x_k)/(1-x_k)$, and its third edge lies on $F=0$. Since $g(w)\le3^{-w}\sum_{j=0}^{w-1}\binom{w-1}{j}=2^{w-1}3^{-w}<1$ for $w\ge1$, one has $0<\lvert x_k\rvert<1$, so $1-x_k>0$. The closed triangle is the intersection of the three closed half-planes bounded by its edge lines and containing the opposite vertex. The opposite vertex of the edge $F=F_k$ is $(x_k,0)$, where $F-F_k=-x_k$; the opposite vertex of the edge $F=(F_k-x_k)/(1-x_k)$ is $(0,0)$, where $F-(F_k-x_k)/(1-x_k)=x_k/(1-x_k)$; the opposite vertex of the edge $F=0$ is $(1,1)$. For odd $k$, $x_k<0$, which gives $F\ge F_k$, $F\le(F_k-x_k)/(1-x_k)$ and $F\ge0$; for even $k$, $x_k>0$, which reverses the first two inequalities. Finally, $F\le1$ on the triangle because all three vertices have $F\le1$.

For $k\ge n$, Theorem 4.1 gives $F_k=F=Q_0\in[0,1]$, and both endpoints are attained by the identity map and by $X\mapsto P_\beta XP_\beta$ with $\beta\ne0$. $\square$

Stance: suspected-novel, except the lower bound $F\ge1-\frac32(1-F_0)$ in (i), which is literature-attested (cited fact (c)), and its attainment for $n\ge2$, which is cited fact (d) (repo-derived; used as a cited step).

**Remark 5.2 (Relation to the semidefinite programs of cited fact (c)).** The maximum of $F$ over CPTP maps with prescribed $F_0$ is the upper edge of $R_0$. Theorem 5.1(i) therefore gives the closed form $\max F=(F_0-3^{-n})/(1-3^{-n})$, $3^{-n}\le F_0\le1$, of the best-case curve that Mayer computed numerically. It is strictly smaller than $F_0$ for $F_0<1$, and $F_0-\max F=(1-F_0)\,3^{-n}/(1-3^{-n})$. The case $n=1$ of Theorem 5.1(i) is the statement of cited fact (c) that $F$ is determined by $F_0$ for one qubit. Stance: repo-derived (comparison carried out in this volume).

## 6. The linear relation among the k-fidelities and their joint range

**Theorem 6.1 (Linear relation).** For every $n\ge1$ and every trace-preserving linear map $\Lambda$ on $M_{2^n}(\mathbb C)$,

$$
3\sum_{k=0}^{n-1}(-2)^kF_k(\Lambda)+(-2)^nF(\Lambda)=1 .
$$

**Proof.** By Theorem 4.1 and Convention 2.1 the left-hand side is $\sum_{w=0}^{n}c_wQ_w$. The coefficient of $Q_0$ is $c_0=3\sum_{k=0}^{n-1}(-2)^k+(-2)^n=(1-(-2)^n)+(-2)^n=1$. For $1\le w\le n$, $F$ does not involve $Q_w$, and

$$
c_w=3\cdot3^{-w}\sum_{k=0}^{n-1}(-2)^k(-1)^k\binom{w-1}{k}=3^{1-w}\sum_{k=0}^{w-1}2^k\binom{w-1}{k}=3^{1-w}\,3^{w-1}=1,
$$

using $\binom{w-1}{k}=0$ for $k\ge w$ and $w-1\le n-1$. Hence the left-hand side equals $\sum_wQ_w=\sum_\beta q_\beta=1$ by trace preservation (Convention 2.1). $\square$

Stance: suspected-novel.

**Corollary 6.2 (Joint range).** Fix $n\ge1$. Let $V_0=(1,\dots,1)\in\mathbb R^n$ and, for $1\le w\le n$, $V_w=\big((-1)^k3^{-w}\binom{w-1}{k}\big)_{k=0}^{n-1}\in\mathbb R^n$. Then $V_0,\dots,V_n$ are affinely independent, and the set of vectors $(F_0(\Lambda),\dots,F_{n-1}(\Lambda))$, with $\Lambda$ ranging over the CPTP maps on $M_{2^n}(\mathbb C)$, is the $n$-simplex $\operatorname{conv}\lbrace V_0,\dots,V_n\rbrace$. The barycentric coordinates of $(F_0(\Lambda),\dots,F_{n-1}(\Lambda))$ in this simplex are $(Q_0,\dots,Q_n)$, and

$$
F(\Lambda)=Q_0=(-2)^{-n}\Big(1-3\sum_{k=0}^{n-1}(-2)^kF_k(\Lambda)\Big).
$$

**Proof.** By Theorem 4.1, $(F_0,\dots,F_{n-1})=\sum_{w=0}^{n}Q_wV_w$, and $(Q_0,\dots,Q_n)$ ranges over the whole probability simplex (Convention 2.1); so the set is $\operatorname{conv}\lbrace V_0,\dots,V_n\rbrace$. Consider the linear map $L:\mathbb R^{n+1}\to\mathbb R^{n+1}$, $(Q_0,\dots,Q_n)\mapsto(F_0,\dots,F_{n-1},F)$ given by Theorem 4.1 and Convention 2.1. Its last coordinate is $Q_0$, and $F_k-Q_0=\sum_{w=1}^{n}(-1)^k\binom{w-1}{k}3^{-w}Q_w$ for $0\le k\le n-1$. The $n\times n$ matrix $\big((-1)^k\binom{w-1}{k}\big)_{k,w}$ vanishes for $k\ge w$ and has entries $(-1)^{w-1}\ne0$ at $k=w-1$, so it is triangular and invertible, and so is $L$. On the hyperplane $\sum_wQ_w=1$, Theorem 6.1 expresses $F$ as an affine function of $(F_0,\dots,F_{n-1})$. Hence $(F_0,\dots,F_{n-1})$ determines $(F_0,\dots,F_{n-1},F)$ and, through $L^{-1}$, the vector $(Q_0,\dots,Q_n)$. The affine map $(Q_0,\dots,Q_n)\mapsto\sum_wQ_wV_w$ is thus injective on the probability simplex, which is equivalent to the affine independence of $V_0,\dots,V_n$, and the barycentric coordinates are the $Q_w$. The formula for $F$ is Theorem 6.1 solved for $F$. $\square$

Stance: suspected-novel.

## 7. Boundaries

**Remark 7.1 (What is not claimed).** All statements concern the process fidelity with respect to the identity map and the product SIC frame of Definition 2.3. Nothing is asserted for other target maps, for other ensembles of input states, or for frames that are not products of qubit SICs. No monotonicity of $F_k$ as a function of $F$ is claimed: by Theorem 5.1 the value of $F_k$ does not determine $F$ for $n\ge2$ and $k\le n-1$. Theorems 4.2 and 5.1 use complete positivity; Theorem 6.1 uses only trace preservation; Lemma 3.1 and Theorem 4.1 hold for every linear map. Stance: repo-derived.

## 8. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves, *Symmetric informationally complete quantum measurements*, J. Math. Phys. 45 (2004) 2171, arXiv:quant-ph/0310075, Section 2 | `literature-attested`: every SIC-POVM is a 2-design, with $\sum_k(\lvert\phi_k\rangle\langle\phi_k\rvert)^{\otimes2}=d^2K_2$ and $K_2=\frac{2}{d(d+1)}\Pi_{\mathrm{sym}}$ (cited fact (a)); used as a step in Lemma 3.1. |
| S. Greenaway, F. Sauvage, K. E. Khosla, F. Mintert, *Efficient assessment of process fidelity*, Phys. Rev. Research 3 (2021) 033031, arXiv:2102.08101, Sections II B and VI | `literature-attested`: the overlap-matrix expansion, the truncation defining the $k$-fidelities, $F_n=F$, the printed expressions for $A$, $\Omega_k$ and $c_m$ discussed in Remark 2.4, and the further-work item of Section VI (cited fact (b)). |
| K. Mayer, *A short note on the 0-fidelity*, arXiv:2109.09629, Sections I and III, Theorem 1 | `literature-attested`: the independence of $F_0$ from the choice of the qubit SICs; $1-\frac32(1-F_0)\le F\le F_0$ for CPTP maps; the semidefinite programs for the extreme values of $F$ at fixed $F_0$, with the minimum reported for $n\le4$ and the maximum computed numerically; the determination of $F$ by $F_0$ for $n=1$; the conjecture that the lower bound is tight for all $n$ (cited fact (c)). |
| A. N. Korotkov, *Error matrices in quantum process tomography*, arXiv:1309.6405, Sections II and III, Eqs. (1)–(5), (12), (13) | `literature-attested`: positivity of the process matrix, the trace-preservation condition, and the process fidelity relative to the identity equal to $\chi_{00}$ (cited fact (e)); used in Convention 2.1. |
| — | `repo-derived`: the notation of Convention 2.1, the matrix $A$ in Definition 2.2, the normalisation in Definition 2.3, Remarks 2.4, 5.2 and 7.1; the identity $F_0=\sum_\beta3^{-\lvert\beta\rvert}q_\beta$ and the attainment of the lower bound of (c) for $n\ge2$ (cited fact (d); used as a cited step; not a load-bearing item of this volume). |
| — | `suspected-novel`: Lemma 3.1 for the values of $\alpha$ and for $k\ge1$, Theorem 4.1 for $1\le k\le n-1$, Theorem 4.2 for $k\ge1$, Theorem 5.1 except the parts attributed above, Theorem 6.1, Corollary 6.2. Searched: the full texts of arXiv:2102.08101 and arXiv:2109.09629; the full text of arXiv:2312.08590 (Chen, Wong, Goan, on the zeroth-order process fidelity under state-preparation and measurement errors), which contains no Pauli-weight expression, region or linear relation for the $k$-fidelities; web searches combining $k$-fidelity, $0$-fidelity, SIC states, process fidelity, Pauli weight, Greenaway and Mayer. No statement of these results was found in the searched scope; this establishes no worldwide priority. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）

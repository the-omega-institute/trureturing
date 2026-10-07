# Stabilizer multi-entropy at replica three as a sum over coarse partitions

This volume is reference input. Lean declarations and their checked proof terms carry the mathematical truth; nothing in this volume is kernel-verified. The atomizer is `generic-v1`. Existing text is append-only; corrections and additions belong after the final append anchor.

## 1. Scope

For a normalized pure qubit stabilizer state whose qubits are assigned to $\mathtt q$ labelled parties, the Rényi multi-entropy at replica index $n=3$ is a weighted count of $\mathbb F_2$-ranks. This volume organizes that count by set partitions of the parties. Every pair of opposite nonzero characters of the replica group $(\mathbb Z/3)^{\mathtt q-1}$ corresponds to exactly one partition of the $\mathtt q$ parties into two or three blocks, so $S_3^{(\mathtt q)}$ is a fixed multiple of the sum, over all such partitions $\pi$, of the rank of the adjacency matrix of a graph form of the state masked to pairs of qubits in different blocks of $\pi$ (Theorem 3.4). Counting the three-block refinements of each two-block partition turns this into an explicit linear expression of $S_3^{(\mathtt q)}$ through the two- and three-party multi-entropies of the coarse-grained states (Theorem 3.8). The same bookkeeping gives a sufficient coefficient criterion for a linear combination of coarse-grained multi-entropies to vanish on all stabilizer states (Proposition 3.10), and shows that the replica-three multi-entropies of all coarsenings are determined by the two- and three-party coarse data (Corollary 3.12).

## 2. Notation and conventions

**Convention 2.1 (Parties and colourings).** Fix $\mathtt q\ge2$ and write $[\mathtt q]=\{1,\dots,\mathtt q\}$. A $\mathtt q$-party pure qubit state is a unit vector $\psi\in(\mathbb C^2)^{\otimes N}$ together with a colouring $\mathrm{col}:[N]\to[\mathtt q]$ assigning each qubit to a party; party $c$ consists of the qubits $u$ with $\mathrm{col}(u)=c$, and parties may be empty. A stabilizer state is a common eigenvector, with eigenvalue $1$, of $N$ independent commuting elements of the $N$-qubit Pauli group not containing $-I$.

**Convention 2.2 (Replica multi-entropy).** Following the replica definition of Gadde, Krishna and Sharma in the form of Appendix A of Akella, Iizuka and Miyata, the replicas are labelled by $r\in(\mathbb Z/n)^{\mathtt q-1}$. Party $c<\mathtt q$ acts on the replica labels by the translation $r\mapsto r+\delta_c$, where $\delta_c$ is the $c$-th standard basis vector of $(\mathbb Z/n)^{\mathtt q-1}$, and the last party $\mathtt q$ acts by the identity, $\delta_{\mathtt q}=0$. In the computational basis,

$$
Z_n^{(\mathtt q)}=\sum_{x:(\mathbb Z/n)^{\mathtt q-1}\to\{0,1\}^N}\ \prod_{r}\overline{\psi(x_r)}\,\psi\big(u\mapsto x_{r+\delta_{\mathrm{col}(u)}}(u)\big),
$$

and

$$
S_n^{(\mathtt q)}=\frac{1}{1-n}\,\frac{1}{n^{\mathtt q-2}}\,\log\frac{Z_n^{(\mathtt q)}}{\big(Z_1^{(\mathtt q)}\big)^{n^{\mathtt q-1}}}.
$$

For a normalized state $Z_1^{(\mathtt q)}=1$. Throughout this volume $n=3$, and $S_3^{(\mathtt q)}$, or $S_3^{(\mathtt q)}(\psi,\mathrm{col})$, denotes this quantity.

**Convention 2.3 (Graph forms).** For a symmetric matrix $\Gamma\in\mathbb F_2^{N\times N}$ with zero diagonal, the graph state is $|\Gamma\rangle=2^{-N/2}\sum_{x\in\{0,1\}^N}(-1)^{\sum_{u<v}\Gamma_{uv}x_ux_v}|x\rangle$. Every normalized pure qubit stabilizer state equals $\lambda\,(U_1\otimes\cdots\otimes U_N)|\Gamma\rangle$ for some such $\Gamma$, single-qubit unitaries $U_u$ and a scalar $\lambda$ with $|\lambda|=1$ (Van den Nest, Dehaene and De Moor; Schlingemann). Such a $\Gamma$ is called a graph form of $\psi$.

**Convention 2.4 (Set partitions).** $\Pi(\mathtt q)$ is the set of set partitions of $[\mathtt q]$, $|\pi|$ the number of blocks of $\pi$, and $\Pi_k(\mathtt q)$ the partitions with exactly $k$ blocks. For $\rho,\sigma\in\Pi(\mathtt q)$, $\rho\le\sigma$ means that $\rho$ refines $\sigma$: every block of $\rho$ lies in a block of $\sigma$. $S(m,k)$ is the Stirling number of the second kind; $S(m,2)=2^{m-1}-1$ for $m\ge1$.

**Convention 2.5 (Coarse-grained states).** For $\pi\in\Pi_k(\mathtt q)$ with blocks listed as $B_1,\dots,B_k$, the coarse-grained colouring is $\mathrm{col}_\pi(u)=j$ when $\mathrm{col}(u)\in B_j$, and $S_3^{(k)}(\pi)=S_3^{(k)}(\psi,\mathrm{col}_\pi)$. By Corollary 3.5 this value does not depend on the order in which the blocks are listed. For the finest partition, $S_3^{(\mathtt q)}(\{\{1\},\dots,\{\mathtt q\}\})=S_3^{(\mathtt q)}(\psi,\mathrm{col})$.

**Recalled replica rank formula.** The following result was previously established and is recalled without proof as a cited step; it is not claimed in this volume. It generalises the bipartite rank formula of Hein, Eisert and Briegel (Remark 3.6) to the replica convention of Appendix A of Akella, Iizuka and Miyata (Convention 2.2). Stance: previously established; not claimed here. Let $\psi$ be a normalized pure qubit stabilizer state with graph form $\Gamma$ and let $\mathrm{col}:[N]\to[\mathtt q]$ be any colouring. For $t\in(\mathbb Z/3)^{\mathtt q-1}$ let $C_t\in\mathbb F_2^{N\times N}$ be the masked matrix

$$
(C_t)_{uv}=\begin{cases}\Gamma_{uv}, & t\cdot\delta_{\mathrm{col}(u)}\ne t\cdot\delta_{\mathrm{col}(v)},\\ 0, & \text{otherwise,}\end{cases}
$$

with $\delta_c$ as in Convention 2.2 for $n=3$. Let $P$ be a set of representatives of the pairs $\{t,-t\}$ with $t\ne0$. Then $Z_3^{(\mathtt q)}$ is a positive real number and

$$
Z_3^{(\mathtt q)}=2^{-\sum_{t\in P}\operatorname{rank}_{\mathbb F_2}C_t}.
$$

The mechanism is as follows. The replica contraction is invariant under applying the same local unitaries and phases to all replicas, so $\psi$ may be replaced by $|\Gamma\rangle$. For a graph state the summand is $(-1)^{F(x)}$ with $F$ a quadratic form over $\mathbb F_2$ in the variables $x_r(u)$. Since $|(\mathbb Z/3)^{\mathtt q-1}|$ is odd, the Fourier transform over $(\mathbb Z/3)^{\mathtt q-1}$ with values in $\mathbb F_4$ is invertible and is defined over $\mathbb F_2$ after pairing each character $t$ with $-t$; in the transformed coordinates $F$ splits into the zero contribution of $t=0$ and one bilinear block $y_t^{\mathsf T}C_tz_t$ for each $t\in P$, and the unnormalised sum over the $2N$ coordinates of the block of $t$ equals $2^{2N-\operatorname{rank}C_t}$. The block $t=0$ contributes $2^N$, so the unnormalised total is $2^{N\cdot3^{\mathtt q-1}-\sum_{t\in P}\operatorname{rank}C_t}$, and the amplitude normalisation $2^{-N/2}$ of each of the $2\cdot3^{\mathtt q-1}$ factors cancels $2^{N\cdot3^{\mathtt q-1}}$.

## 3. Partition structure at replica three

Throughout this section $\psi$ is a normalized pure qubit stabilizer state on $N$ qubits, $\Gamma$ is a graph form of $\psi$, and $\mathrm{col}:[N]\to[\mathtt q]$ is a colouring.

**Definition 3.1 (Masked adjacency and partition rank).** For $\pi\in\Pi(\mathtt q)$ let $\Gamma^\pi\in\mathbb F_2^{N\times N}$ be given by $\Gamma^\pi_{uv}=\Gamma_{uv}$ if $\mathrm{col}(u)$ and $\mathrm{col}(v)$ lie in different blocks of $\pi$, and $\Gamma^\pi_{uv}=0$ otherwise. Put $r(\pi)=\operatorname{rank}_{\mathbb F_2}\Gamma^\pi$. Stance: repo-derived.

**Definition 3.2 (Partition of a character).** For $t\in(\mathbb Z/3)^{\mathtt q-1}$ let $f_t:[\mathtt q]\to\mathbb Z/3$, $f_t(c)=t\cdot\delta_c$, so $f_t(c)=t_c$ for $c<\mathtt q$ and $f_t(\mathtt q)=0$. Let $\pi_t\in\Pi(\mathtt q)$ be the partition of $[\mathtt q]$ into the nonempty fibres of $f_t$. Stance: repo-derived.

**Theorem 3.4 (Replica-three multi-entropy as a sum over coarse partitions).** For every $\mathtt q\ge2$ the assignment $\{t,-t\}\mapsto\pi_t$ is a well-defined bijection from the set of pairs $\{t,-t\}$ with $0\ne t\in(\mathbb Z/3)^{\mathtt q-1}$ onto $\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)$. Consequently

$$
\frac{3^{\mathtt q-1}-1}{2}=S(\mathtt q,2)+S(\mathtt q,3),
$$

and for every normalized pure qubit stabilizer state, every graph form $\Gamma$ of it and every colouring,

$$
S_3^{(\mathtt q)}=\frac{\log2}{2\cdot3^{\mathtt q-2}}\sum_{\pi\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)}r(\pi).
$$

Stance: suspected-novel (§6).

**Proof.** The fibres of $f_{-t}=-f_t$ coincide with those of $f_t$, since negation is a bijection of $\mathbb Z/3$; so $\pi_{-t}=\pi_t$ and the map is well defined. If $t\ne0$, some $c<\mathtt q$ has $f_t(c)\ne0=f_t(\mathtt q)$, so $\pi_t$ has at least two blocks, and it has at most three since $f_t$ takes values in $\mathbb Z/3$. Conversely, the vectors $t$ correspond bijectively to the functions $f:[\mathtt q]\to\mathbb Z/3$ with $f(\mathtt q)=0$, through $t_c=f(c)$. Fix $\pi\in\Pi_k(\mathtt q)$ with $k\in\{2,3\}$. A function $f$ with $f(\mathtt q)=0$ has fibre partition $\pi$ exactly when $f$ is constant on blocks, takes the value $0$ on the block containing $\mathtt q$, and takes pairwise distinct nonzero values on the remaining $k-1$ blocks. For $k=2$ the remaining block receives $1$ or $2$; for $k=3$ the two remaining blocks receive $1$ and $2$ in one of two orders. In both cases there are exactly two such functions, and they are negatives of each other because negation exchanges $1$ and $2$. Hence the preimage of $\pi$ is exactly one pair $\{t,-t\}$, which proves the bijection.

The number of pairs is $(3^{\mathtt q-1}-1)/2$, which gives the counting identity. By the recalled replica rank formula and $Z_1^{(\mathtt q)}=1$,

$$
S_3^{(\mathtt q)}=\frac{1}{1-3}\cdot\frac{1}{3^{\mathtt q-2}}\cdot\log2^{-\sum_{t\in P}\operatorname{rank}C_t}=\frac{\log2}{2\cdot3^{\mathtt q-2}}\sum_{t\in P}\operatorname{rank}C_t.
$$

For every $t$, $C_t=\Gamma^{\pi_t}$: for qubits $u,v$ the condition $t\cdot\delta_{\mathrm{col}(u)}\ne t\cdot\delta_{\mathrm{col}(v)}$ reads $f_t(\mathrm{col}(u))\ne f_t(\mathrm{col}(v))$, which holds exactly when $\mathrm{col}(u)$ and $\mathrm{col}(v)$ lie in different blocks of $\pi_t$; this entrywise unfolding is already implicit in the recalled formula. Hence $\operatorname{rank}C_t=r(\pi_t)$, and by the bijection each $\pi\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)$ occurs for exactly one $t\in P$. ∎

**Corollary 3.5 (Party symmetry and coarse-graining).** $S_3^{(\mathtt q)}(\psi,\mathrm{col})$ is unchanged when the party labels are permuted, that is, when $\mathrm{col}$ is replaced by $\tau\circ\mathrm{col}$ for a permutation $\tau$ of $[\mathtt q]$. For $\pi\in\Pi_k(\mathtt q)$ with $k\ge2$,

$$
S_3^{(k)}(\pi)=\frac{\log2}{2\cdot3^{k-2}}\sum_{\substack{\sigma\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)\\ \sigma\ge\pi}}r(\sigma),
$$

where $r$ is computed for the original colouring $\mathrm{col}$. Stance: suspected-novel (§6).

**Proof.** Relabelling parties by $\tau$ permutes $\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)$ through $\pi\mapsto\tau(\pi)$, and the matrix $\Gamma^{\tau(\pi)}$ for the colouring $\tau\circ\mathrm{col}$ equals $\Gamma^{\pi}$ for $\mathrm{col}$; the right-hand side of Theorem 3.4 is therefore invariant. For the second statement, apply Theorem 3.4 to the $k$-party state $(\psi,\mathrm{col}_\pi)$ with the same graph form $\Gamma$. A partition $\rho$ of $[k]$ determines the partition $\sigma$ of $[\mathtt q]$ whose blocks are the unions $\bigcup_{j\in D}B_j$ over the blocks $D$ of $\rho$; this is a bijection from $\Pi(k)$ onto the set of $\sigma\ge\pi$, preserving the number of blocks. Two qubits lie in different blocks of $\rho$ with respect to $\mathrm{col}_\pi$ exactly when they lie in different blocks of $\sigma$ with respect to $\mathrm{col}$, so the masked matrices coincide and the ranks agree. By the first statement the value does not depend on the order of the blocks $B_1,\dots,B_k$. ∎

**Remark 3.6 (Two parties).** For $\sigma=\{X,Y\}\in\Pi_2(\mathtt q)$, the matrix $\Gamma^\sigma$ is block anti-diagonal with off-diagonal block $\Gamma_{XY}$, the submatrix of $\Gamma$ with rows in the qubits of $X$ and columns in the qubits of $Y$, so $r(\sigma)=2\operatorname{rank}_{\mathbb F_2}\Gamma_{XY}$ and Corollary 3.5 gives $S_3^{(2)}(\sigma)=\log2\cdot\operatorname{rank}_{\mathbb F_2}\Gamma_{XY}$. This agrees with the known value of every Rényi entanglement entropy of a graph state across a bipartition (Hein, Eisert and Briegel), since for $\mathtt q=2$ the multi-entropy is the Rényi entropy of the bipartition. For the three-qubit chain state with one qubit in each of three parties, the four partitions in $\Pi_2(3)\cup\Pi_3(3)$ each have $r=2$, so Theorem 3.4 gives $S_3^{(3)}=\tfrac43\log2$, the value $(1+\tfrac1n)\log2$ at $n=3$ obtained for this state by Czech, Feng, Wu and Xie. Stance: literature-attested for both comparison values; the computation through Theorem 3.4 is repo-derived.

**Theorem 3.8 (Reduction to two- and three-party coarse data).** For every $\mathtt q\ge3$, every normalized pure qubit stabilizer state and every colouring,

$$
S_3^{(\mathtt q)}=3^{2-\mathtt q}\Bigg[\sum_{\pi\in\Pi_3(\mathtt q)}3\,S_3^{(3)}(\pi)+\sum_{\{X,Y\}\in\Pi_2(\mathtt q)}\big(3-2^{|X|-1}-2^{|Y|-1}\big)\,S_3^{(2)}(\{X,Y\})\Bigg].
$$

Stance: suspected-novel (§6).

**Proof.** Write $K=\tfrac12\log2$. By Corollary 3.5, for $\pi\in\Pi_3(\mathtt q)$ the partitions $\sigma\ge\pi$ with two or three blocks are $\pi$ itself and its three two-block coarsenings, so $3\,S_3^{(3)}(\pi)=K\big(r(\pi)+\sum_{\sigma\in\Pi_2(\mathtt q),\,\sigma\ge\pi}r(\sigma)\big)$, and for $\sigma\in\Pi_2(\mathtt q)$, $S_3^{(2)}(\sigma)=K\,r(\sigma)$. Summing over $\pi\in\Pi_3(\mathtt q)$ and exchanging the order of summation, each $\sigma=\{X,Y\}\in\Pi_2(\mathtt q)$ is counted once for each of its $m(\sigma)=2^{|X|-1}+2^{|Y|-1}-2$ three-block refinements; indeed a three-block partition refining $\{X,Y\}$ keeps one of $X,Y$ as a block and splits the other into two nonempty blocks, which for a set of size $m$ can be done in $S(m,2)=2^{m-1}-1$ ways:

$$
\sum_{\pi\in\Pi_3(\mathtt q)}3\,S_3^{(3)}(\pi)=K\sum_{\pi\in\Pi_3(\mathtt q)}r(\pi)+K\sum_{\sigma\in\Pi_2(\mathtt q)}m(\sigma)\,r(\sigma).
$$

Adding $\sum_{\sigma}(1-m(\sigma))S_3^{(2)}(\sigma)=K\sum_\sigma(1-m(\sigma))r(\sigma)$ gives $K\sum_{\pi\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)}r(\pi)$, which by Theorem 3.4 equals $3^{\mathtt q-2}S_3^{(\mathtt q)}$. Since $1-m(\sigma)=3-2^{|X|-1}-2^{|Y|-1}$, the identity follows. ∎

**Remark 3.9 (Small numbers of parties).** For $\mathtt q=3$ every $\sigma\in\Pi_2(3)$ has block sizes $2$ and $1$, its coefficient is $3-2-1=0$, and Theorem 3.8 reduces to the tautology $S_3^{(3)}=S_3^{(3)}$. For $\mathtt q=4$ the coefficients are $-2$ for the four cuts with block sizes $3$ and $1$ and $-1$ for the three cuts with block sizes $2$ and $2$:

$$
S_3^{(4)}=\frac19\Bigg[3\sum_{\pi\in\Pi_3(4)}S_3^{(3)}(\pi)-2\sum_{|X|=1}S_3^{(2)}(\{X,Y\})-\sum_{|X|=|Y|=2}S_3^{(2)}(\{X,Y\})\Bigg].
$$

Stance: repo-derived.

**Proposition 3.10 (A sufficient vanishing criterion).** Let $\mathtt q\ge2$ and let $c:\{\rho\in\Pi(\mathtt q):|\rho|\ge2\}\to\mathbb R$. For a normalized pure qubit stabilizer state with colouring $\mathrm{col}$ put

$$
L=\sum_{|\rho|\ge2}c_\rho\,S_3^{(|\rho|)}(\rho),\qquad w_\sigma=\sum_{\substack{\rho\le\sigma\\ |\rho|\ge2}}3^{2-|\rho|}c_\rho\quad(\sigma\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)).
$$

Then, for every graph form $\Gamma$ of the state,

$$
L=\frac{\log2}{2}\sum_{\sigma\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)}w_\sigma\,r(\sigma).
$$

In particular, if $w_\sigma=0$ for every $\sigma\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)$, then $L=0$ for every normalized pure qubit stabilizer state, every number of qubits and every colouring. Stance: suspected-novel (§6).

**Proof.** By Corollary 3.5, $c_\rho S_3^{(|\rho|)}(\rho)=\tfrac{\log2}{2}\,3^{2-|\rho|}c_\rho\sum_{\sigma\ge\rho}r(\sigma)$, the sum running over $\sigma\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)$. Summing over $\rho$ and exchanging the order of summation collects, for each $\sigma$, the coefficient $\sum_{\rho\le\sigma,\,|\rho|\ge2}3^{2-|\rho|}c_\rho=w_\sigma$. The vanishing statement follows. ∎

**Remark 3.11 (The four-party genuine multi-entropy).** For $\mathtt q=4$, Akella, Iizuka and Miyata define (their Eq. (5))

$$
\mathrm{GM}^{(4)}_3=S_3^{(4)}-\frac13\sum_{\pi\in\Pi_3(4)}S_3^{(3)}(\pi)+\frac13\sum_{|X|=1}S_3^{(2)}(\{X,Y\})-a\,I_3,
$$

with $I_3=\sum_{|X|=1}S_3^{(2)}(\{X,Y\})-\sum_{|X|=|Y|=2}S_3^{(2)}(\{X,Y\})$ and a real parameter $a$. For $L=\mathrm{GM}^{(4)}_3+(a-\tfrac19)I_3$ the weights of Proposition 3.10 are: for $\sigma\in\Pi_3(4)$, $w_\sigma=\tfrac19-\tfrac13\cdot\tfrac13=0$; for a cut with $|X|=1$, the refinements are the finest partition, three three-block partitions and $\sigma$ itself, so $w_\sigma=\tfrac19-3\cdot\tfrac19+\tfrac13-a+(a-\tfrac19)=0$; for a cut with $|X|=|Y|=2$, $w_\sigma=\tfrac19-2\cdot\tfrac19+a-(a-\tfrac19)=0$. Proposition 3.10 therefore gives an independent derivation of the identity $\mathrm{GM}^{(4)}_3=-(a-\tfrac19)I_3$ for all normalized pure qubit stabilizer states. Akella, Iizuka and Miyata state this identity as their Eq. (3), support it numerically on $10^5$ randomly sampled stabilizer states (their §III), and pose in their §VI whether a counting argument exists for $n=3$ as an open question. A proof of the identity for all pure qubit stabilizer states was previously established; it is recalled here and not claimed by this volume. Stance: literature-attested for the definition (their Eq. (5), §II); the identity for all stabilizer states is previously established and not claimed here; the vanishing of the weights $w_\sigma$, and hence the derivation through Proposition 3.10, is repo-derived.

**Corollary 3.12 (Coarse data determine the replica-three multi-entropies).** Let $(\psi,\mathrm{col})$ and $(\psi',\mathrm{col}')$ be normalized pure qubit stabilizer states, on possibly different numbers of qubits, each with a colouring into $[\mathtt q]$. If $S_3^{(2)}(\sigma)$ agrees for the two states for every $\sigma\in\Pi_2(\mathtt q)$ and $S_3^{(3)}(\pi)$ agrees for every $\pi\in\Pi_3(\mathtt q)$, then $S_3^{(k)}(\rho)$ agrees for every $\rho\in\Pi(\mathtt q)$ with $|\rho|\ge2$; in particular $S_3^{(\mathtt q)}(\psi,\mathrm{col})=S_3^{(\mathtt q)}(\psi',\mathrm{col}')$. Stance: suspected-novel (§6).

**Proof.** By Corollary 3.5, $S_3^{(2)}(\sigma)=\tfrac12\log2\cdot r(\sigma)$ for $\sigma\in\Pi_2(\mathtt q)$, and for $\pi\in\Pi_3(\mathtt q)$, $r(\pi)=\tfrac{6}{\log2}S_3^{(3)}(\pi)-\sum_{\sigma\ge\pi,\,|\sigma|=2}r(\sigma)$. Hence the hypotheses determine $r(\sigma)$ for every $\sigma\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)$, computed from any graph forms of the two states, and these values agree. By Corollary 3.5 each $S_3^{(k)}(\rho)$ is a fixed linear combination of these ranks. ∎

## 4. Boundaries

**Remark 4.1 (What is not addressed).** All statements concern normalized pure qubit stabilizer states, the replica index $n=3$ and the replica convention of Convention 2.2. The volume makes no statement about other replica indices, qudit stabilizer states, mixed states or non-stabilizer states. Proposition 3.10 gives a sufficient condition only. The map $c\mapsto w$ is onto, since it is triangular for the refinement order with diagonal entries $3^{2-|\sigma|}\ne0$; hence the converse, that $L$ vanishing on all stabilizer states forces $w_\sigma=0$ for all $\sigma$, holds exactly when the functions $r(\sigma)$, $\sigma\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)$, are linearly independent over the set of stabilizer states and colourings. This is not decided here. The source of Remark 3.11 defines the genuine multi-entropy only for four parties and states a collapse for generic $\mathtt q\ge4$ and $n<\mathtt q$ without fixing a definition for $\mathtt q\ge5$; this volume fixes no such definition and makes no statement about that collapse.

**Open question 4.2 (Necessity of the criterion).** For which $\mathtt q$ are the functions $(\psi,\mathrm{col})\mapsto r(\sigma)$, $\sigma\in\Pi_2(\mathtt q)\cup\Pi_3(\mathtt q)$, linearly independent over normalized pure qubit stabilizer states, so that the criterion of Proposition 3.10 is also necessary?

## 5. Proof dependencies

**Remark 5.1 (Dependency order).** Theorem 3.4 uses Definitions 3.1 and 3.2 and the recalled replica rank formula. Corollary 3.5 uses Theorem 3.4. Theorem 3.8 uses Corollary 3.5. Proposition 3.10 and Corollary 3.12 use Corollary 3.5. Remarks 3.6, 3.9 and 3.11 are applications and are not used in any proof.

## 6. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| S. Akella, N. Iizuka, A. Miyata, *Genuine Multi-Entropy in the Toric Code*, arXiv:2607.06050v1, §I Eq. (3), §II Eq. (5), §III, §VI, Appendix A | `literature-attested`: the replica definition of $Z_n^{(\mathtt q)}$ and $S_n^{(\mathtt q)}$ with the last party unshifted (Convention 2.2, Appendix A), the definition of $\mathrm{GM}^{(4)}_n$ (Eq. (5), Remark 3.11), and the conjectured collapse for generic $\mathtt q$ mentioned in Remark 4.1. The identity $\mathrm{GM}^{(4)}_3=-(a-\tfrac19)I_3$ is stated there (Eq. (3)) and supported only numerically on $10^5$ random stabilizer states (§III); §VI poses a counting argument for $n=3$ as open. The source defines the genuine multi-entropy only for $\mathtt q=4$ and gives no partition formula for $S_3^{(\mathtt q)}$. |
| A. Gadde, V. Krishna, T. Sharma, *New multipartite entanglement measure and its holographic dual*, Phys. Rev. D 106 (2022) 126001, arXiv:2206.09723 | `literature-attested`: the multi-entropy and its replica definition (Convention 2.2). |
| M. Van den Nest, J. Dehaene, B. De Moor, *Graphical description of the action of local Clifford transformations on graph states*, Phys. Rev. A 69 (2004) 022316; D. Schlingemann, *Stabilizer codes can be realized as graph codes*, Quantum Inf. Comput. 2 (2002) 307–323 | `literature-attested`: every stabilizer state is local-Clifford equivalent to a graph state (Convention 2.3). |
| M. Hein, J. Eisert, H. J. Briegel, *Multiparty entanglement in graph states*, Phys. Rev. A 69 (2004) 062311 | `literature-attested`: the entanglement entropy of a graph state across a bipartition equals $\log2$ times the $\mathbb F_2$-rank of the off-diagonal adjacency block (Remark 3.6). |
| B. Czech, Y. Feng, X. Wu, M. Xie, *Fun with Graph States: Nonlocal Bell Pairs and the Arf Invariant*, arXiv:2606.06582v2, Appendix B, Eq. (B.9) | `literature-attested`: the value $S_n^{(3)}=(1+\tfrac1n)\log2$ for the three-qubit chain state (Remark 3.6). The appendix gives values for specific chain states and no partition decomposition. |
| — | Previously established, not claimed here: the replica rank formula recalled in §2, generalising the bipartite rank formula of Hein, Eisert and Briegel to the replica convention of Appendix A of arXiv:2607.06050v1, used as a cited step; and the identity $\mathrm{GM}^{(4)}_3=-(a-\tfrac19)I_3$ for all pure qubit stabilizer states (Remark 3.11). |
| — | `repo-derived`: Definitions 3.1, 3.2, Remark 3.9, the computation in Remark 3.6, and the vanishing of the weights $w_\sigma$ in Remark 3.11. |
| — | `suspected-novel`: Theorem 3.4, Corollary 3.5, Theorem 3.8, Proposition 3.10, Corollary 3.12. Searched: the TeX source of arXiv:2607.06050v1; arXiv:2601.16258 (multi-invariants of stabilizer states, Coxeter counting at $n=2$, explicit tripartite formulas); arXiv:2608.29627 (Chern–Simons multi-entropy, reporting the four-party $n=3$ collapse numerically); Appendix B of arXiv:2606.06582; web searches combining "multi-entropy" with "stabilizer", "graph state", "replica", "rank" and "GF(2)". None of these states a decomposition of $S_3^{(\mathtt q)}$ over partitions into two or three blocks for general $\mathtt q$, the reduction of Theorem 3.8, or the criterion of Proposition 3.10; this establishes no priority beyond the searched scope. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）

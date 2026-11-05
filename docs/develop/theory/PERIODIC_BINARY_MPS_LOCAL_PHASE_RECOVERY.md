# Periodic binary matrix product states: three-site phase recovery

## 1. Actual states and raw reduced densities

**Definition 1.1 (Periodic shared-matrix image).** For a fixed integer $N\ge4$, let $\mathcal H_N=(\mathbb C^2)^{\otimes N}$, with its standard Hermitian inner product. For arbitrary shared matrices $A_0,A_1\in M_2(\mathbb C)$, put

$$
\Psi_N(A_0,A_1)=\sum_{i_1,\ldots,i_N\in\{0,1\}}
\operatorname{tr}(A_{i_1}\cdots A_{i_N})\,|i_1\cdots i_N\rangle,
\qquad
P_N=\{\Psi_N(A_0,A_1):A_0,A_1\in M_2(\mathbb C)\}.
$$

Thus $P_N=\mathrm{PB}(2,2,N)$ is the actual image, rather than its closure. This is the model of Critch and Morton, *Algebraic Geometry of Matrix Product States*, [arXiv:1210.2812v4](https://arxiv.org/abs/1210.2812v4), §2, equation (1). Cyclic invariance of the trace gives $\tau\psi=\psi$ for the cyclic site shift $\tau$ and every $\psi\in P_N$. The set $P_N$ is a complex cone: for $c\in\mathbb C$, choose $z$ with $z^N=c$, so that $\Psi_N(zA_0,zA_1)=c\Psi_N(A_0,A_1)$.

**Definition 1.2 (Raw marginal and phase fibre).** For $1\le k\le N$ and $\psi\in\mathcal H_N$, define

$$
\rho_k(\psi)=\operatorname{Tr}_{k+1,\ldots,N}(|\psi\rangle\langle\psi|),
\qquad
[\rho_k(\psi)]_{u,v}=
\sum_{b\in\{0,1\}^{N-k}}\psi_{ub}\,\overline{\psi_{vb}},
\quad u,v\in\{0,1\}^k.
$$

The empty complement at $k=N$ gives $\rho_N(\psi)=|\psi\rangle\langle\psi|$. In particular,

$$
\operatorname{tr}\rho_k(\psi)=\|\psi\|^2,
\qquad
\rho_k(c\psi)=|c|^2\rho_k(\psi).
$$

For nonzero $\psi\in P_N$, its actual-model fibre is

$$
\mathcal F_{N,k}(\psi)=\{\phi\in P_N:\rho_k(\phi)=\rho_k(\psi)\},
\qquad
S^1\psi=\{c\psi:c\in\mathbb C,\ |c|=1\}.
$$

No norm division occurs in $\rho_k$. This is the raw map displayed after Conjecture 10 of Critch–Morton. One may instead restrict both target and competitor to unit norm; that is an additional domain restriction. Dividing the output by $\|\psi\|^2$ on the unrestricted nonzero cone defines a different map, invariant under every $c\in\mathbb C^*$, whose fibres therefore cannot be $S^1$-orbits. For a cyclically invariant state, every adjacent $k$-site block, including a block crossing the chosen site origin, has the same $\rho_k$ after identification in cyclic order.

**Definition 1.3 (Intrinsic rank locus).** For $\psi\in\mathcal H_N$, let $F_{N,2}(\psi)$ be its $4\times 2^{N-2}$ amplitude flattening, with entries

$$
[F_{N,2}(\psi)]_{u,b}=\psi_{ub},
\qquad u\in\{0,1\}^2,\quad b\in\{0,1\}^{N-2}.
$$

Put

$$
U_N=\{\psi\in P_N:\operatorname{rank}F_{N,2}(\psi)=4\}.
$$

A property is called generic here when it holds on a nonempty relatively complex-Zariski-open dense subset of $P_N$. The criterion defining $U_N$ is intrinsic to the state and imposes no choice of its matrix representation.

## 2. Three-site phase fibres

**Theorem 2.1 (Generic three-site recovery on the actual image).** For every fixed $N\ge4$, the set $U_N$ is nonempty and relatively complex-Zariski-open dense in $P_N$. For every $\psi\in U_N$ and every $\phi\in P_N$,

$$
\rho_3(\phi)=\rho_3(\psi)
\quad\Longleftrightarrow\quad
\phi=c\psi\ \text{for some }c\in\mathbb C\text{ with }|c|=1.
$$

Equivalently, $\mathcal F_{N,3}(\psi)=S^1\psi$. The competitors are all actual states of the same fixed length, with arbitrary complex shared matrices; no genericity, injectivity, or equality of matrix parameterizations is assumed for them. Moreover, the target condition is observable and fibre-saturated:

$$
\psi\in U_N
\quad\Longleftrightarrow\quad
\det\rho_2(\psi)\ne0
\quad\Longleftrightarrow\quad
\det\bigl(\operatorname{Tr}_3\rho_3(\psi)\bigr)\ne0.
$$

Proof. For a representation $\psi=\Psi_N(A_0,A_1)$, write $A_w=A_{w_1}\cdots A_{w_\ell}$ and

$$
S_\ell(A)=\operatorname{span}_{\mathbb C}\{A_w:w\in\{0,1\}^\ell\},
\qquad
\Gamma_\ell^A(X)=\sum_{w\in\{0,1\}^\ell}\operatorname{tr}(XA_w)|w\rangle.
$$

The trace pairing on $M_2(\mathbb C)$ is nondegenerate: $\operatorname{tr}(XE_{ab})=X_{ba}$. Hence $\Gamma_\ell^A$ is injective exactly when $S_\ell(A)=M_2(\mathbb C)$. Also,

$$
[F_{N,2}(\psi)]_{u,b}=\operatorname{tr}(A_uA_b),
\qquad
\operatorname{rank}F_{N,2}(\psi)\le\dim S_2(A)\le4.
$$

Thus $\psi\in U_N$ forces $S_2(A)=M_2(\mathbb C)$ in every representation of $\psi$, and supplies injectivity at length $L_0=2$.

For nonemptiness, take

$$
A_0=\begin{pmatrix}1&0\\0&t\end{pmatrix},
\qquad
A_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},
\qquad t\in\mathbb C\setminus\{0,1,-1\}.
$$

The diagonal matrices $A_0^2=\operatorname{diag}(1,t^2)$ and $A_1^2=I$ are independent. The off-diagonal matrices

$$
A_0A_1=\begin{pmatrix}0&1\\t&0\end{pmatrix},
\qquad
A_1A_0=\begin{pmatrix}0&t\\1&0\end{pmatrix}
$$

are independent because $1-t^2\ne0$. Thus $S_2(A)=M_2(\mathbb C)$. Since $A_0$ is invertible and $S_{\ell+1}(A)\supseteq S_\ell(A)A_0$, induction gives $S_\ell(A)=M_2(\mathbb C)$ for every $\ell\ge2$. Both word maps into the trace pairing, at lengths $2$ and $N-2$, are therefore surjective. Its nondegeneracy gives $\operatorname{rank}F_{N,2}(\Psi_N(A))=4$ for every $N\ge4$, including $N=4$.

The rank-four condition is the nonvanishing of at least one $4\times4$ minor of the flattening. It is therefore relatively Zariski open. The polynomial image $P_N$ of the irreducible space $M_2(\mathbb C)^2$ is irreducible in its induced Zariski topology, so the nonempty open subset $U_N$ is dense. It is also dense in the ordinary topology: the inverse image of the rank-four locus is a nonempty Zariski-open subset of the parameter space, hence ordinarily dense; continuity of $\Psi_N$ then approximates every actual state by states in $U_N$.

Now fix $\psi\in U_N$ and one representation $A$. Let $G_3=\operatorname{im}\Gamma_3^A$ and let $h$ be the orthogonal projector onto $G_3^\perp$. For each complement word $b\in\{0,1\}^{N-3}$, the conditional three-site vector has entries

$$
(v_b)_u=\operatorname{tr}(A_uA_b)=\operatorname{tr}(A_bA_u),
\qquad v_b=\Gamma_3^A(A_b)\in G_3.
$$

Consequently $\rho_3(\psi)=\sum_b v_bv_b^\dagger$ has range contained in $G_3$, and $\operatorname{tr}(h\rho_3(\psi))=0$.

Use the finite-ring parent uniqueness theorem of Pérez-García, Verstraete, Wolf and Cirac, *Matrix Product State Representations*, [quant-ph/0608197v2](https://arxiv.org/abs/quant-ph/0608197v2), Theorem 10, “Uniqueness with TI and PBC”, §4.1.2. Its space $\mathcal G_L$ is precisely $\operatorname{im}\Gamma_L^A$, and its Hamiltonian is the sum of all cyclic translates of the projector onto $\mathcal G_L^\perp$. Its hypotheses are injectivity at length $L_0$, $L_0<L\le N$, and $N\ge2L_0$. Here $L_0=2$, $L=3$, and $N\ge4$, so the theorem yields

$$
H=\sum_{s=0}^{N-1}\tau^s(h\otimes I_{N-3})\tau^{-s},
\qquad
\ker H=\mathbb C\psi.
$$

This invocation uses the published parent theorem, rather than a parameter-identifiability theorem. The ground-space statement concerns a ray; any unit-norm convention for the vector in that theorem is accommodated by scaling both matrices by an $N$th root of $1/\|\psi\|$, which preserves every $G_L$ and every injectivity length.

If an arbitrary $\phi\in P_N$ has $\rho_3(\phi)=\rho_3(\psi)$, then

$$
\|(h\otimes I_{N-3})\phi\|^2
=\operatorname{tr}(h\rho_3(\phi))
=\operatorname{tr}(h\rho_3(\psi))=0.
$$

Every cyclic translate also annihilates $\phi$, because $\tau\phi=\phi$. Hence $H\phi=0$, so $\phi=c\psi$. Taking the trace of the equal raw marginals gives $\|\phi\|^2=\|\psi\|^2$, and $\psi\ne0$ gives $|c|=1$. Conversely every $c\psi$ with $|c|=1$ belongs to $P_N$ by its cone property and has the same raw marginal.

Finally $\rho_2(\psi)=F_{N,2}(\psi)F_{N,2}(\psi)^\dagger$. The kernels of $FF^\dagger$ and $F^\dagger$ agree, since $x^\dagger FF^\dagger x=\|F^\dagger x\|^2$; thus $\operatorname{rank}\rho_2(\psi)=\operatorname{rank}F_{N,2}(\psi)$. The identity $\rho_2=\operatorname{Tr}_3\rho_3$ proves the asserted observable criterion. Equality of three-site marginals therefore forces every competitor into $U_N$ as well, although this was not an assumption of the argument.

At $N=4$, the complement of the three-site block has only one qubit, so $\operatorname{rank}\rho_3(\psi)\le2$. The proof uses only $\operatorname{im}\rho_3(\psi)\subseteq G_3$, never equality of these spaces. The parent theorem's inequalities still hold at $N=4$. This completes the proof for the whole stated range. $\square$

## 3. The four-site assertion and its minimality clause

**Corollary 3.1 (Disposition of the literal four-site claim).** For every fixed $N\ge4$ and every $\psi\in U_N$,

$$
\mathcal F_{N,4}(\psi)=\mathcal F_{N,3}(\psi)=S^1\psi.
$$

Thus four adjacent sites suffice generically on the actual model, while four is not the generic minimum. In the same range, three adjacent sites already suffice on a nonempty relatively Zariski-open dense set of actual states. This disproves the literal “but no fewer” clause in Critch–Morton, [arXiv:1210.2812v4](https://arxiv.org/abs/1210.2812v4), Conjecture 10:

> A generic $N$-qubit $(D=d=2)$ periodic translation invariant matrix product state $\Psi$ is determined up to phase by a reduced density operator which traces out all but a chain of four adjacent states, but no fewer.

Proof. Equality of four-site raw marginals implies equality of their three-site partial traces. Theorem 2.1 gives the phase conclusion, and the converse follows from phase invariance. Cyclic symmetry makes the conclusion independent of the adjacent block's position. For $N=4$, the four-site operator is simply the full rank-one operator $|\psi\rangle\langle\psi|$, while the three-site conclusion still follows from Theorem 2.1. Four distinct adjacent sites are defined only for $N\ge4$; the quoted conjecture gives no separate lower-bound convention for $N<4$. The source describes generic fibres of its real-algebraic raw map without specifying a formal genericity convention; the explicit state locus $U_N$, and its determinant criterion in the observed marginal, supply the genericity used here. No conclusion about whether two adjacent sites suffice follows from this proof. $\square$

## 追加锚（本行以下为增补区）

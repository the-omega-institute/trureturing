# Recursive relational observation: minimal pure records for the five-mode dilation

## 1. Fixed source and three readout contracts

**定义 1.1（Versioned source and parameter domain）。** The source of the configuration matrix and internal transports is [AURIC_FIB_HISTORY_RECORDS_TIME_ARROW, revision 6bfd5342e47ba7eb50a5022e301d228f17daa8d2, §§126–135](https://github.com/the-omega-institute/trureturing/blob/6bfd5342e47ba7eb50a5022e301d228f17daa8d2/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md). Its matrix (129.1), transports (127.1), inverse reverse edges and identity self-loops are fixed throughout this volume. The parameters range over

$$
\mathcal D=\{(p,q,r)\in\mathbb R^3:p,q,r>0,\ p+q+r<1\}.
$$

Write

$$
t=p+q,\qquad B=1-t,\qquad A=B-r,\qquad C=1-r=A+t.
\tag{1.1}
$$

All of $p,q,r,t,A,B,C$ are strictly positive. There is no exclusion of $p=q$ or any other equality inside $\mathcal D$, and no lower cutoff on a positive branch probability.

The configurations, in source order, are

$$
s_0=\mathrm{null}=000,\quad s_1=2=100,\quad
s_2=25=101,\quad s_3=5=001,\quad s_4=3=010,
$$

where the words use the source's low-to-high convention. The source-row, successor-column matrix is

$$
P=\begin{pmatrix}
A&p&0&q&r\\
q&B&p&0&0\\
0&q&B&p&0\\
p&0&q&B&0\\
r&0&0&0&C
\end{pmatrix}.
\tag{1.2}
$$

Let $\mathcal C=\mathbb C^5$, $K=\mathbb C^2$ and $H=\mathcal C\otimes K$. With the standard Pauli matrices, put

$$
a=-\mathrm iX,\qquad b=-\mathrm iY,\qquad c=ba=\mathrm iZ.
$$

The forward square edges and the leaf edge have transports

$$
U_{10}=a,\quad U_{21}=c,\quad U_{32}=a^\dagger,
\quad U_{03}=c^\dagger,\quad U_{40}=b.
\tag{1.3}
$$

Each reverse edge has the adjoint transport, and $U_{ii}=I_K$. In particular, $U_{04}=b^\dagger$. These are the assignments of §127; the different assignment in §124 is not used. Let $\mathcal A=\{(j,i):P_{ij}>0\}$ denote the fifteen positive directed edges, including five loops. A zero entry contributes no edge and requires no record.

**定义 1.2（One common pure-record realization）。** An admissible realization consists of a finite complex Hilbert space $E$ and one jointly existing family of unit vectors $e_{ji}\in E$, $(j,i)\in\mathcal A$, for which

$$
V(|i\rangle\otimes\psi)=
\sum_{j:P_{ij}>0}\sqrt{P_{ij}}\,
|j\rangle\otimes U_{ji}\psi\otimes e_{ji}
\tag{1.4}
$$

is an isometry on the whole ten-dimensional $H$. No restriction to basis preparations or a fixed internal vector is made. The environment is initially pure; $E$ is the entire auxiliary output of this one-step realization. There is no source copy, hidden reference, bypass, extra flag or source-dependent side register. An untouched reference $R$ is allowed as part of the input domain, with the map $V\otimes I_R$; it is not available as an additional record or decoder input.

The source's cross-input criterion (126.1) is reused in precisely this domain:

$$
\sum_j\sqrt{P_{ij}P_{kj}}\,
\langle e_{ji},e_{jk}\rangle U_{ji}^\dagger U_{jk}
=\delta_{ik}I_K.
\tag{1.5}
$$

The inner product is conjugate linear in its first argument. Equation (1.5) follows by comparing all inner products of $|i\rangle\psi$ and $|k\rangle\phi$; hence it tests arbitrary coherent input and arbitrary internal vectors. Merely checking $i=k$ does not establish admissibility. In finite dimension, an isometry with a pure initial environment has a unitary extension on $H\otimes E$, by extending its image of $H\otimes|\mathrm{ready}\rangle$ to an orthonormal basis. The choice of such an extension does not supply physical control permissions.

**定义 1.3（Task-relative record minima）。** Define three minima over the same family (1.4).

1. $d_{\mathrm{un}}$ requires only the common full-input isometry. No exact edge read is required.
2. $d_{\mathrm{succ}}$ also requires exact, deterministic one-shot identification of every positive edge when its actual successor $j$ is available to the decoder. For each $j$, a common POVM on $E$, selected using that actual $j$, must distinguish the vectors $\{e_{ji}:P_{ij}>0\}$. No source label is given to this decoder.
3. $d_E$ requires exact, deterministic one-shot identification of all fifteen positive edges using $E$ alone, with one POVM independent of an unknown edge.

The readout requirement is on every individual positive edge, without dropping rare edges, permitting an inconclusive outcome, or adding an error probability. For coherent input, an edge outcome refers to a specified instrument; an unmeasured superposition is not assigned an already acquired classical edge. In the second task the actual successor interface is an additional permitted read, whose measurement and output carrier are separately counted. The internal input can be arbitrary and is not a known orthogonal label. Definitions of POVMs, completely positive branches and instruments are used at their finite-dimensional scope; see John Watrous, [The Theory of Quantum Information, 2018, Chapter 2, §2.3.2, equations (2.255)–(2.262)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf).

**假设 1.4（Operational supply）。** The parameters, edge transports and phase conventions are supplied model data. Physical access to a register, its preparation, any measurement, a retained result, controlled transport or inverse transport, calibration, and repeated fresh environments are separate assumptions whenever used below. Exact real parameter notation is information-theoretic data; it is not a finite executable precision or calibration guarantee. The five-mode graph is a configuration graph, not a physical spacetime graph. Its $P$ and $U$ are not derived here from native $\alpha/\beta$ syntax or tree replacement.

## 2. Exact unlabelled minimum and a correctable minimizing realization

**定理 2.1（A joint two-dimensional construction on the full domain）。** For every $(p,q,r)\in\mathcal D$,

$$
d_{\mathrm{un}}=2.
\tag{2.1}
$$

There is a minimizing realization $V_2$ whose reduced channel is a mixture of two unitaries on the entire $H$.

Choose a single orthonormal basis $f_0,f_1$ of $E_2=\mathbb C^2$. Assign $f_1$ to all eight non-loop directed square edges; assign $f_0$ to the four loops at $0,1,2,3$ and both leaf edges. Assign the remaining loop the vector

$$
e_{44}=\frac{-\sqrt A\,f_0+\sqrt t\,f_1}{\sqrt C}.
\tag{2.2}
$$

All fifteen vectors belong to this one $E_2$, and (2.2) has norm one because $C=A+t$. The minus sign is part of the record vector; the stipulated $U_{44}=I_K$ is unchanged.

**证明。** The lower bound is the source's already established unique-common-successor obstruction (§129, (129.2), using Lemma 126.3). Sources $1$ and $4$ have the unique common successor $0$, with positive probabilities $q,r$. Equation (1.5) therefore forces $e_{01}\perp e_{04}$. Two normalized orthogonal vectors require $\dim E\ge2$. This argument uses $q,r>0$ and applies at every equality stratum in $\mathcal D$; it does not assume edge readability.

For the upper bound, let

$$
Q=\sum_{i=0}^3|i\rangle\langle i|\otimes I_K,
\qquad F=|4\rangle\langle4|\otimes I_K.
$$

Let $S$ agree with the source's transported square cycle on $QH$ and be zero on $FH$:

$$
S=|1\rangle\langle0|\otimes a
+|2\rangle\langle1|\otimes c
+|3\rangle\langle2|\otimes a^\dagger
+|0\rangle\langle3|\otimes c^\dagger.
\tag{2.3}
$$

The source's square identity (128.1) gives

$$
S^\dagger S=SS^\dagger=Q,\qquad S^4=-Q,
\qquad S^2+(S^\dagger)^2=0.
\tag{2.4}
$$

For completeness, the first equalities follow because the square cycle permutes four orthogonal configuration summands by unitaries. At root $0$ the four-step product is $c^\dagger a^\dagger ca=-I_K$, by $ac=-ca$; at each other root it is a conjugate of this product. On $QH$, $S^{-2}=-S^2$, proving the last equality; on $FH$ both sides vanish. Only these operator identities are borrowed from §128. That section's independent four-state probabilities $p_4+q_4=1$ are not substituted for the full five-state parameters.

Expanding the common vector family in $f_0,f_1$ yields

$$
V_2x=L_0x\otimes f_0+L_1x\otimes f_1,
\tag{2.5}
$$

where

$$
\begin{aligned}
L_0={}&\operatorname{diag}(\sqrt A,\sqrt B,\sqrt B,
\sqrt B,-\sqrt A)\otimes I_K\\
&+\sqrt r\bigl(|4\rangle\langle0|\otimes b
+|0\rangle\langle4|\otimes b^\dagger\bigr),\\
L_1={}&\sqrt p\,S+\sqrt q\,S^\dagger+\sqrt t\,F.
\end{aligned}
\tag{2.6}
$$

For example, the input $4$ contributes $\sqrt r\,|0\rangle b^\dagger\psi\otimes f_0$ and
$|4\rangle\psi\otimes(-\sqrt A f_0+\sqrt t f_1)$, exactly $\sqrt C e_{44}$ on its loop. The other four sources have their prescribed loop and forward/reverse square coefficients. Thus (2.6) implements the exact (1.2)–(1.4).

On the ordered summands $0,4$, $L_0$ is the Hermitian block

$$
\begin{pmatrix}
\sqrt A I_K&\sqrt r\,b^\dagger\\
\sqrt r\,b&-\sqrt A I_K
\end{pmatrix}.
$$

Its square is $(A+r)I=B I$: the diagonal blocks use $b^\dagger b=bb^\dagger=I_K$ and the off-diagonal blocks cancel. On each of $1,2,3$, the square is $B I_K$. Therefore $L_0^\dagger L_0=B I_H$. Since $SF=FS=0$, (2.4) gives

$$
\begin{aligned}
L_1^\dagger L_1
&=(p+q)Q+\sqrt{pq}\bigl(S^2+(S^\dagger)^2\bigr)+tF\\
&=tI_H.
\end{aligned}
\tag{2.7}
$$

Consequently $V_2^\dagger V_2=(B+t)I_H=I_H$. This is an operator identity on the whole $H$, including cross-input blocks. Tensoring with $I_R$ gives the same identity for any untouched reference, and hence for arbitrary entangled input. The fifteen vectors have been supplied jointly; no separate-row Gram assumption is used.

Set

$$
T_0=B^{-1/2}L_0,\qquad T_1=t^{-1/2}L_1.
\tag{2.8}
$$

Each square operator is an isometry on the finite-dimensional $H$ and hence a unitary. Tracing $E_2$ gives

$$
\Phi_2(\rho)=B T_0\rho T_0^\dagger+tT_1\rho T_1^\dagger.
\tag{2.9}
$$

This channel is trace preserving and unital. Its two Kraus operators are linearly independent: the $1,1$ configuration block of $L_0$ is $\sqrt B I_K$, whereas that of $L_1$ is zero, and $L_1$ is nonzero. Its Choi rank is therefore two by the standard Kraus vectorization formula. That fixed-channel fact is additional to, and does not replace, the variable-family lower bound. $\square$

The Gram factorization principle and the Kraus/Choi identities used inside this proof are existing suppliers, not new general theorems: [AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION, revision 6bfd5342e47ba7eb50a5022e301d228f17daa8d2, §109](https://github.com/the-omega-institute/trureturing/blob/6bfd5342e47ba7eb50a5022e301d228f17daa8d2/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md), and Watrous, 2018, Theorem 2.22 and Corollary 2.27. The new bridge in Theorem 2.1 is the joint family (2.2)–(2.6), extending the transported square cancellation to the stipulated leaf and positive loops throughout $\mathcal D$.

**定理 2.2（Conditional entire-input and reference recovery for the named $V_2$）。** The realization of Theorem 2.1 can be supplied with one pure initial state in the same $E_2$ and a unitary interaction on $H\otimes E_2$. If the environment basis $f_0,f_1$ is actually measured and its outcome is supplied to a controller permitted to apply $T_0^\dagger$ or $T_1^\dagger$, the entire input density operator on $H\otimes R$ is recovered, for every untouched reference and every input density operator. This is an existence statement for the named minimizing realization, not a statement that every minimizer is unital or admits this recovery.

**证明。** Prepare

$$
|\mathrm{ready}\rangle=\sqrt B f_0+\sqrt t f_1
$$

in $E_2$ and apply

$$
\mathsf U=T_0\otimes|f_0\rangle\langle f_0|
+T_1\otimes|f_1\rangle\langle f_1|.
\tag{2.10}
$$

Orthogonal control projections and the unitarity of $T_0,T_1$ give $\mathsf U^\dagger\mathsf U=\mathsf U\mathsf U^\dagger=I$. On $x\otimes|\mathrm{ready}\rangle$, its output is (2.5). Thus no second control flag, source register or hidden purification is needed for this one-step interaction.

Write $w_0=B,w_1=t$. Environment outcome $\mu$ gives the unnormalized system-reference branch

$$
w_\mu(T_\mu\otimes I_R)\rho_{HR}
(T_\mu^\dagger\otimes I_R).
\tag{2.11}
$$

Its probability is $w_\mu$, independent of the entire input. The permitted inverse conjugation maps it to $w_\mu\rho_{HR}$. Normalizing either positive branch recovers $\rho_{HR}$; summing the corrected branches also recovers it. This calculation is the finite-dimensional correction criterion of M. Gregoratti and R. F. Werner, [Quantum Lost and Found, arXiv:quant-ph/0209025v1, Proposition 2 and §II.C.1](https://arxiv.org/abs/quant-ph/0209025v1), applied to the specific (2.6). It preserves arbitrary configuration coherence, arbitrary internal input and all reference correlations. $\square$

**假设 2.3（Flag recovery resources）。** The implication in Theorem 2.2 requires access to the actual outgoing $E_2$, the specified basis measurement, its result carrier and communication, the parameter-dependent inverse controls and their calibration. These resources are additional to the two-dimensional pure interaction environment. Recovery reverses the forward system update; it does not retain that update while also recreating an independent copy of the unknown input. The two-valued result is a unitary-mixture flag, not an exact edge label. An environment-only trace-preserving operation followed by discarding the environment is not this feedback operation: it leaves the system's reduced state unchanged, as in second-order completion §108.3.

## 3. Retained logical relations and lost edge distinctions

**定理 3.1（The framed logical factor survives the smaller records）。** For $V_2$ of Theorem 2.1 and $V_4$ of Theorem 4.1 below, the full framed internal matrix algebra is preserved by the reduced channel. In particular, the framed logical-reference marginal is preserved for every joint configuration-logical-reference density operator. This statement does not assert preservation of the whole configuration-logical-reference state.

**证明。** Use exactly the published source frames (§§131–132):

$$
G_0=I_K,\quad G_1=a,\quad G_2=ca=-b,
\quad G_3=a^\dagger ca=-c,\quad G_4=b.
\tag{3.1}
$$

The source's edge factorization is $U_{ji}=\varepsilon_{ji}G_jG_i^\dagger$, where $\varepsilon_{ji}=-1$ exactly for $(j,i)=(0,3),(3,0)$ and is $+1$ on the other positive edges. Let

$$
D=\sum_i|i\rangle\langle i|\otimes G_i^\dagger.
$$

For either supplied vector family, changing input and output frames transforms (1.4) into a configuration map tensored with the identity on $K$:

$$
(D\otimes I_E)VD^\dagger=W\otimes I_K,\qquad
W|i\rangle=\sum_j\varepsilon_{ji}\sqrt{P_{ij}}\,
|j\rangle\otimes e_{ji},
\tag{3.2}
$$

with the harmless tensor-factor permutation understood. Since $V$ is an isometry, $W^\dagger W=I_{\mathcal C}$. Its reduced configuration map $\Psi$ is trace preserving. The framed reduced channel is $\Psi\otimes\operatorname{id}_K$.

For any $M\in M_2(\mathbb C)$ define

$$
\overline M=\sum_i|i\rangle\langle i|\otimes G_iMG_i^\dagger.
$$

In the changed frames this is $I_{\mathcal C}\otimes M$. Equation (3.2) and $W^\dagger W=I_{\mathcal C}$ give $\Phi^\dagger(\overline M)=\overline M$. For a joint framed density operator $\omega_{\mathcal C K R}=\sum_{i,k}|i\rangle\langle k|\otimes\omega_{ik}$, trace preservation gives

$$
\begin{aligned}
\operatorname{Tr}_{\mathcal C}
[(\Psi\otimes\operatorname{id}_{KR})(\omega)]
&=\sum_{i,k}\operatorname{tr}[\Psi(|i\rangle\langle k|)]\,\omega_{ik}\\
&=\sum_i\omega_{ii}=\operatorname{Tr}_{\mathcal C}\omega.
\end{aligned}
\tag{3.3}
$$

Thus the complete logical matrix algebra and its reference marginal, not just three numerical Pauli labels, survive. The source supplied this gauge mechanism for its fixed edge channel; (3.2) establishes its correspondence for the two smaller joint realizations. Actual reading or changing the frames remains an operational assumption. $\square$

**命题 3.2（The named two-dimensional flag does not read actual edges）。** The realization $V_2$ fails exact positive-edge discrimination even with its successor available, and its unread reduced map is different from the published orthogonal-edge channel. More precisely, its environment basis read has conditional probabilities

$$
\begin{array}{c|cc}
\text{edge class}&\Pr(f_0)&\Pr(f_1)\\\hline
\text{four loops at }0,1,2,3\text{ and two leaf edges}&1&0\\
\text{eight non-loop square edges}&0&1\\
4\to4&A/C&t/C
\end{array}
\tag{3.4}
$$

Every input has the same unconditional flag probabilities $B,t$.

**证明。** Equation (3.4) is obtained from the assigned vectors, including (2.2). At successor $0$ one has

$$
e_{00}=e_{04}=f_0,\qquad e_{01}=e_{03}=f_1.
$$

Each listed edge is positive in $\mathcal D$. Identical vectors cannot be perfectly distinguished, so the actual successor does not resolve these pairs. An unknown internal output cannot serve as an extra distinguishable label: for any common unit vector $\phi$, choose the incoming internal vector for edge $i\to j$ to be $U_{ji}^\dagger\phi$. Its output is then the same $\phi$ on all compared edges. This respects the required arbitrary internal-input domain.

Let $\mathcal E_{\mathrm{edge}}(\rho)=\sum_{ji}K_{ji}\rho K_{ji}^\dagger$, with $K_{ji}=\sqrt{P_{ij}}|j\rangle\langle i|\otimes U_{ji}$ as in source §130. From source $1$ and any nonzero internal density operator $\rho$, the $(0,2)$ configuration block of $\Phi_2(|1\rangle\langle1|\otimes\rho)$ is

$$
\sqrt{pq}\,a^\dagger\rho c^\dagger\ne0,
\tag{3.5}
$$

since $1\to0$ and $1\to2$ have the same record $f_1$. The corresponding block of $\mathcal E_{\mathrm{edge}}$ is zero. The flag totals are $B,t$ either by (2.11) or by summing (3.4) with the outgoing row probabilities: at $0$, $A+r=B$; at $1,2,3$, the loop is $B$; and at $4$, $r+A=B$. $\square$

**假设 3.3（Task scope of logical retention）。** The framed internal factor, an actually acquired edge archive, the full input state and a future predictive state are distinct targets. Logical retention (3.3) supplies none of the lost edges in Proposition 3.2. The conditional feedback of Theorem 2.2 supplies full quantum recovery only under its measurement and inverse-control assumptions. A generic correspondence between symbols, frames and density operators does not add a legal read or history update.

## 4. Sharp edge-readable minima and the measurement carrier

**定理 4.1（Successor-assisted exact edge read costs four dimensions）。** In the exact source family,

$$
d_{\mathrm{succ}}=4.
\tag{4.1}
$$

A common four-dimensional family attains the bound on the whole coherent input and permits the published edge instrument when the successor and record are actually read.

**证明。** A normalized pure-state family is exactly deterministically distinguishable by a POVM only if its vectors are pairwise orthogonal. Indeed, if outcome effect $M_i$ identifies unit vector $v_i$ with probability one and $v_k$ with probability zero, positivity gives $M_iv_i=v_i$ and $M_iv_k=0$. To see these implications, use $\langle v_i,(I-M_i)v_i\rangle=0$ and $\langle v_k,M_iv_k\rangle=0$, and take positive square roots. Hence
$\langle v_i,v_k\rangle=\langle M_iv_i,v_k\rangle=\langle v_i,M_iv_k\rangle=0$.
Conversely orthogonal vectors have the distinguishing projection measurement, completed on the unused subspace. This standard discrimination fact is used here as an intermediate step, with no additional known internal label.

The positive incoming sets are

$$
I_0=\{0,1,3,4\},\quad I_1=\{0,1,2\},\quad
I_2=\{1,2,3\},\quad I_3=\{0,2,3\},\quad I_4=\{0,4\}.
\tag{4.2}
$$

Successor $0$ therefore demands four orthogonal record vectors, so $\dim E\ge4$ throughout $\mathcal D$.

For attainment take one orthonormal basis $g_0,g_1,g_2,g_3$ of $E_4=\mathbb C^4$ and the source color

$$
\kappa(0)=0,\quad\kappa(1)=1,\quad\kappa(2)=2,
\quad\kappa(3)=3,\quad\kappa(4)=2.
\tag{4.3}
$$

Set $e_{ji}=g_{\kappa(i)}$ on every positive edge, and call (1.4) with these records $V_4$. The color is injective on each set $I_j$ in (4.2). Thus whenever $i\ne k$ have a common successor, their incoming records there are orthogonal. Every summand of the off-diagonal equation (1.5) vanishes separately. For $i=k$, row normalization gives $I_K$. Consequently $V_4$ is a full-input isometry, also with any untouched reference. This color is the actual outgoing record in $E_4$; a copied-source side register is not appended.

Given actual successor $j$, measurement in the $g$ basis identifies the unique $i\in I_j$ with the returned color. Equivalently, the positive-edge projections on the joint output are

$$
Q_{ji}=|j\rangle\langle j|\otimes I_K
\otimes|g_{\kappa(i)}\rangle\langle g_{\kappa(i)}|,
\qquad (j,i)\in\mathcal A.
\tag{4.4}
$$

They are mutually orthogonal. Complete them with the projection onto the unused output subspace. The latter outcome has probability zero for every input because

$$
Q_{ji}V_4=K_{ji}\otimes g_{\kappa(i)}.
\tag{4.5}
$$

After the actual joint read and tracing the record, the unnormalized system branch is exactly
$K_{ji}\rho K_{ji}^\dagger$, including coherent input and reference extensions. Hence this is the source's edge instrument on the whole input domain, with a different pre-readout dilation. $\square$

The orthogonality/Gram language in this proof follows the unit-vector convention of Leslie Hogben, Kevin F. Palmowski, David E. Roberson and Simone Severini, [Orthogonal Representations, Projective Rank, and Fractional Minimum Positive Semidefinite Rank: Connections and New Directions, arXiv:1502.00016v2, §1.3](https://arxiv.org/abs/1502.00016v2): a required edge means a required zero inner product; no “if and only if” nonzero-pattern requirement is imposed here. The construction is also a source-specific block-unitary lift of incoming-row grouping: Kamil Korzekwa, Stanisław Czachórski, Zbigniew Puchała and Karol Życzkowski, [Coherifying quantum channels, arXiv:1710.04228v2, §III.B.2](https://arxiv.org/abs/1710.04228v2), give the scalar row-grouping supplier. Their successor-row convention is $T_{ji}=P_{ij}$, namely $T=P^{\mathsf T}$. Their scalar theorem does not itself impose the transports (1.3); (4.2)–(4.5) verify the necessary block correspondence and attain four rather than a generic five-dimensional bound.

**定理 4.2（Environment-alone read costs fifteen dimensions）。** For the third contract,

$$
d_E=15.
\tag{4.6}
$$

It is attained by the published $V_{\mathrm{edge}}$, whose unread reduced channel has minimum pure environment dimension fifteen even if no record read is requested.

**证明。** All fifteen positive edge vectors must be pairwise orthogonal by the discrimination argument within Theorem 4.1. Therefore $\dim E\ge15$. Give every edge one vector $h_{ji}$ of a single orthonormal basis of $\mathbb C^{15}$ and take

$$
V_{15}=\sum_{(j,i)\in\mathcal A}K_{ji}\otimes h_{ji}.
\tag{4.7}
$$

The source's §130 construction supplies this isometry: $\sum_{ji}K_{ji}^\dagger K_{ji}=I_H$. The basis measurement on $E$ alone produces exactly the fifteen branches $K_{ji}\rho K_{ji}^\dagger$, and identifies every edge. Thus (4.6) is sharp, independently of parameter equalities inside $\mathcal D$.

The fixed unread channel in (4.7) is $\mathcal E_{\mathrm{edge}}$. Its Choi rank fifteen and minimum pure dilation dimension fifteen are reused from source §130, not claimed as a new bound for the variable-channel class. The exact applicability is as follows. Distinct $|j\rangle\langle i|$ matrix units make the fifteen $\operatorname{vec}K_{ji}$ mutually orthogonal; each has squared norm $2P_{ij}>0$. Hence

$$
J(\mathcal E_{\mathrm{edge}})
=\sum_{ji}|\operatorname{vec}K_{ji}\rangle
\langle\operatorname{vec}K_{ji}|
$$

has rank fifteen. A pure environment of dimension $m$ supplies at most $m$ Kraus components, and this Choi formula then has rank at most $m$. Therefore $m\ge15$, attained by (4.7). The general supplier is Watrous, 2018, Theorem 2.22 and Corollary 2.27. The fixed channel and the edge-readable task happen to have the same minimum here; neither statement raises $d_{\mathrm{un}}$ to fifteen. $\square$

**命题 4.3（Four is a pre-readout record cost, not the whole cost of the fixed edge channel）。** Let $\Phi_4=\operatorname{Tr}_{E_4}\operatorname{Ad}_{V_4}$ and let $\Delta_{\mathcal C}$ dephase the successor configuration. Then

$$
(\Delta_{\mathcal C}\otimes\operatorname{id}_K)\circ\Phi_4
=\mathcal E_{\mathrm{edge}}.
\tag{4.8}
$$

There is a staged pure-environment construction of this unread fixed channel with the carrier $E_4\otimes D_5$, of dimension twenty and with fifteen occupied orthogonal directions. Any pure construction of the same fixed channel, including the added dephasing, still has total environment dimension at least fifteen.

**证明。** Expanding $V_4\rho V_4^\dagger$ and dephasing keeps only equal successor indices. At an equal successor, (4.2)–(4.3) make different source colors orthogonal, so tracing $E_4$ also keeps only equal source indices. The remaining terms are precisely $K_{ji}\rho K_{ji}^\dagger$, proving (4.8).

To supply dephasing by a pure dilation, append a fresh $D_5$ and use the isometry that copies the actual configuration basis label,

$$
|j\rangle\psi\longmapsto|j\rangle\psi\otimes d_j,
\qquad \langle d_j,d_k\rangle=\delta_{jk}.
\tag{4.9}
$$

After $V_4$, the total edge record is $g_{\kappa(i)}\otimes d_j$. Different positive edges have different pairs $(\kappa(i),j)$ by injectivity on $I_j$. These fifteen vectors are orthogonal in a twenty-dimensional carrier. Tracing both carriers gives (4.8). An isometric identification of their occupied span with $\mathbb C^{15}$ recovers the pure-record size of (4.7); this is a mathematical recoding, not a free physical operation. The lower bound on every pure realization of the fixed channel is Theorem 4.2's Choi bound. $\square$

**假设 4.4（Output and measurement accounting）。** Actual successor acquisition and the edge result in (4.4) require a measurement instrument, its permitted coupling and retained output. The complete edge outcome alphabet has fifteen possibilities; a fixed binary encoding needs $\lceil\log_2 15\rceil=4$ bits when that classical output is stored separately. If $j$ is already retained, the additional color alphabet has four possibilities and needs two fixed binary bits, without making the retained $j$ free. Dimension four counts $E_4$ before that readout. Calling the extra instrument a measurement does not supply a four-dimensional pure dilation of the unread fixed channel. Likewise dimension two in Theorem 2.1 counts a different, unlabelled channel and does not supply the fifteen-valued edge output.

## 5. Unmeasured repetitions and actual measured continuation

**命题 5.1（An all-domain unmeasured-history counterexample for $V_2$）。** Start $V_2$ at the known configuration $0$, with any internal density operator, including an arbitrary untouched reference. Use the same $V_2$ twice with two fresh pure $E_2$ environments. Make no intermediate successor measurement. A terminal configuration measurement then has return probability

$$
\Pr_{\mathrm{unmeasured}}(i_2=0)=B^2+4pq.
\tag{5.1}
$$

The Markov chain with the identical one-step matrix (1.2) has

$$
(P^2)_{00}=A^2+r^2+2pq,
\qquad B^2+4pq-(P^2)_{00}=2Ar+2pq>0.
\tag{5.2}
$$

Thus definite-source one-step agreement and fresh environments do not imply the Markov history law for unmeasured repetitions of this named minimizing realization, at any point of $\mathcal D$.

**证明。** Tracing the fresh environments yields $\Phi_2^2$, with Kraus words $L_\nu L_\mu$, $\mu,\nu\in\{0,1\}$. These words are mutually distinguished by the two environment basis factors, so their terminal probabilities add. Theorem 2.1 gives $L_0^2=B I_H$. Also

$$
L_1^2=pS^2+q(S^\dagger)^2+2\sqrt{pq}\,Q+tF
=(p-q)S^2+2\sqrt{pq}\,Q+tF.
\tag{5.3}
$$

The $0\to0$ block of $L_1^2$ is $2\sqrt{pq}I_K$. The words $L_1L_0$ and $L_0L_1$ have no $0\to0$ block: $L_0$ connects $0$ only to $0,4$, while $L_1$ connects $0$ to $1,3$ and fixes $4$; $L_0$ fixes $1,3$ up to a scalar. The return effects are consequently $(B^2+4pq)I_K$, giving (5.1) also with a reference. The classical return is the sum over $0\to0\to0$, $0\to1\to0$, $0\to3\to0$ and $0\to4\to0$, namely $A^2+pq+pq+r^2$. Since $B=A+r$, subtraction gives (5.2). Every term in its positive difference is strictly positive in $\mathcal D$. In particular $p=q$ does not remove it. $\square$

**命题 5.2（Branch expressions in $V_2$ do not acquire arbitrary history labels）。** In the two-step expansion from root $0$, the legal histories $(0,0,0)$ and $(0,4,0)$ have identical normalized terminal-internal-record vectors, for every internal input. At four steps, the two oppositely oriented square loops also have identical normalized terminal-internal-record vectors, although their signed square currents are different. These collisions occur throughout $\mathcal D$.

**证明。** The loop history $(0,0,0)$ contributes
$A|0\rangle\psi\otimes f_0\otimes f_0$. The leaf return contributes
$r|0\rangle b^\dagger b\psi\otimes f_0\otimes f_0
=r|0\rangle\psi\otimes f_0\otimes f_0$. Both coefficients are positive, but the normalized vectors agree. A putative isometry sending two independently orthogonal history inputs to these vectors would violate inner-product preservation, irrespective of internal or reference input. In the actual two-step map, those inputs were never independently supplied; their amplitudes interfere.

For $h_+=(0,1,2,3,0)$ the transport is $S^4=-I_K$, and for $h_-=(0,3,2,1,0)$ it is $(S^\dagger)^4=-I_K$. All four edge records are $f_1$ on either loop. The normalized outputs are therefore $-|0\rangle\psi\otimes f_1^{\otimes4}$ for both. If these paths are actually acquired by the measured instrument of Theorem 5.4, their probabilities from root $0$ are respectively $p^4,q^4$ and their currents are $+4,-4$. Under the separately declared uniform stationary initialization they are $p^4/5,q^4/5$. Their source §123.2 stationary direction-likelihood values are $\pm4\log(p/q)$; when $p=q$ both likelihood values vanish but the two paths and currents still differ. This uses the stipulated §127 transports; it does not import §124's assignment. The source's current statistic is sufficient for a fixed stationary forward/reverse likelihood comparison, not a bounded exact path archive or a proof of future prediction. $\square$

**定义 5.3（Measured continuation and initialization）。** Supply a successor measurement after each use of $V_2$. Its branches on $H$ are

$$
\mathcal J_j(\rho)=\Pi_j\Phi_2(\rho)\Pi_j,
\qquad \Pi_j=|j\rangle\langle j|\otimes I_K.
\tag{5.4}
$$

Supply one fresh pure $E_2$ per step and actually retain the returned successor labels in temporal order. The measurement is a different instrument from the unmeasured evolution and from flag feedback. It dephases successor alternatives; the environment flag need not be read and no inverse feedback is applied.

There are two initialization contracts, matching source Definition 130.1. One has a fixed known root $i_0$ and arbitrary internal-reference state. The other has an actually prepared block-diagonal configuration state with a declared law $\pi$, together with an actual retained orthogonal initial record $R_0$:

$$
\rho_{\mathrm{in},R_0}
=\sum_i\pi_i|i\rangle\langle i|_{\mathcal C}
\otimes\rho_{KR}^{(i)}\otimes|i\rangle\langle i|_{R_0},
\qquad\pi_i\ge0,\quad\sum_i\pi_i=1.
\tag{5.5}
$$

Each $\rho_{KR}^{(i)}$ is a density operator, and $R$ is untouched. The uniform stationary source is the special case $\pi_i=1/5$. From an arbitrary coherent configuration, producing $R_0$ requires an additional coupling $|i\rangle\psi\mapsto|i\rangle\psi\otimes|i\rangle_{R_0}$ and its acquisition contract. Reading or ignoring this record changes configuration coherence. Equation (5.5) is not obtained from arbitrary coherent input for free.

**定理 5.4（Common measured finite-history law for $V_2$）。** Under Definition 5.3, every finite positive-probability acquired history $h=(i_0,\ldots,i_N)$ has

$$
\Pr(h)=\pi_{i_0}\prod_{s=1}^N P_{i_{s-1}i_s},
\qquad
\rho_{KR}\mid h=(U_h\otimes I_R)\rho_{KR}^{(i_0)}
(U_h^\dagger\otimes I_R),
\tag{5.6}
$$

where $U_h=U_{i_Ni_{N-1}}\cdots U_{i_1i_0}$. For a fixed known root, omit $\pi$ or take it to be the point mass there. The actual retained initial root and successive returned successors recover every directed edge by the common update $(i,j)\mapsto j$ and the label $(i\to j)$. Conditioned on the acquired prefix, the future measured successors have the same kernel $P$.

**证明。** First, for every positive edge $i\to j$, every definite source $i$ and every internal-reference state $\sigma$,

$$
(\mathcal J_j\otimes\operatorname{id}_R)
(|i\rangle\langle i|\otimes\sigma)
=P_{ij}|j\rangle\langle j|\otimes
(U_{ji}\otimes I_R)\sigma(U_{ji}^\dagger\otimes I_R).
\tag{5.7}
$$

To prove it, project the single-source expansion (1.4) onto $j$. There is one edge amplitude $\sqrt{P_{ij}}U_{ji}$ and its normalized record. Tracing that record gives (5.7). If $P_{ij}=0$, the corresponding branch is zero; no transport on an absent edge is required. Summing the completely positive branches in (5.4) is trace preserving, so this is one common instrument for all inputs, not a choice made using an unavailable old source.

At step zero, (5.5), or the known root, supplies the stated configuration and internal state. Suppose a retained prefix through $i_s$ has its product probability and normalized state as in (5.6). Equation (5.7) supplies conditional probability $P_{i_si_{s+1}}$ for its next returned successor, independent of its internal-reference state, and composes the transport on the left. Multiplication gives the product probability for the extended prefix and the claimed $U_h$. Induction proves (5.6) for every finite $N$. It excludes no rare positive history. Applying the same induction from the attained definite successor proves the complete finite-future continuation law.

The decoder uses the actually retained root and returned symbols; it never reads an unrecorded source. For $N=0$ the product is one and $U_h=I_K$. A known-root domain has one empty-edge history, whereas different roots in (5.5) are distinguished by actual $R_0$. $\square$

The product-of-branches and fresh-register iteration supplier is already present in source §130 and [AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION, revision 6bfd5342e47ba7eb50a5022e301d228f17daa8d2, §110](https://github.com/the-omega-institute/trureturing/blob/6bfd5342e47ba7eb50a5022e301d228f17daa8d2/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md). Equation (5.7) is the necessary interface check for the smaller $V_2$ instrument; it is not inferred from one-step normalization alone.

**假设 5.5（Finite archive and continued acquisition）。** A simple classical successor archive for known length $N$ has at most $5^N$ words, in addition to a supplied $R_0$ when used. This is an upper representation, not an optimal storage theorem. The instrument and all future actual reads must continue to be available. A current successor predicts the subsequent measured chain but does not reconstruct its discarded past. Ordered acquisition, retained outputs, initialization and a specified end of the observation interval are part of this history contract. No result above supplies an unlimited reusable pure reset, erasure of an acquired archive, a free clock, or an unbounded archive in a fixed finite memory.

## 6. Exact finite histories from ordered four-dimensional records and a terminal successor

**定义 6.1（Common unmeasured record iteration）。** For a specified finite length $N$, apply the same $V_4$ of Theorem 4.1 sequentially to the current $H$ and $N$ fresh pure environments $E_4^{(1)},\ldots,E_4^{(N)}$. Retain each outgoing environment without subsequently coupling it to the current system. Their order is part of the protocol. No intermediate successor measurement is required for this construction. Let $V_4^{[N]}$ denote this composition, with $V_4^{[0]}=I_H$. For a legal length-$N$ path $h=(i_0,\ldots,i_N)$ write

$$
w(h)=\prod_{s=1}^NP_{i_{s-1}i_s},\qquad
r_h=g_{\kappa(i_0)}\otimes\cdots\otimes g_{\kappa(i_{N-1})}
\in E_4^{\otimes N},
\tag{6.1}
$$

where the empty tensor at $N=0$ is the unit scalar. Terminal configuration $i_N$ is an actual additional read interface. For stochastic path weights use either the fixed known root or the actually prepared initialization (5.5). This construction does not supply that initialization from an arbitrary input.

**定理 6.2（Ordered records plus terminal successor recover every finite legal path）。** For all $N\ge0$ and $(p,q,r)\in\mathcal D$,

$$
V_4^{[N]}(|i_0\rangle\psi)
=\sum_{h\in\mathcal H_N(i_0)}\sqrt{w(h)}\,
|i_N\rangle\otimes U_h\psi\otimes r_h.
\tag{6.2}
$$

For fixed $N$, the vectors $|i_N\rangle\otimes r_h$ are pairwise orthonormal over all legal length-$N$ paths, including paths with different roots. A single decoder using the actual terminal successor and the ordered $N$ record colors recovers the entire path. A common terminal joint measurement produces exactly the source path branches

$$
K_h=\sqrt{w(h)}\,|i_N\rangle\langle i_0|\otimes U_h.
\tag{6.3}
$$

Consequently, under the stated initialization, the acquired path law and conditional internal-reference state are (5.6), with no intermediate measurement.

**证明。** For $N=0$, (6.2) is the identity, with one path $(i_0)$ for each supplied root, $w=1$ and $U_h=I_K$. At any induction step, apply (1.4) for $V_4$ to the terminal summand $|i_s\rangle U_{h_s}\psi$. It appends $g_{\kappa(i_s)}$ in the next ordered environment, multiplies the amplitude by $\sqrt{P_{i_si_{s+1}}}$ and multiplies the internal transport by $U_{i_{s+1}i_s}$ on the left. Summing all legal extensions proves (6.2). Every composition acts on a fresh environment; its tensor-extended isometry preserves the previously retained environments and any untouched reference.

For orthogonality, paths with different terminal configurations are separated by the terminal basis label. Suppose $h,k$ have the same terminal label and differ somewhere. Let $\ell<N$ be the largest index with $i_\ell\ne k_\ell$. Their next configurations agree: $i_{\ell+1}=k_{\ell+1}=j$. Both differing sources belong to $I_j$, so $\kappa(i_\ell)\ne\kappa(k_\ell)$ by (4.2)–(4.3). The $(\ell+1)$-st tensor factors of $r_h,r_k$ are orthogonal, and hence the product vectors are orthogonal. Norms are one. For $N=0$, different roots have different terminal labels, covering that boundary case as well.

The same argument gives a constructive decoder without a history-dependent rule. Start with the acquired $i_N$. The last returned color determines the unique predecessor in $I_{i_N}$. With that predecessor as the new successor, the preceding color determines its unique predecessor. Repeat backward through the ordered registers. Each lookup depends only on the supplied graph, one current successor and one acquired color. Thus every legal codeword is uniquely decoded by a common rule for the given length. The composition produces legal codewords by the preceding induction; no legality decision for a fabricated word is mistaken for an acquired event.

Let $q_h=|i_N\rangle\otimes r_h$. On the configuration-record factors measure the mutually orthogonal projections $|q_h\rangle\langle q_h|$, tensored with $I_K$, and include the complementary outcome. Applying a path projection to (6.2) isolates (6.3), with the normalized retained record $r_h$. For an arbitrary input superposition, linearity gives the same $K_h$ operator, because the terminal codewords are orthogonal even for different roots. The complementary outcome is zero on the image. Moreover

$$
\sum_hK_h^\dagger K_h
=\sum_i\left(\sum_{h\in\mathcal H_N(i)}w(h)\right)
|i\rangle\langle i|\otimes I_K=I_H,
\tag{6.4}
$$

since iterating row normalization makes each inner sum one, including the empty product. The instrument is therefore common and trace preserving on all $H$.

For an initialized root, $K_h^\dagger K_h=w(h)|i_0\rangle\langle i_0|\otimes I_K$ gives the product probability and transported state in (5.6). For (5.5), it gives the factor $\pi_{i_0}$ and the same reference-preserving conditional state, while $R_0$ remains its actual initial record. Measuring separate terminal/configuration and record bases followed by the backward decoder is an equivalent readout of these path outcomes on the generated image. $\square$

**命题 6.3（The independently supplied coherent-history domain is a different domain）。** Let $\mathcal H_N$ contain all legal length-$N$ paths with their roots, and supply an independent history-label space with orthonormal basis $|h\rangle$. The map

$$
T_N:\mathbb C^{\mathcal H_N}\otimes K
\longrightarrow\mathcal C\otimes K\otimes E_4^{\otimes N},
\qquad
T_N(|h\rangle\psi)=|i_N\rangle U_h\psi\otimes r_h
\tag{6.5}
$$

is an isometry on that whole domain, including arbitrary coherent histories, internal inputs and untouched reference extensions. The actual $H$-input iteration (6.2) supplies a weighted subspace of its image. For $N\ge1$ this is a proper subspace and does not freely supply an arbitrary vector in the larger history-input domain; at $N=0$ the domains identify with $H$. This construction does not provide a general environment-alone history decoder.

**证明。** Theorem 6.2 gives orthogonality of $q_h$ for $h\ne k$, irrespective of internal vectors. For $h=k$, $U_h$ is unitary and preserves every internal inner product. Thus

$$
\langle T_N(|h\rangle\psi),T_N(|k\rangle\phi)\rangle
=\delta_{hk}\langle\psi,\phi\rangle.
$$

Linearity and tensoring with $I_R$ give the full isometry assertion. Its adjoint is a mathematical inverse on its image: it maps the encoded path with $U_h\psi$ back to $|h\rangle\psi$. Physical coherent reversal requires all carriers, phase-compatible controls and the permitted inverse; a classical path measurement instead removes between-path coherences.

The actual iteration factors as $V_4^{[N]}=T_N A_N$, where

$$
A_N(|i\rangle\psi)
=\sum_{h\in\mathcal H_N(i)}\sqrt{w(h)}\,|h\rangle\psi.
\tag{6.6}
$$

Row normalization makes $A_N$ an isometry, but its domain is $H$. At $N=1$ it has only the ten input dimensions, whereas the independent history-internal domain has $15\cdot2=30$ dimensions. Every vertex has at least two positive successors, so $|\mathcal H_N|\ge5\cdot2^N$; for each $N\ge1$ the independent domain has dimension strictly greater than ten. At $N=0$, $A_0$ is the identification $|i\rangle\psi\mapsto|(i)\rangle\psi$. Thus for $N\ge1$ existence of (6.5) does not acquire its extra independent input degrees of freedom. This explicitly separates arbitrary history-domain recovery from the generated image of a common physical iteration, while retaining the empty-history boundary.

Finally, already at $N=1$ with known root $0$, the edges $0\to0$ and $0\to1$ have the identical record $g_0$ and both have positive probability. $E_4$ alone cannot distinguish them. The terminal successor is essential to this construction's exact path decoder. At $N=0$, all environment records are the same empty scalar; the actually read terminal configuration, rather than that scalar, distinguishes different roots. $\square$

**假设 6.4（Ordered finite carrier cost and length framing）。** The record carrier in Theorem 6.2 has dimension $4^N$, in addition to the actual terminal $\mathcal C$ of dimension five, the internal $K$ of dimension two, any supplied $R_0$, and the measurement/control/output apparatus. This is an upper construction for the finite ordered-record contract. It is not an optimal total-history dimension, an environment-alone history decoder, or an upper bound on an indefinitely long archive in fixed memory. Reading $N$ colors gives a simple $2N$-bit color archive plus the separately retained terminal label; this is also only an upper encoding.

The protocol specifies a finite $N$ and tensor order. At $N=0$ there is no edge record and the terminal label equals the root; stochastic preparation still has the explicit initialization (5.5). If observation length varies and is not supplied by a fixed protocol, an actual end marker, length or equivalent framing must be retained and counted. No uncharged time counter or infinite reusable reset is inferred from (6.2). Fresh pure environments are a preparation resource, and reading or erasing their records is an additional operation.

## 7. Source correspondences, resource boundaries and remaining questions

**定义 7.1（Published comparison interfaces）。** The later comparison source is [AURIC_FIB_HISTORY_RECORDS_TIME_ARROW, revision 3530ef6c199cd5e1738f652be69fb43dad3f54ca, §§136–151 and earlier context](https://github.com/the-omega-institute/trureturing/blob/3530ef6c199cd5e1738f652be69fb43dad3f54ca/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md). These interfaces do not change (1.2), (1.3), $\mathcal D$ or the input domain of (1.4). Their correspondences with this volume are the following explicitly restricted ones.

The actual-observation interface of §136 requires acquisition, retention and legal continuation. Its task-relative quotients in §140 correspond here to the different tasks of Definitions 1.2–1.3, not to a claim that the same record solves every task. Its §141 capacity conditions correspond to the orthogonal distinguishability arguments in §4 and the common inner-product conditions in §§2 and 6. A classical label cardinality is not by itself the dimension of a quantum realization.

The complete events of §144 have the form “actual action, returned result, calibration/source/control fields”. The five-mode path labels of this volume recover a complete such event archive only if the other fields are supplied fixed model data or are actually retained in additional registers. A path label alone does not recover unknown event fields. Section 145's preserving symbolic replacement pairs a known source tree with its replacement; it is neither copying an arbitrary unknown quantum input nor acquiring a new unknown fact. The classical archive tower and finite candidate-law $L^2$ innovations of §146 have their own candidate domain and measure. They do not count dimensions of $E_2$ or $E_4$, supply an independent quantum reference, or define physical axes.

The guarded-window states and transitions in §§147 and 149, and the associated Fibonacci counts, use a different legal history set. No identification of that set with paths of (1.2) is supplied. The periodic object inverse in §148 acts on its defined object; it is not an erasure of a retained acquired-event archive. Section 150's serial representation of a finite rooted graph is a mathematical encoding, not acquisition of an unknown graph or permission to realize (1.3). The conditioned synthesis of §151 retains these distinctions and provides no native physical spacetime bridge. The geometric conclusions of §§137–139 and the uncertainty/conditional-combination interfaces of §§142–143 likewise do not grant a new record, dynamics, read or feedback controller.

These comparisons also retain the original native source boundary: [FIB_RELATIONAL_CONTINUATION_GEOMETRY, revision 6247af628aac8e4688aedb6a4cb1cd42642b578a, §§1–2](https://github.com/the-omega-institute/trureturing/blob/6247af628aac8e4688aedb6a4cb1cd42642b578a/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) defines legal continuation and observation in its own configuration/window interfaces. Numerical encoding is not acquisition or an executable operation, as in [RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS, the same revision, Proposition 1.1](https://github.com/the-omega-institute/trureturing/blob/6247af628aac8e4688aedb6a4cb1cd42642b578a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md). A common physical realization of these native operations with the added $P,U$ and the readouts remains a separate obligation.

**命题 7.2（Record distinctions cannot be restored by postprocessing alone）。** Within the named constructions, the read/control contracts in §§2, 4, 5 and 6 are additional to one-step admissibility. A postprocessing of $V_2$'s flag alone cannot provide exact edges or an acquired path. A postprocessing of the $V_4$ records alone cannot provide the path decoder of Theorem 6.2. Representation of a history or an inverse map does not establish that the corresponding history was acquired.

**证明。** Proposition 3.2 supplies two positive edge realizations with identical $(j,e)$ and even a common terminal internal state. Any classical randomized postprocessing of their identical read laws has identical output laws; it cannot deterministically return two different correct edges. Proposition 5.2 supplies identical normalized terminal/internal/record vectors for distinct $V_2$ branch histories, so any POVM on those output carriers has the same statistics on that pair. Proposition 6.3 gives identical $E_4$ records for two distinct positive paths even with a known root. These are equal-observation, different-target instances in the same source and permitted parameter domain, not examples from a substituted graph.

Theorem 2.2 adds an actual flag read and controlled inverse; Theorem 4.1 adds actual successor-assisted readout; Theorem 5.4 adds an actually iterated successor measurement and retained results; Theorem 6.2 retains fresh ordered environments and adds a terminal read. Their conclusions follow from these supplied joint operations. Omitting $V_2$'s intermediate successor measurement gives the different law (5.1); omitting $V_4$'s terminal successor leaves the identical environment records of Proposition 6.3. Admissibility (1.4) supplies neither a retained classical output nor an inverse controller. An abstract encoding such as (6.5) states what inner products an independently supplied domain can preserve, not an acquisition rule for the absent input labels. $\square$

**定义 7.3（Reused suppliers and the source-specific bridge）。** The following are distinct mathematical uses, with their hypotheses retained.

The cross-input equation and dimension-at-least-two obstruction are those of original §§126 and 129. The transported square identity is from §128, at its operator level only. The fixed orthogonal-edge channel, fifteen-dimensional attainment, Choi-rank calculation and initialized product-path law are from §130. The framed factorization is from §§131–132. Gram positivity/factorization and fresh-register iteration are from second-order completion §§109–110. Deterministic pure-state discrimination, Choi/Kraus rank and conditional environment-assisted correction are the general suppliers cited within §§2–4. None is asserted here as a new general theorem.

The source/resource bridge added here consists of the full-domain joint $V_2$ records and leaf-loop sign, their two-unitary component identities, the distinct sharp successor-assisted read cost, the selected realization's all-domain unmeasured return and history collisions, and the four-color common finite-path encoding with its terminal-assisted backward decoder. The corresponding ordinary proofs verify the stipulated $P$ and $U$ without adding a free source copy. In particular, the random-unitary existence is stronger than an unspecified small Gram rank, and the decoder is stronger than a collection of separately feasible one-step readouts.

Scalar stochastic-matrix coherification is an applicable comparison only after matching conventions and block transports. Korzekwa et al., arXiv:1710.04228v2, Proposition 1, identify rank-one coherification with a scalar unistochastic matrix. That assertion permits choice of a scalar unitary for the given diagonal transition data; it does not impose all the $2\times2$ transport blocks in (1.3). Its row-grouping method provides the intermediate orthogonality organization used in §4 after the explicit $T=P^{\mathsf T}$ correspondence, not the sharp two-dimensional construction of §2. Generic Stinespring existence supplies a pure dilation of a chosen channel, not minimization over (1.4) with prescribed transports. Generic Gram rank characterizes already jointly supplied vectors, not admissibility of independently selected rows or a numerical relaxation. No literature-search miss is used as a proof of global originality.

**命题 7.4（The original arbitrary-history compression bound has a separate domain）。** The original source's fixed-root compression bound §134 remains applicable to a separately supplied arbitrary coherent history domain with retained summary $(i_N,W(h))$. It does not imply that $d_{\mathrm{un}}$, $d_{\mathrm{succ}}$, or the minimum pure environment of the terminal channel must grow exponentially in $N$.

**证明。** The original compression map has the form

$$
|h\rangle\psi\longmapsto
|(i_N,W(h))\rangle\,U_h\psi\otimes r'_h
\tag{7.1}
$$

on every independent history basis vector and its arbitrary superpositions. The source's inner-product argument forces orthogonal residuals within each common-summary fibre and gives

$$
\dim R'\ge\max_b|\{h:(i_N,W(h))=b\}|
\ge\left\lceil\frac{2^N}{5(2N+1)}\right\rceil
\tag{7.2}
$$

for all legal fixed-root paths in $\mathcal D$. This is the published bound and not a new counting result. Its domain is the entire independent history-label space, with a retained summary that includes $W$. The one-step (1.4) has domain $H$; the actual iteration (6.2) has domain $H$ and retains a different terminal/ordered-record boundary; and the fixed terminal channel forgets that boundary. Equation (6.6) explicitly exhibits the restricted weighted history image generated by an $H$ input. Thus none of these domains or output contracts equals (7.1), and (7.2) cannot be transferred without the missing domain and interface correspondence. The source's $(i_N,W)$ also carries a named stationary forward/reverse likelihood comparison; for a point-mass root it is not the root-initialized law's own reversal likelihood. $\square$

**假设 7.5（Remaining boundaries）。** The exact one-step minimum and the three specified readout minima are settled by §§2 and 4 at their declared abstract contracts. A classification of all minimizing realizations, an optimum total finite-history record carrier, and an environment-alone history optimum are not supplied. The logical marginal, full-input feedback recovery, actually measured Markov history and separately supplied coherent-history domain remain distinct recoveries.

Physical realization and acquisition of the stipulated $P,U$, fresh pure records, frame transformations, phase-compatible inverse controls and measurement pointers are not derived from the native alphabet. No claim is made about physical spatial dimension or distance, a global thermodynamic entropy balance, heat dissipation, unlimited record erasure/reset, an external free clock, or finite executable cost for arbitrary exact real parameters. A parameter-dependent mathematical vector family does not establish the precision with which an apparatus can prepare it. The finite-$N$ results require the explicitly supplied finite carrier and framing; they do not supply indefinitely continued recovery at a fixed total resource budget.

## 追加锚（本行以下为增补区）

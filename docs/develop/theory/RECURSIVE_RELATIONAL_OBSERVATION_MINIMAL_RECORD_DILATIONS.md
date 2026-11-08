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


## 8. Balanced terminal channels and homogeneous Kraus-word rank

**定义 8.1（Balanced terminal iteration）。** Restrict the fixed source (1.2)–(1.3) to

$$
p=q>0,\qquad r>0,\qquad 2p+r<1.
\tag{8.1}
$$

Retain the entire $H=\mathbb C^5\otimes\mathbb C^2$, the published $V_2$, its exact operators $L_0,L_1$ in (2.6), and all untouched reference extensions. Write $\Phi=\Phi_2$ for its unread reduced channel. For $N\in\mathbb N$ let

$$
\begin{aligned}
\mathcal W_N&=\{L_{\mu_N}\cdots L_{\mu_1}:\mu_s\in\{0,1\}\},\\
W_N&=\operatorname{span}_{\mathbb C}\mathcal W_N,\qquad
\mathcal W_0=\{I_H\}.
\end{aligned}
\tag{8.2}
$$

The terminal map $\Phi^N$ composes the same reduced channel $N$ times. Its iterated dilation uses an independently supplied fresh pure environment at each step, with every outgoing environment traced or subsequently retained without further coupling to $H$. No intermediate successor measurement is inserted. Repeated application of (2.10) to one retained environment defines a different map.

**定理 8.2（Uniform balanced terminal rank）。** For every parameter pair in (8.1) and every $N\ge0$,

$$
\boxed{\operatorname{rank}J(\Phi^N)=\dim_{\mathbb C}W_N=\min\{N+1,4\}.}
\tag{8.3}
$$

Consequently the minimum dimension of a pure environment implementing the fixed terminal channel $\Phi^N$ on all $H$ is $1,2,3,4$ for $N=0,1,2,3$, respectively, and is four for every $N\ge3$. Equality of the terminal maps also holds on all untouched reference extensions.

**证明。** Here $t=2p$, $B=1-2p$ and $A=B-r$. Define the real scalars

$$
\eta=\frac{\sqrt A}{\sqrt B},\qquad
\zeta=\frac{\sqrt r}{\sqrt B},\qquad
\kappa=\frac1{\sqrt2}.
\tag{8.4}
$$

The full strict domain gives $0<\eta<1$, $\zeta>0$, $\kappa>0$, $\eta^2+\zeta^2=1$ and $2\kappa^2=1$. These statements do not require a positive lower cutoff on $p$, $r$ or $A$.

Apply exactly the frames $D$ of (3.1)–(3.2) to both the input and output. In those frames the normalized (2.8) become

$$
DT_0D^\dagger=U\otimes I_K,\qquad
DT_1D^\dagger=V\otimes I_K,
\tag{8.5}
$$

where, in the original configuration order $0,1,2,3,4$,

$$
U=\begin{pmatrix}
\eta&0&0&0&\zeta\\
0&1&0&0&0\\
0&0&1&0&0\\
0&0&0&1&0\\
\zeta&0&0&0&-\eta
\end{pmatrix},\qquad
V=\begin{pmatrix}
0&\kappa&0&-\kappa&0\\
\kappa&0&\kappa&0&0\\
0&\kappa&0&\kappa&0\\
-\kappa&0&\kappa&0&0\\
0&0&0&0&1
\end{pmatrix}.
\tag{8.6}
$$

The two leaf coefficients are positive in these frames because $G_4=b$ and the supplied leaf transports are $b,b^\dagger$. The minus signs on the $0,3$ and $3,0$ entries are exactly the published square sign, not a replacement transport. Equations (2.4), or direct multiplication of (8.6), give

$$
U^\dagger=U,\quad V^\dagger=V,\quad U^2=V^2=I_5.
\tag{8.7}
$$

Let $R=UV$. Its inverse is $VU$. Direct multiplication, using only the two scalar equations following (8.4), gives

$$
R^4+(1+\eta)R^3-(1+\eta)R-I_5=0.
\tag{8.8}
$$

To prove that this quartic cannot be replaced by a polynomial of smaller degree, evaluate $I_5,R,R^2,R^3$ at the four entries $(0,0),(0,4),(4,0),(1,2)$. Their column matrix is

$$
M=\begin{pmatrix}
1&0&\eta&1-\eta^2\\
0&\zeta&-\eta\zeta&\eta(\eta+1)\zeta\\
0&0&\zeta&-\eta\zeta\\
0&\kappa&0&\kappa
\end{pmatrix},\qquad
\det M=\kappa(1-\eta)^2(1+\eta)>0.
\tag{8.9}
$$

Thus the four powers are linearly independent over $\mathbb C$ at every allowed parameter pair. The minimal polynomial of $R$ is exactly

$$
f(X)=X^4+(1+\eta)X^3-(1+\eta)X-1
=(X-1)(X+1)\bigl(X^2+(1+\eta)X+1\bigr).
\tag{8.10}
$$

The quartic identity bounds the span of all nonnegative powers by four, while (8.9) supplies the uniform lower bound. In particular, for every $\ell\ge0$,

$$
\dim\operatorname{span}\{I_5,R,\ldots,R^\ell\}
=\min\{\ell+1,4\}.
\tag{8.11}
$$

For completeness the quadratic in (8.10) has two nonreal conjugate roots: its discriminant $(1+\eta)^2-4$ is negative for $0<\eta<1$. It shares neither $1$ nor $-1$ with the other factors. This spectral observation is consistent with the four independent powers, but is not needed to replace the explicit lower bound.

Let $\mathcal P_N$ be the set of length-$N$ products of $U,V$. The normal form for two involutions is the standard infinite-dihedral normal form; see Iain Raeburn and Allan M. Sinclair, *The $C^*$-algebra generated by two projections*, Mathematica Scandinavica 65 (1989), 278–290, Proposition 1.1 and the proof of Theorem 1.3 on p. 280, [original article](https://journals.msp.org/mscand/article/download/1364/1363), [DOI](https://doi.org/10.7146/math.scand.a-12283). The exact length restrictions are verified here. Adjacent equal letters cancel by (8.7). Every surviving word alternates, and its length has the same parity as $N$. Conversely any alternating word of that parity and length at most $N$ can be padded to length $N$ by inserting $UU$. With $m\ge0$, this proves the exact set identities

$$
\mathcal P_{2m}=\{R^k:-m\le k\le m\},\qquad
\mathcal P_{2m+1}=\{UR^k:-m\le k\le m+1\}.
\tag{8.12}
$$

For positive $k$, $UR^k=V(UV)^{k-1}$ has length $2k-1$; for $k\le0$, $UR^k=U(VU)^{-k}$ has length $1-2k$. This verifies both endpoints of the odd interval. The even interval includes the empty product when $m=0$.

Multiplication by the invertible $R^m$ maps the span in the even case to the span of $I_5,R,\ldots,R^{2m}$. In the odd case, first multiply by $U$ and then by $R^m$; this maps the span to that of $I_5,R,\ldots,R^{2m+1}$. These are invertible linear transformations, so (8.11) gives both the upper and lower ranks in (8.3) for the normalized configuration words, including $N=0,1,2$.

The substitution back to $H$ loses no dimension. The map $X\mapsto D^\dagger(X\otimes I_K)D$ is complex linear and injective; evaluating at any fixed diagonal internal coordinate recovers $X$ after undoing $D$. Moreover $L_0=\sqrt B\,T_0$ and $L_1=\sqrt t\,T_1$. Each length-$N$ Kraus word is therefore a positive nonzero scalar times the corresponding normalized word. Individual nonzero rescalings preserve a span, even when distinct words coincide. This proves the asserted $\dim W_N$ on all ten dimensions of $H$, rather than on a single internal vector or a restricted preparation.

Expanding the channel composition yields a Kraus family consisting of all the exact words in (8.2). This exact-length word-span/Choi-rank correspondence is explicitly stated in Mikel Sanz, David Pérez-García, Michael M. Wolf and Juan I. Cirac, *A quantum version of Wielandt’s inequality*, §II, following equation (1), [arXiv:0909.5347](https://arxiv.org/abs/0909.5347); its generic correspondence is reused, without assuming quantum primitivity. The standard vectorization identity gives

$$
J(\Phi^N)=\sum_{w\in\{0,1\}^N}
|\operatorname{vec}L_w\rangle\langle\operatorname{vec}L_w|.
\tag{8.13}
$$

The range of a finite sum of positive rank-one operators is the span of their vectors: its kernel is their common orthogonal complement, since its quadratic form is the sum of the squared inner products. Vectorization is injective, so the rank in (8.13) is exactly $\dim W_N$. The Choi/Kraus correspondence and attainment of the pure-environment minimum are the mature finite-dimensional suppliers of Watrous, *The Theory of Quantum Information*, Chapter 2, Theorem 2.22 and Corollary 2.27, [author-hosted Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). A pure environment of dimension $d$ supplies at most $d$ Kraus components, giving the lower bound; the positive spectral decomposition of (8.13) supplies exactly its rank many Kraus components, giving attainment. The $N=0$ case is the identity channel with the single nonzero Kraus operator $I_H$. Complete equality on $H$ tensor-extends to any untouched reference. $\square$

**命题 8.3（One retained environment has different balanced repetitions）。** For the interaction $\mathsf U$ in (2.10), throughout (8.1),

$$
\mathsf U^2=I_{H\otimes E_2}.
\tag{8.14}
$$

With the same initially prepared $|\mathrm{ready}\rangle$ and the same retained $E_2$, applying $\mathsf U$ $N$ times and tracing only at the end gives the identity channel for even $N$ and $\Phi$ for odd $N$. Its terminal Choi rank is one for even $N$ and two for odd $N$. It is not the fresh-environment channel power in Theorem 8.2 when $N\ge2$.

**证明。** Equations (8.5)–(8.7) imply $T_0^2=T_1^2=I_H$. Squaring (2.10) eliminates cross terms through the orthogonality of its two control projections and gives (8.14). Even powers restore the complete joint input $x\otimes|\mathrm{ready}\rangle$; odd powers give the one-step dilation (2.5). The same operator identities hold after tensoring with every untouched reference. The identity channel has rank one, and the published one-step rank is two by Theorem 2.1. Fresh independent environments instead produce (8.13), whose rank is three at $N=2$ and four at every $N\ge3$. $\square$

**假设 8.4（Terminal realization and archive boundaries）。** Theorem 8.2 concerns only the fixed unread terminal channel and its full input/reference action. It permits an abstract pure terminal dilation with at most four environment dimensions for each specified finite $N$. A coherent change of environment coordinates in the occupied Kraus span can relate that dilation to the original fresh-register dilation. It does not preserve all independent flag-history basis states, supply an acquired edge or path output, or optimize a decoder subject to those readout contracts.

The measured continuation in Theorem 5.4 inserts successor measurements and retains their results; its path law is a separate instrument. The arbitrary coherent history domain of Proposition 7.4 has independent input dimensions and a retained summary; it remains subject to (7.2). Neither domain is the image generated by iterating a ten-dimensional $H$ input and then forgetting the history boundary. Hence the terminal rank plateau is compatible with the existing coherent-history archive lower bound. It does not bound an unlimited retained archive or charge away fresh preparations, measurements, communication, framing, controls or physical erasure.

Native $\alpha/\beta$ acquisition, realization of (1.2)–(1.3), actual result carriers, calibration and executable precision remain separately supplied conditions of Assumptions 1.4 and 7.5. The classical transition matrix retains its positive loops and legal paths. These do not imply quantum primitivity: (8.5) acts trivially on the entire framed logical factor $K$, in agreement with Theorem 3.1. The Choi/Kraus and pure-environment principles used in the proof are existing suppliers; the new source-specific conclusion is the homogeneous terminal rank (8.3), established by (8.8)–(8.12) on the exact balanced source.

## 追加锚（本行以下为增补区）

## 9. Common autonomous prefixes on the balanced source

**定义 9.1（Common-prefix contract and its two minima）。** Keep the balanced source (8.1), the full ten-dimensional $H$, and the channel $\Phi$ of §8. For a finite horizon $N$, a common autonomous realization is a finite environment $E$, one density operator $\sigma$ on $E$ independent of the input and of $n$, and one unitary $W$ on $H\otimes E$ such that, for every density operator $\rho_{HR}$ and every untouched reference $R$,

$$
\operatorname{Tr}_{E}\!\left[(W^n\otimes I_R)(\rho_{HR}\otimes\sigma)(W^{-n}\otimes I_R)\right]
=(\Phi^n\otimes\operatorname{id}_R)(\rho_{HR}),\qquad 0\le n\le N .
\tag{9.1}
$$

Every clock, reset supply, controller or other interacting carrier belongs to $E$. The unitary and $\sigma$ may depend on $N$ and on the source parameters, but not on the input or on the time index. Let $d_{\mathrm{pure}}(N)$ be the minimum $\dim E$ when $\sigma$ is pure, and let $d_{\mathrm{any}}(N)$ allow every density $\sigma$. The terminal problem in Theorem 8.2 asks only for one channel $\Phi^N$ and may choose a new terminal dilation for each $N$; (9.1) asks one $W$ and one initial density to realize every requested prefix power. Equality in (9.1) is an identity on the full matrix algebra and therefore includes all coherent inputs and all untouched references.

Put

$$
\alpha=1-2p,\qquad \beta=2p,\qquad \alpha,\beta>0,\qquad \alpha+\beta=1,
\tag{9.2}
$$

and work first in the fixed frame (8.5), writing again $U,V$ for $U\otimes I_K,V\otimes I_K$ and $R=UV$, $S=VU=R^{-1}$. Thus $\Phi=\alpha\,\operatorname{Ad}_U+\beta\,\operatorname{Ad}_V$ and $U^2=V^2=I$.

**引理 9.2（Whole-input Gram compatibility for one temporal unitary）。** Let $J_0,\ldots,J_N:H\to\mathcal K$ be isometries into one finite-dimensional joint space. There is a unitary $W$ on $\mathcal K$ with

$$
WJ_n=J_{n+1}\qquad(0\le n<N)
\tag{9.3}
$$

if and only if the block Gram operators agree:

$$
J_n^*J_m=J_{n+1}^*J_{m+1}\qquad(0\le n,m<N).
\tag{9.4}
$$

**证明。** Define $F,G:H^{\oplus N}\to\mathcal K$ by $F(x_0,\ldots,x_{N-1})=\sum_nJ_nx_n$ and $G(x_0,\ldots,x_{N-1})=\sum_nJ_{n+1}x_n$. Equation (9.4) is exactly $F^*F=G^*G$. It makes $Fx\mapsto Gx$ well-defined and isometric, including all coherent superpositions of inputs; its domain and range have the same dimension. Extend this partial isometry to a unitary between the two orthogonal complements in $\mathcal K$. Conversely, any $W$ satisfying (9.3) preserves every block inner product and hence gives (9.4). For two boundaries $J_0,J_1$ and $J_1,J_2$, the condition reduces to $J_0^*J_1=J_1^*J_2$ because each $J_n$ is an isometry. This is the exact operator-Gram condition; checking basis vectors or one internal vector is insufficient. $\square$

**定理 9.3（Exact pure and unrestricted minima at $N=2$）。** Throughout (8.1),

$$
\boxed{d_{\mathrm{pure}}(2)=3,}
\qquad
\boxed{
 d_{\mathrm{any}}(2)=
\begin{cases}
2,&p=q=1/4,\\
3,&p=q\ne1/4.
\end{cases}}
\tag{9.5}
$$

The same $W$ and the same input-independent initial density realize $n=0,1,2$ on all $H$ and on every untouched reference. The qubit exclusion below ranges over every joint unitary and every density on a two-dimensional environment; it is not a restricted controlled ansatz.

**证明。** Since $U^2=V^2=I$,

$$
\Phi^2=(\alpha^2+\beta^2)\operatorname{Ad}_I
+\alpha\beta\operatorname{Ad}_R+\alpha\beta\operatorname{Ad}_S .
\tag{9.6}
$$

The operators $I,R,S$ are linearly independent: a relation becomes a relation among $I,R,R^2$ after multiplication by $R$, and those powers are independent by (8.9). All three coefficients in (9.6) are positive, so the Choi rank of $\Phi^2$ is three. A pure environment of dimension $d$ supplies at most $d$ Kraus operators at each time, hence $d_{\mathrm{pure}}(2)\ge3$.

For attainment, let $E_3$ have orthonormal basis $f_0,f_1,f_2$ and prepare the single state

$$
|e\rangle=\beta f_0+\alpha f_1+\sqrt{2\alpha\beta}\,f_2 .
\tag{9.7}
$$

Its norm is one. Define whole-input isometries $J_j:H\to H\otimes E_3$ by

$$
\begin{aligned}
J_0x&=x\otimes |e\rangle,\\
J_1x&=\sqrt\alpha\,Ux\otimes f_0+\sqrt\beta\,Vx\otimes f_1,\\
J_2x&=\sqrt{\alpha\beta}\,Rx\otimes f_0+\sqrt{\alpha\beta}\,Sx\otimes f_1
       +\sqrt{\alpha^2+\beta^2}\,x\otimes f_2 .
\end{aligned}
\tag{9.8}
$$

The reduced maps of $J_0,J_1,J_2$ are respectively $\operatorname{id},\Phi,\Phi^2$. The only nontrivial Gram block is

$$
J_0^*J_1=\beta\sqrt\alpha\,U+\alpha\sqrt\beta\,V=J_1^*J_2=:C,
\tag{9.9}
$$

where the second equality uses $U^*R=V$ and $V^*S=U$. The norm bound

$$
\|C\|\le\beta\sqrt\alpha+\alpha\sqrt\beta
=\sqrt{\alpha\beta}(\sqrt\alpha+\sqrt\beta)\le\frac1{\sqrt2}<1
\tag{9.10}
$$

makes $Q=\begin{psmallmatrix}I&C\\ C&I\end{psmallmatrix}$ positive definite. Let $F=[J_0\ J_1]$ and $G=[J_1\ J_2]$. Then $F^*F=G^*G=Q$. Lemma 9.2, or its explicit extension

$$
W=GQ^{-1}F^*+L_G L_F^* ,
\tag{9.11}
$$

where $L_F,L_G$ are unitary identifications of the two orthogonal complements, supplies one unitary on $H\otimes E_3$ with $WJ_0=J_1$ and $WJ_1=J_2$. Since $J_0x=x\otimes|e\rangle$, induction gives the required powers. Conjugating by the fixed source frame $D$ returns a unitary on the declared $H\otimes E_3$ and does not change dimensions or any reference extension. Thus $d_{\mathrm{pure}}(2)\le3$.

It remains to classify a possible mixed qubit. If $\dim E=2$ and $\sigma$ were pure, the preceding lower bound would already contradict the prefix, so $\sigma$ has full support. In an eigenbasis of $\sigma$, every environment block of $W$ is a Kraus operator of the one-step channel up to a nonzero scalar. The Choi range of $\Phi$ is exactly $\operatorname{span}\{U,V\}$; positivity of a Kraus sum forces every block into that range. Consequently every possible $W$ has the forced form

$$
W=U\otimes A+V\otimes B
\tag{9.12}
$$

for two $2\times2$ matrices $A,B$. Comparing the coefficients of the independent $I,R,S$ in both $W^*W=I$ and $WW^*=I$ gives

$$
A^*B=B^*A=AB^*=BA^*=0,\qquad
A^*A+B^*B=AA^*+BB^*=I.
\tag{9.13}
$$

Writing $T=A+B$, (9.13) says that $T$ is unitary and, in the output basis of the complementary projections,

$$
A=|0\rangle\langle0|\,T,\qquad B=|1\rangle\langle1|\,T,\qquad
W=(U\otimes|0\rangle\langle0|+V\otimes|1\rangle\langle1|)(I\otimes T).
\tag{9.14}
$$

Let $\tau=T\sigma T^*$ and set $x=|T_{01}|^2=|T_{10}|^2$. The one-step equality gives $\tau_{00}=\alpha$ and $\tau_{11}=\beta$. Expanding the two-step Choi operator in the independent operator basis $\{I,R,S\}$, the diagonal coefficients of $|R\rangle\langle R|$ and $|S\rangle\langle S|$ are respectively

$$
\beta x,\qquad \alpha x .
\tag{9.15}
$$

The target coefficients from (9.6) are both $\alpha\beta$. Uniqueness of the coefficient matrix in an independent vectorized operator basis therefore gives $\beta x=\alpha\beta$ and $\alpha x=\alpha\beta$. Since $\alpha,\beta>0$, $x=\alpha=\beta=1/2$, hence $p=q=1/4$. At this point all entries of $T$ are nonzero. The target $I,R$ off-diagonal coefficient in the same exact expansion is $T_{00}\overline{T_{01}}\,\tau_{01}$; it must vanish, so $\tau_{01}=0$. Therefore $\tau=I_2/2$ and $\sigma=I_2/2$. This proves that no arbitrary mixed qubit works away from the stated locus.

At $p=q=1/4$, take instead

$$
\sigma=I_2/2,\qquad
W={1\over\sqrt2}
\begin{pmatrix}U&U\\ V&-V\end{pmatrix}
=(U\otimes|0\rangle\langle0|+V\otimes|1\rangle\langle1|)(I\otimes H_2),
\tag{9.16}
$$

where $H_2$ is the Hadamard matrix. This $W$ is unitary. Its square is

$$
W^2={1\over2}
\begin{pmatrix}I+R&I-R\\ S-I&S+I\end{pmatrix}.
\tag{9.17}
$$

With the maximally mixed initial qubit, the four block Kraus operators have all cross terms cancel, leaving

$$
\Psi_1={1\over2}\operatorname{Ad}_U+{1\over2}\operatorname{Ad}_V=\Phi,\qquad
\Psi_2={1\over2}\operatorname{Ad}_I+{1\over4}\operatorname{Ad}_R+{1\over4}\operatorname{Ad}_S=\Phi^2.
\tag{9.18}
$$

This is a full-channel equality on $H$, not a restricted sector calculation, and it tensor-extends to every untouched reference. Dimension one cannot realize the rank-two channel $\Phi$, so $d_{\mathrm{any}}(2)=2$ at the locus. Together with the qutrit construction and the exclusion, (9.5) follows. $\square$

**命题 9.4（What the N=2 boundary does and does not recover）。** The Gram equality (9.9) is the exact compatibility needed to turn the three whole-input boundary embeddings into one common temporal unitary. It does not assert equality for inserted interventions, measured successor histories, or a process tensor. The pure qutrit and mixed qubit states are prepared once in $E$; no environment is reset between $n=0,1,2$, and no clock label is read out. The qutrit result is a common-prefix realization, whereas the terminal rank statement (8.3) is a fresh terminal-channel contract.

**证明。** This is the direct specialization of Lemma 9.2 to $F=[J_0\ J_1]$ and $G=[J_1\ J_2]$. The reduced identities are linear identities on all matrices, so untouched references are included. The stated intervention and history claims would require additional joint maps and readout interfaces absent from (9.1), and therefore do not follow from the Gram calculation. $\square$

## 10. Quantitative finite-prefix growth and charged attainability

**定理 10.1（Arbitrary-density finite-prefix lower bound）。** For every strict balanced source and every finite realization (9.1),

$$
\boxed{d_{\mathrm{any}}(N)^2\ge N+1,\qquad d_{\mathrm{pure}}(N)^2\ge N+1.}
\tag{10.1}
$$

The first inequality allows arbitrary rank and arbitrary coherences in the initial density. It is a source-specific application of the existing arbitrary-complex-weight Prony annihilator, not a new generic Prony theorem.

**证明。** Work in the frame (8.5). Define

$$
x_\pm={e_1+e_3\over2}\pm {e_2\over\sqrt2},\qquad
h_\pm=x_\pm\otimes k,\qquad O=|h_+\rangle\langle h_-|,
\tag{10.2}
$$

for any unit $k\in K$. Direct multiplication of the actual matrices (8.6) gives $x_\pm$ orthonormal, $Ux_\pm=x_\pm$, and $Vx_\pm=\pm x_\pm$, independently of $\eta,\zeta$. In the original source coordinates these are the actual full-input states

$$
g_\pm=D^\dagger h_\pm
={1\over2}|1\rangle\otimes ak-{1\over2}|3\rangle\otimes ck
\mp {1\over\sqrt2}|2\rangle\otimes bk .
\tag{10.3}
$$

Thus $P_\pm=|h_\pm\rangle\langle h_\pm|$ are fixed by $\Phi$, while

$$
\Phi(O)=\lambda O,\qquad \lambda=1-4p,\qquad |\lambda|<1.
\tag{10.4}
$$

Although $O$ is not a density operator, equality on densities implies equality on all matrices. Explicitly, $O$ is the complex polarization combination of the four projectors onto $(h_+\pm h_-)/\sqrt2$ and $(h_+\pm i h_-)/\sqrt2$. Hence, for the reduced maps $\Psi_n$ in (9.1),

$$
f_n:=\langle h_+|\Psi_n(O)|h_-\rangle=\lambda^n,\qquad 0\le n\le N.
\tag{10.5}
$$

Let $S=\operatorname{supp}\sigma$ and write its spectral decomposition as $\sigma=\sum_j s_j|e_j\rangle\langle e_j|$ with every $s_j>0$ on $S$. Since $\Psi_n(P_\pm)=P_\pm$ and the summands of a positive leakage probability are nonnegative,

$$
W^n(h_\pm\otimes e)=h_\pm\otimes T_{\pm,n}e\qquad(e\in S,\ 0\le n\le N)
\tag{10.6}
$$

for isometries $T_{\pm,n}:S\to E$. This step uses the actual positive spectral support and does not purify $\sigma$ or assume that it is diagonal in a source basis. On

$$
F_\pm=\operatorname{span}\{T_{\pm,n}S:0\le n<N\},
$$

the same $W$ defines the isometry $T_{\pm,n}e\mapsto T_{\pm,n+1}e$. Extending it on $E$ gives a unitary $A_\pm$ with $A_\pm^ne=T_{\pm,n}e$ for $e\in S$ and $n\le N$. Consequently,

$$
f_n=\operatorname{Tr}(A_+^n\sigma A_-^{-n}).
\tag{10.7}
$$

Diagonalize the two auxiliary unitaries, $A_+=\sum_i u_iP_i$ and $A_-=\sum_jv_jQ_j$. Then

$$
f_n=\sum_{i,j}c_{ij}(u_i\overline v_j)^n,\qquad
c_{ij}=\operatorname{Tr}(P_i\sigma Q_j).
\tag{10.8}
$$

After combining equal frequencies and deleting zero combined coefficients, this is $\sum_{\ell=1}^K a_\ell\omega_\ell^n$ with $1\le K\le d^2$ and $|\omega_\ell|=1$. The coefficients may be arbitrary complex numbers; no positivity is used.

Reuse the existing finite Prony annihilator with

$$
q(z)=\prod_{\ell=1}^K(z-\omega_\ell)=\sum_{j=0}^Kq_jz^j .
$$

It gives $\sum_{j=0}^Kq_jf_j=0$. If $N\ge K$, (10.5) would imply $q(\lambda)=0$, impossible because every root of $q$ lies on the unit circle and $|\lambda|<1$. Therefore $N<K\le d^2$, proving (10.1). The endpoint is exact: the contradiction uses $f_0,\ldots,f_K$, so the conclusion is $N<K$. At $\lambda=0$ one has $q(0)=(-1)^K\prod_\ell\omega_\ell\ne0$; the zeroth sample is essential. The faces excluded by (8.1) would allow $|\lambda|=1$, so the strict domain is used.

For mixed $\sigma$, the usual Choi accounting is only

$$
\operatorname{rank}J(\Psi_n)\le d\,\operatorname{rank}(\sigma)\le d^2,
\tag{10.9}
$$

not $\operatorname{rank}J(\Psi_n)\le d$. The latter is a pure-environment statement and is not used in this proof. $\square$

**推论 10.2（Finite dimensions are unbounded across exact horizons）。** No single finite environment dimension can satisfy (9.1) for every horizon. In particular, for $N=16$ the terminal pure minimum from Theorem 8.2 is four, whereas every common-prefix realization, including arbitrary mixed initial densities, has $d\ge\lceil\sqrt{17}\rceil=5$. At this horizon the fully labelled construction below uses $62$ dimensions and the endpoint-sharing construction uses $61$; these are upper bounds, not optima.

**证明。** Letting $N$ increase in (10.1) rules out a fixed finite $d$. For $N=16$, (10.1) gives $d^2\ge17$. The terminal statement is a separate rank-of-one-channel contract and is therefore not contradicted. $\square$

**定理 10.3（Charged fully labelled upper construction and its finite return）。** Let $\Lambda_0=\operatorname{id}_H,\Lambda_n=\Phi^n$ and $r_n=\operatorname{rank}J(\Lambda_n)$. For every finite $N$ there is a pure initial state, one unitary $W$ and one charged environment with

$$
\dim E=\sum_{n=0}^N r_n
\tag{10.10}
$$

that satisfies (9.1). For the balanced source this gives

$$
\dim E=1,3,4N-2\quad\text{for }N=0,1,N\ge2,
\tag{10.11}
$$

using $r_n=\min(n+1,4)$ from Theorem 8.2. For $N\ge2$ the construction has an exact global return at time $N+1$, but that return is the boundary of the finite contract and does not assert $\Phi^{N+1}$.

**证明。** Choose minimal Stinespring isometries $V_n:H\to H\otimes E_n$ for $\Lambda_n$, with $\dim E_n=r_n$, and take $E=\bigoplus_{n=0}^NE_n$. Embed the ranges $M_n=V_nH$ in their mutually orthogonal environment summands. Let $V_{N+1}=V_0$ and define

$$
W=\sum_{n=0}^NV_{n+1}V_n^*+(I-P),\qquad
P=\sum_{n=0}^NV_nV_n^* .
\tag{10.12}
$$

The first term cyclically permutes the orthogonal copies $M_n$ and the second is the identity on their orthogonal complement. Thus $W$ is unitary, $W^{N+1}=I$ on the whole joint space, and $W^n(x\otimes e_0)=V_nx$ for $0\le n\le N$, where $V_0x=x\otimes e_0$. Partial tracing gives $\Lambda_n$ on all matrices, and tensoring the identities with $I_R$ gives all untouched-reference cases. All time sectors, including the finite clock, are in $E$; no clock readout, reset or external controller is used. The return at $N+1$ gives the identity channel on the prepared boundary state, which generally differs from $\Phi^{N+1}$, so it is not an all-horizon realization. The one-step two-dimensional construction of Theorem 2.1 and the exact N=2 values of Theorem 9.3 remain sharper small-horizon results. $\square$

**引理 10.4（One endpoint can share one charged environment dimension）。** Let a channel $\Lambda$ have Choi rank $r>0$ and Choi operator $J$ supported on $S$. For any nonzero $k\in S$, there is a Kraus family of $\Lambda$ with $r$ members whose first member is $cK$, where $\operatorname{vec}K=k$ and $c>0$, and whose other $r-1$ members span the residual support. Indeed, with $J_S^{-1}$ the inverse on $S$, choose

$$
c^2=\langle k,J_S^{-1}k\rangle^{-1}.
\tag{10.13}
$$

Then $J-c^2|k\rangle\langle k|$ is positive semidefinite of rank $r-1$, and its rank-one decomposition supplies the remaining Kraus operators.

**证明。** On the support, $J_S$ is positive definite. The rank-one Schur-complement identity gives $J_S-c^2kk^*\succeq0$ for (10.13), with one-dimensional kernel generated by $J_S^{-1}k$; hence its rank is $r-1$. Vectorizing a rank-one decomposition is exactly a Kraus decomposition. $\square$

**定理 10.5（Endpoint-sharing upper construction, with a distinct boundary）。** For every $N\ge2$ the same contract (9.1) has a pure realization with

$$
\dim E=\sum_{n=0}^Nr_n-1=4N-3 .
\tag{10.14}
$$

This construction shares one environment coordinate between the initial and final boundary embeddings. It has no guaranteed cyclic return and does not provide distinct initial and final time labels; those are different contracts from the fully labelled construction.

**证明。** Use $E_0=\mathbb C e_0$ and mutually orthogonal $E_n$ for $1\le n<N$, with $\dim E_n=r_n$. Apply Lemma 10.4 to $\Lambda_N$ and write a minimal Kraus family whose first operator is $K_0$ on the shared coordinate $e_0$ and whose other $r_N-1$ operators use a fresh space $F_N$. Define $V_0x=x\otimes e_0$, use arbitrary minimal $V_n$ in $E_n$ for $1\le n<N$, and use the split family for $V_N$ in $e_0\oplus F_N$. Then $V_0,\ldots,V_{N-1}$ have pairwise orthogonal ranges, and $V_1,\ldots,V_N$ also have pairwise orthogonal ranges; only $V_0$ and $V_N$ may overlap. Therefore every off-diagonal block on the two sides of (9.4) is zero, while diagonal blocks are $I_H$, so Lemma 9.2 extends $V_n\mapsto V_{n+1}$ to one unitary $W$ on $H\otimes E$. With the pure initial state $|e_0\rangle$, induction gives $W^n(x\otimes e_0)=V_nx$ for $n\le N$. The environment dimension is

$$
1+\sum_{n=1}^{N-1}r_n+(r_N-1)=\sum_{n=0}^Nr_n-1.
$$

For the source, (8.3) gives (10.14). The shared $e_0$ component in $V_N$ prevents interpreting the final embedding as a distinct time label. The extension on the orthogonal complement is arbitrary, so neither $W^{N+1}=I$ nor any cyclic return is guaranteed. Nevertheless this is the same full-input/reference and no-clock-readout contract (9.1). $\square$

**命题 10.6（No automatic positive-moment strengthening）。** Equation (10.7) is not in general a positive-definite unitary moment sequence. A positive-moment argument is valid under the additional hypothesis $[A_-,\sigma]=0$: then, for the Hilbert--Schmidt unitary $\mathcal U:X\mapsto A_+XA_-^*$, $\sqrt\sigma$ is a moment vector with $f_n=\langle\sqrt\sigma,\mathcal U^n\sqrt\sigma\rangle_{\mathrm{HS}}$, and the Gram matrix of the first $N+1$ orbit vectors is $(\lambda^{|i-j|})$, whose determinant is $(1-\lambda^2)^N>0$ for real $|\lambda|<1$. That conditional route can yield a stronger $d\,\operatorname{rank}\sigma\ge N+1$, but the commutation/stationarity hypothesis is not part of (9.1).

A source-compatible one-step counterexample at $p=q=1/4$ makes the missing hypothesis concrete. On an environment qubit take

$$
C={I-iZ\over\sqrt2},\qquad P={I+X\over2},\qquad Q={I-X\over2},\qquad
\sigma={I+Y/2\over2},
$$

and $W=(I_H\otimes C)(U\otimes P+V\otimes Q)$. The one-step reduced channel is $\Phi$ on the full $H$ and all references, while on the two sectors $h_\pm$ the branch unitaries are $A_+=C$ and $A_-=CX$. Direct exact multiplication gives

$$
(f_0,f_1,f_2,f_3,f_4)=(1,0,0,-1/2,-1).
\tag{10.15}
$$

Define $t_n=f_n$ for $n\ge0$ and $t_{-n}=\overline{f_n}$ for $n>0$. The Hermitian Toeplitz matrix $(t_{i-j})_{0\le i,j\le4}$ has determinant $-7/16$, so this completion is not positive semidefinite. This completion differs from extending the trace formula (10.7) to negative powers, which gives $f_{-1}=1/2$ while $f_1=0$ and is not Hermitian. The example is only a one-step source counterexample to automatic positivity; it is not claimed to satisfy a longer prefix. Thus no conclusion $d\ge N+1$ is automatic. The proved general statement is the arbitrary-complex-weight bound (10.1). $\square$

## 11. Source correspondence, literature and limits

**定义 11.1（What the quantitative addition reuses）。** The matrices, frame $D$, channel and terminal ranks are exactly those of §§1--3 and 8. The vectors (10.2)--(10.3) are the source's actual full-input states, not a substituted configuration-only model. The finite-frequency annihilator is reused from the existing arbitrary-field Prony suppliers `prony_moment_linear_recurrence` and `pronyAnnihilator` in `D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction.lean`; no generic Prony theorem is introduced here. Choi/Kraus rank and finite Stinespring dilations are standard suppliers. The charged clock method is the finite-dimensional specialization of the Stinespring-plus-clock construction in vom Ende--Dirr, arXiv:1804.00918v3, Theorem 4. Theorem 7.4 of RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md contains a related $4N-2$ direct-sum clock argument under a different receiving/blank-output contract; it is credited as a method comparison and is not used as a stronger lower bound. The exact endpoint-sharing construction is the same finite isometry-extension mechanism with one deliberately shared boundary coordinate.

**假设 11.2（Operational and epistemic limits）。** Every displayed equality is finite-dimensional exact mathematics about the abstract source channel. It does not certify physical preparation of arbitrary real $\alpha,\beta,\eta,\zeta$, calibration, native $\alpha/\beta$ acquisition, a physical clock, spatial geometry, thermodynamic or erasure cost, or executable finite precision. It does not reproduce an acquired edge or path archive, a measured-history instrument, arbitrary inserted interventions, feedback, or an intervened process tensor. The untouched reference is a proof of complete input action and is not a memory or an extra environment. The finite clock sectors are internal charged degrees of freedom and are not read out. No optimum for $N\ge3$, matching lower and upper rate, or exact classification beyond (9.5) is claimed. The small-$N$ constructions already established in §§2 and 9 are retained. The long-term restoration problem remains open beyond this finite prefix result.

**本批核验。** Exact symbolic checks for the source vectors, the eigenoperator equation (10.4), the mixed one-step counterexample (10.15), the $N=2$ block construction (9.16)--(9.18), the four-node Prony endpoint, and the charged cyclic embeddings agree with the displayed identities. These are ordinary algebraic checks, not Lean verification or a replacement for the repository's required checks. No digestion, Lean addition, judge/tool change, experiment material, publication or physical implementation is part of this addition.

## 追加锚（本行以下为增补区）

## 12. Strict-unbalanced terminal rank and exact homogeneous length

**定义 12.1（The strict-unbalanced terminal contract）。** Keep the source configurations, transports, full input space and frame of §§1–3. Let

$$
\mathcal D_{\ne}=\{(p,q,r):p,q,r>0,\ p+q+r<1,\ p\ne q\}.
$$

For $(p,q,r)\in\mathcal D_{\ne}$ set

$$
t=p+q,\qquad B=1-t,\qquad A=B-r,\qquad
\alpha=\sqrt{p/t},\quad \beta=\sqrt{q/t},\quad
\eta=\sqrt{A/B},\quad \zeta=\sqrt{r/B}.
\tag{12.1}
$$

Then $B,t,A>0$, $\alpha,\beta,\eta,\zeta>0$, $\alpha^2+\beta^2=1$, $\eta^2+\zeta^2=1$, and $\alpha\ne\beta$. Let $L_0,L_1$ be exactly the two source Kraus operators in (2.6), and put

$$
T_0=B^{-1/2}L_0,\qquad T_1=t^{-1/2}L_1,\qquad
\Phi_{\ne}(X)=B T_0XT_0^*+tT_1XT_1^*.
\tag{12.2}
$$

The terminal contract is the fixed unread channel power $\Phi_{\ne}^N$, obtained by composing this same reduced channel with an independently prepared fresh pure environment at every step and tracing each outgoing environment. No successor measurement, retained control, clock readout or intervention is inserted. The input is the whole $H=\mathbb C^5\otimes\mathbb C^2$ and may be coherent or entangled with any untouched finite reference.

**定理 12.2（Uniform strict-unbalanced exact-length span and terminal rank）。** For every $(p,q,r)\in\mathcal D_{\ne}$, let $\mathcal S_N$ be the complex span of products of exactly $N$ letters from the two normalized configuration operators defined below. Then

$$
\boxed{\mathcal S_N=M_5(\mathbb C)\quad\text{for every }N\ge12.}
\tag{12.3}
$$

Consequently, for every $N\ge12$,

$$
\boxed{\operatorname{rank}J(\Phi_{\ne}^N)=25.}
\tag{12.4}
$$

The minimum environment dimension for a terminal realization with an initially pure environment is exactly $25$. The same channel and the same minimum act on every untouched reference extension. The assertion is about this terminal contract; it is not a claim about one autonomous interaction realizing all prefix powers.

**证明。** Write $F=|4\rangle\langle4|$ and $Q=I_5-F$. The source frame is the one fixed in (3.1)–(3.2), namely

$$
G_0=I_K,\quad G_1=a,\quad G_2=ca=-b,\quad
G_3=a^\dagger ca=-c,\quad G_4=b,
$$

and $D=\sum_i|i\rangle\langle i|\otimes G_i^\dagger$. Apply $D$ to both the input and output of the normalized operators in (12.2). Directly substituting the source transports (1.3) into (2.6), with the positive leaf transports $b,b^\dagger$ and the published negative closing square edge, gives

$$
DT_0D^*=U\otimes I_K,\qquad DT_1D^*=V\otimes I_K,
\tag{12.5}
$$

where

$$
U=
\begin{pmatrix}
\eta&0&0&0&\zeta\\
0&1&0&0&0\\
0&0&1&0&0\\
0&0&0&1&0\\
\zeta&0&0&0&-\eta
\end{pmatrix}
$$

and, with the signed square cycle $Ce_0=e_1$, $Ce_1=e_2$, $Ce_2=e_3$, $Ce_3=-e_0$, $Ce_4=0$,

$$
V=\alpha C+\beta C^*+F
=\begin{pmatrix}
0&\beta&0&-\alpha&0\\
\alpha&0&\beta&0&0\\
0&\alpha&0&\beta&0\\
-\beta&0&\alpha&0&0\\
0&0&0&0&1
\end{pmatrix}.
\tag{12.6}
$$

This is the actual source frame: the sign in $Ce_3=-e_0$ is retained, the two leaf entries are positive, and the protected logical factor is $I_K$. Since $C^*C=CC^*=Q$, $C^4=-Q$, and $C^2+(C^*)^2=0$, the normalization in (12.1) gives

$$
U^*=U,\quad U^2=I_5,\qquad V^*V=VV^*=I_5.
\tag{12.7}
$$

Let $\mathcal S_N$ denote the span of all words of exactly $N$ letters from $\{U,V\}$, with $\mathcal S_0=\mathbb C I_5$. Put

$$
h=\alpha^2-\beta^2,\qquad s=\alpha\beta,\qquad
d=2(1-2s)=2(\alpha-\beta)^2.
$$

The strict hypotheses give $h\ne0$ and $d>0$. On $Q\mathbb C^5$,

$$
V^2=2sQ+hC^2,
$$

and the full-space identity is

$$
V^4-4sV^2+I_5=dF.
\tag{12.8}
$$

Because $U^2=I_5$, each term on the left has an exact length-four representation: $V^4$ is already such a word, $V^2=V^2U^2$ is represented by $VVUU$, and $I_5=U^4$. Hence

$$
F=d^{-1}(V^4-4sV^2U^2+U^4)\in\mathcal S_4.
\tag{12.9}
$$

The square-sector columns $e_0,Ve_0,V^2e_0,V^3e_0$ have determinant

$$
\det[e_0\ Ve_0\ V^2e_0\ V^3e_0]=h^2(\alpha^2+\beta^2)=h^2\ne0,
\tag{12.10}
$$

as follows by inserting $V^2e_0=2s e_0+h e_2$ and
$V^3e_0=(3\alpha^2\beta-\beta^3)e_1+(\alpha^3-3\alpha\beta^2)e_3$. The row family $e_0^*,e_0^*V,e_0^*V^2,e_0^*V^3$ has the same determinant (the direct row expansion gives the same factor $h^2(\alpha^2+\beta^2)$). Thus both the square columns and square rows are bases of $Q\mathbb C^5$.

Now use the source leaf coupling in $U$. The five exact-length-four words

$$
V^4,\qquad V^kUV^{3-k}\quad(0\le k\le3)
$$

send $e_4$ to $e_4$ and to $\zeta V^ke_0-\eta e_4$, respectively. By (12.10) their five images form a basis of $\mathbb C^5$, with determinant $\zeta^4h^2\ne0$. The five words

$$
V^4,\qquad V^{3-k}UV^k\quad(0\le k\le3)
$$

give, after applying $e_4^*$ on the left, the basis $e_4^*$ and $\zeta e_0^*V^k-\eta e_4^*$. Therefore

$$
\mathcal S_4e_4=\mathbb C^5,
\qquad e_4^*\mathcal S_4=(\mathbb C^5)^*.
\tag{12.11}
$$

For arbitrary $x\in\mathbb C^5$ and covector $y\in(\mathbb C^5)^*$ choose $A_x,B_y\in\mathcal S_4$ with $A_xe_4=x$ and $e_4^*B_y=y$. Since $F=|e_4\rangle\langle e_4|$,

$$
A_xFB_y=xy\in\mathcal S_{12}.
$$

Every rank-one matrix $xy$ is therefore in $\mathcal S_{12}$, so $\mathcal S_{12}=M_5(\mathbb C)$. If $\mathcal S_n=M_5(\mathbb C)$, prefixing every word by the invertible $U$ gives $M_5(\mathbb C)=U\mathcal S_n\subseteq\mathcal S_{n+1}\subseteq M_5(\mathbb C)$. Induction proves (12.3) for every exact $N\ge12$. This is a homogeneous-length statement; no cumulative bounded-length span or generic algebra-generation assertion is being substituted.

Return to the actual ten-dimensional source. A length-$N$ Kraus word of (12.2) is a nonzero scalar $B^{n_0/2}t^{n_1/2}$ times $D^*(W\otimes I_K)D$ for the corresponding configuration word $W$, where $n_0+n_1=N$. Both weights are strictly positive. The map $W\mapsto D^*(W\otimes I_K)D$ is complex-linear and injective, so the full-input Kraus span has dimension $25$ for every $N\ge12$. Expanding the fresh-environment channel power gives

$$
J(\Phi_{\ne}^N)=\sum_{w\in\{0,1\}^N}
|\operatorname{vec}L_w\rangle\langle\operatorname{vec}L_w|,
\tag{12.12}
$$

where $L_w$ is the corresponding actual product of $L_0,L_1$. The kernel of this positive sum is the common orthogonal complement of the vectorized Kraus family, hence its rank is exactly the Kraus-span dimension, proving (12.4) on all of $H$. Tensoring every Kraus operator with $I_R$ preserves linear independence for every finite untouched reference $R$, so the same fresh terminal channel has Choi rank $25$ on $H\otimes R$ and acts on arbitrary coherent or entangled inputs.

A pure terminal environment of dimension $d$ supplies at most $d$ Kraus components, so (12.4) forces $d\ge25$. Conversely, a rank-$25$ positive Choi decomposition supplies $25$ Kraus operators. Trace preservation makes $x\mapsto\sum_{a=1}^{25}K_ax\otimes|a\rangle$ an isometry from $H$ into $H\otimes\mathbb C^{25}$, and finite-dimensional isometry extension gives a unitary with one fixed pure ready state. Thus the pure minimum is attained at $25$. If the terminal environment has dimension $d$ and initial state $\sigma$ of rank $s$, the same spectral decomposition argument gives only

$$
25\le d\,\operatorname{rank}(\sigma)=ds\le d^2;
\tag{12.13}
$$

no mixed-environment minimum or attainment at dimension five is asserted. The framed map remains a configuration channel tensored with $\operatorname{id}_K$; this theorem makes no primitivity claim for the full ten-dimensional channel.
$\square$

**定理 12.3（Balanced comparison at the same fresh terminal contract）。** At the balanced stratum $p=q>0$, $2p+r<1$, with the same full input, fresh independent environments, unread terminal output and untouched-reference convention, the published Theorem 8.2 gives

$$
\operatorname{rank}J(\Phi^N)=\min\{N+1,4\},
$$

so the terminal rank is $4$ for every $N\ge3$. Under the same contract, the strict-unbalanced theorem above gives rank $25$ for every $N\ge12$. The change is caused by the exact-length leaf projector and the two nonzero cyclic determinants: their only interior obstruction is $\alpha=\beta$, namely $p=q$. This comparison keeps the source frame, logical factor, coherent full input, positive fresh weights and terminal convention fixed.

**证明。** The balanced equality is exactly (8.3), whose proof uses the involution relation $V^2=I_5$ and the infinite-dihedral normal form. When $p\ne q$, $V$ is not an involution; the proof of (12.3) instead uses (12.8)–(12.11). Both statements concern the same terminal channel-power contract and neither is a statement about a retained environment.

## 13. Exact discriminator, source limits and contract separations

**定义 13.1（Existing suppliers and exact correspondences）。** The source-specific bridge in Theorem 12.2 uses the matrices and frames already fixed in §§1–3, especially (2.6), (2.8), (2.9) and (3.1)–(3.2). The signed-cycle operator identity comes from the source square transport (2.4); the strict-domain factors are computed in (12.1), and the homogeneous proof is the new leaf-projector/evaluation construction (12.8)–(12.11).

Sanz, Pérez-García, Wolf and Cirac, *A quantum version of Wielandt’s inequality*, arXiv:0909.5347v2, §II, discussion following equation (1), identifies exact Kraus-word spans with Choi rank; §III, Lemma 2 and Theorem 1, supplies the cyclic/rank-one quantum-Wielandt background. The present proof checks the source-specific homogeneous length directly and does not invoke a generic primitivity theorem or a generic algebra-generation claim. Watrous, *The Theory of Quantum Information*, Chapter 2, Theorem 2.22 and Corollary 2.27 supply the finite-dimensional Kraus/Choi representation and Choi-rank pure Stinespring attainment used after (12.12). Existing repository results TwoInvolutionWordRank and BalancedFiveModeWordRank cover involutive/balanced words, while FiniteWordReachability concerns bounded lengths; none is reused as the strict-unbalanced homogeneous theorem.

**命题 13.2（Exact rational discriminator）。** At

$$
(p,q,r)=(9/50,8/25,8/25),\qquad
(\alpha,\beta,\eta,\zeta)=(3/5,4/5,3/5,4/5),
$$

the exact-length configuration spans and the full-input terminal Choi ranks satisfy

$$
\dim\mathcal S_7=\operatorname{rank}J(\Phi_{\ne}^7)=24,
\qquad
\dim\mathcal S_8=\operatorname{rank}J(\Phi_{\ne}^8)=25.
\tag{13.1}
$$

Consequently, the least uniform cutoff $N_*$ for which every source in $\mathcal D_{\ne}$ has terminal Choi rank $25$ at every exact length $N\ge N_*$ satisfies $8\le N_*\le12$.

**证明。** The parameters lie in $\mathcal D_{\ne}$ and give $t=B=1/2$, $A=9/50$ in (12.1). Clear the common denominator of (12.5)–(12.6), writing $X=5U$ and $Y=5V$:

$$
X=\begin{pmatrix}
3&0&0&0&4\\
0&5&0&0&0\\
0&0&5&0&0\\
0&0&0&5&0\\
4&0&0&0&-3
\end{pmatrix},\qquad
Y=\begin{pmatrix}
0&4&0&-3&0\\
3&0&4&0&0\\
0&3&0&4&0\\
-4&0&3&0&0\\
0&0&0&0&5
\end{pmatrix}.
\tag{13.2}
$$

Here is a finite integer linear-algebra certificate. Set $W_0(0)=I_5$ and, for $0\le m<2^n$, define

$$
W_{n+1}(2m)=W_n(m)X,\qquad
W_{n+1}(2m+1)=W_n(m)Y.
\tag{13.3}
$$

Thus $m$ indexes the word whose $n$ binary digits, including leading zeros, choose $X$ for $0$ and $Y$ for $1$, from left to right. Use the row-order vectorization $\operatorname{v}(Z)_{5i+j}=Z_{ij}$ for $0\le i,j\le4$, and put

$$
M_n=[\operatorname{v}(W_n(0))\ \cdots\ \operatorname{v}(W_n(2^n-1))].
$$

All its columns are $5^n$ times the corresponding configuration words, so $\operatorname{rank}_{\mathbb C}M_n=\dim\mathcal S_n$. Define

$$
H=\begin{pmatrix}
0&42&0&56&0\\
56&70&8&0&28\\
0&-6&0&-8&0\\
42&0&6&-70&21\\
0&21&0&28&0
\end{pmatrix}
$$

and the ordered index lists

$$
\begin{aligned}
I_7={}&(0,1,2,3,5,6,7,10,11,13,14,15,21,22,23,27,29,30,\\
&45,47,55,59,111,119),\\
I_8={}&(I_7,239),\\
R_7={}&(0,1,\ldots,22,24),\qquad R_8=(0,1,\ldots,24).
\end{aligned}
$$

The certificate consists of the following exact integer identities and residues, with submatrix rows and columns taken in the displayed order:

$$
\operatorname{v}(H)^{\mathsf T}M_7=0_{1\times128},\qquad
\det M_7[R_7,I_7]\equiv2\pmod{101},\qquad
\det M_8[R_8,I_8]\equiv35\pmod{101}.
\tag{13.4}
$$

These identities use only the two integer matrices (13.2) and the finite recurrence (13.3). In particular, each of the $128$ entries in the first identity is the integer sum $\sum_{i,j=0}^4H_{ij}(W_7(m))_{ij}$; the two other identities are determinants of the specified $24\times24$ and $25\times25$ matrices reduced in $\mathbb F_{101}$. This specifies every entry and operation of the certificate without a rounding or tolerance convention.

Since $H\ne0$, the first identity confines the length-seven span to a hyperplane, giving rank at most $24$. The residue $2$ shows that its displayed $24\times24$ minor is a nonzero integer, giving rank at least $24$ over $\mathbb C$. The residue $35$ gives rank $25$ at length eight. Positive source word weights and the injective full-input map $W\mapsto D^*(W\otimes I_K)D$, as in the proof of (12.12), identify these span dimensions with the actual terminal Choi ranks. The failure at length seven gives $N_*\ge8$, and Theorem 12.2 gives $N_*\le12$.
$\square$

**假设 13.3（Domain limits and distinct operational contracts）。** The strict domain excludes $p=q$ and all degenerate boundary strata. Its nonzero factors $h,d,\zeta$ need not have a uniform positive lower bound. Proposition 13.2 is a single-source discriminator; a universal $N=8$ theorem, a universal early-rank profile and a robust finite-precision margin remain unresolved.

The one-retained-environment interaction of Proposition 8.3 is a different contract: it has terminal rank one for even repetitions and two for odd repetitions. The common-autonomous-prefix contract (9.1) asks for one fixed $W$ and one fixed initial density reproducing every $\Phi^n$ through a horizon; Theorem 12.2 is a separate terminal realization for each selected $N$ and supplies no such autonomous-prefix construction. The measured continuation and ordered path records of §§5–6 retain acquired successor/history information and are not identified with a terminal Choi rank. In particular, rank $25$ does not compress an acquired edge or path archive.

The theorem assumes the abstract source data, frame operations, positive weights, fresh pure records and terminal trace supplied in Assumptions 1.4 and 7.5. It does not prove a native $\alpha/\beta$ acquisition bridge, physical preparation or calibration, finite executable precision, a clock or readout apparatus, an acquired event/path archive, reset or erasure cost, or an all-horizon autonomous interaction.

## 追加锚（本行以下为增补区）

## 14. Sharp uniform exact-length terminal horizon

**定义 14.1（Source parameters and indexed length-eight minor）。** Use exactly the strict-unbalanced domain $\mathcal D_{\ne}$ and the fresh unread terminal-channel contract of Definition 12.1. In particular,

$$
t=p+q,\quad B=1-p-q,\quad A=B-r,\qquad
(\alpha,\beta,\eta,\zeta)
=\left(\sqrt{p/t},\sqrt{q/t},\sqrt{A/B},\sqrt{r/B}\right).
\tag{14.1}
$$

The source Kraus operators remain (2.6), with the transports (1.3), inverse reverse edges and identity self-loops. The same input/output frame $D=\sum_i|i\rangle\langle i|\otimes G_i^\dagger$, with $(G_0,G_1,G_2,G_3,G_4)=(I_K,a,ca,a^\dagger ca,b)$, gives precisely

$$
DL_0D^*=\sqrt B\,U\otimes I_K,\qquad
DL_1D^*=\sqrt t\,V\otimes I_K,
\tag{14.2}
$$

where $U,V$ are the actual matrices (12.5)–(12.6). Thus the negative square closing edge and both positive leaf entries are retained. The factor $I_K$, $K=\mathbb C^2$, is the protected logical factor, not an additional environment.

Put $\mathsf G_0=U,\mathsf G_1=V$ for the two word letters. For $m=\sum_{j=1}^8w_j2^{8-j}$, with all eight binary digits retained, define

$$
\Gamma_8(m)=\mathsf G_{w_8}\cdots \mathsf G_{w_1},\qquad
\operatorname v(Z)_{5i+j}=Z_{ij}\quad(0\le i,j\le4).
\tag{14.3}
$$

Fix the ordered column list

$$
\mathcal I=(0,1,2,3,5,6,7,10,11,13,14,15,21,22,23,27,29,30,
45,47,55,59,111,119,239)
\tag{14.4}
$$

and let $M=[\operatorname v(\Gamma_8(m))]_{m\in\mathcal I}$, with rows $0,\ldots,24$ in the order (14.3). The recurrence (13.3) instead multiplies letters on the right. Reversal permutes the complete set of length-eight words and therefore preserves its span; it does not justify transferring an individually indexed minor between the two conventions. The determinant below uses only (14.3)–(14.4); the integer minors in (13.4) retain their original recurrence and indexing.

**引理 14.2（All-parameter polynomial certificate for the source minor）。** Throughout $\mathcal D_{\ne}$,

$$
\boxed{\det M=
\frac{768\,\zeta^{36}(\alpha+\beta)^{16}(\beta-\alpha)^{36}}
{(1+\eta)^{12}}\ne0.}
\tag{14.5}
$$

**证明。** Rationalize the two positive unit circles by

$$
x=\frac{\zeta}{1+\eta},\qquad y=\frac{\beta}{1+\alpha},\qquad
\eta=\frac{1-x^2}{1+x^2},\quad \zeta=\frac{2x}{1+x^2},\quad
\alpha=\frac{1-y^2}{1+y^2},\quad \beta=\frac{2y}{1+y^2}.
\tag{14.6}
$$

Here $0<x,y<1$. In the polynomial ring $\mathbb Z[x,y]$ write

$$
f=1+x^2,\quad g=1+y^2,\quad h_-=y^2-2y-1,\quad
h_+=y^2+2y-1,\quad \ell=y^2-1.
$$

The scaled letters are the following polynomial matrices, with exactly the source's signs and configuration order:

$$
\widehat U=fU=
\begin{pmatrix}
1-x^2&0&0&0&2x\\
0&f&0&0&0\\
0&0&f&0&0\\
0&0&0&f&0\\
2x&0&0&0&x^2-1
\end{pmatrix},\qquad
\widehat V=gV=
\begin{pmatrix}
0&2y&0&y^2-1&0\\
1-y^2&0&2y&0&0\\
0&1-y^2&0&2y&0\\
-2y&0&1-y^2&0&0\\
0&0&0&0&g
\end{pmatrix}.
\tag{14.7}
$$

Let $\widehat\Gamma_8(m)$ and $\widehat M$ use (14.3)–(14.4) with these scaled letters. The selected words contain altogether $114$ zero letters and $86$ one letters, so

$$
\det\widehat M=f^{114}g^{86}\det M.
\tag{14.8}
$$

The following finite fraction-free certificate specifies the entire polynomial calculation. Since $\widehat U^2=f^2I_5$, adjacent pairs of zero letters can be removed, contributing powers of $f$. In the column order (14.4), the numbers of removed letters are

$$
(e_0,\ldots,e_{24})=
(8,6,6,6,4,4,4,4,4,4,4,4,2,2,2,2,2,2,2,2,2,2,0,0,0),
\qquad \sum_j e_j=78.
\tag{14.9}
$$

Thus $Z^{(0)}_{ij}=f^{-e_j}\widehat M_{ij}$ is a polynomial matrix and $\det\widehat M=f^{78}\det Z^{(0)}$. This also gives a direct way to form $Z^{(0)}$: delete every adjacent $00$ pair in each binary word, then multiply the remaining scaled letters in the order (14.3).

Index all rows and columns from zero. For $k=0,\ldots,23$, first swap rows $(k,r_k)$ in the current $Z^{(k)}$ at precisely these stages:

$$
(k,r_k)=(2,4),(3,4),(4,5),(5,6),(11,24),(12,13),(14,15),(17,20),(19,21).
\tag{14.10}
$$

There is no swap at any other stage. Call the resulting matrix $\widetilde Z^{(k)}$, put $p_k=\widetilde Z^{(k)}_{kk}$ and $p_{-1}=1$, and update the trailing block simultaneously by

$$
Z^{(k+1)}_{ij}=
\frac{p_k\widetilde Z^{(k)}_{ij}
-\widetilde Z^{(k)}_{ik}\widetilde Z^{(k)}_{kj}}{p_{k-1}}
\quad(i,j>k).
\tag{14.11}
$$

Set $Z^{(k+1)}_{ik}=0$ for $i>k$ and keep the other entries of $\widetilde Z^{(k)}$. All divisions in (14.11) are exact polynomial divisions. This is fraction-free determinant elimination, equivalently the successive-minor identity; it uses $\sum_{j=1}^{24}j^2=4900$ such divisions. To make the intermediate identities reproducible as well as the final factorization, define the five residual polynomials

$$
\begin{aligned}
R_1={}&x^2y^3-x^2y+y^4+3y^3+2y^2-3y+1,\\
R_2={}&2x^2y^5-4x^2y^4-4x^2y^3+4x^2y^2+2x^2y
+y^6+4y^5-3y^4+3y^2+4y-1,\\
R_3={}&2x^2y^3-4x^2y^2-2x^2y+y^4+4y^3-6y^2-4y+1,\\
R_4={}&y^4+4y^3-6y^2-4y+1,\\
R_5={}&y^6-2y^5+y^4+12y^3-y^2-2y-1.
\end{aligned}
$$

For $0\le k<24$ the pivots, and for $k=24$ the final entry $p_{24}=Z^{(24)}_{24,24}$, have the form

$$
p_k=c_k x^{i_k}y^{j_k}f^{u_k}g^{v_k}
h_-^{a_k}h_+^{b_k}\ell^{d_k}T_k,
\tag{14.12}
$$

with the following complete table. Each row is an identity in $\mathbb Z[x,y]$ determined by (14.7), (14.9)–(14.11).

| $k$ | $c_k$ | $(i_k,j_k,u_k,v_k,a_k,b_k,d_k)$ | $T_k$ |
| --- | --- | --- | --- |
| 0 | $1$ | $(0,0,0,0,0,0,0)$ | $1$ |
| 1 | $2$ | $(0,1,1,0,0,0,0)$ | $1$ |
| 2 | $4$ | $(1,1,1,1,0,0,0)$ | $1$ |
| 3 | $-4$ | $(1,1,1,1,1,1,0)$ | $1$ |
| 4 | $16$ | $(3,1,1,0,1,3,1)$ | $1$ |
| 5 | $-64$ | $(5,1,1,0,1,3,1)$ | $R_1$ |
| 6 | $32$ | $(5,0,2,2,2,4,1)$ | $R_1$ |
| 7 | $-128$ | $(7,1,3,3,2,6,1)$ | $1$ |
| 8 | $-256$ | $(9,2,4,4,3,6,1)$ | $1$ |
| 9 | $1024$ | $(10,2,4,4,3,7,3)$ | $1$ |
| 10 | $-2048$ | $(12,2,4,5,4,7,1)$ | $R_2$ |
| 11 | $-4096$ | $(12,2,4,7,4,9,1)$ | $R_2$ |
| 12 | $8192$ | $(14,1,5,7,4,10,2)$ | $R_2R_3$ |
| 13 | $65536$ | $(18,2,6,8,5,12,3)$ | $R_3$ |
| 14 | $-262144$ | $(20,2,6,11,6,13,2)$ | $R_3$ |
| 15 | $-524288$ | $(21,2,7,11,7,15,1)$ | $R_3R_4$ |
| 16 | $262144$ | $(23,0,8,13,8,17,1)$ | $R_3R_5$ |
| 17 | $3145728$ | $(24,0,9,15,8,19,1)$ | $R_3R_5$ |
| 18 | $6291456$ | $(28,0,10,19,11,21,1)$ | $1$ |
| 19 | $50331648$ | $(29,1,10,21,11,23,1)$ | $1$ |
| 20 | $-100663296$ | $(31,1,10,23,13,25,0)$ | $1$ |
| 21 | $-402653184$ | $(32,1,10,25,12,27,0)$ | $R_4$ |
| 22 | $1610612736$ | $(33,1,11,27,13,30,0)$ | $R_4$ |
| 23 | $-3221225472$ | $(34,0,12,30,14,34,1)$ | $1$ |
| 24 | $-12884901888$ | $(36,0,12,34,16,36,0)$ | $1$ |

Every listed pivot is a nonzero polynomial. The nine row swaps give

$$
\begin{aligned}
\det Z^{(0)}&=-p_{24}
=3\cdot2^{32}x^{36}f^{12}g^{34}h_-^{16}h_+^{36},\\
\det\widehat M&=3\cdot2^{32}x^{36}f^{90}g^{34}h_-^{16}h_+^{36}.
\end{aligned}
\tag{14.13}
$$

The certificate is a symbolic calculation over $\mathbb Q(x,y)$ whose input and final output lie in $\mathbb Z[x,y]$. It proves a polynomial identity before specialization. Individual intermediate pivots, including the $R_i$, may vanish at particular real parameters; no nonvanishing assumption on those specialized pivots is used, and no parameter locus is lost by the elimination.

Finally, (14.6) gives $1+\eta=2/f$, $\zeta=2x/f$, $\alpha+\beta=-h_-/g$ and $\beta-\alpha=h_+/g$. Dividing (14.13) by the factor in (14.8) yields

$$
\det M=3\cdot2^{32}x^{36}f^{-24}g^{-52}h_-^{16}h_+^{36}
=\frac{768\,\zeta^{36}(\alpha+\beta)^{16}(\beta-\alpha)^{36}}
{(1+\eta)^{12}}.
$$

This proves (14.5) for every source parameter: $\zeta>0$, $\alpha+\beta>0$, $1+\eta>0$, and $\beta-\alpha\ne0$ is exactly $p\ne q$. $\square$

**定理 14.3（Sharp uniform horizon and full-input pure terminal minimum）。** For the actual strict-unbalanced source on the whole $H=\mathbb C^5\otimes\mathbb C^2$, under Definition 12.1's independently fresh pure environments, unread output and terminal trace, the exact-length configuration spans satisfy

$$
\boxed{\mathcal S_N=M_5(\mathbb C)\quad\text{and}\quad
\operatorname{rank}J(\Phi_{\ne}^N)=25\qquad(N\ge8).}
\tag{14.14}
$$

The least uniform cutoff is exactly

$$
\boxed{N_*=8.}
\tag{14.15}
$$

For every such source and every selected $N\ge8$, the minimum dimension of an initially pure terminal environment is $25$, attained by a full-input dilation. The same dimension suffices and is necessary with any untouched finite reference, including coherent and entangled inputs. For a mixed terminal environment of dimension $d$ and initial state $\sigma_E$, the conclusion is only

$$
25\le d\,\operatorname{rank}\sigma_E\le d^2.
\tag{14.16}
$$

**证明。** The $25$ columns in Lemma 14.2 are independent exact-length-eight words, so $\mathcal S_8=M_5(\mathbb C)$. Reuse the homogeneous propagation step of Theorem 12.2: $U$ is invertible and $U\mathcal S_N\subseteq\mathcal S_{N+1}$, hence full span at one exact length implies full span at its successor. This gives (14.14)'s span assertion for all exact $N\ge8$, without replacing exact length by a cumulative span.

Reuse the exact interior obstruction of Proposition 13.2 with its original certificate (13.2)–(13.4). At $(p,q,r)=(9/50,8/25,8/25)$, (14.1) gives $t=B=1/2$, $A=9/50$, and $(\alpha,\beta,\eta,\zeta)=(3/5,4/5,3/5,4/5)$, equivalently $x=y=1/2$. Its exact length-seven span has dimension $24$. Thus no cutoff at most seven works for every source and every subsequent exact length. Together with the all-parameter upper bound eight, this proves (14.15). This sharpness argument reuses the published witness; it is not a new rank computation or a claim that every source first saturates at eight.

For the channel consequence, the established Sanz–Choi supplier has the precise correspondence

$$
\mathcal E_{\mathcal A}(Z)=B UZU^*+tVZV^*,\qquad
\mathcal A=(\sqrt B\,U,\sqrt t\,V),\qquad D_{\mathrm{Sanz}}=5,
\quad d_{\mathrm{Sanz}}=2.
$$

Sanz, Pérez-García, Wolf and Cirac, *A quantum version of Wielandt's inequality*, arXiv:0909.5347v2, §II following equation (1), identifies $\operatorname{rank}J(\mathcal E_{\mathcal A}^N)$ with the span of products of exactly $N$ Kraus operators. Since $B,t>0$, these spans are precisely $\mathcal S_N$. Its generic Proposition 3 and Theorem 1(2) concern this configuration channel; the source-specific identity (14.5) supplies the sharper horizon here. No primitivity conclusion for a ten-dimensional channel is being inferred.

In the actual source coordinates, every chronological Kraus word satisfies

$$
L_{w_N}\cdots L_{w_1}
=B^{n_0/2}t^{n_1/2}
D^*\bigl((\mathsf G_{w_N}\cdots \mathsf G_{w_1})\otimes I_K\bigr)D,
\qquad n_0+n_1=N.
\tag{14.17}
$$

All scalar weights are nonzero and $Z\mapsto D^*(Z\otimes I_K)D$ is injective. Therefore the full-input Kraus span has exactly the same dimension $25$. The positive Choi sum (12.12) and the pure-environment minimality/attainment argument of Theorem 12.2 apply unchanged at these earlier lengths. These are the existing Kraus/Choi/Stinespring suppliers of Watrous, *The Theory of Quantum Information*, Theorem 2.22 and Corollary 2.27, not new generic results. Tensoring the actual Kraus operators with $I_R$ preserves linear independence and realizes the channel on every untouched reference. The same spectral Kraus expansion as (12.13) gives (14.16), with no mixed-environment optimum or attainment at dimension five inferred. $\square$

**假设 14.4（Exact conclusion and remaining contracts）。** Theorem 14.3 closes the uniform $N=8$ question left in Assumption 13.3 and tightens Proposition 13.2's interval $8\le N_*\le12$ to (14.15). Theorem 12.2's sufficient $N\ge12$ result, its proof, and the exact interior witness remain valid. The source-specific polynomial identity is a repo-derived ordinary proof; no Lean verification or worldwide novelty claim is made. The balanced stratum $p=q$ retains the separate rank-$4$ plateau of Theorem 8.2. The strict-domain determinant has no uniform positive lower bound near balance or the excluded boundary strata, so no uniform numerical conditioning or finite-precision margin follows. The pointwise earliest saturation time of other sources at lengths below eight is not classified.

Every operational premise of Definitions 1.1, 12.1 and Assumptions 1.4, 7.5 remains in force. This is a terminal realization for each selected $N$ of the fixed unread channel power with independently fresh environments, not one common autonomous interaction and initial density realizing all prefix powers. It supplies no measured-successor instrument, intervened process tensor, feedback or recovery/compression of an acquired edge/path archive. It does not establish native $\alpha/\beta$ acquisition, physical parameter preparation or calibration, a readout apparatus, a clock, erasure/reset cost, or a realization of physical space or time. Untouched references remain input correlations, not available memory. The framed logical tensor identity is preserved; terminal rank $25$ is not a full-$M_{10}$ primitivity claim. The broader relational restoration and acquisition problems remain open.

## 追加锚（本行以下为增补区）

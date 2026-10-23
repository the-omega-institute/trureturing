# Recursive relational observation: joint event error bounds

For the original five-mode preparation and fixed scalar-port problem, this
volume gives the common bracket

$$
\boxed{c\leq\varepsilon _1\leq\lambda_{\rm J}},\qquad
c=
\frac{1164818900643714322803106334310684065027405466845668603}
{2222222197396449354330681466502460539165328075000000000},
\tag{0.1}
$$

where $\lambda_{\rm J}$ is the explicitly specified algebraic number below and

$$
\frac{52416918331}{10^{11}}<\lambda_{\rm J}<
\frac{52416918333}{10^{11}},\qquad
0<\lambda_{\rm J}-c<\frac7{10^7}.
\tag{0.2}
$$

The lower covers every original complex scalar port. The upper is the exact
all-history error of one fixed fourteen-flag port and is attained at wait zero.
These endpoints do not match. In particular, neither endpoint evaluates the
original optimum.

This is reference mathematics: ordinary proofs and finite exact arithmetic,
without new Lean kernel certification. The volume uses the generic-v1 clause
conventions and is append-only. Its premise contract and existing text remain
fixed; corrections and extensions belong after the terminal append anchor.

## 1. Original problem and credited ingredients

**Assumption 1.1 (Preparation, actions and observations).** Let
$\mathsf S=(N,2,3,5,25)$ index an orthonormal basis of $\mathbb C^5$, put
$\Pi_s=e_se_s^\dagger$, and allow every complex density input. The preparation
hypothesis is exactly QMB Assumption 1.1:

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad U(t)=e^{-itK},\qquad t\geq0.
\tag{1.1}
$$

The future menu consists of nonnegative waits, the complete five-outcome
rank-one Lüders read $X\mapsto(\Pi_sX\Pi_s)_s$, and Stop. Include all finite
adaptive depths, retaining outcomes, controls and stops. Random controls are
source-independent and the same policy is used for both compared inputs.
Grouping an outcome is classical postprocessing of this complete read.
There is no coarse-block Lüders instrument, independent mode phase, arbitrary
future unitary, probability oracle, readable hidden Kraus record, source copy,
reset or external quantum side information. This preparation is an explicit
independent hypothesis; no native-tree or tensor-cut preparation is inferred.

**Definition 1.2 (Resource and objective).** Before the input and future policy
are chosen, fix CPTP maps

$$
\operatorname{Enc}:M_5\longrightarrow\bigoplus_{f\in F}M_1,\qquad
\operatorname{Dec}_f:M_1\longrightarrow M_5,
\tag{1.2}
$$

with finite fixed $F$ and each decoder CPTP on its whole block. Write
$T(X)=\sum_f\operatorname{Dec}_f(\operatorname{Enc}(X)_f)$. The input is
replaced once, before the common future protocol. Flags are free for this
dimension criterion, consumed by decoding, and not additionally exposed to
future policy. No input retention, bypass or entangled assistance is allowed.
Let $\mathfrak C_1$ be the full complex class of such composites, and define

$$
e(T)=\sup_{\rho\in\mathcal D(\mathbb C^5)}
\sup_{\pi\ {\rm actual,\ finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),\qquad
\varepsilon_1=\inf_{T\in\mathfrak C_1}e(T).
\tag{1.3}
$$

TV is half the $\ell^1$ difference, with the corresponding measure convention
for randomized controls. This is a system-history criterion. It does not
include a joint-reference measurement and is not replaced by trace or diamond
distance. No reality, unitality, covariance, projector or orbit-support
condition is imposed on competitors.

**Convention 1.3 (Supplier roles).** The following existing results supply
definitions and reusable mathematics. The particular certificates in Sections
3–6 are derived here; the supplier results are credited as such.

| Name | Source and exact use |
| --- | --- |
| QMB | [Measurement-relative quantum boundary](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md), Assumption 1.1 and Theorem 2.1: the contract and exact first-read reduction. |
| QPC | [Port covariance and certified frontier](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md): stationary event reduction and the limits on stronger no-loss symmetry claims. |
| QFA | [Finite port attainment](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_FINITE_PORT_ATTAINMENT.md), Lemma 2.2: the three-by-three and five-point quadrature mechanism. |
| QEC | [Classical-port exact certificates](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_CLASSICAL_PORT_EXACT_CERTIFICATES.md): decomposable/TP certificates and exact event-minor methods. |
| QRC | [Real-port boundary coordinates](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_REAL_PORT_BOUNDARY_COORDINATES.md): passive sector coordinates, independent factors and the full three-equation TP marginal. |
| QWS | [Witness slack and independent decoding](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_WITNESS_SLACK_AND_INDEPENDENT_DECODING.md): independent measurement/preparation factors and the adjoint orientation. |
| QJM | [Joint marginal and attaining port](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_JOINT_MARGINAL_AND_ATTAINING_PORT.md), Sections 4 and 6: all-event/TP coupling and the remaining common-kernel obligation; its lower is $129931/250000$. |
| QAP | [Atom positivity and support](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_ATOM_POSITIVITY_AND_SUPPORT.md): full product-atom positivity and equality-face boundaries, without an optimizer-support classification. |
| QSD | [Splitting events and decoder descent](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_SPLITTING_EVENTS_AND_DECODER_DESCENT.md), Theorem 5.2: a legal port of error $e_{\rm mix}>52417598/10^8$. |
| QME | [Marginal-preserving extension repair](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_MARGINAL_PRESERVING_EXTENSION_REPAIR.md): conditional extraction, not an instantiated matching endpoint. |
| QCB | [Cycle compatibility and PPT boundaries](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_CYCLE_COMPATIBILITY_AND_PPT_BOUNDARIES.md): full-space factorization and conditional compatibility, without unrestricted PPT sufficiency. |

The finite-Kraus theorem in
[D5/S3/Quantum/Foundation/FiniteKrausChannel.lean](../../../D5/S3/Quantum/Foundation/FiniteKrausChannel.lean)
gives an existing CP/TP interface for finite rectangular Kraus families with
$\sum K_f^\dagger K_f=I$. The channel and Born-marginal definitions in
[FiniteStateChannel.lean](../../../D5/S3/Quantum/Foundation/FiniteStateChannel.lean)
and
[FiniteKrausInstrumentBornMarginal.lean](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean)
have the corresponding all-complex state and complete-instrument meanings.
These interface correspondences do not certify the present coefficients or
norm calculations.

## 2. Passive coordinates and exact arithmetic

**Definition 2.1 (Spectral sectors).** Put

$$
D=\operatorname{diag}(1,i,i,i,1),\quad
A=-iD^\dagger KD,\quad O(t)=e^{tA},\quad
r=\sqrt {17},\quad \mu_\pm=\frac{5\pm r}{2},\quad
\omega_\pm=\sqrt{\mu_\pm}.
\tag{2.1}
$$

Thus $A$ is real skew-symmetric and $D^\dagger U(t)D=O(t)$. Define
$B=-A^2$ and

$$
R_\pm=\frac{B(B-\mu_\mp I)}{\mu_\pm(\mu_\pm-\mu_\mp)},\qquad
R_0=I-R_+-R_-=dd^T,\qquad d=\frac{e_2-e_5}{\sqrt2}.
\tag{2.2}
$$

Use sector order $(0,+,-)$ and dimensions $(n_0,n_+,n_-)=(1,2,2)$.
In block order $L=(N,25)$, $V=(2,3,5)$, all $L/V$ cross entries vanish, and

$$
R_+|_L=
\begin{pmatrix}(r+1)/(2r)&2/r\\2/r&(r-1)/(2r)\end{pmatrix},
\quad
R_+|_V=
\begin{pmatrix}
(r+3)/(4r)&1/r&(r+3)/(4r)\\
1/r&(r-3)/(2r)&1/r\\
(r+3)/(4r)&1/r&(r+3)/(4r)
\end{pmatrix},
\tag{2.3}
$$

$$
R_0|_L=0,\qquad
R_0|_V=\frac12
\begin{pmatrix}1&0&-1\\0&0&0\\-1&0&1\end{pmatrix},
\qquad R_-=I-R_0-R_+.
\tag{2.4}
$$

These matrices directly give $R_iR_j=\delta_{ij}R_i$,
$\operatorname{tr}R_i=n_i$ and $BR_\pm=\mu_\pm R_\pm$.
For $j=\pm$ put

$$
W_j=\frac{AR_j}{\omega_j},\quad
u_\pm=\frac{R_\pm e_N}{\sqrt{(1\pm1/r)/2}},\quad
w_j(\theta)=\cos\theta\,u_j+\sin\theta\,W_ju_j,
\tag{2.5}
$$

and

$$
G(\alpha,\beta)=R_0+\cos\alpha\,R_++\sin\alpha\,W_+
+\cos\beta\,R_-+\sin\beta\,W_-.
\tag{2.6}
$$

These are passive design and integration coordinates, not new allowed
physical controls. The actual walk is $G(\omega_+t,\omega_-t)$.

**Convention 2.2 (Choi order).** For
$S(X)=D^\dagger T(DXD^\dagger)D$, use the normalized output-first Choi state

$$
\chi=(S\otimes{\rm id})(|\Omega\rangle\langle\Omega|),\qquad
|\Omega\rangle=\frac1{\sqrt5}\sum_s e_s\otimes e_s.
\tag{2.7}
$$

The partial transpose $\Gamma$ acts on the input factor. TP gives
$\operatorname{Tr}_{\rm out}\chi=I/5$, and

$$
\operatorname{tr}(Q S(\rho))
=5\operatorname{tr}\bigl(\chi(Q\otimes\rho^T)\bigr).
\tag{2.8}
$$

Every original scalar port has separable $\chi$, even when its scalar
decoders prepare mixed states. Indeed its encoder consists of positive
functionals $\operatorname{tr}(M_fX)$ with $\sum_fM_f=I$, and its decoder
prepares a density $\sigma_f$, so
$\chi=\frac15\sum_f\sigma_f\otimes M_f^T$.
Consequently $\chi\geq0$ and $\chi^\Gamma\geq0$ for every complex competitor.
No converse from PPT to separability is used.

**Convention 2.3 (Finite arithmetic certificate).** Write elements of
$\mathbb Q(r)$ as pairs $(a,b)=a+br$. Addition is componentwise and

$$
(a,b)(c,d)=(ac+17bd,ad+bc).
\tag{2.9}
$$

The integer inequalities

$$
4123105625617660549^2<17\cdot10^{36}
<4123105625617660550^2
\tag{2.10}
$$

give rational endpoints $r_-,r_+$ with denominator $10^{18}$. Define

$$
\operatorname{lb}(a+br)=
\begin{cases}a+br_-,&b\geq0,\\a+br_+,&b<0,\end{cases}
\qquad
\operatorname{ub}(x)=-\operatorname{lb}(-x).
\tag{2.11}
$$

All interval endpoints below are rational. Interval sums and differences
use endpoint arithmetic; the product of $[a,b]$ and $[c,d]$ has endpoints
$\min(ac,ad,bc,bd)$ and $\max(ac,ad,bc,bd)$. In particular, symmetric
determinants are evaluated by

$$
\det\begin{pmatrix}x&u\\u&y\end{pmatrix}=xy-u^2,\qquad
\det\begin{pmatrix}x&u&v\\u&y&w\\v&w&z\end{pmatrix}
=xyz+2uvw-xw^2-yv^2-zu^2.
\tag{2.12}
$$

Intervals in (2.12) may repeat an uncertain entry independently; this
only enlarges the enclosing interval. These rules and the integer tables
below specify finite certificates, including their rounding directions.

## 3. A normalized universal lower certificate

**Definition 3.1 (Four event tests and all TP multipliers).** In the original
basis order let

| $s$ | $v_s^T$ | $w_s$ |
| --- | --- | --- |
| $N$ | $(99647052,0,0,0,8394339)$ | $46079267/10^8$ |
| $2$ | $(0,99648416,-6062523,5782645,0)$ | $29026410/(2\cdot10^8)$ |
| $3$ | $(0,3825517,-99853547,3825517,0)$ | $24894323/10^8$ |
| $5$ | $(0,5782645,-6062523,99648416,0)$ | $29026410/(2\cdot10^8)$ |

Put $V_s=v_sv_s^T/(v_s^Tv_s)$. Each $V_s$ is a real rank-one density and
$\sum_sw_s=1$. Among the fifteen singleton/pair representatives, use
positive-event multipliers $w_sV_s$ for these four singletons, zero for the
other eleven, and zero for every negative-event multiplier. Their total
trace is exactly one. This assigns multipliers to the complete signed-event
system; it does not discard constraints on a candidate channel.

Let

$$
(\ell_0,\ell_+,\ell_-)
=\frac1{10^{10}}(687411962,1044032526,961353618),\qquad
Y=\sum_i\ell_iR_i.
\tag{3.1}
$$

In the normalized sector basis $R_i/\sqrt{n_i}$, the three TP multipliers
are $\sqrt{n_i}\ell_i$. All three are retained. Define the output-first tensor

$$
\mathcal V=\int_{\mathbb T^2}
\sum_sw_s(G^T\Pi_sG)\otimes(G^TV_sG)\,dG,\qquad
W=I\otimes Y-\mathcal V.
\tag{3.2}
$$

The torus measure has total mass one. There is no factor $5$ in
$\mathcal V$; that factor enters the Choi pairing (2.8).

**Definition 3.2 (An explicit decomposable lift).** Let $F$ swap the two real
five-dimensional factors, let $\eta_i=\operatorname{vec}(R_i)$, and put

$$
I_i=R_i\otimes R_i,\quad F_i=I_iF,\quad E_i=\eta_i\eta_i^T,
$$

$$
F_{ij}=(R_i\otimes R_j+R_j\otimes R_i)F,\qquad
E_{ij}=\eta_i\eta_j^T+\eta_j\eta_i^T\quad(i<j).
\tag{3.3}
$$

Use the exact rational numbers

$$
t_+=-\frac{393052110}{10^{10}},\quad
t_-=-\frac{342190210}{10^{10}},\quad
(U_{0+},U_{0-},U_{+-})
=-\frac1{10^{10}}(243175091,98502039,301019632),
\tag{3.4}
$$

and define

$$
P=W+\sum_{j=\pm}t_j(F_j-E_j)+
\sum_{i<j}U_{ij}(F_{ij}-E_{ij}).
\tag{3.5}
$$

**Lemma 3.3 (Full twenty-five-dimensional block identity).** Define

$$
p_{si}=e_s^TR_ie_s,\quad
q_{si}=\frac{v_s^TR_iv_s}{v_s^Tv_s},\quad
h_{sij}=\frac{(e_s^TR_iv_s)(e_s^TR_jv_s)}{v_s^Tv_s},
$$

$$
a_{ij}=\ell_j-\sum_s\frac{w_sp_{si}q_{sj}}{n_in_j},
\quad
d_j=\frac12\sum_sw_sp_{sj}q_{sj}\ (j=\pm),
\quad
g_{ij}=-\sum_s\frac{w_sh_{sij}}{n_in_j}\ (i<j).
\tag{3.6}
$$

Let $N$ be the symmetric matrix with

$$
N_{00}=a_{00},\quad
N_{jj}=\frac{a_{jj}-d_j/2-t_j}{2}\ (j=\pm),\quad
N_{ij}=g_{ij}-U_{ij}\ (i<j),
\tag{3.7}
$$

and let

$$
D_{ij}=
\begin{pmatrix}a_{ij}&g_{ij}+U_{ij}\\g_{ij}+U_{ij}&a_{ji}\end{pmatrix}.
\tag{3.8}
$$

The blocks of $P$ consist of:
the three-dimensional trace block
$\operatorname{diag}(\sqrt n)\,N\,\operatorname{diag}(\sqrt n)$;
$D_{ij}$ repeated $n_in_j$ times for every $i<j$;
$a_{jj}+t_j$ repeated twice for each $j=\pm$;
and $a_{jj}+d_j/2-t_j$ once for each $j=\pm$.
These blocks exhaust $3+16+4+2=25$ dimensions. Moreover

$$
W=\frac12(P+P^\Gamma).
\tag{3.9}
$$

**Proof.** Each $e_s$ and its corresponding $v_s$ lie in the same one of
$L,V$. In each nonzero two-dimensional sector the intersections with $L$
and $V$ are one-dimensional. Therefore $R_je_s$ and $R_jv_s$ are
collinear, including the possibility of a zero vector. Circle second
moments are $I_2/2$, while fourth moments give
$(I_2\otimes I_2+F+|\operatorname{vec}I_2\rangle
\langle\operatorname{vec}I_2|)/8$. Independent rotation of the two planes
therefore gives the exact identity

$$
W=\sum_{i,j}a_{ij}R_i\otimes R_j
+\sum_{j=\pm}\frac{d_j}{4}(I_j-F_j-E_j)
+\sum_{i<j}g_{ij}(F_{ij}+E_{ij}).
\tag{3.10}
$$

The signed products $h_{sij}$ are essential; they are not replaced by
their absolute values. On the span of $\eta_i/\sqrt{n_i}$, (3.10) and
(3.5) give (3.7). On
$(R_i\mathbb R^5\otimes R_j\mathbb R^5)\oplus
(R_j\mathbb R^5\otimes R_i\mathbb R^5)$, paired by the swap, they give
(3.8). In either two-dimensional sector, the remaining symmetric
traceless subspace has dimension two, $F_j=1$ and $E_j=0$; the
antisymmetric subspace has dimension one, $F_j=-1$ and $E_j=0$.
This gives the scalar blocks and the dimension count. Finally every
integrand in (3.2) is a product of real symmetric matrices, so
$W^\Gamma=W$. Partial transpose exchanges $F_i,E_i$ and
$F_{ij},E_{ij}$. Applying it to (3.5) proves (3.9). $\square$

**Lemma 3.4 (Exact strict positivity evidence).** The matrix $P$ is positive
definite, as a real symmetric and hence complex Hermitian matrix.

**Proof.** Here is a rational interval certificate for every block in Lemma
3.3. Set $S_0=10^{18}$. In the next display, replacing every integer $k$ by
$[k,k+1]/S_0$ encloses the corresponding exact matrix entry:

$$
N:\quad
\begin{pmatrix}
4804846375909143&-5697541416591817&3958250582249144\\
-5697541416591817&6756290549986033&-4693766868413287\\
3958250582249144&-4693766868413287&3260950040838118
\end{pmatrix},
\tag{3.11}
$$

$$
D_{0+}:\quad
\begin{pmatrix}
71778638263756656&-54332559616591817\\
-54332559616591817&41126976818631650
\end{pmatrix},
$$

$$
D_{0-}:\quad
\begin{pmatrix}
88162126048288771&-15742157217750856\\
-15742157217750856&64387240669322921
\end{pmatrix},
\quad
D_{+-}:\quad
\begin{pmatrix}
63653805247019027&-64897693268413287\\
-64897693268413287&66166091718179535
\end{pmatrix}.
\tag{3.12}
$$

These enclosures follow by (2.9)–(2.11) applied to (2.3)–(2.4) and (3.6)–(3.8).
For example the exact first entry is the rational number

$$
N_{00}=\frac{48048463661219644318657}
{9999999979630610000000000};
\tag{3.13}
$$

multiplication by its positive denominator proves the two endpoints in
(3.11). Every other entry is specified by the same explicit rational-pair
operations; no unknown channel or optimization variable occurs.

For additional finite determinant evidence, the following are the integer
lower endpoints obtained by substituting the intervals (3.11)–(3.12) into
(2.12). A degree-$k$ entry is divided by $S_0^k$.

| Block | First leading minor, degree 1 | Second leading minor, degree 2 | Third leading minor, degree 3 |
| --- | ---: | ---: | ---: |
| $N$ | $4804846375909143$ | $959969910492427430335638230$ | $64208938768507794453579842791584226953$ |
| $D_{0+}$ | $71778638263756656$ | $11357455962805439627708400911$ | — |
| $D_{0-}$ | $88162126048288771$ | $5428700513921967044404647968487355$ | — |
| $D_{+-}$ | $63653805247019027$ | $12924624343406758667308868076$ | — |

For instance the degree-two entry for $D_{0+}$ is exactly

$$
71778638263756656\cdot41126976818631650
-54332559616591817^2
=11357455962805439627708400911.
\tag{3.14}
$$

The four scalar blocks, in order
$(a_{++}+t_+,a_{--}+t_-,a_{++}+d_+/2-t_+,
a_{--}+d_-/2-t_-)$, lie respectively in $[k,k+1]/S_0$ with

$$
k=(100349986033,\ 99440838118,\
143708463600000000,\ 130354382800000000).
\tag{3.15}
$$

Thus all three leading minors of $N$, both leading minors of each
$D_{ij}$, and every scalar block are strictly positive. The congruence
in the trace block preserves positive definiteness. Sylvester's
criterion and Lemma 3.3 prove the assertion on all twenty-five dimensions.
In particular no restriction to a boundary product face is involved.
$\square$

**Theorem 3.5 (Original all-complex lower).** Every $T\in\mathfrak C_1$
satisfies $e(T)\geq c$, with the exact rational $c$ in (0.1). In particular

$$
\varepsilon_1\geq c>\frac{65521}{125000}>
\frac{129931}{250000},\qquad
c-\frac{129931}{250000}>\frac{1111}{250000}.
\tag{3.16}
$$

**Proof.** For every actual nonnegative wait $t$ and each of the four tests,
use the legitimate original input

$$
\rho_s(t)=D O(t)^T V_s O(t)D^\dagger,
\tag{3.17}
$$

then wait $t$, perform the complete read and Stop. The ideal probability
of outcome $s$ is
$\beta_s=v_{s,s}^2/(v_s^Tv_s)$. The replaced probability is

$$
f_s(t)=\operatorname{tr}\left[
O(t)^T\Pi_sO(t)\,
S(O(t)^TV_sO(t))\right].
\tag{3.18}
$$

The full-read TV is at least $\beta_s-f_s(t)$, even when this difference
is negative. Since the weights are positive and sum to one,

$$
e(T)\geq\beta-\sum_sw_sf_s(t),\qquad
\beta=\sum_sw_s\beta_s.
\tag{3.19}
$$

The squared frequency ratio
$(\omega_+/\omega_-)^2=(21+5\sqrt {17})/4$ is irrational.
Every nonconstant Fourier monomial of (3.18) therefore has zero forward-time
mean. Its mean is the torus mean in (3.2), so (2.8) gives

$$
e(T)\geq\beta-5\operatorname{tr}(\chi\mathcal V).
\tag{3.20}
$$

This argument does not assume $T$ is stationary or real. By (3.9),
Lemma 3.4 and $\chi,\chi^\Gamma\geq0$,

$$
\operatorname{tr}(\chi W)
=\frac12\left[\operatorname{tr}(\chi P)
+\operatorname{tr}(\chi^\Gamma P)\right]\geq0.
\tag{3.21}
$$

The full TP marginal and the input location of $Y$ give
$5\operatorname{tr}(\chi(I\otimes Y))=\operatorname{tr}Y$.
Consequently

$$
e(T)\geq\beta-\operatorname{tr}Y+5\operatorname{tr}(\chi W)
=c+5\operatorname{tr}(\chi W)\geq c.
\tag{3.22}
$$

For explicit normalization arithmetic,

$$
\beta=
\frac{1104429916712276629523507015039780167081355358825225239}
{1111111098698224677165340733251230269582664037500000000},
\qquad
\operatorname{tr}Y=\frac{18792737}{40000000}.
\tag{3.23}
$$

Their difference is (0.1). Cross multiplication gives (3.16).
This proves the necessary lower for the entire original complex class,
without treating a PPT point as a scalar port. $\square$

**Corollary 3.6 (Finite actual-wait alternatives).** Given a rational
$0<\delta<1$, put

$$
h=\delta/48,\qquad n=\left\lceil153600/\delta^2\right\rceil.
\tag{3.24}
$$

For every original competitor, one of the $4n$ inputs (3.17) and actual waits
$t=jh$, $0\leq j<n$, followed by one complete read and Stop, has TV
strictly greater than $c-\delta$.

**Proof.** The weighted score $f=\sum_sw_sf_s$ on the torus lies in $[0,1]$.
Its Fourier support satisfies $|k|+|l|\leq4$, so it has at most forty
nonconstant coefficients, each of absolute value at most one.
The elementary bounds $2.13<\omega_+<2.14$ and
$0.66<\omega_-<0.67$ imply
$|k\omega_++l\omega_-|>1/10$ on that finite nonzero support.
Indeed the closest opposite-sign combination is bounded below by
$\omega_+-3\omega_->2.13-3(0.67)=0.12$; the other combinations with
$|k|+|l|\leq4$ have the larger elementary lower bounds.
For $H=nh$, the integral mean differs from the torus mean by at most
$800/H\leq\delta/4$. Differentiating the two rotated projectors in
(3.18), using trace-norm contraction of a CPTP map on Hermitian inputs,
gives $|f'_s(t)|\leq4\|A\|<12$. The left-sum mean over $jh$ differs from
the integral mean by at most $12h=\delta/4$. Thus the weighted mean
of the actual signed differences is at least $c-\delta/2$ by (3.20)–(3.22).
One of them is at least that large, hence greater than $c-\delta$.
Every listed wait is finite and nonnegative; (3.24) is an explicit
termination bound, without an additional physical control. $\square$

## 4. One fixed fourteen-flag port

**Definition 4.1 (Independent factors and common weights).** Use the following
exact parameters, independently of the lower tuple:

$$
s=\frac{8104433}{20000000},\quad
r_A=\frac{101784321}{10^8},\quad
r_B=\frac{37819381}{50000000},
$$

$$
W_A=\frac2{1-s}=\frac{40000000}{11895567},\quad
W_B=5-W_A=\frac{19477835}{11895567},\quad
t=\frac1{W_B}=\frac{11895567}{19477835},
\tag{4.1}
$$

$$
d_A=r_A^2s+1-s,\quad d_B=r_B^2t+1-t,\quad
\alpha=\frac{r_A^2s}{d_A}
=\frac{27987438301460591968251}{67639328301460591968251},
$$

$$
\beta_U=\frac{r_B^2t}{d_B}
=\frac{17014295848122919627287}{35969965848122919627287},
$$

$$
g=\frac{W_Br_Bt(1-t)}{d_B}
=\frac{14337834116805400000000}{35969965848122919627287},
\quad
h_U=\frac{W_Ar_As(1-s)}{d_A}
=\frac{54993613999666200000000}{67639328301460591968251}.
\tag{4.2}
$$

Let $F$ be the disjoint union of nine flags $(A,k,l)$,
$0\leq k,l<3$, and five flags $(B,k)$, $0\leq k<5$. With
$\theta_k=2\pi k/3$ and $\phi_k=2\pi k/5$, set

$$
b_{Akl}=\sqrt{s}\,w_+(\theta_k)+\sqrt{1-s}\,w_-(\theta_l),
$$

$$
a_{Akl}=
\frac{r_A\sqrt{s}\,w_+(\theta_k)+\sqrt{1-s}\,w_-(\theta_l)}
{\sqrt{d_A}},\qquad c_{Akl}=W_A/9,
\tag{4.3}
$$

$$
b_{Bk}=\sqrt{t}\,d+\sqrt{1-t}\,w_+(\phi_k),
$$

$$
a_{Bk}=
\frac{r_B\sqrt{t}\,d+\sqrt{1-t}\,w_+(\phi_k)}
{\sqrt{d_B}},\qquad c_{Bk}=W_B/5.
\tag{4.4}
$$

Define the encoder rows, whole-block decoders and composite by

$$
B_f=\sqrt{c_f}\,b_f^TD^\dagger,\quad
\operatorname{Enc}(X)=(B_fXB_f^\dagger)_f,\quad
\operatorname{Dec}_f(z)=z\,Da_fa_f^TD^\dagger,
$$

$$
C_f=\sqrt{c_f}\,Da_fb_f^TD^\dagger,\qquad
T_{\rm J}(X)=\sum_f C_fXC_f^\dagger.
\tag{4.5}
$$

The constants in this definition specify one common channel for all
events and every input; they are not eventwise choices.

**Lemma 4.2 (Whole-block CPTP legality and exact TP).** The maps (4.5) are a
legal fixed scalar port. The full output-first Choi marginal is $I/5$.

**Proof.** Every $a_f,b_f$ is unit and every $c_f$ is positive. The exact
circle second moments give

$$
\sum_fc_fb_fb_f^T
=W_BtR_0+\frac{W_As+W_B(1-t)}2R_+
+\frac{W_A(1-s)}2R_-.
\tag{4.6}
$$

The three independent identities are

$$
W_Bt=1,\qquad W_A(1-s)=2,\qquad
W_As+W_B(1-t)=2.
\tag{4.7}
$$

The right side of (4.6) is $I$. Hence $\sum_fB_f^\dagger B_f=I$:
the flagged encoder is CP and TP. Each decoder has the unit column
$Da_f$ as Kraus matrix and is CP and TP on all of $M_1$.
Each composite $C_f$ has rank one. In passive coordinates,

$$
\chi_{\rm J}=\frac15\sum_fc_f
(a_fa_f^T)\otimes(b_fb_f^T),\qquad
\operatorname{Tr}_{\rm out}\chi_{\rm J}=I/5.
\tag{4.8}
$$

This constructs an actual finite port, with its flags consumed during
decoding, rather than a point in a separability relaxation. $\square$

**Lemma 4.3 (Finite quadrature and the actual walk).** The finite channel
(4.5) equals the independent two-plane torus average of its two seed
product tensors and commutes with $O(t)$ on all complex matrices.

**Proof.** In branch $A$, the coefficient tensor
$a_fa_f^T\otimes b_fb_f^T$ has plane bidegrees
$(4,0),(3,1),(2,2),(1,3),(0,4)$.
On a circle, a homogeneous even degree two or four has only even
Fourier modes of absolute value at most four. Three equally spaced
points integrate those modes exactly. In bidegrees $(3,1)$ and $(1,3)$,
the degree-one factor has zero three-point average; it kills the
degree-three alias as well. This proves exact three-by-three quadrature.
In branch $B$, all Fourier frequencies have absolute value at most four,
so five equally spaced points integrate them exactly. The independent
radial coefficients in (4.3)–(4.4) do not change this argument.
The equality is of full coefficient tensors, hence of superoperators
on complex matrices. The torus average is covariant under both
rotations, in particular under the actual $O(t)$. These quadratures
specify fixed apparatus coefficients; they add no future control or
flag visible to the policy. $\square$

**Proposition 4.4 (The actual adjoint and all population equations).** Let

$$
\Lambda=
\begin{pmatrix}
\beta_U&W_B\beta_U(1-t)&0\\
1-\beta_U&W_A\alpha s+W_B(1-\beta_U)(1-t)&2\alpha\\
0&W_A(1-\alpha)s&2(1-\alpha)
\end{pmatrix}.
\tag{4.9}
$$

Its column sums are exactly $(1,2,2)$. For real symmetric $E$ and
$t_i(E)=\operatorname{tr}(R_iE)$, the passive adjoint
$\mathcal A=S_{\rm J}^\dagger$ is

$$
\begin{aligned}
\mathcal A(E)={}&
\Lambda_{00}t_0(E)R_0+
\sum_{j=\pm}\frac{\Lambda_{jj}}8
\bigl(t_j(E)R_j+2R_jER_j\bigr)\\
&+\sum_{i\ne j}\frac{\Lambda_{ij}t_i(E)}{n_in_j}R_j
+g(R_0ER_++R_+ER_0)\\
&+\frac{h_U}{2}(R_+ER_-+R_-ER_+).
\end{aligned}
\tag{4.10}
$$

For a general complex matrix apply the same formula to $(E+E^T)/2$;
this is a complex-linear extension. In particular $\mathcal A(I)=I$.
All three full TP equations are retained:
in QRC coordinates $M_{ij}=\Lambda_{ij}/\sqrt{n_in_j}$ and
$M^T(\sqrt{n_i})_i=(\sqrt{n_i})_i$.

**Proof.** For each flag the effect map is
$E\mapsto c_fb_fb_f^T(a_f^TEa_f)$, with the measurement factor on the
outside. The sector population tensor is

$$
\Lambda=W_A(0,\alpha,1-\alpha)^T(0,s,1-s)
+W_B(\beta_U,1-\beta_U,0)^T(t,1-t,0).
\tag{4.11}
$$

This gives (4.9), its three column sums and the $i\ne j$ terms of
(4.10). Circle fourth moments give the diagonal-plane coefficient
$\Lambda_{jj}/8$. Circle second moments in the $0,+$ cross term give
$g$, and the two independent plane second moments in the $+,-$ term
give $h_U/2$. The zero-plane term is as displayed. This also proves
the complex-linear extension, since $a_f^TEa_f$ annihilates the
transpose-antisymmetric part. Substitution of $I$ gives the identity.
This is the adjoint, not the state map; no self-adjointness or
unitality of $S_{\rm J}$ is asserted. $\square$

## 5. Complete event certificate and an explicit cubic

**Definition 5.1 (Every event of the same channel).** Let

$$
\mathcal J_{15}=\{\{s\}:s\in\mathsf S\}
\ \cup\ \{\{s,t\}:s,t\in\mathsf S,\ s<t\},
\qquad
H_J=\Pi_J-\mathcal A(\Pi_J).
\tag{5.1}
$$

All fifteen matrices are block diagonal in $L|V$ and have entries in
$\mathbb Q(r)$ by (2.3)–(2.4) and (4.10).
Put $C_2=H_{\{2\}}|_V$. The following exact coefficient table makes the
cubic fully explicit. With

$$
Q=3970630424917410837589475743639983799408656540384,
\tag{5.2}
$$

write $Q(C_2)_{ij}=A_{ij}+B_{ij}r$ in the ordered coordinates
$V=(2,3,5)$; fill the other entries symmetrically.

| $ij$ | $A_{ij}$ | $B_{ij}$ |
| --- | ---: | ---: |
| $11$ | $2462447872393907165594742826748064690060193918633$ | $-97149978487090015194554054260372481474396926665$ |
| $12$ | $77526457255990821914612636164388646712073853330$ | $-57763577519389231503693111648403110923979492442$ |
| $13$ | $88136602052124428246561281896349695359065648441$ | $18833083584870050850167099228156384114403073335$ |
| $22$ | $-449874008591688900130441339844682516567218533300$ | $25148131890936974098744618018584369823144623996$ |
| $23$ | $77526457255990821914612636164388646712073853330$ | $35337363500625109920237237544142043194420507558$ |
| $33$ | $-716824553853381769891324948755285299342062621751$ | $42501433042931496941341469528445249703203073335$ |

For $x=(C_2)_{11}$, $y=(C_2)_{22}$, $z=(C_2)_{33}$,
$u=(C_2)_{12}$, $v=(C_2)_{13}$, $w=(C_2)_{23}$, define the monic
$\mathbb Q(\sqrt {17})$ cubic

$$
p(X)=X^3-(x+y+z)X^2+
(xy+xz+yz-u^2-v^2-w^2)X
-(xyz+2uvw-xw^2-yv^2-zu^2).
\tag{5.3}
$$

Thus $p(X)=\det(XI_3-C_2)$ with exact displayed coefficients, not an
unevaluated minimization prescription.

**Lemma 5.2 (Finite all-event evidence).** Put

$$
z_0=\frac{524169183}{10^9},\quad
l=\frac{52416918331}{10^{11}},\quad
u_*=\frac{52416918333}{10^{11}}.
\tag{5.4}
$$

For every $J\in\mathcal J_{15}\setminus\{\{2\},\{5\}\}$ and both signs,
$z_0I\pm H_J$ is positive definite. Also
$I/2+H_{\{2\}}$ is positive definite, and

$$
p(l)<-\frac1{10^{12}},\qquad p(u_*)>\frac1{10^{12}}.
\tag{5.5}
$$

**Proof.** The following finite rational evidence specifies all signed-event
tests, including the nearly tight $N$ and $3$ residuals. Set $S_0=10^{18}$.
In the next two tables an integer $k$ means the interval
$[k,k+2]/S_0$ for the corresponding entry of $E_s=\mathcal A(\Pi_s)$.
All $L/V$ cross entries are exactly zero.

| $s$ | $L_{11}$ | $L_{12}$ | $L_{22}$ |
| --- | ---: | ---: | ---: |
| $N$ | $480260457762033490$ | $-52583099673878827$ | $100031013225950149$ |
| $2$ | $123075258232797040$ | $18535659605342947$ | $113807428430125566$ |
| $3$ | $175301858201513681$ | $16028281832695697$ | $167287717285165833$ |
| $5$ | $123075258232797040$ | $18535659605342947$ | $113807428430125566$ |
| $25$ | $98287167570858746$ | $-516501369502767$ | $505066412628632883$ |

| $s$ | $V_{11}$ | $V_{12}$ | $V_{13}$ | $V_{22}$ | $V_{23}$ | $V_{33}$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| $N$ | $157225073694156928$ | $-9346378490310084$ | $-6474659653390691$ | $178789549511696488$ | $-9346378490310084$ | $157225073694156928$ |
| $2$ | $480715143714731665$ | $40456768064317151$ | $-41753418774067379$ | $87186559178595029$ | $-56219319254462598$ | $136398152993179565$ |
| $3$ | $92248382017615896$ | $25775048467436646$ | $56361538202527506$ | $477805769190856216$ | $25775048467436646$ | $92248382017615896$ |
| $5$ | $136398152993179565$ | $-56219319254462598$ | $-41753418774067379$ | $87186559178595029$ | $40456768064317151$ | $480715143714731665$ |
| $25$ | $133413247580315944$ | $-666118786981118$ | $33619958998997940$ | $169031562940257236$ | $-666118786981118$ | $133413247580315944$ |

To obtain these intervals, substitute the exact (4.1)–(4.2), (4.9)
into (4.10), use (2.3)–(2.4), and apply (2.9)–(2.11).
In particular the same calculation yields the exact $C_2$ table (5.2).
For a subset $J$, form the interval matrix
$\Pi_J-\sum_{s\in J}E_s$ by endpoint arithmetic. For each of its signed
matrices $z_0I\pm H_J$, apply (2.12) to the leading minors in the fixed
order

$$
\Delta_1(L),\ \Delta_2(L),\ \Delta_1(V),\
\Delta_2(V),\ \Delta_3(V).
\tag{5.6}
$$

The next table gives integer lower bounds after scaling these rational
interval lower endpoints by $10^{12}$ and rounding down. It therefore
directly specifies a lower bound $m/10^{12}$ for every listed minor.
Here $J$ lists actual mode labels: for example $\{2,5\}$ is a pair,
whereas $\{25\}$ is a singleton.

| $J$ | sign | $\Delta_1(L)$ | $\Delta_2(L)$ | $\Delta_1(V)$ | $\Delta_2(V)$ | $\Delta_3(V)$ |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| $\{N\}$ | $+$ | $1043908725237$ | $439996553762$ | $366944109305$ | $126647667191$ | $46427213557$ |
| $\{N\}$ | $-$ | $4429640762$ | $261$ | $681394256694$ | $478904688235$ | $326232780943$ |
| $\{3\}$ | $+$ | $348867324798$ | $124247376395$ | $431920800982$ | $451281770687$ | $191232245928$ |
| $\{3\}$ | $-$ | $699471041201$ | $483397172169$ | $616417565017$ | $553042097$ | $177$ |
| $\{25\}$ | $+$ | $425882015429$ | $434017275001$ | $390755935419$ | $138771689214$ | $53824245374$ |
| $\{25\}$ | $-$ | $622456350570$ | $18197615388$ | $657582430580$ | $455836187681$ | $298966080356$ |
| $\{N,2\}$ | $+$ | $920833467005$ | $284603704294$ | $886228965591$ | $227850324828$ | $47922903796$ |
| $\{N,2\}$ | $-$ | $127504898994$ | $92940359463$ | $162109400408$ | $127122123132$ | $101621533962$ |
| $\{N,3\}$ | $+$ | $868606867036$ | $221765812125$ | $274695727288$ | $238048932432$ | $63130823221$ |
| $\{N,3\}$ | $-$ | $179731498963$ | $140919054399$ | $773642638711$ | $139577224885$ | $107351145813$ |
| $\{N,5\}$ | $+$ | $920833467005$ | $284603704294$ | $230545956312$ | $55226508509$ | $47922903796$ |
| $\{N,5\}$ | $-$ | $127504898994$ | $92940359463$ | $817792409687$ | $641875961373$ | $101621533962$ |
| $\{N,25\}$ | $+$ | $945621557667$ | $866274498968$ | $233530861725$ | $41082466776$ | $9435224615$ |
| $\{N,25\}$ | $-$ | $102716808332$ | $10458285854$ | $814807504274$ | $710403986287$ | $578123716081$ |
| $\{2,3\}$ | $+$ | $225792066565$ | $53689523159$ | $951205657267$ | $907987796923$ | $267303555089$ |
| $\{2,3\}$ | $-$ | $822546299434$ | $661172527603$ | $97132708732$ | $4273845592$ | $3049452501$ |
| $\{2,5\}$ | $+$ | $278018666534$ | $81073355600$ | $907055886292$ | $317036121416$ | $284946345625$ |
| $\{2,5\}$ | $-$ | $770319699465$ | $577739772940$ | $141282479707$ | $98443330496$ | $8960509952$ |
| $\{2,25\}$ | $+$ | $302806757196$ | $273804856734$ | $910040791704$ | $242263099812$ | $58622109423$ |
| $\{2,25\}$ | $-$ | $745531608803$ | $106318405791$ | $138297574295$ | $106342375538$ | $83971452148$ |
| $\{3,5\}$ | $+$ | $225792066565$ | $53689523159$ | $295522647989$ | $282531630346$ | $267303555089$ |
| $\{3,5\}$ | $-$ | $822546299434$ | $661172527603$ | $752815718010$ | $66195333576$ | $3049452501$ |
| $\{3,25\}$ | $+$ | $250580157227$ | $213207334598$ | $298507553402$ | $261259725974$ | $70582879515$ |
| $\{3,25\}$ | $-$ | $797758208772$ | $156537470758$ | $749830812597$ | $127595495850$ | $93931173120$ |
| $\{5,25\}$ | $+$ | $302806757196$ | $273804856734$ | $254357782426$ | $64919484583$ | $58622109423$ |
| $\{5,25\}$ | $-$ | $745531608803$ | $106318405791$ | $793980583573$ | $616376414870$ | $83971452148$ |

Every entry is positive. More specifically the five columns exceed,
respectively,

$$
\frac1{250},\quad\frac1{4000000000},\quad
\frac9{100},\quad\frac1{2000},\quad\frac1{6000000000}.
\tag{5.7}
$$

For $I/2+H_{\{2\}}$, the same five interval-minor lower bounds,
scaled and rounded down in the same way, are

$$
(376924741767,\ 145221964634,\ 1019284856285,\
419137738618,\ 148268082340)/10^{12}.
\tag{5.8}
$$

They exceed $(3/8,7/50,1,2/5,7/50)$.
For the two cubic evaluations, use the $V$ intervals of
$I X-H_{\{2\}}$ and the degree-three formula (2.12).
The resulting rational enclosures are

$$
\frac{-3540855440925}{10^{24}}
<p(l)<
\frac{-3540854372389}{10^{24}},
$$

$$
\frac{4529412813536}{10^{24}}
<p(u_*)<
\frac{4529413882072}{10^{24}}.
\tag{5.9}
$$

The endpoint directions here allow a harmless outward rounding of the
interval evaluation. Equations (5.9) imply (5.5). Equations (5.6)–(5.8)
and Sylvester's criterion prove the matrix assertions. All entries of
this certificate are obtained from the displayed rational parameters,
the single square-root enclosure, and the two determinant polynomials;
there is no time mesh or numerical eigenvalue assumption. $\square$

**Theorem 5.3 (Exact all-history upper and actual attainment).** The cubic
(5.3) has exactly one positive root $\lambda_{\rm J}$. The port (4.5)
has

$$
e(T_{\rm J})=\lambda_{\rm J},\qquad
l<\lambda_{\rm J}<u_*.
\tag{5.10}
$$

Among the fifteen representatives in (5.1), exactly $\{2\}$ and
$\{5\}$ attain this error. A pure input, wait zero, one complete read
and Stop attain the full-history TV.

**Proof.** The positive map $\mathcal A$ gives
$H_{\{2\}}=\Pi_2-\mathcal A(\Pi_2)$, whose quadratic form is nonpositive
on $e_2^\perp$. It has at most one positive eigenvalue, including
multiplicity. Its $L$ block is nonpositive. By the sign change in
(5.5), its $V$ block $C_2$ has a positive eigenvalue in $(l,u_*)$.
It is therefore the unique positive eigenvalue and the unique positive
root of $p$. By (5.8), every negative eigenvalue of $H_{\{2\}}$ is
greater than $-1/2$. Since $l>1/2$, its operator norm is
$\lambda_{\rm J}$. Swapping modes $2$ and $5$ fixes the projectors
(2.3)–(2.4) under conjugation and hence conjugates
$H_{\{2\}}$ to $H_{\{5\}}$ by (4.10). Their norms are equal.
Every other representative has norm strictly below $z_0<l$ by Lemma
5.2.

For completeness, QMB's first-read identity in passive coordinates is

$$
e(T)=\sup_{t\geq0}\max_{J\subseteq\mathsf S}
\|O(t)^T\Pi_JO(t)-S^\dagger(O(t)^T\Pi_JO(t))\|_{\rm op}.
\tag{5.11}
$$

The reason it covers every finite adaptive history is that the first
complete rank-one read resets the conditional quantum state to its
outcome basis state. All subsequent common controls and reads are
classical postprocessing of that first outcome, with the corresponding
identical conditional laws. Stop without any read has no state-dependent
history. Source-independent randomized controls give mixtures of these
comparisons. Conversely a single actual read realizes the event tests.

For the stationary channel of Lemma 4.3 the matrix inside (5.11) is an
orthogonal conjugate of $H_J$. Since $\mathcal A(I)=I$, complementary
events have opposite residuals. Empty/full events vanish, so all
thirty-two subsets reduce to the fifteen singletons/pairs. The preceding
norm calculation proves the upper in (5.10) for all complex density
inputs and all actual finite histories, without using a reference
measurement or a different norm.

To give the attaining input explicitly, partition the actual exact matrix
$C_2$ in $V=(2,3,5)$ as

$$
C_2=\begin{pmatrix}a&q^T\\q&B_2\end{pmatrix},\qquad
v_0=\begin{pmatrix}1\\(\lambda_{\rm J}I_2-B_2)^{-1}q\end{pmatrix}.
\tag{5.12}
$$

Here $B_2\leq0$, being the compression to $e_2^\perp$.
Thus the inverse exists. The Schur-complement identity
$p(\lambda_{\rm J})=0$ gives $C_2v_0=\lambda_{\rm J}v_0$.
Normalize $v_0$, extend by zero on $L$ to a real unit vector $v$, and
take the original input $\rho_{\rm J}=Dvv^TD^\dagger$.
At the actual wait zero, the complete-read event $\{2\}$ has probability
difference $v^TH_{\{2\}}v=\lambda_{\rm J}$. The full-read TV is at least
this number and at most the proved bound. It equals
$\lambda_{\rm J}$ and attains (5.10). $\square$

## 6. The common bracket and the nonmatching boundary

**Theorem 6.1 (Strict original endpoint progress).** For the unchanged
problem (1.3),

$$
c\leq\varepsilon_1\leq\lambda_{\rm J},\qquad
0<\lambda_{\rm J}-c<\frac7{10^7},\qquad
e_{\rm mix}-\lambda_{\rm J}>
\frac{679667}{10^{11}}.
\tag{6.1}
$$

**Proof.** Theorems 3.5 and 5.3 concern precisely the same source, menu,
input quantifier and resource class, so they combine. Direct rational
comparison gives $c<l$ and

$$
u_*-c=
\frac{5974973522349992451074993109708889744120314409547}
{8888888789585797417322725866009842156661312300000000000}
<\frac7{10^7}.
\tag{6.2}
$$

The credited QSD Theorem 5.2 gives $e_{\rm mix}>52417598/10^8$.
Subtracting $u_*$ from this rational lower enclosure gives exactly
$679667/10^{11}$. Equations (5.10) and (3.16) prove the remaining
strict comparisons. $\square$

**Proposition 6.2 (Strict product slack prevents matching this tuple).**
The normalized lower tuple of Definition 3.1 has strictly positive
slack on every nonzero complex product. It has no nonzero real product
kernel and therefore cannot itself be complementary to positive scalar
atoms of a legal attaining port at $c$.

**Proof.** For complex nonzero $a,b$, partial transposition gives

$$
(a\otimes b)^\dagger W(a\otimes b)
=\frac12\left[
(a\otimes b)^\dagger P(a\otimes b)
+(a\otimes\overline b)^\dagger P(a\otimes\overline b)\right]>0.
\tag{6.3}
$$

Lemma 3.4 proves both strict inequalities; it covers all complex
factors and every zero-population or interior configuration.
For real factors (6.3) is the global real-product quadratic form of
the event/TP tuple. Thus its preparation-dependent matrix is positive
definite for every nonzero preparation vector, including all radial
and tangent sectors, without omitting the signed interior cubic.
A separable TP Choi state is a positive sum of nonzero product states.
Its pairing with $W$ is strictly positive. Equality in (3.22) for this
tuple would require that pairing to vanish, which is impossible.
This is an obstruction to equality for this particular strictly
positive rounded certificate. It does not exclude boundary or
nondecomposable certificates that match a legal port. $\square$

**Open problem 6.3 (The same joint obligation).** The original exact
$\varepsilon_1$ remains open inside (6.1). A matching solution requires
one normalized set of all signed-event multipliers and all three TP
multipliers, global product positivity including degenerate and interior
populations, and one legal positive-weight port on its actual kernel
face satisfying the same TP and complementary event equations.
The port in Section 4 is not asserted to lie on the kernel of another
valid tuple. The lower and upper have not been made complementary.

The upper changes the encoder population and both independent decoder
ratios together. Its active representatives are the splitting singletons
$\{2\},\{5\}$, rather than the keep-only active set of the credited QSD
ports. This is a sufficient design within a known construction family;
it supplies no no-loss restriction of original competitors or proof of
an optimizer in that family. Positive boundary atoms, separate TP
feasibility, pair saturation, cycle compatibility and a feasible PPT
point do not supply the missing common equality.

## 7. Correspondence, literature and remaining resources

**Convention 7.1 (Evidence and literature scope).** The particular normalized
certificate, coefficient tables, port parameters, bracket and strict-slack
obstruction are repo-derived ordinary mathematics. The first-read theorem,
finite quadrature mechanism, independent-factor constructions and the
distinction between full TP and eventwise contact are credited in
Convention 1.3. There is no worldwide-originality claim.

| Primary source | Supported ingredient and boundary |
| --- | --- |
| [Horodecki–Shor–Ruskai, quant-ph/0302031v2, Theorem 4](https://arxiv.org/html/quant-ph/0302031v2) | Literature-attested measure/prepare, separable-Choi and rank-one Kraus equivalences; the CPTP version separately imposes a POVM or Kraus completeness. Equations (4.6)–(4.8) prove that condition for the actual port. It does not evaluate the present menu optimum. |
| [Doherty–Parrilo–Spedalieri, quant-ph/0308032v3, Section VI](https://arxiv.org/html/quant-ph/0308032v3) | Literature-attested decomposable witnesses and PSD/PPT pairing. Here (3.9) and (3.21) give the full explicit elementary argument. No hierarchy or PPT sufficiency is inferred. |
| [Bluhm–Rauber–Wolf, 1708.04898v4, Definition 4.1](https://arxiv.org/html/1708.04898v4) | Fixed CPTP encoder/decoder compression with all-state quantifiers provides related context. Its observation contract does not replace (1.3). |
| [Gulati–Nechita–Park, 2509.15201v4](https://arxiv.org/html/2509.15201v4) | Pairwise copositivity, symmetry and extension methods concern their specified classes. No matching event/TP certificate or no-loss support theorem for (1.3) is imported. |

The stated literature does not supply the particular common equality
missing in Open problem 6.3. That limited correspondence statement is
not an impossibility, noncomputability or originality assertion.

**Convention 7.2 (Scope of the conclusions).** The lower uses only original
complex scalar-port CPTP legality, actual single-read probabilities and
the full input TP marginal; it imposes no real-Kraus or stationarity
restriction on competitors. The upper is one legal finite complex
channel whose covariance is proved directly. Both retain all complex
inputs and the entire finite adaptive menu. Mathematical torus variables
are integration or fixed design coefficients. The lower's finite
alternatives are actual nonnegative waits; the upper attains its error
at wait zero. Classical flags are hidden after decoding. No input
retention, copy, reset, reference-assisted test or extra future control
is used.

The exact $q=2,3,4$ endpoints, native preparation, native cofinality,
memory-rate and complete all-view recovery questions remain open.
No source/action/observation/resource map from a native tree, Schur
fiber, tensor-cut or other source is established here. Fourteen finite
scalar flags and exact algebraic design coefficients are mathematical
resources of the sufficient construction. Physical acquisition,
coefficient synthesis, finite-precision implementation, clocks,
transport and storage duration have no bound supplied by these proofs.
The finite arithmetic certificates establish the displayed operator
inequalities; the ordinary first-read, covariance and Choi arguments
provide the all-input/all-history quantifiers. No new Lean certification,
sharpness or broader-programme completion is claimed.

## 追加锚（本行以下为增补区）

# AURIC FIB ATOM quantum principles and coherent reconstruction — continuation

## 37. The fixed polar support and a finite randomized read

**Definition 37.1 (The source and the two complex spaces).** Continue the
numbering of [Quantum Principles and Coherent Reconstruction][QR], §§20,
34–36. Retain exactly its ordered physical modes $(N,2,3,5,25)$, physical
Hilbert space $\mathbb C^5$, all physical density inputs, and operations:
nonnegative passive waits, complete rank-one mode reads, Stop, finite
record feedback and input-independent classical randomization. There is
no additional preparation, reference, auxiliary system, inverse control
or postselection. In the fixed mathematical frame
$D=\operatorname{diag}(1,i,i,i,1)$, set

$$
A=\begin{pmatrix}
0&1&1&1&0\\-1&0&0&0&-1\\-1&0&0&0&0\\
-1&0&0&0&-1\\0&1&0&1&0
\end{pmatrix},\quad O(t)=e^{tA},\quad U(t)=DO(t)D^\dagger,
\quad P_j=e_je_j^T.
\tag{37.1}
$$

Thus $U(t)$ is the original physical wait $V(t)$ of [QR, §35][QR]. Put

$$
z=(e_2-e_5)/\sqrt2,\quad R_0=zz^T,\quad P=I-R_0,\quad
E=z^\perp\subset\mathbb R^5,\quad E_{\mathbb C}=E+iE.
\tag{37.2}
$$

The polar complex structure on the real four-space $E$ is exactly
$J=J_p=A|_E(-A^2|_E)^{-1/2}$ from [QR, (36.2)][QR]. The internal complex
two-space $E_J$ identifies $u$ and $e^{\theta J}u$ as one unit ray. It is
different from the physical complex four-space $E_{\mathbb C}$ and from
physical multiplication by $i$ on $\mathbb C^5$. Physical input $Du$ means
the density $Duu^TD^\dagger$, not a preparation supplied by the menu.

**Definition 37.2 (Spectral coordinates with fixed orientation).** For
calculations only, reorder the real coordinates as
$X=(N,25)$ and $Y=(2,3,5)$. Then

$$
A=\begin{pmatrix}0&B\\-B^T&0\end{pmatrix},\quad
B=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},\quad
C=BB^T=\begin{pmatrix}3&2\\2&2\end{pmatrix},
\tag{37.3}
$$

with frequencies

$$
a=\sqrt{(5+\sqrt{17})/2},\quad
b=\sqrt{(5-\sqrt{17})/2},\quad \delta=a-b>0.
\tag{37.4}
$$

These are the existing frequencies of [Second Order, Theorem 63.2][SO],
[Static Compatibility, (44.1)][SC] and [Measurement Relative Boundary,
Theorem 4.1][MR]. Choose orthonormal eigenvectors $v_+,v_-$ of $C$ for
$a^2,b^2$, each with positive first component. Define

$$
l_+=(v_+,0),\quad l_-=(v_-,0),\quad
r_+=(0,B^Tv_+/a),\quad r_-=(0,B^Tv_-/b).
\tag{37.5}
$$

For $u\in E$ write uniquely

$$
u=x_+l_+-y_+r_++x_-l_--y_-r_-,\qquad
\zeta(u)=(x_++iy_+,x_-+iy_-)^T.
\tag{37.6}
$$

Then $\zeta(Ju)=i\zeta(u)$ and
$\zeta(O(t)u)=W(t)\zeta(u)$, where
$W(t)=\operatorname{diag}(e^{iat},e^{ibt})$.
For each original mode let

$$
\xi_j=\zeta(Pe_j),\qquad
h_\pm=(v_\pm)_N,\qquad f=(e_2+e_5)/\sqrt2,
\qquad q_\pm=\langle r_\pm,f\rangle.
\tag{37.7}
$$

All these are coordinates, without adding any control or phase reference.

**Definition 37.3 (Eight positive branches).** Let
$\epsilon=(\epsilon_1,\epsilon_2,\epsilon_3)\in\{0,1\}^3$ be uniformly
distributed independently of the input, and put

$$
\tau_1=\frac\pi{2a},\quad \tau_2=\frac\pi{2b},\quad
\tau_3=\frac\pi{a+b},\quad
T_\epsilon=\epsilon_1\tau_1+\epsilon_2\tau_2+\epsilon_3\tau_3.
\tag{37.8}
$$

For a fixed setting $s\ge0$, the protocol selects $\epsilon$, waits
$t_\epsilon=s+T_\epsilon$, performs the original complete five-label
read and then Stops. Every branch has weight $1/8$ and nonnegative
finite wait. Its complete resolved record is
$(\epsilon,t_\epsilon,j,\mathrm{Stop})$. A label marginal sums over
$\epsilon$ and the selected wait while retaining all five $j$; a binary
event further selects a set of labels. These are probability marginals
of the same recorded protocol, without changing its retained record or
replacing its rank-one read by a coherent coarse-block instrument.
Set

$$
\gamma(\omega)=\frac18\sum_\epsilon e^{i\omega T_\epsilon}
=\prod_{k=1}^3\frac{1+e^{i\omega\tau_k}}2,\qquad
g=\gamma(\delta).
\tag{37.9}
$$

The random-time/Fourier mechanism is mature: Boixo–Knill–Somma,
[§II.2, (4), (6), and §II.3, Example 1][BKS], give characteristic-function
multipliers, convolution and the two-point cancellation for a known gap.
The present filter selects the three sums $2a,2b,a+b$ and retains the
difference $a-b$ for this source; it is not a new general dephasing theorem.

## 38. Exact polar-ray effects with a noncommuting pair

**Theorem 38.1 (All label marginals, and a nonspectral event).** For every
$s\ge0$, Definition 37.3 is a permitted protocol on every physical density
$\rho\in M_5(\mathbb C)$. Its physical label effects are

$$
F_j(s)=\frac18\sum_\epsilon
U(t_\epsilon)^\dagger P_jU(t_\epsilon),\qquad
0\le F_j(s)\le I,\qquad \sum_jF_j(s)=I.
\tag{38.1}
$$

For every real unit $u\in E$, all five probabilities descend to the unit
rays of $E_J$, and their internal complex matrices are

$$
\begin{aligned}
p_j(s;Du)&=\zeta(u)^\dagger M_j(s)\zeta(u),\\
M_j(s)&=\frac12\begin{pmatrix}
|\xi_{j,+}|^2&\xi_{j,+}\overline{\xi_{j,-}}\,\bar g e^{-i\delta s}\\
\overline{\xi_{j,+}}\xi_{j,-}\,g e^{i\delta s}&|\xi_{j,-}|^2
\end{pmatrix},\\
0&\le M_j(s)\le I_2,\qquad \sum_jM_j(s)=I_2.
\end{aligned}
\tag{38.2}
$$

In particular the actual event $j=N$ has

$$
M_N(s)=\begin{pmatrix}
(1+1/\sqrt{17})/4&\bar g e^{-i\delta s}/\sqrt{17}\\
g e^{i\delta s}/\sqrt{17}&(1-1/\sqrt{17})/4
\end{pmatrix},\qquad 0<|g|<1.
\tag{38.3}
$$

It is nonconstant on unit polar rays. With the second nonnegative setting
$s_1=\pi/(2\delta)$ the same event gives a genuinely noncommuting pair:

$$
[M_N(0),M_N(s_1)]_{++}=\frac{2i|g|^2}{17}\ne0.
\tag{38.4}
$$

Both also fail to commute with $\operatorname{diag}(a,b)$. Thus they are
neither scalar nor solely spectral functions of the passive frequency
operator. Noncommutativity alone makes no assertion of measurement
incompatibility for these unsharp effects.

Proof. From (37.3), the four vectors in (37.5) are real orthonormal,
$Al_\pm=-a_\pm r_\pm$, $Ar_\pm=a_\pm l_\pm$ with $a_+=a,a_-=b$,
and $Jl_\pm=-r_\pm$, $Jr_\pm=l_\pm$. This proves the coordinate
relations in Definition 37.2 using precisely the polar factor of §36.
Since the zero mode is orthogonal to $u$, the physical read probability
at a deterministic time $t$ is

$$
|e_j^TU(t)Du|^2
=(e_j^TO(t)u)^2
=\bigl(\operatorname{Re}(\xi_j^\dagger W(t)\zeta)\bigr)^2.
\tag{38.5}
$$

The phase multiplying the $j$th coordinate in $D$ disappears in its
absolute square. Use the elementary identity
$(\operatorname{Re}w)^2=|w|^2/2+\operatorname{Re}(w^2)/2$ inside
(38.5). In $w^2$, the only time frequencies are $2a,2b,a+b$.
By (37.8)–(37.9),

$$
\gamma(2a)=\gamma(2b)=\gamma(a+b)=0.
\tag{38.6}
$$

Consequently their average vanishes exactly, for every $\zeta$ and every
$s$. The remaining $|w|^2/2$ has diagonal frequency zero and off-diagonal
frequency $\pm\delta$; expanding it gives (38.2). Multiplying $\zeta$
by any $e^{i\theta}$ leaves this quadratic form unchanged. Positivity,
normalization and the upper bounds follow either from the average of
nonnegative read probabilities for every unit $\zeta$, or directly from
(38.1) and the real isometry (37.6). This also proves validity for every
physical input in (38.1), although the ray statement concerns the
specified real $E$, not all physical rays in $\mathbb C^5$.

The spectral projectors of $C$ give the source weights

$$
h_+^2=\frac{1+1/\sqrt{17}}2,\quad
h_-^2=\frac{1-1/\sqrt{17}}2,\quad
h_+h_-=\frac2{\sqrt{17}}.
\tag{38.7}
$$

These are $r_{N,+},r_{N,-}$ in the existing mode-weight table
[MR, proof of Theorem 4.1, (4.3)][MR], with the signs fixed by (37.5).
Indeed the $NN$ entry of $(C-b^2I)/(a^2-b^2)$ is the first expression;
the complementary projector gives the second and the chosen positive
first components give the sign of the product. Since $\xi_N=(h_+,h_-)^T$,
(38.7) proves (38.3).

For completeness no exact cancellation has removed its cross term.
The ratio $r=a/b$ satisfies
$r^2=(21+5\sqrt{17})/4$, hence $3<r<4$. Therefore

$$
0<\frac\delta{2a}<\frac12,\qquad
1<\frac\delta{2b}<\frac32,\qquad
0<\frac\delta{a+b}<1.
\tag{38.8}
$$

A factor $(1+e^{i\pi x})/2$ vanishes exactly when $x$ is an odd integer;
none of (38.8) is one. Thus $g\ne0$. The first factor has modulus
$\cos(\pi\delta/(4a))$ strictly between zero and one; all others have
modulus at most one, so $|g|<1$.

The diagonal entries of $M_N$ differ by $1/(2\sqrt{17})$, so it is
nonconstant. Write its off-diagonal entry at zero as
$c=\bar g/\sqrt{17}$. At $s_1$ that entry is $-ic$.
The $++$ commutator entry is $c(i\bar c)-(-ic)\bar c=2i|c|^2$,
proving (38.4). Its commutator with $\operatorname{diag}(a,b)$ has
$+-$ entry $(b-a)c e^{-i\delta s}\ne0$. All waits and event rules are
fixed independently of $u$ and use only the original permissions. ∎

## 39. Resolved records, actual outputs and a sharp leakage interval

**Theorem 39.1 (The same protocol does not give the full polar instrument).**
For every setting $s\ge0$ and physical density $\rho$, put
$\widehat\rho=D^\dagger\rho D$. The resolved branch probabilities,
unnormalized physical outputs and label marginals are exactly

$$
\begin{aligned}
p_{\epsilon j}&=\tfrac18
\operatorname{tr}(P_jO(t_\epsilon)\widehat\rho O(t_\epsilon)^T),\\
\mathcal I_{\epsilon j}(\rho)&=\tfrac18P_jU(t_\epsilon)\rho
U(t_\epsilon)^\dagger P_j=p_{\epsilon j}P_j,\\
p_j&=\sum_\epsilon p_{\epsilon j},\quad
\mathcal I_j(\rho)=p_jP_j,\quad
\mathcal I(\rho)=\sum_jp_jP_j,\quad
\sum_{\epsilon,j}p_{\epsilon j}=1.
\end{aligned}
\tag{39.1}
$$

Every positive branch outputs its original physical basis state $P_j$.
Every run Stops and there is no discarded or failure mass. The full
resolved record does not descend to $E_J$ rays, even though the five-label
marginal in (38.2) does. For real polar inputs even the label-marginal
physical output maps $\mathcal I_j$ are constant on internal rays, since
they equal $p_jP_j$. This is a valid measure-and-prepare instrument with
physical output $\mathbb C^5$; it does not assert output closure on the
same internal polar carrier. In fact, for each $s$, take

$$
x_s=O(-s)e_N,\qquad y_s=Jx_s.
\tag{39.2}
$$

These are real unit vectors in one polar ray, and the single resolved
record with $\epsilon=000,j=N$ has probabilities $1/8$ and $0$.
The total variation distance of their resolved record laws is therefore
at least $1/8$. The wait $s$ occurs only for $\epsilon=000$, so the same
obstruction holds if the complete record retains the selected wait but
omits the literal seed. The negative exponent in (39.2) only specifies
two admissible test inputs; it is not an executed inverse or a preparation.

The dark-line mass of the actual nonselective output, in the $D$ frame,
is exactly

$$
\ell_s(\rho)=\operatorname{tr}(R_0D^\dagger\mathcal I(\rho)D)
=\frac{p_2+p_5}{2}\in[0,1/2].
\tag{39.3}
$$

If $P\widehat\rho P=\widehat\rho$, then $p_2=p_5=\ell_s(\rho)$ and
the sharper, attainable interval is

$$
\lambda_-\le\ell_s(\rho)\le\lambda_+,\qquad
\lambda_\pm=\frac18\left(1\pm
\sqrt{\frac{9+8|g|^2}{17}}\right),\qquad
0<\lambda_-<\lambda_+<\frac14.
\tag{39.4}
$$

In particular every polar-supported input leaks positive mass under this
protocol. The two branches $j=2,5$ have dark fraction $1/2$ individually;
$j=N,3,25$ have dark fraction zero. Projecting the nonselective output
back to $DE_{\mathbb C}$ would leave mass $1-\ell_s(\rho)$ and is a
different operation.

Proof. Unitarity and the complete rank-one read give (39.1). This is the
same first-read/reset identity used in [MR, Theorem 2.1][MR] and
[SC, §9.3][SC]: the positive branch state is $P_j$, independent of the
input. The correspondence is the same five original modes, wait $U(t)$,
first outcome $j$, independent seed $\epsilon$ and immediate Stop.
Subsequent allowed feedback, if appended while preserving the
record, is an input-independent suffix kernel conditional on these
first outcomes; it cannot erase their recorded separation.

Since $J$ commutes with $O(s)$, (39.2) gives
$O(s)x_s=e_N$ and $O(s)y_s=Je_N\perp e_N$. This proves the stated
record probabilities, the event lower bound on total variation, and
failure of resolved ray descent. More generally each compressed
seed-label effect is nonzero real rank one on $E$ and hence cannot
commute with a complex structure: an invariant one-dimensional real
range would have to contain both $v$ and $Jv$. Here
$Pe_N,Pe_3,Pe_{25}$ are nonzero and
$Pe_2=Pe_5=f/\sqrt2$, so this applies to every seed-label effect.

Only $R_0$'s mode-$2$ and mode-$5$ diagonal entries are nonzero, each
$1/2$. Taking the trace of (39.1) proves (39.3) for all physical inputs,
including ones outside the polar support. On the supported subspace,
$O(t)$ preserves $E_{\mathbb C}$ and the two coordinate functionals
$e_2^T,e_5^T$ agree there. Thus $p_2=p_5$, and
$p_2+p_5$ is the randomized read quadratic form for the real vector $f$.

To obtain its exact spectrum, the $Y$-block singular vectors in (37.5)
can be computed on the ordered basis $(f,e_3)$, where

$$
B_E=\begin{pmatrix}\sqrt2&1\\\sqrt2&0\end{pmatrix},\qquad
B_E^TB_E=\begin{pmatrix}4&\sqrt2\\\sqrt2&1\end{pmatrix}.
\tag{39.5}
$$

Its spectral projectors, with the same eigenvalues $a^2,b^2$, give

$$
q_+^2=\frac{1+3/\sqrt{17}}2,\qquad
q_-^2=\frac{1-3/\sqrt{17}}2,\qquad
q_+q_-=-\sqrt{2/17}.
\tag{39.6}
$$

The squared weights are twice $r_{2,+},r_{2,-}$ (also twice
$r_{5,+},r_{5,-}$) in [MR, (4.3)][MR], because $Pe_2=Pe_5=f/\sqrt2$.
The sign follows from the orientation in (37.5): writing
$v_+=(\cos\alpha,\sin\alpha)$ and
$v_-=(\sin\alpha,-\cos\alpha)$ gives $0<\alpha<\pi/4$, since the
first diagonal entry of $C$ exceeds the second and $C_{12}>0$.
Hence $q_+>0$ and $q_-<0$.
Because $\zeta(f)=-i(q_+,q_-)^T$, (38.2) and
$\ell_s=(p_2+p_5)/2$ show that for real unit $u\in E$,

$$
\ell_s(Duu^TD^\dagger)=\zeta(u)^\dagger L_s\zeta(u),\quad
L_s=\frac14\begin{pmatrix}
q_+^2&q_+q_-\bar g e^{-i\delta s}\\
q_+q_-g e^{i\delta s}&q_-^2
\end{pmatrix}.
\tag{39.7}
$$

Its trace is $1/4$, its squared diagonal difference is $9/(16\cdot17)$,
and four times the squared off-diagonal modulus is
$8|g|^2/(16\cdot17)$. The two eigenvalues are exactly (39.4).
Since $0<|g|<1$, their stated strict bounds follow. Each is attained by
an internal unit eigenvector, whose inverse under $\zeta$ is an allowed
real test input in $E$. The real symmetric operator of (39.7) has these
eigenvalues each twice; its physical complex-linear extension on
$E_{\mathbb C}$ has the same extrema. Spectral decomposition therefore
extends the sharp bounds to every physical supported density, not only
real pure inputs. Finally the per-branch dark fractions and projected
mass follow directly from $|z^Te_2|^2=|z^Te_5|^2=1/2$. ∎

## 40. The scope of the partial complex representation

**Definition 40.1 (The represented interface and the remaining bridge).**
The represented interface consists of the real polar input rays, the
family of five-label probability marginals (38.2), their event sums, and
passive waits. Its input correspondence is $u\mapsto\zeta(u)$, its
passive transport is $O(t)|_E\mapsto W(t)$, and its event effects are
$M_j(s)$. Mixtures of these internal ray states use the usual positive
trace-one $2$-by-$2$ matrices by affine extension. This interface does
not identify the full retained records or physical branch outputs with
an instrument on the same $E_J$ carrier.

A full same-carrier operational representation would have to preserve
the originally retained records, their probabilities, actual output
support and legal continuations for the entire native menu. Theorem
39.1 obstructs it for this randomized protocol: its resolved record
separates one internal ray and its output leaves $DE_{\mathbb C}$ with
uniform positive mass on supported inputs. Independently, the immediate
complete read in [QR, (36.3)–(36.5)][QR] already separates one polar ray
with total variation one. Averaging events does not remove that legal
native test. Even the outputs $P_N,P_3,P_{25}$, which remain inside the
support, are the original physical rank-one states, not replacement
instruments inferred from their effects. No assertion excludes other
encodings or different output carriers under separately proved contracts.

The source-specific consequence in Theorems 38.1 and 39.1 is the joint
finite positive construction, survival of the actual $a-b$ cross term,
the noncommuting $N$-event pair, and the sharp full-label/record/output
relations including (39.4). The general random-time mechanism is from
[BKS][BKS]; the fixed spectral decomposition and polar factor are from
[SO][SO], [SC][SC], [MR][MR] and [QR, §36][QR]. Effect-span membership,
density of an orbit and an infinite-time dephasing limit are not used
as operational attainability arguments here. These consequences are
`repo-derived` source-relative deductions, without a claim of worldwide
priority or exhaustive literature exclusion.

The full quantum-origin problem still requires a common state, effect,
instrument, composition and reference interface, of the kind explicitly
assumed in [QR, Definitions 20.2 and 34.1][QR]. This construction starts
from the physical $\mathbb C^5$/Born model, its coherent waits and its
rank-one instruments; it does not derive those assumptions. It supplies
no physical preparation, exact timing technology, independent phase
reference, empirical realization or resource-cost equivalence. Nor does
it instantiate the relativistic hypotheses of Moretti–Oppio or the
observable-wise dynamical correspondence of Niestegge discussed in
[QR, §36][QR]. The finite probability representation above leaves
these mathematical and empirical bridges unresolved.

[QR]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md
[SO]: AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md
[SC]: AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md
[MR]: RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md
[BKS]: ../../../Library/Quantum/boixoknillsomma2009randomization.md

## 追加锚（本行以下为增补区）

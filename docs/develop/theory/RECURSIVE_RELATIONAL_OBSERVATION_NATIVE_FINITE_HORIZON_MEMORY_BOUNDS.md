# Recursive Relational Observation: Native Finite Horizon Memory Bounds

## 1. Original source and complete classical memory

**Definition 1.1 (source and observation premises).** The source is the original complex native system of [III145–148][III] and [XI1.1–1.4][XI]. Its configuration space and carrier are

$$
E=\{q\subseteq\{1,\ldots,9\}:q\text{ has no adjacent occupied sites}\},
\qquad |E|=89,\qquad \mathcal K=\mathbb C^E.
$$

Retain its original $26+63$ decomposition, fixed exterior bits, and unique actual ready
$q_0=q_{\rm r}=\{3,7\}$. Put

$$
x=\varphi^{-1}=(\sqrt5-1)/2,\quad y=\sqrt x,\quad
\zeta=e^{3\pi i/5},\quad
Q_*=\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix},\quad
K_j=\zeta[I+(\zeta-1)\mathcal P_j].
\tag{1.1}
$$

The original projections $\mathcal P_j$, all their singleton blocks, and the full positive unit pulses $K_j$ are unchanged. In particular $\mathcal P_0=n_1$, and address $1$ acts by $Q_*$ when its two neighbours are zero. The prefix menu is $\mathsf W_{11}=\{0,\ldots,10\}^{<\infty}$ and the external post-read menu is $\mathsf W_7=\{0,\ldots,6\}^{<\infty}$, both including the empty word. Concatenation is chronological, so $K_{aj}=K_jK_a$.

The programme $\mathsf T(a)$ executes $a$ and then the original terminal. The programme $\mathsf R(a,f)$ executes $a$, reports $I=b_9(Q_-)$ with $Q_+=Q_-$, applies the original positive-branch pure update $M_I\psi/\|M_I\psi\|$, executes the external word $f$ independently of the report, and uses that same terminal. Its literal report is

$$
W(Q)=(b_{-1},\ldots,b_8)(Q)\in\{0,1\}^{10}.
\tag{1.2}
$$

Assume the original ideal zero-failure process, coherent execution, Born terminal law and original read/update contracts, for example as supplied by [XI6.1–6.2][XI]. Every actual archive retains its original causal kernel and the conditional sufficiency required there. All original terminal labels, failure, refusal, stop and alarm coordinates remain in the readable law; zero ideal mass does not remove them. No arbitrary preparation, reset, fork, hidden-path reader, new archive algorithm or additional control is included in these premises.

**Definition 1.2 (one original positive word and its phase).** Set

$$
q_1=\{1,3,7\},\quad w_*=W(q_1)=1010100010,\quad
g=0^5 1^5,\quad c=xy=x\sqrt x,\quad d=x-x^2,
$$

and define

$$
\theta=\arccos(-d)\in(0,\pi),\qquad z=e^{2i\theta},\qquad
p_n=\frac{1-\operatorname{Re}z^n}{2}=\sin^2(n\theta),\quad n\ge0.
\tag{1.3}
$$

The word $g$ consists of five original positive calls at address $0$ followed by five at address $1$; $g^n$ costs exactly $10n$ such calls. Its fifth-power identities are the endpoint reflections already supplied by [V15, §§3.1 and 4.1–4.3][V15]. They abbreviate those five actual calls and do not authorize negative or fractional physical calls. The two-dimensional subspace used below is an invariant subspace of the full source, not a replacement configuration space or a new preparation.

**Definition 1.3 (closed finite stochastic comparator).** For an integer $S\ge1$, a comparator has at most $S$ possible complete persistent states. After padding unused states, its response to the repeated block and terminal event has the form

$$
q_n=\alpha P^n b,\qquad
\alpha\in\Delta_S,\qquad P\in[0,1]^{S\times S},\quad
P\mathbf1=\mathbf1,\qquad b\in[0,1]^S.
\tag{1.4}
$$

Here $\alpha$ is a probability row and $b$ is a column of terminal-event probabilities. All information affecting future kernels or terminal reports is included in the state: source and controller memory, programme position, counters, clocks, rereadable archives, retained randomness and any retained exact phase. An inaccessible passive record can be omitted only if it does not affect those future kernels or reports. Fresh independent innovations can be integrated into the kernels. Retained correlated randomness must satisfy the same closure condition; its effect cannot be treated as a fresh independent innovation merely by renaming it.

The per-address kernels and report kernel are fixed within each comparator. For a native comparator with kernels $P_0,P_1$, the row convention gives $P=P_0^5P_1^5$; allowing every stochastic $P$ in (1.4) enlarges this class. A read at the start of $\mathsf R(\emptyset,g^n)$ may change the comparator's initial distribution; arbitrary $\alpha$ already includes it. The externally supplied symbols are only the original requests. Neither the integer $n$, the whole future programme nor the elapsed index is an additional free input to a kernel or report rule. A time-dependent rule is permitted only when its controlling information is included in the finite closure.

Arbitrary fixed real entries of $\alpha,P,b$ are allowed, even when their effective or physical implementation has not been supplied. The coefficients may be designed for a chosen horizon, but the same triple is used at every index in that horizon. The theorem is uniform over these designs. A probability distribution on $S$ states can vary continuously; no identification of its possible beliefs with $S$ deterministic predictions is made. This is the persistent-information convention of [PhaseBoundary350.1][PB] specialized to original symbols.

**Definition 1.4 (finite phase data and cutoff).** For a unit complex number $z$ that is not a root of unity, let

$$
\delta_M(z)=\min_{1\le r\le M}|1-z^r|>0\qquad(M\ge1).
\tag{1.5}
$$

For $0\le\varepsilon<1/2$, choose an integer $k\ge0$ satisfying

$$
c_k=4^{-k}\binom{2k}{k},\quad
r_k=\frac{2k+1}{2k+2},\quad
a_k=c_k(r_k/2-\varepsilon)>0,\quad L=2k+1.
\tag{1.6}
$$

One definite choice is $k=\lfloor(2-4\varepsilon)^{-1}\rfloor$: indeed $k+1>(2-4\varepsilon)^{-1}$ and $r_k/2=1/2-1/[4(k+1)]>\varepsilon$. Define

$$
\begin{aligned}
D_{\rm ph}(S,\varepsilon,z)
 &=\frac{16S}{\delta_{LS}(z)^2}
   +\frac{2(1+\varepsilon)}{\delta_{2k+2}(z)},\\
N_{\rm ph}(S,\varepsilon,z)
 &=1+\left\lfloor\frac{D_{\rm ph}(S,\varepsilon,z)}{a_k}\right\rfloor,\\
D_{\rm nat}(S,\varepsilon)
 &=16S\,70^{LS}+2(1+\varepsilon)70^{k+1},\\
N_{\rm nat}(S,\varepsilon)
 &=1+\left\lfloor\frac{D_{\rm nat}(S,\varepsilon)}{a_k}\right\rfloor.
\end{aligned}
\tag{1.7}
$$

The subscript $\rm nat$ refers only to the specific original phase in Definition 1.2. The finite phase formula also permits certified positive lower bounds for the two displayed gaps, with the corresponding enlarged cutoff. For rational $\varepsilon$, the native cutoff uses only integer and rational arithmetic; no numerical test for irrationality or unknown minimum transition probability is an input.

## 2. Effective original-call exposure

**Theorem 2.1 (uniform finite native window).** Under Definitions 1.1–1.4, the original probability of the unconditional terminal event $W=w_*$ is $p_n$ for both $\mathsf T(g^n)$ and $\mathsf R(\emptyset,g^n)$. In the latter programme $I=0$ almost surely and the original pure update leaves ready unchanged.

For every integer $S\ge1$, every $0\le\varepsilon<1/2$, every closed comparator (1.4), and every integer $m\ge0$, there is an index

$$
n\in\{m,\ldots,m+N_{\rm ph}(S,\varepsilon,z)-1\}
\quad\text{with}\quad |p_n-q_n|>\varepsilon.
\tag{2.1}
$$

The same assertion holds with $N_{\rm nat}$ in place of $N_{\rm ph}$. Thus in the first window some original programme with at most $10(N_{\rm nat}-1)$ positive gate calls fails this tolerance; $\mathsf R$ additionally has its one original initial read. In a window starting at $m$, the total gate-call bound is $10(m+N_{\rm nat}-1)$, including the actual $g^m$ prefix. Each index specifies a separately requested original programme with one terminal, not several terminal observations in one run.

For any specified full readable joint laws $\mu_n,\nu_n$ of source and comparator, with the original terminal event among their coordinates,

$$
\operatorname{TV}(\mu_n,\nu_n)\ge |p_n-q_n|.
\tag{2.2}
$$

The failing index may depend on the comparator. The conclusion is $\forall(\alpha,P,b)\,\exists n$ in the stated bounded window, not a common failing index for all comparators and not a finite-sample identification procedure.

**Proof.** First identify the actual source response. On the ordered pair $(e_{q_0},e_{q_1})$, addresses $0,1$ preserve every other bit. Site $2$ is zero, so their projections restrict respectively to $\operatorname{diag}(0,1)$ and $Q_*$. These restrictions have no coupling to the other $87$ configurations. The supplied reflection identity $K_j^5=2\mathcal P_j-I$ gives

$$
K_0^5=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\qquad
K_1^5=\begin{pmatrix}d&2c\\2c&-d\end{pmatrix},\qquad
U=K_g=\begin{pmatrix}-d&2c\\-2c&-d\end{pmatrix}.
\tag{2.3}
$$

The relation $x+x^2=1$ gives $d^2+4c^2=1$, with $c>0$. Consequently

$$
U^ne_{q_0}=\cos(n\theta)e_{q_0}-\sin(n\theta)e_{q_1}.
\tag{2.4}
$$

The original terminal distinguishes these two configurations by $b_1$, so its Born pushforward gives (1.3). At the initial read $b_9(q_0)=0$, $M_0e_{q_0}=e_{q_0}$, and the zero-mass $I=1$ branch remains zero without a normalized state. Both addresses also preserve $b_9$. The original unconditional read/terminal formula therefore gives the same $p_n$. This uses the source and update premises, not a change of terminal or postselection.

Next make the phase separation effective. The trace $-2d=4-2\sqrt5$ is the existing reflection-pair trace of V15. For $z=e^{2i\theta}$,

$$
t=z+z^{-1}=34-16\sqrt5,\qquad
t'=34+16\sqrt5,\qquad t+t'=68,\quad tt'=-124.
$$

Since $-2<t<2$, $z$ is nonreal. Moreover $\mathbb Q(t)=\mathbb Q(\sqrt5)$ is real, and $z$ solves $Z^2-tZ+1=0$, so its degree over that field is two. Its minimal polynomial over $\mathbb Q$ is therefore

$$
F(Z)=(Z^2-tZ+1)(Z^2-t'Z+1)
 =Z^4-68Z^3-122Z^2-68Z+1.
\tag{2.5}
$$

Its conjugates are $z,z^{-1},R,R^{-1}$, where $R>1$ and
$R+R^{-1}=t'<70$. In particular $R<70$, and $z$ is not a root of unity: a conjugate of a root of unity would again have modulus one. For every integer $r\ge1$, the algebraic integer $1-z^r$ has nonzero integer norm. Hence

$$
\begin{aligned}
1&\le |N_{\mathbb Q(z)/\mathbb Q}(1-z^r)|\\
 &=|1-z^r|^2(R^r-1)(1-R^{-r})
 <|1-z^r|^2\,70^r.
\end{aligned}
$$

This proves the finite, strict separation

$$
|1-z^r|^2>70^{-r},\qquad
\delta_M(z)^2>70^{-M}.
\tag{2.6}
$$

Here the integer norm is the ordinary product over all four embeddings; the expanding real conjugate bounds the two factors not on the unit circle.

We now prove the quantitative stochastic step inside this derivation. For any row-stochastic $S\times S$ matrix $P$ and $|w|=1$ with
$\gamma=\min_{1\le r\le S}|1-w^r|>0$, the induced complex maximum norm satisfies

$$
\|(I-wP)^{-1}\|_{\infty\to\infty}\le\frac{8S}{\gamma^2}.
\tag{2.7}
$$

To see this, normalize a nonzero complex column $v$ to $\|v\|_\infty=1$ and rotate it by a global phase so $v_{i_0}=1$ at a maximum coordinate. Put $e=(I-wP)v$ and $\eta=\|e\|_\infty$. Nonnegative stochastic rows imply $\|P^j\|_{\infty\to\infty}=1$. Finite telescoping gives

$$
v-w^tP^tv=\sum_{j=0}^{t-1}(wP)^j e,\qquad
\operatorname{Re}\bigl(w^t(P^tv)_{i_0}\bigr)\ge1-t\eta.
\tag{2.8}
$$

For each $t=0,\ldots,S$, the row $(P^t)_{i_0,\cdot}$ is a probability row, so some coordinate $i_t$ satisfies
$\operatorname{Re}(w^t v_{i_t})\ge1-t\eta$; at $t=0$ choose $i_0$. Since $|v_{i_t}|\le1$,

$$
|v_{i_t}-w^{-t}|^2\le2t\eta.
$$

Two of the $S+1$ chosen indices coincide, say $i_a=i_b$ with $0\le a<b\le S$. Thus

$$
\gamma\le |1-w^{b-a}|
 =|w^{-a}-w^{-b}|
 \le\sqrt{2a\eta}+\sqrt{2b\eta}\le\sqrt{8S\eta}.
\tag{2.9}
$$

Undoing normalization yields
$\|v\|_\infty\le8S\|(I-wP)v\|_\infty/\gamma^2$ for every $v$. The square matrix is injective and therefore invertible; this proves (2.7). Positivity of the rows, rather than a lower bound on a particular edge, is the reason the estimate is uniform. There is no irreducibility, aperiodicity, normality or mixing assumption. This is a quantitative finite version of the maximum-coordinate mechanism behind PhaseBoundary350.4. General power-bounded resolvent estimates and stochastic eigenvalue regions are mature background [Szehr, Theorem IV.1][SZ] and [Johnson–Paparella, Theorem 2.1][KP]; (2.7) supplies the particular finite phase bound used here without a distance to an unspecified spectrum.

Write $\langle u\rangle=N^{-1}\sum_{n=m}^{m+N-1}u_n$, for $N\ge1$. For a nonzero integer $j$, the finite geometric identity and (2.7) imply

$$
\left|\left\langle q_n z^{jn}\right\rangle\right|
 \le\frac{16S}{N\min_{1\le r\le S}|1-z^{jr}|^2}.
\tag{2.10}
$$

Indeed the sum before division by $N$ is

$$
z^{jm}\alpha P^m[I-(z^jP)^N](I-z^jP)^{-1}b.
$$

The probability row $\alpha P^m$ has norm one as a functional on the maximum norm, $\|b\|_\infty\le1$, and the square bracket has norm at most two. Negative $j$ have the same gap by complex conjugation. The scalar geometric sum similarly gives

$$
|\langle z^{jn}\rangle|\le\frac{2}{N|1-z^j|}.
\tag{2.11}
$$

All these are finite sums and hold uniformly in the starting index $m$.

For the full error range, put $t_n=\operatorname{Re}z^n$, so $p_n=(1-t_n)/2$. The Laurent expansion

$$
t_n^r=2^{-r}\sum_{j=0}^r\binom rj z^{(r-2j)n}
\tag{2.12}
$$

has nonnegative coefficients with sum one. Odd powers have no constant term; the constant coefficient of power $2k$ is $c_k$. In particular $c_{k+1}=c_kr_k$. Applying (2.10)–(2.11) to (2.12), and writing $\Delta=\delta_{2k+2}(z)$, gives

$$
\begin{aligned}
|\langle q_nt_n^{2k+1}\rangle|
 &\le\frac{16S}{N\delta_{LS}(z)^2},\\
|\langle t_n^{2k+1}\rangle|&\le\frac2{N\Delta},\\
|\langle t_n^{2k+2}\rangle-c_{k+1}|&\le\frac2{N\Delta},\\
\langle t_n^{2k}\rangle&\le c_k+\frac2{N\Delta}.
\end{aligned}
\tag{2.13}
$$

For the first bound every occurring $|j|\le L$ and every $r\le S$ give $|jr|\le LS$. For each other bound all nonzero frequencies have absolute value at most $2k+2$. Deleting a constant coefficient only reduces the sum of the remaining absolute coefficients; the last estimate also holds when $k=0$ and its remainder is exactly zero.

Suppose $|q_n-p_n|\le\varepsilon$ at every index in this window. Since $|t_n|^{2k+1}\le t_n^{2k}$, we have

$$
|\langle(q_n-p_n)t_n^{2k+1}\rangle|
 \le\varepsilon\langle t_n^{2k}\rangle.
$$

On the other hand,

$$
\langle(q_n-p_n)t_n^{2k+1}\rangle
 =\langle q_nt_n^{2k+1}\rangle
  -\tfrac12\langle t_n^{2k+1}\rangle
  +\tfrac12\langle t_n^{2k+2}\rangle.
$$

Use the triangle inequality and (2.13) to isolate its positive constant coefficient. The result is

$$
\frac{c_{k+1}}2
 \le\varepsilon c_k
 +\frac{16S}{N\delta_{LS}(z)^2}
 +\frac{2(1+\varepsilon)}{N\Delta},
\qquad N a_k\le D_{\rm ph}(S,\varepsilon,z).
\tag{2.14}
$$

Taking $N=N_{\rm ph}$ contradicts this last inequality. This establishes (2.1) uniformly over all initial rows, stochastic entries and report probabilities. It also explains the higher odd power: the first power alone has $r_0/2=1/4$, whereas $r_k/2$ tends to $1/2$. No infinite-time limit is substituted for (2.14).

Finally (2.6) gives $D_{\rm ph}<D_{\rm nat}$, so $N=N_{\rm nat}>D_{\rm ph}/a_k$ also contradicts (2.14). This proves the entirely numerical native cutoff. The source correspondence (2.3)–(2.4) gives its original call count. For (2.2), take the measurable joint event whose terminal coordinate is $w_*$; its two masses are $p_n,q_n$. The variational definition of total variation yields the inequality. This last step retains the entire specified joint law and does not assert that agreement on its terminal projection implies joint or path agreement. A common failing index is impossible in this permissive class: for each fixed index $n$, the one-state report probability $b=p_n$ matches that index exactly. $\square$

## 3. Continuation length, state count and bits

**Corollary 3.1 (necessary memory for a finite continuation window).** Fix $0\le\varepsilon<1/2$ and an admissible $k$ as in (1.6). If a comparator agrees within $\varepsilon$ on $H\ge1$ consecutive indices of this native family, then

$$
H a_k\le D_{\rm ph}(S,\varepsilon,z)
 <16S\,70^{LS}+E_\varepsilon,
\qquad E_\varepsilon=2(1+\varepsilon)70^{k+1}.
\tag{3.1}
$$

In particular, with

$$
A_\varepsilon=2\,70^L,\qquad
C_\varepsilon=1+\frac{16+E_\varepsilon}{a_k},
$$

one has

$$
H<C_\varepsilon A_\varepsilon^S,\qquad
S>\frac{\log(H/C_\varepsilon)}{\log A_\varepsilon}.
\tag{3.2}
$$

If all persistent information is encoded in $B$ classical bits, so $S\le2^B$, and $H>C_\varepsilon$, then

$$
B>\log_2\!\left(\frac{\log(H/C_\varepsilon)}{\log A_\varepsilon}\right).
\tag{3.3}
$$

These are nonoptimal necessary bounds, with no matching simulation or optimal rate asserted.

**Proof.** The assumption gives (2.14) with $N=H$, proving (3.1). For $S\ge1$, $S\le2^S$ and $A_\varepsilon^S\ge1$, so

$$
16S\,70^{LS}+E_\varepsilon
 \le(16+E_\varepsilon)A_\varepsilon^S
 <a_k C_\varepsilon A_\varepsilon^S.
$$

This proves (3.2). Substitute $S\le2^B$ and take logarithms when $H>C_\varepsilon$ to obtain (3.3).

The closure hypothesis is essential to these implications. An uncharged counter feeding $p_n$ to the decoder would reproduce the terminal curve with one nominal state, but violates (1.4). Conversely, a genuine finite counter with states $0,\ldots,H-1$, transition $j\mapsto\min(j+1,H-1)$, initial state zero and report table $b_j=p_j$ matches the first $H$ indices exactly. This is the already supplied finite-table construction of PhaseBoundary350.9; it confirms that the new necessary bound does not exclude finite-window fits when their memory grows.

Nor is this a claim of optimal exposure time. If $\xi=\theta/\pi$ and integers $a,h$ with $h\ge1$ are chosen, the deterministic $h$-cycle with report table $b_j=\sin^2(\pi a j/h)$ has response $\sin^2(\pi a n/h)$. The derivative bound $|\sin^2 u-\sin^2 v|\le|u-v|$ gives error at most $\pi n|\xi-a/h|$. Thus an accurate rational approximation can shadow the curve for a long finite window. This elementary comparison is also the mechanism used for the rational-cycle baseline in [Lumbreras–Ma–Thompson–Gu, Appendix D.2][LM]. It is compatible with the coarse upper exposure bound, not a matching lower construction for (3.2). $\square$

## 4. Supplier correspondence and mathematical boundaries

**Definition 4.1 (scope of the quantitative relation).** The relation established here connects three fixed data: the original allowed continuation word, the finite phase gaps against periods at most $LS$, and the complete persistent state count. Its consumer is the original terminal boundary. The new `repo-derived` synthesis is the finite residual estimate (2.7)–(2.10), the finite weighted error inequality (2.14), and their effective native arithmetic and original-call specialization. Reflection identities, irrational rotation, binomial coefficients, geometric sums, algebraic-integer norms and total-variation projection are reused mathematical tools within that derivation, with no worldwide priority claim.

The sharp all-time $1/2$ floor is already [PhaseBoundary350.7–350.9][PB]. Its one-state constant $1/2$ response attains that error, so the present strict range cannot be extended to $\varepsilon=1/2$ in the permissive terminal comparison class. PhaseBoundary351.9–351.10 also supplies qualitative capacity divergence by compactness. The present relation additionally supplies the numerical finite programme window, uniform in the comparator coefficients. [III143.2–143.5][III] supplies a different finite prefix/continuation table obstruction with a size-dependent margin, without quantitative word lengths or a common error tolerance. It is not replaced by a claim that arbitrary continuation response tables must have the homogeneous form (1.4).

The finite phase dependence is substantive. For any prescribed $H$ and positive tolerance, a sufficiently small positive irrational $\theta/\pi$ makes $\sin^2(n\theta)\le\varepsilon$ for $0\le n<H$, so a one-state constant-zero comparator succeeds on that window. This follows from $|\sin(n\theta)|\le n\theta$. Hence no cutoff uniform over all irrational phases follows from state count and error alone. The fixed native phase avoids this ambiguity through (2.5)–(2.6).

An ordinary mixing argument would require additional data. For example $P_t=\left(\begin{smallmatrix}1-t&t\\t&1-t\end{smallmatrix}\right)$, $0<t<1/2$, has decaying eigenvalue $1-2t$, arbitrarily near one. For every fixed $N$, $(1-2t)^N$ tends to one as $t$ tends to zero. There is consequently no common ordinary mixing time even in this two-state primitive family. Formula (2.7) controls the nonresonant oscillatory response directly. The repository's [FiniteStochasticMixing][MIX], including its private minorization construction and `primitive_convergence`, supplies matrix-dependent primitive mixing; [FiniteOrbitPeriodBound][ORB] supplies deterministic finite-orbit periodicity. Neither such premise is imposed on (1.4). Pinned mathlib's [stochastic-matrix submonoid][ML] supplies the standard positivity and power closure used here. These are mathematical source correspondences, not a new Lean certification of Theorem 2.1.

The repository's [Kingman pointwise theorem][KING] concerns an actual finite measure, measure-preserving transformation and nonnegative integrable subadditive cocycle. Its [finite greedy-block bound][BLOCK] also gives explicit finite estimates while retaining bad-start and final-strip costs. Without those actual cost hypotheses and a common source mapping, neither statement supplies a numerical $S,\varepsilon,z$ horizon for this terminal experiment. No assertion that all existing suppliers are merely asymptotic is needed.

For primary literature, [Szehr, Theorem IV.1][SZ] bounds power-bounded matrix resolvents in an arbitrary matrix norm, with spectral separation retained; a Hilbert-contraction estimate is not automatically an induced-maximum-norm estimate for every stochastic matrix. [Johnson–Paparella, Theorem 2.1][KP] describes the stochastic eigenvalue region and its unit-circle roots. [Lumbreras–Ma–Thompson–Gu, Lemma 16 and Proposition 19][LM] treats conditioned FRDN predictions through normalized substochastic powers and residue-class limits; its Appendix D.2 discusses finite fitting and rational-cycle shadowing. [Zonnios–Boyd–Binder, Theorems 1–3][ZBB] compares exact generators agreeing on every finite output word, through paired transfer spectra and exact memory bounds. Those inspected statements have these distinct contracts; none is used as an asserted fixed-native approximate-terminal cutoff. This bounded source correspondence is not a global nonexistence or originality claim.

Finite quantum dimension, the $89$ configuration labels, finite algebraic formula size and $S$ complete classical persistent states are different quantities. The invariant corner in (2.3) does not make the source a classical two-state chain, and a continuous belief distribution does not give its comparator infinitely many mutually exclusive persistent states. Conversely, admitting fixed exact real stochastic entries does not supply their precision cost, fair-bit implementation or physical realization. The lower bound allows those entries to strengthen its comparison class.

The result supplies no continuous-history matching algorithm, acquisition of actual cut laws, implementation of arbitrary archives, noise-uniform long-time source stability or finite-sample certification. Terminal discrepancy lower-bounds the full specified readable-joint discrepancy; terminal matching has no converse implication. No hidden-trajectory error bound is obtained. Spatial recovery, lawful acquisition and mutual recoverability of space, continuation, boundary and memory require their own source correspondences; the finite continuation/memory relation here is one conditional part of that programme.

[III]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[XI]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md
[V15]: AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md
[PB]: RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md
[MIX]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing.lean
[ORB]: ../../../D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean
[ML]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Stochastic.lean
[KING]: ../../../D5/S3/Analytic/Probability/KingmanPointwise.lean
[BLOCK]: ../../../D5/S3/Analytic/Probability/KingmanEstimates.lean
[SZ]: https://arxiv.org/html/1305.7208v2 "Oleg Szehr, Eigenvalue estimates for the resolvent of a non-normal matrix"
[KP]: https://arxiv.org/html/1611.06970v2 "Charles R. Johnson and Pietro Paparella, A matricial view of the Karpelevič Theorem"
[LM]: https://arxiv.org/html/2608.19779v2 "Josep Lumbreras, Hailan Ma, Jayne Thompson and Mile Gu, An Irreducible Quantum Advantage in Aligning World Models with Reality"
[ZBB]: https://arxiv.org/html/2412.12812v2 "Magdalini Zonnios, Alec Boyd and Felix C. Binder, Quantum generation of stochastic processes: spectral invariants and memory bounds"

## 追加锚（本行以下为增补区）

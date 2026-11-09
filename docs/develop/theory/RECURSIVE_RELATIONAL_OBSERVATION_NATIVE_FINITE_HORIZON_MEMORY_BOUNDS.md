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

## 5. Fixed native logarithms and polynomial phase separation

**Definition 5.1 (native logarithmic constants).** Retain exactly Definitions 1.1–1.4, including the $89$-configuration source, the alternating positive word $g^n=(0^5 1^5)^n$ and the unconditional terminal event $W=w_*$. All logarithms below are natural. Let $R>1$ be the expanding real conjugate in (2.5), and put

$$
\begin{aligned}
\phi&=2\theta-2\pi\in(-\pi,0),&
\ell_z&=i\phi,&\ell_{-1}&=i\pi,\\
\chi&=\max\{\log R,|\phi|,1\},&
C_0&=18\cdot3!\cdot2^3\cdot128^4\log16
     =864\cdot128^4\log16,\\
\kappa&=\frac{C_0\pi\chi}{16},&
K_0&=2^{40}=1099511627776.
\end{aligned}
\tag{5.1}
$$

Here $d=\sqrt5-2>0$ in (1.3), so $\pi/2<\theta<\pi$ and the displayed interval for $\phi$ follows. The values $\ell_z$ and $\ell_{-1}$ are fixed determinations of the logarithms of $z$ and $-1$. They are arithmetic proof data and change neither the word nor its physical calls.

**Theorem 5.2 (polynomial separation for the original phase).** With the constants (5.1), one has $0<\kappa<K_0$, and for every integer $r\ge1$,

$$
|1-z^r|>\frac2\pi r^{-\kappa}
            >\frac1{2r^{K_0}}.
\tag{5.2}
$$

Consequently, for every integer $M\ge1$,

$$
\delta_M(z)>\frac2\pi M^{-\kappa}
                 >\frac1{2M^{K_0}},\qquad
\delta_M(z)^2>\max\left\{70^{-M},\frac1{4M^{2K_0}}\right\}.
\tag{5.3}
$$

The source-specific application (5.2)–(5.3) is `repo-derived`. Its logarithmic-form supplier is the `literature-attested` main theorem of Baker–Wüstholz [BW93, printed pp.19–20 and §2][BW93] ([primary scan](https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0442/LOG_0005.pdf)); that general theorem is used inside the proof.

**Proof.** Reuse the degree-four minimal polynomial (2.5), its conjugates $z,z^{-1},R,R^{-1}$, the inequality $R<70$, and the non-root-of-unity conclusion in Theorem 2.1. Thus

$$
K=\mathbb Q(z,-1)=\mathbb Q(z),\qquad [K:\mathbb Q]=4,
\qquad z^r\ne1\quad(r\ge1).
\tag{5.4}
$$

For clarity about normalization, [BW93, pp.21–22][BW93] uses the relative projective height
$h_K(a_0:\cdots:a_t)=\sum_v\log\max_j|a_j|_v$, with local-degree powers in the absolute values. Its absolute logarithmic height is $h_K/4$ here. Since $z$ is an algebraic integer, finite places contribute zero to $h_K(1:z)$. Of the four archimedean conjugates, only $R$ has positive logarithm of its modulus; the conjugate pair on the unit circle has modulus one. Therefore

$$
h_K(z)=\log R,\qquad h_K(-1)=0,\qquad
h'_K(z)=\frac14\max\{h_K(z),|\ell_z|,1\}=\frac\chi4,
\qquad h'_K(-1)=\frac\pi4.
\tag{5.5}
$$

These are the modified heights used in the cited main theorem. In particular $\log R/4$ is the absolute height of $z$, and must not be substituted for $h_K(z)$ in (5.5).

For an integer $r\ge2$, put

$$
s_r=-\frac{r\phi}{2\pi}\in(0,r/2),\qquad
j_r=\left\lfloor s_r+\frac12\right\rfloor,\qquad
\Lambda_r=r\ell_z+2j_r\ell_{-1}=i u_r.
\tag{5.6}
$$

Then $|j_r-s_r|\le1/2$, so $|u_r|\le\pi$. Also $j_r\ge0$ and $2j_r\le r$: if $r=2a$, then $s_r<a$ gives $j_r\le a$; if $r=2a+1$, then $s_r<a+1/2$ again gives $j_r\le a$. Exponentiation gives $e^{\Lambda_r}=z^r$. Hence $\Lambda_r\ne0$ by (5.4).

The integer form $\mathcal L_r(X,Y)=rX+2j_rY$ is nonzero. With $g_r=\gcd(r,2j_r)>0$, its primitive integer coefficient pair has maximum absolute value $r/g_r$. The relative projective height is consequently

$$
h_K(\mathcal L_r)=4\log(r/g_r),\qquad
h'_K(\mathcal L_r)=\frac14\max\{h_K(\mathcal L_r),1\}
 =\max\{\log(r/g_r),1/4\}\le\log r.
\tag{5.7}
$$

Indeed primitive integer coordinates have maximum local norm one at every finite place, while the sum of the archimedean local degrees is four. The last inequality uses $r\ge2$ and $\log2>1/4$, and includes $j_r=0$.

The cited Baker–Wüstholz main theorem permits algebraic numbers different from $0,1$, fixed complex logarithms and an integer linear form whose value is nonzero. For $n$ logarithms in degree $D$ its constant is
$18(n+1)!n^{n+1}(32D)^{n+2}\log(2nD)$, with modified algebraic heights $D^{-1}\max\{h_K(\alpha),|\log\alpha|,1\}$ and form height $D^{-1}\max\{h_K(\mathcal L),1\}$. Apply it with $n=2$, $D=4$, $(\alpha_1,\alpha_2)=(z,-1)$, the fixed values $(\ell_z,\ell_{-1})$, and $\mathcal L_r$. All its exclusions and the nonzero-value hypothesis have been checked in (5.4)–(5.7). It gives

$$
\log|\Lambda_r|>
 -C_0\frac\chi4\frac\pi4\,h'_K(\mathcal L_r)
 \ge-\kappa\log r,\qquad
|\Lambda_r|>r^{-\kappa}.
\tag{5.8}
$$

This is the main fixed-logarithm theorem, rather than its separate crude principal-logarithm consequence with coefficient bounds at least $e$. No real-log specialization or additional independence hypothesis is inserted.

On $|u_r|\le\pi$, concavity of sine on $[0,\pi/2]$ gives

$$
|1-z^r|=2\sin(|u_r|/2)
 \ge\frac2\pi |u_r|=\frac2\pi|\Lambda_r|
 >\frac2\pi r^{-\kappa}.
\tag{5.9}
$$

The omitted exponent $r=1$ is elementary: by (2.5),

$$
|1-z|^2=2-(34-16\sqrt5)=16(\sqrt5-2)>1,
\tag{5.10}
$$

where $\sqrt5>33/16$ follows by squaring. Since $2/\pi<1$, this proves (5.2)'s first inequality also at $r=1$, with no logarithmic coefficient estimate at $\log1=0$.

For the integer enlargement, $\log R<\log70<5$, $|\phi|<\pi<4$ and $\log16<3$ imply $\chi<5$ and

$$
0<\kappa<3240\cdot128^4=869730877440
                <1099511627776=K_0.
\tag{5.11}
$$

The logarithmic inequalities can, for example, be obtained from the positive exponential series $e>8/3$, giving $e^3>16$ and $e^5>70$. Since $2/\pi>1/2$, (5.11) proves the second strict inequality in (5.2), including $r=1$. Taking the minimum over $1\le r\le M$ proves the first two bounds in (5.3); combining their squares with the original strict norm bound (2.6) proves its last bound. $\square$

## 6. Hybrid original-call exposure and polynomial capacity

**Definition 6.1 (two-gap arithmetic cutoff).** For every $S\ge1$ and $0\le\varepsilon<1/2$, choose any admissible $k,c_k,r_k,a_k,L$ from (1.6), and write $J=2k+2$. Define

$$
\begin{aligned}
D_{\rm BW}
 &=4\pi^2 S(LS)^{2\kappa}+\pi(1+\varepsilon)J^{\kappa},\\
D_{\rm int}
 &=64S(LS)^{2K_0}+4(1+\varepsilon)J^{K_0},\\
D_{\rm hyb}
 &=16S\min\{70^{LS},\,4(LS)^{2K_0}\}
   +2(1+\varepsilon)\min\{70^{k+1},\,2J^{K_0}\},\\
N_{\rm hyb}
 &=1+\left\lfloor D_{\rm hyb}/a_k\right\rfloor.
\end{aligned}
\tag{6.1}
$$

All these quantities depend on $(S,\varepsilon,k)$ and the fixed native phase; no comparator coefficient is an input. For rational $\varepsilon$, the definite choice $k=\lfloor(2-4\varepsilon)^{-1}\rfloor$ makes $N_{\rm hyb}$ an integer/rational arithmetic formula. The real exponent $\kappa$ is unnecessary for evaluating that formula. Effectivity here does not assert a useful computation cost for its very large integer powers.

**Theorem 6.2 (uniform hybrid window with the original consumer).** For every integer $S\ge1$, every $0\le\varepsilon<1/2$, every comparator $q_n=\alpha P^n b$ in exactly the complete class (1.4), every admissible $k$, and every integer $m\ge0$, there exists

$$
n\in\{m,\ldots,m+N_{\rm hyb}-1\}
\quad\text{such that}\quad |p_n-\alpha P^n b|>\varepsilon.
\tag{6.2}
$$

The arithmetic cutoff retains the pointwise comparisons

$$
N_{\rm ph}(S,\varepsilon,z)\le N_{\rm hyb}
                 \le N_{\rm nat}(S,\varepsilon).
\tag{6.3}
$$

The witness is an original $\mathsf T(g^n)$ or $\mathsf R(\emptyset,g^n)$ with $g^n=(0^5 1^5)^n$. It uses exactly $10n$ positive gate calls, hence at most $10(m+N_{\rm hyb}-1)$, including its actual $g^m$ prefix. Each requested programme has one original terminal; $\mathsf R$ additionally has its one original initial read. For any specified readable joint laws containing that terminal event, the same witness has total variation distance greater than $\varepsilon$.

**Proof.** Under agreement at every index of a window of length $N$, the already established stochastic inequality (2.14) gives $Na_k\le D_{\rm ph}$, uniformly in $\alpha,P,b,m$. No stochastic resolvent or weighted-moment argument is changed. Apply (5.3) separately at $M=LS$ and $M=J$. The first supplies the squared gap in $16S/\delta_{LS}^2$; the second supplies the unsquared gap in $2(1+\varepsilon)/\delta_J$. The original bound at the even index $J$ gives $\delta_J>70^{-J/2}=70^{-(k+1)}$. Therefore

$$
D_{\rm ph}<D_{\rm hyb}\le D_{\rm nat},\qquad
D_{\rm ph}<D_{\rm BW},\qquad
D_{\rm hyb}\le D_{\rm int}.
\tag{6.4}
$$

Since $N_{\rm hyb}a_k>D_{\rm hyb}$, agreement on the entire asserted window contradicts (2.14). Monotonicity of the floor function proves (6.3). Theorem 2.1 supplies the unchanged event probability for both original programmes, the $10n$ call identity and the total-variation projection (2.2). The failure index can depend on the comparator: the quantifier is $\forall(\alpha,P,b)\,\exists n$, with the stated uniform window, rather than a common failing index.

In particular the result still includes arbitrary fixed real stochastic coefficients, reducible, periodic and non-normal matrices. All retained controller, programme-position, counter, clock, seed, phase and rereadable-archive information is charged exactly as in Definition 1.3. There is no mixing, irreducibility or edge-probability premise, no deterministic-comparator restriction, and no extra time index supplied to the observer. The original initial read in $\mathsf R$ remains covered by the arbitrary initial row $\alpha$. $\square$

**Corollary 6.3 (necessary states and persistent register bits).** If a comparator in (1.4) agrees within $\varepsilon$ on $H\ge1$ consecutive native indices beginning at any $m\ge0$, then

$$
Ha_k\le D_{\rm ph}<D_{\rm BW},\qquad
Ha_k<D_{\rm hyb}\le A_\varepsilon S^{\nu_0}+E_\varepsilon,
\tag{6.5}
$$

where

$$
\nu_0=2K_0+1,\qquad
A_\varepsilon=64L^{2K_0},\qquad
E_\varepsilon=4(1+\varepsilon)J^{K_0},\qquad
C_\varepsilon^{\rm pol}=\frac{A_\varepsilon+E_\varepsilon}{a_k}.
\tag{6.6}
$$

Thus

$$
H<C_\varepsilon^{\rm pol}S^{\nu_0},\qquad
S>\left(H/C_\varepsilon^{\rm pol}\right)^{1/\nu_0}.
\tag{6.7}
$$

More precisely, when $Ha_k>E_\varepsilon$, put
$X=(Ha_k-E_\varepsilon)/A_\varepsilon>0$. Then

$$
S>X^{1/\nu_0},\qquad
S\ge\max\{1,\lfloor X^{1/\nu_0}\rfloor+1\}.
\tag{6.8}
$$

If all complete persistent information fits in an integer $B\ge0$ of classical bits, so that $S\le2^B$, one has

$$
B>\frac{\log_2(H/C_\varepsilon^{\rm pol})}{\nu_0},
\qquad
B>\frac{\log_2 X}{\nu_0}\quad(Ha_k>E_\varepsilon).
\tag{6.9}
$$

For the latter inequality the integral version is
$B\ge\max\{0,\lfloor\log_2 X/\nu_0\rfloor+1\}$. These bounds retain the elementary necessary inequalities (3.1)–(3.3) as well; either bound can be stronger at finite parameters.

**Proof.** Use (2.14) with $N=H$ and (6.4). Formula (6.1) gives
$D_{\rm int}=A_\varepsilon S^{\nu_0}+E_\varepsilon$. Since $S\ge1$, this is at most $(A_\varepsilon+E_\varepsilon)S^{\nu_0}$, proving (6.5)–(6.7). Subtract $E_\varepsilon$ when the stated difference is positive, and use integrality for (6.8). Substituting $S\le2^B$ gives both logarithmic inequalities and their strict integer rounding.

The sharper real-exponent version follows from the first inequality in (6.5): replace $\nu_0,A_\varepsilon,E_\varepsilon$ respectively by

$$
2\kappa+1,\qquad
4\pi^2L^{2\kappa},\qquad
\pi(1+\varepsilon)J^\kappa,
\tag{6.10}
$$

and define its corresponding $C$ by the same sum divided by $a_k$. The integer version is a convenient explicit certificate rather than an optimal exponent. If an original gate budget $G\ge10m$ covers every requested index from $m$ to $\lfloor G/10\rfloor$, the same inequalities apply with $H=1+\lfloor G/10\rfloor-m$; the initial read and terminal remain separately counted as above. $\square$

**Proposition 6.4 (pointwise protection and asymptotic order).** For each fixed $\varepsilon$ and fixed admissible $k$, the hybrid cutoff satisfies

$$
N_{\rm hyb}=O_{\varepsilon,k}(S^{2K_0+1}),
\qquad
N_{\rm hyb}\le N_{\rm nat}\quad(S\ge1).
\tag{6.11}
$$

A sufficient, deliberately conservative condition for strict improvement after integer rounding is

$$
LS\ge16K_0^2\quad\Longrightarrow\quad
N_{\rm hyb}<N_{\rm nat}.
\tag{6.12}
$$

This condition is not a least crossover or a useful practical exposure bound.

**Proof.** The polynomial bound follows from $D_{\rm hyb}\le D_{\rm int}$ and $a_k>0$; the pointwise bound is (6.3). To certify (6.12), set $M=LS\ge16K_0^2$. The elementary bound $\log M\le\sqrt M$ follows by minimizing $\sqrt t-\log t$ for $t\ge1$. Hence

$$
\log(4M^{2K_0})
 \le\log4+2K_0\sqrt M
 \le\log4+M/2<M\log70.
\tag{6.13}
$$

Here $M\ge16$ and $\log4<2< M/2$, while $\log70>1$. Thus $4M^{2K_0}<70^M$. Both sides are integers, so their difference is at least one. The first minimum in (6.1) consequently decreases $D_{\rm nat}$ by at least $16S$, and the second cannot increase it. Since $0<a_k\le1/2$, division by $a_k$ decreases the value inside the floor by more than one; (6.12) follows. The large certified exponent supplies an asymptotic order improvement over the exponential elementary cutoff, while the minimum retains its finite-parameter advantages. $\square$

## 7. The exact terminal-register comparison and its recovery boundary

**Definition 7.1 (terminal-curve state-register cost).** For an integer $H\ge1$ and fixed $0\le\varepsilon<1/2$, let

$$
\begin{aligned}
S^*_\varepsilon(H)
 &=\min\left\{S\in\mathbb N_{\ge1}:\ \exists(\alpha,P,b)\text{ as in (1.4)},\quad \max_{0\le n<H}|\alpha P^n b-p_n|\le\varepsilon\right\},\\
B^*_\varepsilon(H)&=\left\lceil\log_2 S^*_\varepsilon(H)\right\rceil.
\end{aligned}
\tag{7.1}
$$

The minimum is over the same block-response comparator and the same unconditional terminal event as Definitions 1.2–1.3. Its nonempty feasible set is supplied by the finite counter in Corollary 3.1. The full persistent state register is charged; fixed exact-real coefficients in the transition and terminal tables have the same convention as (1.4). Table description length and coefficient precision, their acquisition, computation and physical realization are additional resources not assigned a cost by (7.1). A retained archive, seed or clock that affects future kernels or reports remains part of the charged persistent state.

**Theorem 7.2 (logarithmic terminal-register bit order).** For the cost (7.1), each fixed $0\le\varepsilon<1/2$ and any fixed admissible $k$ satisfy

$$
\frac{\log_2(H/C_\varepsilon^{\rm pol})}{\nu_0}
 <B^*_\varepsilon(H)\le\lceil\log_2 H\rceil,
\qquad
B^*_\varepsilon(H)=\Theta_\varepsilon(\log H)
\quad(H\longrightarrow\infty).
\tag{7.2}
$$

For the asymptotic notation one may fix the definite $k$ in Definition 1.4 as a function of $\varepsilon$. This determines the bit order for precisely the terminal-curve contract (7.1); it does not determine a matching exponent for the necessary state count in (6.8).

**Proof.** Apply (6.7) to a minimizing comparator and set $B=B^*_\varepsilon(H)$, so $S^*_\varepsilon(H)\le2^B$. This gives the strict lower inequality. For the upper inequality reuse the original finite counter of Corollary 3.1 and [PhaseBoundary350.9][PB]: take states $0,\ldots,H-1$, initial state zero, transition $j\mapsto\min(j+1,H-1)$ and the fixed table $b_j=p_j$. Then $\alpha P^n b=p_n$ for $0\le n<H$, so $S^*_\varepsilon(H)\le H$. Its index is carried by its counted register, without an external free input $n$. This construction includes $H=1$ and $\varepsilon=0$.

For sufficiently large $H$, $\log_2(H/C_\varepsilon^{\rm pol})\ge\tfrac12\log_2 H$, while $\lceil\log_2 H\rceil\le2\log_2 H$ for $H\ge2$. These inequalities prove the stated order. The upper comparison is this same original terminal counter with a fixed horizon-dependent table. It supplies no per-address realization for every allowed stochastic $P$, full readable-joint approximation or conditional-history matching. In particular a sufficient workspace bound for a different recurrent approximation of a full joint law is not an upper bound used in this proof. The $H$ table entries and their description precision remain outside the cost (7.1). $\square$

**Definition 7.3 (reconstruction data beyond the terminal relation).** A reconstruction target specifies an admissible class $\mathcal X$ of actual source realizations with their permitted operations, an accessible observation map $O:\mathcal X\to\mathcal Y$, and a target relation $T:\mathcal X\to\mathcal Z$. Exact recovery requires a map $D$ satisfying $T=D\circ O$ on that class; usable recovery additionally requires an allowed acquisition and decoding realization with its stated resources. Mutual recovery of spatial, continuation, boundary and memory relations requires the corresponding maps in each asserted direction, with common source identity, operation domains and resource accounts.

Theorems 5.2–7.2 concern the fixed source of Definition 1.1 and the single terminal projection $p_n$ along its original positive words. Their lower-bound consumer is that projection; their upper-bound consumer is exactly (7.1). They do not specify reconstruction maps on a class of unknown actual sources, acquired cut laws or archives. Original ideal coherence, zero failure, Born readout, read/update and archive sufficiency remain the stated source assumptions. Agreement on this projection is not an asserted inverse of the full readable-joint projection. A sufficient joint-history construction, lawful acquisition of the required boundary data and source-preserving recovery maps remain additional mathematical requirements for the mutual-recovery target.

[BW93]: https://doi.org/10.1515/crll.1993.442.19 "A. Baker and G. Wüstholz, Logarithmic forms and group varieties, J. reine angew. Math. 442 (1993), 19–62; main theorem pp.19–20, heights pp.21–22; primary scan https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0442/LOG_0005.pdf"

## 追加锚（本行以下为增补区）

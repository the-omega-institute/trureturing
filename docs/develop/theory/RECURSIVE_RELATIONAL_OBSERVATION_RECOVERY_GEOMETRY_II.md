# Recursive Relational Observation: Recovery Geometry II

This is a same-topic continuation of [Recovery Geometry](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md). Its numbering continues after §35 of that volume. The original volume's definitions, hypotheses, results and open problems retain their original scopes. This volume is a mathematical reference input in the `generic-v1` format; Lean declarations remain the repository's mathematical truth source. The proofs below are ordinary mathematical proofs, without a claim of new Lean verification. Subsequent additions belong after the terminal append anchor.

## 36. One unknown digital path and its actual endpoint service

**Definition 36.1 (the promised source).** A source consists of an unknown integer $N\ge1$, cells at rooted distances $0,\ldots,N-1$, and a fixed matrix

$$
T=\begin{pmatrix}
a_0&b_0&&0\\
b_0&a_1&\ddots&\\
&\ddots&\ddots&b_{N-2}\\
0&&b_{N-2}&a_{N-1}
\end{pmatrix}\in\mathbb Q^{N\times N},
\qquad b_i>0,\qquad 0<T<I.
$$

The last inequalities mean positive definiteness of both $T$ and $I-T$. For $N=1$ there are no $b_i$. The source's state is $x\in\mathbb Q^N$, authentically prepared as $e_0$. Its native geometry is this rooted path with its coefficients and current cell values. Rooted distance identifies its cells; no manufactured cell identifiers, Euclidean positions or metric lengths are included.

The installed endpoint service has the following serial operations, on this same state and matrix.

| Operation | Actual successor | Declared output |
| --- | --- | --- |
| Read | $x$ | the literal rational $e_0^{\mathsf T}x$ |
| Tick | $Tx$ | the literal rational $e_0^{\mathsf T}Tx$ after the update |
| Hold | $x$, with source ticks prevented during the held interval | a fixed acknowledgement |
| Add$(u)$, when the input right is installed | $x+u e_0$, $u\in\mathbb Q$ | a fixed acknowledgement |

One may additionally declare a post-Add root readout; all results below include it by applying the Read formula to the successor. Acknowledgements contain no hidden metadata. There is no autonomous tick between serial operations. Hold permits arbitrarily long local processing without advancing the source. There are no coefficient reads, chosen-index impulse-response queries, size announcements or observable size/work/timing side channels.

**Assumption 36.2 (what the observations do not install).** Fixed-law and root binding, authentic unit-pulse preparation, the rational path/positive-link/strict-contraction class, exact signed rational serialization and nondestructive reads are installed premises. The observer has the actual source handle, call rights, storage backing and Hold control needed for its calls. Add, when used, has its own installed input right and supplied rational input. The public installation contains no source-dependent coefficient or size advice; a handle binds the endpoint without exposing such advice. Coefficient lengths, $N$, the spectral gap from either endpoint and the time for local calculation have no public upper bound. These premises concern an exact digital service; the transcript does not certify a physical instrument into this class.

**Definition 36.3 (passive moments and acquired time).** In a passive run only Tick advances the prepared state; Read and Hold may be interspersed, and Add is unused. For $j\ge0$ put

$$
x_j=T^j e_0,\qquad m_j=e_0^{\mathsf T}T^j e_0.
$$

Here $m_0=1$. The finite Time expression at passive epoch $k$ is the ordered list of the actual readouts $(m_0,\ldots,m_k)$: one initial Read and the return of each of the $k$ paid Ticks. The epoch counts source Ticks from the authentic preparation, not observer instructions, wall time, Hold duration or an arbitrary control journal.

**Definition 36.4 (finite blocks).** For $r\ge0$ let

$$
H_r=(m_{i+j})_{0\le i,j\le r},\qquad
K_r=[e_0,Te_0,\ldots,T^r e_0].
$$

The identity $H_r=K_r^{\mathsf T}K_r$ is the existing positive-moment Gram identity, instantiated here by symmetry of this actual $T$ and this prepared $e_0$. Thus the ordinary Gram rank and positivity results apply. There is no new moment-realization framework in this notation.

## 37. Earning the first flat block and recovering the native cells

**Lemma 37.1 (native triangularity).** For every source of Definition 36.1 and $0\le j<N$, $T^j e_0$ is supported on cells $0,\ldots,j$, and its coordinate at cell $j$ is

$$
\beta_j=\prod_{i=0}^{j-1}b_i>0,\qquad \beta_0=1.
$$

Consequently $K_{N-1}$ is invertible, $H_r$ is positive definite for $r<N$, and $H_N$ has rank $N$, equal to the rank of $H_{N-1}$.

**Proof.** The assertion at $j=0$ is the preparation. Multiplication by a tridiagonal matrix enlarges support by at most one cell. The new cell $j+1$ can receive a contribution only from cell $j$, so its value is $b_j\beta_j$. Induction proves the assertion. The first $N$ columns form a triangular square matrix with positive diagonal $\beta_j$. All shorter column families are independent. Apply the Gram identity in Definition 36.4; adding $T^N e_0$ to an already complete $N$-dimensional basis cannot increase the rank. $\square$

**Theorem 37.2 (unknown-size actual acquisition).** There is one exact endpoint protocol, independent of $N$ and of the unknown coefficients, that on every promised source terminates after exactly $2N$ actual Ticks and $2N+1$ scalar outputs. It determines $N$, the full native rooted matrix $T$ and its complete impulse law $(m_j)_{j\ge0}$. It uses no order advice, response oracle or source-size side channel.

**Proof.** Hold the prepared source and Read $m_0$. At stage $r=1,2,\ldots$, execute two source Ticks, recording their returned $m_{2r-1},m_{2r}$. Hold the source while constructing $H_r$ and testing singularity by exact rational elimination. Continue precisely when it is nonsingular. By Lemma 37.1 the first singular block is $H_N$. The observed prefix at that point is exactly $(m_0,\ldots,m_{2N})$ and the actual state is $T^{2N}e_0$.

The stopping block is a positive semidefinite Hankel extension with

$$
\operatorname{rank}H_N=\operatorname{rank}H_{N-1}=N,
\qquad H_{N-1}>0.
$$

Its shifted block also satisfies

$$
S_{N-1}=(m_{i+j+1})_{0\le i,j<N}
=K_{N-1}^{\mathsf T}T K_{N-1}>0.
$$

These are all the ordinary even-flatness and shifted-positivity hypotheses of [Main §137.13](RECURSIVE_RELATIONAL_OBSERVATION.md). Its flat-prefix uniqueness result applies to the actual symmetric positive-moment realization: use its scalar input space $U=\mathbb R$, truncation index $r=N$, input map $J(c)=ce_0$, normalization $m_0=1$, and the displayed blocks. It supplies the all-future moment uniqueness; we reuse that result. The explicit native reconstruction, which is stronger than a realization only up to a change of basis, is given in Proposition 37.3. It completes this protocol's output specification. All moment entries used were obtained along this single actual passive trajectory. $\square$

**Proposition 37.3 (the acquired orthogonal coordinates are the actual cells).** From the acquired prefix in Theorem 37.2 define, for $0\le j<N$, the unique monic polynomial $p_j$ of degree $j$ orthogonal to all smaller degrees for

$$
\langle p,s\rangle_m=\sum_{i,l}p_i s_l m_{i+l},
\qquad h_j=\langle p_j,p_j\rangle_m.
$$

In particular $p_0=1$ and $h_0=1$. The actual native coefficients are exactly

$$
a_j=\frac{\langle Xp_j,p_j\rangle_m}{h_j}
\quad(0\le j<N),\qquad
b_j=\sqrt{h_{j+1}/h_j}>0
\quad(0\le j<N-1).
$$

All these quantities are effectively recoverable as exact rationals from moments through $m_{2N-1}$. The additional $m_{2N}$ earns the unknown-tail termination certificate, rather than an additional native coefficient.

**Proof.** If $p_j=X^j+\sum_{i<j}c_i X^i$, its orthogonality equations are

$$
H_{j-1}(c_i)_{i<j}=-(m_{j+l})_{l<j}.
$$

They have a unique rational solution since $H_{j-1}>0$; the $j=0$ case needs no solve. The moment pairing is the actual Euclidean pairing after the map $p\mapsto p(T)e_0$.

The mature Jacobi/Gram--Schmidt construction is reused here. Its source-specific correspondence is the following exact identity:

$$
p_j(T)e_0=\beta_j e_j,\qquad h_j=\beta_j^2.
$$

Indeed, the vectors of degrees less than $j$ span exactly the first $j$ native cells by Lemma 37.1. Removing their orthogonal projections from $T^j e_0$ therefore leaves only its coordinate $\beta_j$ in cell $j$. Monicity preserves that coordinate. This proves the identity, including its positive orientation. Hence the normalized polynomial vector is the actual $e_j$, not a freely chosen orthogonal gauge. Taking its diagonal matrix entry gives the displayed $a_j$, and dividing successive squared native leading coordinates gives $b_j^2=h_{j+1}/h_j$.

For clarity, the coefficient-driven Jacobi supplier applies with $E=\mathbb R^N$, power basis $T^j e_0$ for $j<N$, the ordinary Euclidean inner product, and the characteristic recurrence $q$ of Proposition 37.4. Its coefficient multiplication is the actual $T$ in that power basis; the Hankel inner-product identity, strict positivity and self-adjointness hypotheses are exactly the ones just verified. Its monic orthogonal matrix has subdiagonal $1$ and opposite entry $h_j/h_{j-1}$; normalization gives the native symmetric entries above. No normalized-companion-trace-moment hypothesis is used.

The diagonal pairing uses degrees at most $2j+1\le2N-1$, and the link norms use degrees at most $2N-2$. Each link ratio is a positive rational square because the actual promised $b_j$ is rational and positive. In reduced form $A/C>0$, both coprime integers $A,C$ are squares: the prime exponents in a rational square are even. Integer square-root extraction on numerator and denominator, with exact squaring checks, therefore gives the unique positive rational root. This is an effective integer calculation, not an oracle for arbitrary real square roots. $\square$

**Proposition 37.4 (least recurrence and endpoint transfer).** The monic polynomial

$$
q(z)=z^N+\sum_{j=0}^{N-1}q_j z^j,\qquad
H_{N-1}(q_j)_{j<N}=-(m_N,\ldots,m_{2N-1})^{\mathsf T}
$$

is the characteristic polynomial of the actual $T$. Its degree is the least order of a monic recurrence holding for all nonnegative shifts of the impulse law. In particular

$$
m_{s+N}=-\sum_{j<N}q_jm_{s+j}\quad(s\ge0).
$$

The endpoint transfer is the rational function

$$
F_T(z)=e_0^{\mathsf T}(zI-T)^{-1}e_0
=\frac{\det(zI-T_{\{1,\ldots,N-1\}})}{\det(zI-T)}
=\sum_{j\ge0}m_jz^{-j-1}.
$$

The empty determinant in the numerator is $1$. In reduced form the monic denominator of $F_T$ is $q$, without cancellation. These are finite rational polynomial data, not an infinite response-query capability.

**Proof.** The solve is nonsingular. Its equations say that $q(T)e_0$ is orthogonal to each member of the basis $T^i e_0$, $i<N$, so $q(T)e_0=0$. It follows that $q(T)$ vanishes on every $T^i e_0$, since it commutes with $T$. Thus $q(T)=0$. No nonzero polynomial of degree below $N$ can annihilate $e_0$ by Lemma 37.1. Equivalently the coefficient multiplication on this basis is the companion-shaped matrix of $q$; the existing coefficient-multiplication characteristic-polynomial result gives $\det(zI-T)=q(z)$. The recurrence follows by multiplying $q(T)e_0=0$ by $e_0^{\mathsf T}T^s$.

If a smaller monic scalar recurrence held at every shift, its polynomial evaluated at $T$ on $e_0$ would again be orthogonal to all $T^i e_0$, hence zero, contradicting independence. The transfer formula is the cofactor identity and its Laurent expansion is the formal geometric-series identity at infinity. A cancellation would leave a smaller monic denominator; multiplication of the Laurent series by that denominator would yield a smaller all-shift recurrence, the same contradiction. The Hankel solve, cofactor polynomial arithmetic or path continuants compute the stated finite encoding from earned data. $\square$

## 38. The sharp tick horizon on every promised path

**Lemma 38.1 (a positive rational extra cell).** For every promised $N$-cell $T$, there is a promised $(N+1)$-cell matrix

$$
\widetilde T=
\begin{pmatrix}T&\varepsilon e_{N-1}\\
\varepsilon e_{N-1}^{\mathsf T}&1/2\end{pmatrix},
\qquad \varepsilon\in\mathbb Q_{>0},
$$

whose authentic root moments satisfy

$$
\widetilde m_j=m_j\quad(0\le j<2N),\qquad
\widetilde m_{2N}-m_{2N}
=\varepsilon^2\left(\prod_{i=0}^{N-2}b_i\right)^2>0.
$$

The empty product at $N=1$ is $1$.

**Proof.** Put $A=(T^{-1})_{N-1,N-1}>0$ and $C=((I-T)^{-1})_{N-1,N-1}>0$. Both are finite positive rationals. Choose a positive integer $L$ with $L^2>2\max(A,C)$ and set $\varepsilon=1/L$. The Schur complements in $\widetilde T$ and $I-\widetilde T$ are respectively $1/2-\varepsilon^2 A$ and $1/2-\varepsilon^2 C$, both positive. Hence $0<\widetilde T<I$; all adjacent links remain rational and positive.

Expand the root matrix-power entry as weighted closed walks, allowing diagonal stays. A walk that touches the extra cell must traverse the $N$ edges from the root and the $N$ edges back, requiring at least $2N$ steps. At length $2N$ there is exactly one such walk, with no stays or detours. Its weight is the displayed positive product. All walks avoiding the extra cell are precisely the old ones. $\square$

**Lemma 38.2 (the actual control observations).** After $t$ Ticks from authentic preparation and finitely many Add pulses $u_l$ applied at tick epochs $s_l\le t$, the actual state and root are

$$
x=T^t e_0+\sum_lu_lT^{t-s_l}e_0,
\qquad e_0^{\mathsf T}x=m_t+\sum_lu_lm_{t-s_l}.
$$

The same formula applies at every intermediate completed cut, with the pulses already applied there. Thus root observations made using at most $t$ Ticks depend only on moments through index $t$, even when Read, Hold and Add are adaptive.

**Proof.** Initially the formula has $t=0$ and no pulses. Tick multiplies every term by $T$ and increments $t$; Add appends the term with exponent zero; Read and Hold leave the state unchanged. Induction on the actual operations proves both identities. $\square$

**Theorem 38.3 (every-source lower horizon).** Let a protocol in the interface of Definition 36.1 be uniformly correct on all promised finite paths when it certifies source length or the full impulse law. For each individual $N$-cell source it cannot issue such an exact certificate at a completed cut with fewer than $2N$ source Ticks. The statement allows arbitrary finite adaptive rational Add pulses, Read and Hold calls and arbitrary local computation. It is a tick lower bound, not a minimum number of Read calls or a total-cost optimum.

**Proof.** Fix that source and the single extension of Lemma 38.1. For every $t<2N$ the two systems have the same moments through index $t$. Lemma 38.2 gives equal literal root outputs for the same command prefix, including a post-Add root output if declared. Fixed acknowledgements are equal as well. Inductively an adaptive protocol has identical observed histories, selects identical next inputs and commands, and makes the same stopping decision on both sources until the $2N$th Tick. Computation duration or physical size cannot distinguish them in the declared interface.

A certificate of the actual length $N$ is wrong on the extension, whose length is $N+1$. A certificate of the old full impulse law is wrong there by the strict difference at index $2N$. Uniform exact correctness therefore excludes early certification on the original source. This argument fixes the original source first; it is not merely a worst-case pair at each order.

For a zero-error randomized protocol, use a common random tape. Histories agree up to this horizon on every tape. A positive-probability early certification event on the first source is consequently a positive-probability error event on the fixed extension. Thus the same lower bound holds almost surely for any uniformly zero-error protocol. $\square$

Theorem 37.2 attains this horizon without Add. Its $2N+1$ scalar-output count is attained, not asserted minimal among all protocols. The extra cell is an indistinguishability witness, not a physical operation the observer must perform or an input right the observer acquires.

## 39. Four independently specified passive expressions

**Definition 39.1 (the passive domain and the four data types).** Consider all pairs $(T,k)$ satisfying Definition 36.1 and $k\ge2N$, with authentic passive state $x=T^k e_0$. Define the expressions as follows.

| Expression | Its own exposed mathematical data |
| --- | --- |
| Space | the actual rooted weighted path $T$ and current native cell vector $x$ |
| Time | the actual paid ordered root transcript $(m_0,\ldots,m_k)$ of Definition 36.3 |
| Boundary | the finite rational endpoint transfer $F_T$ of Proposition 37.4 and the current endpoint value $m_k$ |
| Memory | the least monic recurrence $q$, the initial values $\mu=(m_0,\ldots,m_{N-1})$, and the predictive state $w=(e_0^{\mathsf T}T^j x)_{0\le j<N}$ |

Memory's $w_j$ means the next $j$-tick autonomous root prediction from the current state, including $j=0$. It is a length-$N$ sufficient predictive state, not a stored complete journal. Boundary is a law and one current endpoint value, without a tick index. Space has native adjacency and a present field, without a journal. Time contains scalar observations and their order, without a coefficient list. None of these four mathematical data types contains a source handle or proof of the installed assumptions.

**Lemma 39.2 (a faithful passive phase mark).** On every promised source,

$$
1=m_0>m_1>m_2>\cdots>0,\qquad \lim_{j\to\infty}m_j=0.
$$

Given the exact finite encoding of $T$ and a rational $y$ promised to equal some actual passive $m_k$, a terminating exact procedure recovers the unique $k$ by enumerating $m_0,m_1,\ldots$ until equality. No uniform enumeration bound in $N$ alone is claimed.

**Proof.** The finite spectral theorem writes $m_j=\sum_\lambda c_\lambda\lambda^j$, with $0<\lambda<1$, $c_\lambda\ge0$ and $\sum c_\lambda=1$. This directly gives positivity, strict decrease and the limit. Equivalently $T^j(I-T)$ is positive definite, so $m_j-m_{j+1}>0$. Enumeration uses rational matrix-vector multiplication and exact equality. On the stated actual image it eventually reaches $k$ and cannot reach another index with the same value. Inputs outside that image are not given a terminating recognition algorithm by this assertion. $\square$

**Proposition 39.3 (effective recovery from each expression).** Each of the four expressions in Definition 39.1 effectively determines the same triple $(T,k,x)$ and hence each of the other three expressions. The procedures terminate on their declared actual images.

**Proof.** From Space read $T$ and $y=x_0$. Lemma 39.2 recovers $k$. Authentic passivity supplies $x=T^k e_0$; the given vector is that vector.

From Time take $k$ to be its length minus one. Run the block test of Theorem 37.2 on its initial segments, without issuing new source calls. Since $k\ge2N$, the first singular block occurs within the given list. Propositions 37.3–37.4 recover $T$. Compute $x=T^k e_0$.

From Boundary expand its encoded rational function formally at infinity to generate moments one at a time. These are local rational computations on a finite encoding; they are not newly acquired source readouts. The same first-flat-block test terminates at $N$ and recovers native $T$. Apply Lemma 39.2 to the given current endpoint value to recover $k$, and then compute $x$.

From Memory the degree of its least recurrence is $N$. Its $N$ initial moments and the monic recurrence generate every subsequent moment, in particular the finite prefix used in Theorem 37.2. This recovers native $T$. The number $w_0$ is the current $m_k$, giving $k$ by Lemma 39.2. Finally define

$$
\mathcal O_N=\begin{pmatrix}
e_0^{\mathsf T}\\ e_0^{\mathsf T}T\\ \vdots\\ e_0^{\mathsf T}T^{N-1}
\end{pmatrix}.
$$

Here $\mathcal O_N=K_{N-1}^{\mathsf T}$ because $T$ is symmetric, so it is invertible by Lemma 37.1. The existing finite observability inverse therefore applies exactly as $w=\mathcal O_N x$, $x=\mathcal O_N^{-1}w$. This also agrees with $T^k e_0$. Generic observability is reused, with native invertibility earned by triangularity.

Conversely $(T,k,x)$ computes every displayed expression: its recurrence and transfer by Proposition 37.4, its first $k+1$ moments and predictive entries by finite rational operations. Reconstructing the numeric Time list reproduces the actual paid list; it does not create observation provenance, replace the paid source calls or recover the timing of Read/Hold insertions. $\square$

**Proposition 39.4 (route agreement and passive Tick).** On the domain of Definition 39.1 every composition of the recovery procedures between these four expressions gives the direct result. Their transported Tick updates agree with the actual successor $(T,k+1,Tx)$. Explicitly, Time appends $m_{k+1}$, Boundary keeps $F_T$ and replaces its current value by $m_{k+1}$, Space replaces $x$ by $Tx$, and Memory keeps $(q,\mu)$ and updates

$$
w'_j=w_{j+1}\quad(0\le j<N-1),\qquad
w'_{N-1}=-\sum_{j<N}q_jw_j.
$$

For $N=1$ only the last formula is present.

**Proof.** Proposition 39.3 recovers the unique native $T$ and, by strict passive phase separation, the unique $k$ and $x$. Every route factors through those same data, proving route agreement. For the update, $w'_j=e_0^{\mathsf T}T^{j+1}x$. The first $N-1$ entries shift and the last is given by $q(T)=0$. The remaining updates are their actual definitions at epoch $k+1$, which remains in the passive domain. $\square$

This is a recovery statement about one rooted digital process. It does not obtain physical space from an abstract law, nor identify the path's cells with another source's states merely because that source also has moment notation.

## 40. Retaining the earned law and using the same source

**Definition 40.1 (installed predictive record).** At the end of Theorem 37.2 keep the same source held at its actual epoch $2N$. Retain the earned native $T$, recurrence $q$, initial vector $\mu$, and the current predictive state $w$. A concrete redundant implementation also retains a native vector $\widehat x$.

Initialize $\widehat x=T^{2N}e_0$ by local arithmetic on the recovered coefficients, and set $w=\mathcal O_N\widehat x$. The extra moments needed for this local calculation are predictions from the earned law, without extra source Ticks. Keep the actual source handle, call/input rights and backing separately. Serialize calls and commit the corresponding local state update before exposing the next completed cut. Hold is kept during installation and any processing that requires it. This defines an actual retained and callable observer configuration, conditional on Assumption 36.2.

The state operations on the record are:

| Command | Predictive update | Native-record update | Predicted declared output |
| --- | --- | --- | --- |
| Read | $w$ | $\widehat x$ | $w_0$ |
| Tick | the shift/recurrence of Proposition 39.4 | $T\widehat x$ | the new $w_0$ |
| Add$(u)$ | $w_j+u\mu_j$ for every $j<N$ | $\widehat x+u e_0$ | fixed acknowledgement; also the new $w_0$ if declared |
| Hold | $w$ | $\widehat x$ | fixed acknowledgement |

No operation on a scratch copy sends a command to the source. A hypothetical forecast and an actual call have different effects even when their arithmetic formulas coincide.

**Theorem 40.2 (complete finite common adaptive use).** For every promised source and every finite common adaptive continuation using the installed Read/Tick/Hold operations and, when authorized, rational Add inputs, the record of Definition 40.1 predicts all declared outputs exactly and remains synchronized with the corresponding actual native successor. At every completed cut

$$
\widehat x=x_{\mathrm{actual}},\qquad w=\mathcal O_Nx_{\mathrm{actual}}.
$$

The conclusion includes policies choosing their next command, rational input or stopping decision from earlier outputs, and includes a common random tape if the policy uses randomness. It supplies no additional call right and makes no claim that controlled state determines the prior control journal.

**Proof.** The invariant is true at installation because acquisition used exactly $2N$ passive source Ticks and the source was held while the record was computed. Read and Hold preserve it. For Add,

$$
(\mathcal O_N(x+u e_0))_j
=(\mathcal O_Nx)_j+u e_0^{\mathsf T}T^j e_0=w_j+u\mu_j.
$$

For Tick, $q(T)=0$ gives exactly the predictive shift of Proposition 39.4 for every $x\in\mathbb Q^N$, including controlled states. The retained native update is the identical multiplication by the recovered actual $T$. Therefore each operation gives both the declared output and the full native successor under the same rooted-cell correspondence, not merely an equal scalar trajectory.

Induct on the finite continuation. Equal prior outputs make the adaptive policy choose the same next command and input on source and predictor; the one-operation identities maintain the invariant. The same induction includes fixed acknowledgements, optional post-Add roots and common-tape choices. Serial commits exclude an unaccounted in-flight source step. This instantiates the already supplied finite-word transport principle with the actual acquisition cut and this native state invariant; it is not another generic word-transport theorem. $\square$

The predictor remains valid after controls. The passive phase recovery of §39 then has a different domain and cannot be invoked merely because the law is still known. Exclusive serialization, legal commands and successful calls are part of the installed service, not properties inferred by solving the Hankel equations.

## 41. Resources that coexist on the same run

**Convention 41.1 (encoding and arithmetic charges).** Encode a rational by its reduced signed numerator and positive denominator in binary, with framing. Let $B$ be the total encoding length of the $2N-1$ native coefficient words; in particular $B=\Omega(N)$. Storage means actual bits at the stated cut, in addition to the actual cells and links. Exact arithmetic is charged at the widths of its operands and results.

For the arithmetic-operation count, distinguish rational field operations from positive rational-square-root extractions on promised squares. There are $O(N^4)$ field operations and $N-1$ such extractions below. Counting each extraction as an arithmetic operation, with its own width-dependent implementation cost, the attained arithmetic count is $O(N^4)$. This convention does not treat a root extraction as a bounded number of field operations or as a unit-cost real oracle. If only field operations are counted, the separate extraction costs must still be added. Integer comparisons, gcd/serialization and control are also charged; no bit-cost bound independent of $B$ is asserted.

**Proposition 41.2 (source resources and exact traffic).** The source uses $N$ cells, $N-1$ links and $2N-1$ rational coefficient words. A direct simultaneous-buffer Tick uses $3N-2$ scalar multiplications and $2N-2$ scalar additions. The acquisition of Theorem 37.2 uses exactly

$$
2N\ \text{Ticks},\qquad 2N+1\ \text{scalar outputs},
$$

and hence $2N(3N-2)$ source multiplications and $2N(2N-2)$ source additions with this implementation. There is one initial Read and $N+1$ explicit Hold calls, one before that Read and one after each tick pair; their fixed acknowledgements and control traffic are added to the scalar traffic. The final held interval includes record installation. Pulse preparation, exact encoding, class/calibration/root assurance, actual rights/backing and Hold resources are additional setup costs on the same source.

**Proof.** Each diagonal entry contributes one product and each of the $N-1$ undirected links contributes two directed products, for $N+2(N-1)$. Summing the tridiagonal rows takes the total number of nonzero row terms minus the $N$ row outputs, namely $(3N-2)-N=2N-2$ additions. For $N=1$ this is one multiplication and zero additions. Two state buffers implement the simultaneous update without overwritten inputs. The acquisition call and output counts follow from its actual operation sequence. Preparing one pulse includes setting the other cells to zero; it is not obtained for free by inferring $m_0=1$. $\square$

**Proposition 41.3 (attained width and observer calculation).** There is a straightforward exact implementation of acquisition, native coefficient/recurrence decoding and current-record installation with $O(N^4)$ arithmetic operations in Convention 41.1 and a conservative maximum intermediate rational/integer width

$$
U=O\bigl(N^2B+N\log(N+1)\bigr).
$$

It tests the blocks by elimination, without a determinant oracle. This is an attained upper bound, not an optimal arithmetic or bit complexity.

**Proof.** Let $D$ be the product of the positive denominators of the actual native coefficients. This is a proof bound, not advance advice to the observer. Then $\log_2D\le B$, and every coordinate of $T^j e_0$ has denominator dividing $D^j$. Since $\|T\|<1$, these coordinates have absolute value at most $1$. Thus for $j\le2N$ the source coordinates and acquired moments have reduced width $O(NB+1)$.

The observer can compute $L$, the lcm of the acquired moment denominators, from the transcript. During stage $r$ its test uses only the lcm $L_r$ of the currently acquired denominators; $L_r\mid L$, so the final $L$ bounds all these computations without being supplied before the stop. Every denominator divides $D^{2N}$, so $L\mid D^{2N}$ and $\log_2L=O(NB)$. Every entry of every scaled block $LH_r$ is an integer of absolute value at most $L$. An $s$-row minor for $s\le N+1$ has, by Hadamard's bound, absolute value at most $s^{s/2}L^s$. Its binary width is

$$
O\bigl(s\log L+s\log(s+1)\bigr)\subseteq O(U).
$$

Fraction-free elimination uses these minors and exact ratios of preceding pivots. All positive-definite leading blocks have nonzero leading pivots; at the first singular block the last pivot is zero after the preceding $N$ positive pivots. Numerator products before exact division still have $O(U)$ width. One cubic elimination for each $r\le N$ costs $O(\sum_{r\le N}(r+1)^3)=O(N^4)$ operations. The counter $r$ and new storage are expanded as necessary; no unknown bound is tested or supplied first.

Solve the monic orthogonality equations separately for each $j<N$, and the recurrence equations once, using the same integer-scaled matrices and fraction-free augmented elimination. The right-hand sides are scaled moments of absolute value at most $L$, so their augmented minors obey the same bound. This costs another $O(N^4)$ field operations. Retain one common determinant denominator for the coefficients of each $p_j$. If that denominator is $\Delta_j$, the pairings for $h_j$ and $\langle Xp_j,p_j\rangle_m$ can be formed with common denominator $L\Delta_j^2$. Each numerator is a sum of at most $(j+1)^2$ products of two coefficient numerators and one scaled moment. Their widths, including the sums, are $O(U)$. This avoids multiplying unrelated denominators at every term. The resulting $a_j$, $h_j$ and ratios $h_{j+1}/h_j$ have the same conservative width. The $N-1$ positive rational roots of Proposition 37.3 also have width $O(U)$.

After native $T$ has been decoded, sparse multiplication computes $T^{2N}e_0$ and the additional locally predicted moments needed for $w$ in $O(N^2)$ operations. All exponents needed here are $O(N)$, so their reduced widths remain $O(NB)$. Alternatively constructing $\mathcal O_N$ and solving for $x$ uses at most cubic additional arithmetic with the same minor bound. Transfer polynomials can be computed by tridiagonal continuants in polynomial arithmetic: their coefficient widths are $O(NB+N\log(N+1))$ and a conservative cubic operation allowance suffices. These costs fit inside the displayed bound.

To make the extraction charge explicit, let $A(U)$ bound the bit cost of a rational field operation and $R(U)$ that of an integer square-root extraction at width $O(U)$. Numerator/denominator root tests cost at most $O(NR(U))$. Schoolbook arithmetic and binary-search integer roots give, conservatively, $A(U)=O(U^2)$ and $R(U)=O(U^3)$; faster routines are unnecessary. Thus one explicit bit upper bound for the algebraic decoding is

$$
O\bigl(N^4 A(U)+N R(U)\bigr),
$$

with gcd/lcm, comparisons, allocation, serialization, setup, source work and traffic charged in addition. The stated $O(N^4)$ arithmetic count therefore carries actual width charges and a specified rational-root subroutine. $\square$

**Definition 41.4 (a simultaneous storage layout).** One admissible implementation keeps all the following at the acquisition/installation cut. Its bound adds the stores; it does not select the cheapest component from incompatible implementations.

| Store or actual resource | Attained size or separate charge |
| --- | --- |
| Native source | $N$ cells, $N-1$ links, coefficient bits $B$ |
| Two source state buffers through acquisition | $O(N^2B+N)$ bits in total |
| Acquired $2N+1$-value transcript | $O(N^2B+N)$ bits |
| Elimination and polynomial scratch | $O(N^2)$ words, each at most $O(U)$ bits |
| Retained native law, recurrence, $\mu,w$ and optional redundant $\widehat x$ | $O(B+NU+N^2B+N)$ bits |
| Counters, parser, generic program and framing | their actual allocated bits, including $O(\log(N+1))$-bit indices |
| Class/calibration/root/initialization assurance and source-control installation | their actual preparation and backing resources |
| Handle, Read/Tick/Hold rights and optional Add right | their actual retained representation and backing resources |
| Output serialization buffers and any separately retained output copy | their actual simultaneous length $L_{\rm out}$ |

In particular the acquired transcript, scratch and installed record can coexist with both source buffers, the source coefficients and the rights. The bit contribution of these explicitly bounded numerical stores is at most

$$
O\bigl(B+N^2B+N^2B+N^2U+(B+NU+N^2B)+L_{\rm out}\bigr),
$$

plus the separately named program, assurance, rights and backing stores. If outputs are copied to another retained log, that copy is added. A shared backing may be counted once only when it is in fact shared. There is no universal numeric price assigned to an unimplemented physical calibration or assurance mechanism by this digital model.

**Proposition 41.5 (later use is not bounded-width use).** Every later actual call, predictor update, input transfer, phase enumeration and materialized Time expression pays its own cost and width. Finite $N$ and a finite law description do not imply bounded total memory or bounded literal output width, even with no controls.

**Proof.** At passive epoch $k$, denominators of native state coordinates divide $D^k$ and their reduced widths are at most $O(kB+1)$. A literal Tick return must serialize its actual reduced fraction. The case $N=1$, $T=(1/2)$ already has

$$
m_k=2^{-k},
$$

whose reduced denominator has $k+1$ binary digits. No bounded-width canonical rational output store can hold all these outputs. A complete separately materialized Time list through $k$ can require $\Theta(k^2)$ bits in this example. Holding only a current predictive state and streaming outputs has different storage behavior and does not materialize Time for free.

In the retained predictive implementation, Read uses the existing $w_0$ and pays literal output traffic; Add uses $N$ products $u\mu_j$ and $N$ additions for $w$, and its input width is not bounded by $B$; Tick uses $N$ recurrence products, $N-1$ additions and a shift/copy, all at current widths. If the redundant native vector is also kept, its actual native update work is added, including the direct Tick count of Proposition 41.2. The fixed-law moments needed for Add are retained $\mu$, without extra source queries. A policy may keep an arbitrarily long command/output journal; that is additional storage.

Lemma 39.2's enumeration performs as many local prediction steps and exact comparisons as the actual recovered phase requires, storing the current candidate and a growing index. There is no phase-independent bound in $N$ alone. If Space or Boundary is recovered from an already late epoch, this work is not part of the $2N$ acquisition horizon and cannot be charged as zero. Predictive-state arithmetic and optional journal generation use their own growing widths. $\square$

## 42. Countermodels at the hypothesis boundaries

**Counterexample 42.1 (controlled journals and durations are not passive phase).** Take the promised source $N=1$, $T=(1/2)$. At the acquisition cut $x=1/4$. One continuation is Hold, with zero additional Ticks. Another is Tick, returning $1/8$, followed by Add$(1/8)$, which restores $x=1/4$. The final native law and state, current Boundary and predictive Memory are identical, and all subsequent common endpoint behavior agrees. The tick count and the pulse history differ. Hence the current expressions do not invert arbitrary controlled journals, even after actual acquisition. Their differing intermediate outputs could distinguish the journals only if those outputs had actually been retained as a journal.

Inserting Read calls or Hold intervals likewise changes the observer journal without changing current source state. Varying a Hold interval changes elapsed physical duration without changing any declared output. An Add pulse that sets this scalar state to zero makes every subsequent autonomous root read zero, independent of how many later Ticks have occurred. These are admitted controlled operations; they do not contradict the strict-decrease result, whose authentic passive domain excludes them.

**Counterexample 42.2 (even complete endpoint behavior is not an arbitrary graph inverse).** Consider the rooted three-cell path

$$
T=\frac12 I+\frac18
\begin{pmatrix}0&1&0\\1&0&1\\0&1&0\end{pmatrix},
\quad
Q=\begin{pmatrix}1&0&0\\0&4/5&-3/5\\0&3/5&4/5\end{pmatrix}.
$$

The rational symmetric matrix

$$
T'=QTQ^{\mathsf T}
=\begin{pmatrix}
1/2&1/10&3/40\\
1/10&19/50&7/200\\
3/40&7/200&31/50
\end{pmatrix}
$$

has a triangle as its positive-link graph. Both matrices have eigenvalues $1/2$ and $1/2\pm\sqrt2/8$, so both satisfy $0<T<I$. Both are connected and root-cyclic; cyclicity of $T$ follows from Lemma 37.1 and is transported by $Q$. Thus the discrepancy is not a hidden disconnected component or a nonminimal realization.

Since $Qe_0=e_0$, the state map $x\mapsto Qx$ preserves the authentic preparation, Read, Add and Hold, and intertwines Tick. It consequently preserves the full adaptive endpoint behavior, with matching outputs at every finite continuation. In particular the complete transfer functions and all moments agree. The native path and triangle are different actual graphs. The triangle lies outside the path-class premise, showing why neither the finite stopping transcript nor even all endpoint behavior certifies that premise. A minimal symmetric realization up to an orthogonal root-fixing map is weaker than arbitrary native graph identification.

**Counterexample 42.3 (unrestricted signs are invisible).** If $S$ is diagonal with entries $\pm1$ and $S e_0=e_0$, then $STS$ has the same spectral order and root behavior as $T$, by the state map $x\mapsto Sx$. On a path its links are $s_i s_{i+1}b_i$. Flipping one nonroot sign changes at least one link but changes no endpoint impulse or root-control response. Positive links fix exactly the orientation used in Proposition 37.3; endpoint behavior alone does not recover unrestricted link signs.

**Counterexample 42.4 (an unauthenticated origin).** Even with known $T$, arbitrary preparation $x=0$ gives a zero autonomous endpoint sequence and no faithful passive clock. Preparing instead $T^r e_0$ makes a subsequent $k$-tick passive state equal to the authentic state at epoch $r+k$. Without the certified unit-pulse origin its present data cannot distinguish the elapsed $k$ from that shifted authentic phase. The authentic initialization is a load-bearing premise, not a consequence of transfer-function knowledge.

**Counterexample 42.5 (no uniform finite-prefix noise margin).** Compare $T_1=(1/2)$ with

$$
T_2=\begin{pmatrix}1/2&\varepsilon\\\varepsilon&1/2\end{pmatrix},
\qquad \varepsilon\in\mathbb Q,\quad0<\varepsilon<1/2.
$$

The second source is promised, has order two and moments

$$
m_j^{(2)}=\tfrac12\bigl((1/2+\varepsilon)^j+(1/2-\varepsilon)^j\bigr).
$$

For every fixed finite $J$, its moments through $J$ tend to those of $T_1$ as $\varepsilon\downarrow0$, while their orders differ. In particular the first block determinant is $0$ for $T_1$ and $\varepsilon^2$ for $T_2$. Hence the exact zero test used in §37 has no positive class-wide passive finite-prefix noise margin. The exact digital theorem supplies no noisy finite-precision rank instrument. This example does not assert a lower bound for every different noisy adaptive-control task; a noise model, gain/input limits and accuracy target would first have to be declared.

**Observation 42.6 (why the installed service matters).** A finite numeric transfer or recurrence does not contain a source handle. Two installations may have the same numerical law and current state while only one retains a callable endpoint capability. The numerical inverse cannot create the missing handle, backing, exclusivity or Add right. Likewise an arbitrary-index response service is stronger than the chronological Read/Tick interface: a computed prediction at an unobserved index is not a paid source observation. The acquisition and continued-use results preserve this distinction.

## 43. Supplier subtraction, correspondence and remaining scope

**Convention 43.1 (source status).** The repository references in this section are interpreted at the fixed public revision [5cec4fa83ae7bbb4e787c42606525db4cd11ed48](https://github.com/the-omega-institute/trureturing/tree/5cec4fa83ae7bbb4e787c42606525db4cd11ed48). `literature-attested` identifies mature supplied mathematics; `repo-derived` identifies the source-specific synthesis proved here, without asserting global literature priority. No `suspected-novel` priority assertion is needed.

| Supplier | Exact use and subtraction |
| --- | --- |
| [Main §§125–126 and 137.1–137.18](RECURSIVE_RELATIONAL_OBSERVATION.md) | Positive moments, finite cyclic realizations, support/contraction restrictions, flat-prefix uniqueness and its finite-prefix caveats are already supplied. Theorem 37.2 applies §137.13 to the actually earned even flat block. Generic positivity, realization and word inversion are not new results here. |
| [Recovery Geometry §§11–14 and 19–21](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) | Known continuous sampled/Gram and initial-state recovery, calibrated finite endpoint recovery and its spectral/Prony conditions remain in their original domains. The new service has unknown finite rational path size, actual chronological unit-pulse acquisition and exact native distance coordinates. It does not enlarge the old continuous, calibrated or fixed-apparatus scopes. |
| [Recovery Geometry §§34–35](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) | Common-source separation and compatible recovery routes are already required by §34; Proposition 39.4 verifies them for this actual image rather than claiming a new generic naturality principle. The periodic derivative and full-frequency Duhamel results in §35 have analytic field hypotheses, without an identified digital endpoint service. They supply no unknown-path acquisition premise here. |
| `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks` and its owning Scribe | Its finite-rank block reconstruction uses a specified order and nonsingular selected reference blocks; its arbitrary-candidate dimension consequence is a lower bound. It supplies finite realization algebra. It does not by itself turn that lower bound into a certified unknown native source size. Here the path's native triangularity and paid first flat block supply that missing correspondence. |
| `D5/S3/Constants/FiniteStieltjesOperatorRealization` and its owning Scribe | Finite positive-moment operator realization and associated spectral data are supplied. A finite abstract diagonal/atomic realization does not expose the actual native cells or execute the endpoint protocol. |
| `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde` and its owning Scribe | Atomic Hankel/Vandermonde algebra is supplied. Distinct atoms and nonzero weights/rank must have their own hypotheses; identities alone do not prove the native cyclicity required here. Lemma 37.1 earns it directly. |
| `D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial` and its owning Scribe | Monic orthogonal-basis triangularity, the positive norm-ratio Jacobi entries and the coefficient-multiplication characteristic polynomial are supplied, including the helper facts used by their proof. Proposition 37.3 supplies the actual power-basis/Hankel/self-adjoint correspondence and identifies its normalized vectors with native cells. The generic Jacobi proof is not duplicated as new content. |
| `D5/S3/Constants/Moments/GramSchmidtCoefficientField` and its owning Scribe | Its normalized companion-trace moment hypothesis is additional. Root spectral weights here are not assumed to be uniform trace weights, so that hypothesis is not imported merely because both constructions use Gram--Schmidt. The inner-product coefficient-driven supplier above has the hypotheses actually verified here. |
| G. Teschl, *Jacobi Operators and Completely Integrable Nonlinear Lattices*, [§2.5, equations (2.109)–(2.118), printed pp.42–43, and the finite-support paragraph on p.44](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf) | `literature-attested`: moment orthogonalization, norm/determinant reconstruction, Jacobi sign freedom and finite termination after $N$ atoms. In Teschl's indexing the finite-support condition is $C(N+1)=0$; our $H_N$ is that $(N+1)$-row block. His offdiagonal $a(n)$ corresponds to our $b_{n-1}$ and diagonal $b(n)$ to our $a_{n-1}$. Theorem 2.13 itself assumes nonfinite support and is not literally instantiated by this finite path. Its following finite-support paragraph already supplies finite Jacobi reconstruction; that is credited, not claimed as new. |
| M. Laurent and B. Mourrain, [*A generalized flat extension theorem for moment matrices*, arXiv:0812.2563v1, Theorem 1.2 and Corollary 1.3](https://arxiv.org/abs/0812.2563v1) | `literature-attested`: flat moment extension and positive representing-measure consequences. Here there is one variable, monomials $1,X,\ldots,X^N$, truncation $2N$, and the equal ranks of $H_N,H_{N-1}$. The existing Main theorem supplies the needed actual-realization consequence. No new general flat-extension theorem is asserted. |

**Correspondence 43.2 (the acquired-input bridge).** The proof uses the following single-source chain, with no hidden oracle substitution:

$$
\text{prepared actual }(T,e_0)
\ \xrightarrow{\ 2N\ \text{actual Ticks}\ }
(m_0,\ldots,m_{2N})
\ \xrightarrow{\ \text{exact local decoding}\ }
(N,T,q,\mu,T^{2N}e_0,w).
$$

The first arrow is a real chronological experiment in Definition 36.1 and Theorem 37.2. The second is arithmetic on earned data. Its native correspondence is $p_j(T)e_0=\beta_j e_j$, not equality of a symbol name or arbitrary choice of realization. The separately retained source installation and the invariant in Theorem 40.2 then justify future actual calls. Four-view recovery is restricted to authentic passive cuts; control transport is justified by its own invariant for arbitrary current vectors.

**Correspondence 43.3 (other public source contracts).** [Arithmetic Acquisition Return](RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_ACQUISITION_RETURN.md) supplies actually allocated arithmetic/growth services, paid records and return/call semantics in its own declared sources. [Finite-Start Predictive Memory §§19–23](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md) uses one stationary five-mode stochastic stream, observable returns, an earned categorical sample, and catalogue-risk or finite-horizon approximation conclusions. Its preparation is stationary, its sampling time is random and its five-state transition law is not the symmetric digital path law of §36. [Self-Generated Predictive Memory §§17–20](RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md) supplies normalized periodic startup-lasso laws, phase constraints and same-update predictive use for that original source. These are prior acquisition/retention and word-use suppliers, not missing generic principles to restate. None of the corresponding source ports, calibration inputs or alphabets is silently identified with this path's root service. The conjunction proved here concerns its native coordinates, unknown-size exact horizon and passive phase.

The public FIB addition, [Native Central Noise Green Stability §§26–35](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md), concerns the original free Brownian cylinder, its $L^2$ forcing/trace families, raw seam or one-face flux, approximation rank and original-clock resolvent/Green correspondence. Positivity, Schur complements and spectral/resolvent algebra are mature shared tools and receive no novelty claim here. The FIB analytic family does not install this digital source's finite rational order, authentic endpoint pulse, exact chronological port or source-call rights. No transport from its actual killed-cylinder law to Definition 36.1 has been proved or used.

The public `NoRepetitionSequenceUnambiguousDiscrimination` result assumes normalized equal-overlap pure states, injective product-state labels and unambiguous POVM measurements, and compares uniform success probabilities. Its Gram positivity does not supply a path impulse experiment: there is no state-preparation/measurement correspondence from those hypotheses to this actual root Tick service. The public Headley coordinate/kernel/doubling/elementary-cycle/two-group-induction and normalization results concern finite abelian groups, their cyclic prime-power coordinates, actual index-four reduction kernels, directed-difference cycles and strict exponent-sum induction; the odd-product visibility exposes a supplier for those group constructions. This manuscript has no such group operation or quotient-kernel realization assumption. Their reconstruction/transport conclusions therefore have no instantiated native-source bridge here. Common words such as rank, kernel, phase or recurrence are not that bridge.

**Conclusion 43.4 (retained application and exact limits).** The `repo-derived` application consists of the single paid unknown-size path experiment and native-cell correspondence in §37, the every-source positive-tail indistinguishability horizon in §38, the four independently specified passive expressions with effective phase and compatible routes in §39, and their actual retained common adaptive use and simultaneous resources in §§40–41. It reuses generic positive-moment/Jacobi reconstruction, observability and finite-word transport. The acquisition port, native correspondence, horizon witnesses, passive phase and installed predictor all refer to the same actual digital source. This source-relative synthesis is not a claim that inverse Jacobi theory, flatness or observability originated here.

The countermodels in §42 locate essential restrictions: positive-link rooted path membership, authentic origin and passive chronology; fixed exact law and literal rational access; and retained rights for operational use. No unknown-coefficient minimum-Read count, optimal total resource, minimum total memory or physical cost is proved. No arbitrary graph/sign inverse, controlled-journal/duration inverse, noisy finite instrument or membership certificate is supplied. These conclusions do not solve an old fixed-$G_{\rm gc}$/original-$Q$ task, identify this source with another author's common-moment source, derive physical space, reduce all sources to universal $\alpha/\beta$ generators or complete the unrestricted four-expression programme. Those tasks retain their own assumptions and missing realization/proof obligations.

## 追加锚（本行以下为增补区）
